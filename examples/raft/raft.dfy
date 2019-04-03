include "MissingLibrary.dfy"

/*
 * Translation of Diego Ongaro's TLA spec into JCF.
 * This translation: Jon Howell, CC-BY 4.0
 *
 * Original:
 * Copyright 2014 Diego Ongaro.
 * This work is licensed under the Creative Commons Attribution-4.0
 * International License https://creativecommons.org/licenses/by/4.0/
 */

// Not a state machine, just shared definitions
module context {

type ServerID(!new,==)

type Value(!new,==)

datatype LogEntry = LogEntry(term:int, value:Value)

type Log = seq<LogEntry>

datatype Message =
      RequestVoteRequest(
        source:ServerID,
        dest:ServerID,
        term:int,
        lastLogTerm:int,
        lastLogIndex:int)
    | RequestVoteResponse(
        source:ServerID,
        dest:ServerID,
        term:int,
        voteGranted:bool)
    | AppendEntriesRequest(
        source:ServerID,
        dest:ServerID,
        term:int,
        prevLogIndex:int,
        prevLogTerm:int,
        entries:seq<LogEntry>,
        commitIndex:int)
    | AppendEntriesResponse(
        source:ServerID,
        dest:ServerID,
        term:int,
        success:bool,
        matchIndex:int)

} // context

// XXX JCF We'd probably like to make the network module parameterized on Message, so
// it can be declared in the "trusted" area without depending on the
// algorithm's Message definition. But I'll put it here for now to avoid
// needing to add Generic<T>s to the one-weekend language.
// XXX JCF I'm giving you modules here; delete them for the one-weekend language version.
// Unfortunately, I'm a jerk and reuse names, so some manual mangling will be needed.
module network {
import opened MissingLibrary
import opened context

// This module defines no constants
datatype Constants = Constants()

// Raft's network model counts copies of outstanding messages in a bag. That's
// kind of silly, since duplicate and drop are allowed. The set model is
// simpler: 'duplicate' is implicit; in the absence of liveness constraints,
// 'drop' is 'never get around to delivering'; and of course 'deliver' is
// 'deliver and then never get around to delivering anymore'.
datatype Variables = Variables(messages:set<Message>)

predicate Init(k:Constants, v:Variables) {
    v.messages == {}
}

// In one atomic message step, a host may receive a message (or not), and send
// some set of messages. The caller specifies which host is being updated, and
// we confirm that the messages received and sent are addressed appropriately.
datatype NetworkActivity = NetworkActivity(receive:Option<Message>, send:set<Message>)

predicate ReceiveAndSend(k:Constants, v:Variables, v':Variables, host:ServerID,
    na:NetworkActivity)
{
    && (
        || na.receive.None?
        || (na.receive.value in v.messages && na.receive.value.dest == host)
       )
    && (forall m :: m in na.send ==> m.source == host)
    && v'.messages == v.messages + na.send
}

function NoActivity() : NetworkActivity {
    NetworkActivity(None, {})
}

} // network

module server {
import opened MissingLibrary
import opened context
import network
type NetworkActivity = network.NetworkActivity

datatype Constants = Constants(
    serverIDs:set<ServerID>,
    id:ServerID // My ID
)

datatype ServerState = Follower | Candidate | Leader

// Variables every follower maintains
// Jon folds 'server' and 'log' structs from Diego's TLA spec into a single 'follower' struct.
// This is intuitive in that the follower struct is what's used by nodes in the Follower state.
// It makes the mapping back to Diego's spec a little more complicated because his will
// sometimes UNCHANGED an entire struct, like .server, and I have to break out each subfield.
datatype FollowerVars = FollowerVars(
    // The server's term number.
    currentTerm:int,

    // The server's state (Follower, Candidate, or Leader).
    state:ServerState,

    // The candidate the server voted for in its current term, or
    // Nil if it hasn't voted for any.
    votedFor:Option<ServerID>,

    // A Sequence of log entries. The index into this sequence is the index of
    // the log entry.
    log:Log,

    // The index of the latest entry in the log the state machine may apply.
    commitIndex: int
)

// Variables only candidates maintain
datatype CandidateVars = CandidateVars(
    // The set of servers from which the candidate has received a RequestVote
    // response in its currentTerm.
    votesResponded:set<ServerID>,

    // The set of servers from which the candidate has received a vote in its
    // currentTerm.
    votesGranted:set<ServerID>
)

// Variables only leaders maintain
datatype LeaderVars = LeaderVars(
    // The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
    // leader does not send itself messages. It's still easier to include these
    // in the functions.

    // The next entry to send to each follower.
    nextIndex:map<ServerID, int>,

    // The latest entry that each follower has acknowledged is the same as the
    // leader's. This is used to calculate commitIndex on the leader.
    matchIndex:map<ServerID, int>
)

predicate WFLeaderVars(k:Constants, l:LeaderVars) {
    && l.nextIndex.Keys == k.serverIDs
    && l.matchIndex.Keys == k.serverIDs
}

datatype Variables = Variables(
    follower:FollowerVars,
    candidate:CandidateVars,
    leader:LeaderVars)


//////////////////////////////////////////////////////////////////////////////

// Helpers

// The set of all quorums. This just calculates simple majorities, but the only
// important property is that every quorum overlaps with every other.
// jonh rewhacked as predicate for easier predicate logicking.
predicate IsQuorum(k:Constants, servers:set<ServerID>)
{
    |servers| * 2 > |k.serverIDs|
}

// The term of the last entry in a log, or 0 if the log is empty.
function LastTerm(xlog:Log) : int {
    if |xlog| == 0 then 0 else xlog[|xlog|-1].term
}

function Min(a:int, b:int) : int
{
    if a < b then a else b
}

function Max(a:int, b:int) : int
{
    if a > b then a else b
}

predicate WFVars(k:Constants, v:Variables) {
    WFLeaderVars(k, v.leader)
}

function {:opaque} MapAll(k:Constants, i:int) : (m:map<ServerID, int>)
    ensures m.Keys == k.serverIDs
    ensures forall s :: s in m ==> m[s] == i
{
    map s | s in k.serverIDs :: i
}


//////////////////////////////////////////////////////////////////////////////
// Init

predicate Init(k:Constants, v:Variables) {
    && k.id in k.serverIDs  // sanity check on Constants.

    && v.follower.currentTerm == 1
    && v.follower.state == Follower
    && v.follower.votedFor == None
    && v.follower.log == []
    && v.follower.commitIndex == 0

    && v.candidate.votesResponded == {}
    && v.candidate.votesGranted == {}

    && v.leader.nextIndex == MapAll(k, 1)
    && v.leader.matchIndex == MapAll(k, 0)
}

//////////////////////////////////////////////////////////////////////////////
// Define state transitions

// Server i restarts from stable storage.
// It loses everything but its currentTerm, votedFor, and log.
predicate Restart(k:Constants, v:Variables, v':Variables, na:NetworkActivity)
{
    // JCF proposal: bring in the TLA+ 'UNCHANGED' syntax.
    && /*UNCHANGED*/ v'.follower.currentTerm == v.follower.currentTerm
    && v'.follower.state == Follower
    && /*UNCHANGED*/ v'.follower.votedFor == v.follower.votedFor
    && /*UNCHANGED*/ v'.follower.log == v.follower.log
    && v'.follower.commitIndex == 0
    && v'.candidate.votesResponded == {}
    && v'.candidate.votesGranted == {}
    && v'.leader.nextIndex == MapAll(k, 1)
    && v'.leader.matchIndex == MapAll(k, 0)
    && na == network.NoActivity()
}

// Server i times out and starts a new election.
predicate Timeout(k:Constants, v:Variables, v':Variables, na:NetworkActivity)
{
    && (v.follower.state.Follower? || v.follower.state.Candidate?)
    && v'.follower.state.Candidate?
    && v'.follower.currentTerm == v.follower.currentTerm + 1
    && v'.follower.votedFor == None
    && v'.follower.log == v.follower.log
    && v'.follower.commitIndex == v.follower.commitIndex
    && v'.candidate.votesResponded == {}
    && v'.candidate.votesGranted == {}
    && v'.leader == v.leader
    && na == network.NoActivity()
}


// Candidate i sends j a RequestVote request.
predicate RequestVote(k:Constants, v:Variables, v':Variables, j:ServerID, na:NetworkActivity)
    requires WFVars(k, v) && WFVars(k, v')
{
    && j in k.serverIDs
    && v.follower.state.Candidate?
    && !(j in v.candidate.votesResponded)
    && na == network.NetworkActivity(None, {RequestVoteRequest(
            k.id,
            j,
            v.follower.currentTerm,
            LastTerm(v.follower.log),
            |v.follower.log|)})
}

function PrevLogIndex(k:Constants, v:Variables, j:ServerID) : int
    requires WFLeaderVars(k, v.leader)
    requires j in k.serverIDs
    requires v.follower.state.Leader?
{
    v.leader.nextIndex[j] - 1
}

function PrevLogTerm(k:Constants, v:Variables, j:ServerID) : int
    requires WFLeaderVars(k, v.leader)
    requires j in k.serverIDs
    requires v.follower.state.Leader?
{
    if PrevLogIndex(k, v, j) > 0
        // jonh new constraint needed for Dafny's eager bounds checking
        && PrevLogIndex(k, v, j) < |v.follower.log|
    then v.follower.log[PrevLogIndex(k, v, j)].term
    else 0
}

// Send up to 1 entry, constrained by the end of the log.
function LastEntry(k:Constants, v:Variables, j:ServerID) : int
    requires WFLeaderVars(k, v.leader)
    requires j in k.serverIDs
    requires v.follower.state.Leader?
{
    Min(|v.follower.log|, v.leader.nextIndex[j])
}

function Entries(k:Constants, v:Variables, j:ServerID) : seq<LogEntry>
    requires WFLeaderVars(k, v.leader)
    requires j in k.serverIDs
    requires v.follower.state.Leader?
    requires 0 <= v.leader.nextIndex[j] < |v.follower.log|
{
    v.follower.log[v.leader.nextIndex[j] .. LastEntry(k, v, j)]
}

// Leader i sends j an AppendEntries request containing up to 1 entry.
// While implementations may want to send more than 1 at a time, this spec uses
// just 1 because it minimizes atomic regions without loss of generality.
predicate AppendEntries(k:Constants, v:Variables, v':Variables, j:ServerID, na:NetworkActivity)
    requires WFVars(k, v) && WFVars(k, v')
{
    && j in k.serverIDs // NB TLA spec never actually establishes this type constraint
    && k.id != j
    && v.follower.state.Leader?

    && /* UNCHANGED */ v' == v
    && 0 <= v.leader.nextIndex[j] < |v.follower.log| // NB absent from TLA source spec; is it an invariant? No, because |v.follower.log| can be zero.
    && na == network.NetworkActivity(None, {AppendEntriesRequest(
            k.id,
            j,
            v.follower.currentTerm,
            PrevLogIndex(k, v, j),
            PrevLogTerm(k, v, j),
            Entries(k, v, j),
            Min(v.follower.commitIndex, LastEntry(k, v, j))
            )})
}

// Candidate i transitions to leader.
predicate BecomeLeader(k:Constants, v:Variables, v':Variables, na:NetworkActivity)
{
    && v.follower.state.Candidate?
    && IsQuorum(k, v.candidate.votesGranted)
    && v'.follower.state.Leader?
    && v'.follower.currentTerm == v.follower.currentTerm
    && v'.follower.votedFor == v.follower.votedFor
    && v'.follower.log == v.follower.log
    && v'.follower.commitIndex == v.follower.commitIndex
    && v'.candidate == v.candidate
    && v'.leader.nextIndex == MapAll(k, |v.follower.log| + 1)  // XXX +1 for 1-based TLA seqs?
    && v'.leader.matchIndex == MapAll(k, 0)
    && na == network.NoActivity()
}

// Leader i receives a client request to add value to the log.
predicate ClientRequest(k:Constants, v:Variables, v':Variables, value:Value, na:NetworkActivity)
{
    && v.follower.state.Leader?
    && var entry := LogEntry(v.follower.currentTerm, value);
    && v'.follower.log == v.follower.log + [entry]
    // bunch o' UNCHANGED below
    && v'.follower.commitIndex == v.follower.commitIndex
    && v'.follower.currentTerm == v.follower.currentTerm
    && v'.follower.state == v.follower.state
    && v'.follower.votedFor == v.follower.votedFor
    && v'.candidate == v.candidate
    && v'.leader == v.leader
}

// Leader i advances its commitIndex.
// This is done as a separate step from handling AppendEntries responses,
// in part to minimize atomic regions, and in part so that leaders of
// single-server clusters are able to mark entries committed.

// The set of servers that agree up through index.
function {:opaque} Agree(k:Constants, v:Variables, index:int) : (a:set<ServerID>)
    requires WFLeaderVars(k, v.leader)
    ensures forall h :: h in a ==> h in k.serverIDs
    ensures forall h :: h in a ==> v.leader.matchIndex[h] >= index
{
    set h | h in k.serverIDs && v.leader.matchIndex[h] >= index
}

predicate QuorumAtIndex(k:Constants, v:Variables, index:int)
    requires WFLeaderVars(k, v.leader)
{
    IsQuorum(k, Agree(k, v, index))
}

// The [sic: maximum] indexes for which a quorum agrees
// jonh uses a seq instead of a set to simplify MaxAgreeIndex definition.
// This is still probably overkill, since there's surely a stability property.
// But I'm trying to stay close to the source TLA.
function {:opaque} AgreeIndexesDef(k:Constants, v:Variables, limit:nat) : (ai:seq<int>)
    requires WFLeaderVars(k, v.leader)
    ensures forall index :: index in ai ==> 0 <= index < limit
    ensures forall index :: index in ai ==> QuorumAtIndex(k, v, index)
    decreases limit
{
    if limit == 0
    then []
    else AgreeIndexesDef(k, v, limit-1) + if QuorumAtIndex(k, v, limit-1) then [limit-1] else []
}

function AgreeIndexes(k:Constants, v:Variables) : (ai:seq<int>)
    requires WFLeaderVars(k, v.leader)
{
    AgreeIndexesDef(k, v, |v.follower.log|)
}

function {:opaque} SeqMax(q:seq<int>) : (m:int)
    requires 0<|q|
    ensures forall i :: 0<=i<|q| ==> m >= q[i]
    ensures m in q
{
    if |q| == 1
    then q[0]
    else Max(SeqMax(q[..|q|-1]), q[|q|-1])
}

function MaxAgreeIndex(k:Constants, v:Variables) : (index:int)
    requires WFLeaderVars(k, v.leader)
    requires AgreeIndexes(k, v) != []
    ensures index in AgreeIndexes(k, v)
    ensures forall i2 :: i2 in AgreeIndexes(k, v) ==> i2 <= index
{
    SeqMax(AgreeIndexes(k, v))
}

function NewCommitIndex(k:Constants, v:Variables) : int
    requires WFLeaderVars(k, v.leader)
{
    if |AgreeIndexes(k, v)| == 0
        then v.follower.commitIndex
    else if v.follower.log[MaxAgreeIndex(k, v)].term != v.follower.currentTerm
        then v.follower.commitIndex
    else
        MaxAgreeIndex(k, v)
}

predicate AdvanceCommitIndex(k:Constants, v:Variables, v':Variables, na:NetworkActivity)
    requires WFLeaderVars(k, v.leader)
{
    && v.follower.state.Leader?
    && v'.follower.commitIndex == NewCommitIndex(k, v)
    && v'.follower.log == v.follower.log
    && v'.follower.currentTerm == v.follower.currentTerm
    && v'.follower.state == v.follower.state
    && v'.follower.votedFor == v.follower.votedFor
    && v'.candidate == v.candidate
    && v'.leader == v.leader
    // NB bug in source TLA doesn't constrain elections
    && na == network.NoActivity()
}

// NB TLA spec doesn't actually define "applying a log entry at a given index
// to its state machine", so State Machine Safety isn't even definable yet! Sigh.

//////////////////////////////////////////////////////////////////////////////
// Message handlers
// i = recipient, j = sender, m = message

// Server i receives a RequestVote request from server j with
// m.mterm <= currentTerm[i].

predicate Grant(k:Constants, v:Variables, j:ServerID, m:Message)
    requires j in k.serverIDs
    requires m.RequestVoteRequest?
{
    && m.term == v.follower.currentTerm
    && (|| v.follower.votedFor.None?
        || v.follower.votedFor == Some(j))
}

predicate WFMessage(k:Constants, m:Message)
{
    && m.source in k.serverIDs
    && m.dest in k.serverIDs
}

predicate HandleRequestVoteRequest(k:Constants, v:Variables, v':Variables, m:Message, send:set<Message>)
    requires WFMessage(k, m)
    requires m.RequestVoteRequest?
{
    var j := m.source;
    && m.term <= v.follower.currentTerm
    // jonh rewrote for readibility (imperative style)
    && v'.follower.votedFor == (if Grant(k, v, j, m) then Some(j) else v.follower.votedFor)
    && v'.follower.state == v.follower.state
    && v'.follower.currentTerm == v.follower.currentTerm
    && v'.follower.log == v.follower.log
    && v'.follower.commitIndex == v.follower.commitIndex
    && v'.candidate == v.candidate
    && v'.leader == v.leader
    && send == {RequestVoteResponse(
            k.id,
            j,
            v.follower.currentTerm,
            Grant(k, v, j, m)
        )}
}

// Server i receives a RequestVote response from server j with
// m.mterm = currentTerm[i].
predicate HandleRequestVoteResponse(k:Constants, v:Variables, v':Variables, m:Message, send:set<Message>)
    requires m.RequestVoteResponse?
{
    var j := m.source;
    // This tallies votes even when the current state is not Candidate, but
    // they won't be looked at, so it doesn't matter.
    && m.term == v.follower.currentTerm
    && v'.candidate.votesResponded == v.candidate.votesResponded + {j}
    // jonh rewrote TLA source into imperative style.
    && v'.candidate.votesGranted ==
        v.candidate.votesGranted + (if m.voteGranted then {j} else {})
    && send == {}
}

predicate AppendLogOk(v:Variables, m:Message)
    requires m.AppendEntriesRequest?
{
    || m.prevLogIndex == -1
    || (
        && m.prevLogIndex >= 0
        && m.prevLogIndex < |v.follower.log|
        && m.prevLogTerm == v.follower.log[m.prevLogIndex].term
       )
}

predicate AlreadyDoneWithRequest(k:Constants, v:Variables, v':Variables, m:Message, index:int, send:set<Message>)
    requires m.AppendEntriesRequest?
{
    // already done with request
    && (
        || m.entries == []
        || (
            && 0 <= index   // jonh added check that's probably inductive in TLA spec
            && index < |v.follower.log|
            && v.follower.log[index].term == m.entries[0].term
           )
       )
      // This could make our commitIndex decrease (for
      // example if we process an old, duplicated request),
      // but that doesn't really affect anything.
      // [jonh: doesn't it? Couldn't you re-execute a re-commited entry!?] 
    && v'.follower.commitIndex == m.commitIndex
    && /*UNCHANGED*/ v'.follower.currentTerm == v.follower.currentTerm
    && /*UNCHANGED*/ v'.follower.state == v.follower.state
    && /*UNCHANGED*/ v'.follower.votedFor == v.follower.votedFor
    && /*UNCHANGED*/ v'.follower.log == v.follower.log
    && send == {AppendEntriesResponse(
            k.id, m.source, v.follower.currentTerm, true, m.prevLogIndex + |m.entries|)}
    // NB TLA source spec erroneously sets commitIndex & unchanged logVars,
    // leading to a case that can't ever occur. (Spec wasn't live.)
}

predicate Conflict(k:Constants, v:Variables, v':Variables, m:Message, index:int, send:set<Message>)
    requires m.AppendEntriesRequest?
{
    && m.entries != []
    && 0 <= index   // jonh adds check; probably inductive in TLA spec
    && index < |v.follower.log|
    && v.follower.log[index].term != m.entries[0].term
    && v'.follower.log == v.follower.log[..|v.follower.log| - 1]
    && /*UNCHANGED*/ v'.follower.commitIndex == v.follower.commitIndex
    && /*UNCHANGED*/ v'.follower.currentTerm == v.follower.currentTerm
    && /*UNCHANGED*/ v'.follower.state == v.follower.state
    && /*UNCHANGED*/ v'.follower.votedFor == v.follower.votedFor
    && send == {}
}

predicate NoConflict(k:Constants, v:Variables, v':Variables, m:Message, index:int,  send:set<Message>)
    requires m.AppendEntriesRequest?
{
    // no conflict: append [jonh: exactly one] entry
    // jonh: ...yet we don't send a reply. How does leader discover that it shouldn't
    // re-send the same prefix over and over? It seems this isn't live!
    && m.entries != []
    && |v.follower.log| == m.prevLogIndex
    && v'.follower.log == v.follower.log + m.entries[..1]
    && /*UNCHANGED*/ v'.follower.commitIndex == v.follower.commitIndex
    && /*UNCHANGED*/ v'.follower.currentTerm == v.follower.currentTerm
    && /*UNCHANGED*/ v'.follower.state == v.follower.state
    && /*UNCHANGED*/ v'.follower.votedFor == v.follower.votedFor
    && send == {}
}

predicate HandleAppendEntriesRequest(k:Constants, v:Variables, v':Variables, m:Message, send:set<Message>)
    requires m.AppendEntriesRequest?
{
    && m.term <= v.follower.currentTerm
    && (
        || ( // reject request
            && (
                || m.term < v.follower.currentTerm
                || (
                    && m.term == v.follower.currentTerm
                    && v.follower.state.Follower?
                    && !AppendLogOk(v, m)
                   )
               )
            && /*UNCHANGED*/ v'.follower == v.follower
            && /*UNCHANGED*/ v'.candidate == v.candidate
            && send == {AppendEntriesResponse(k.id, m.source, v.follower.currentTerm, false, 0)}
           )
        || ( // return to follower state
            && m.term == v.follower.currentTerm
            && v.follower.state.Candidate?
            && v'.follower.state.Follower?
            && /*UNCHANGED*/ v'.follower.currentTerm == v.follower.currentTerm
            && /*UNCHANGED*/ v'.follower.votedFor == v.follower.votedFor
            && /*UNCHANGED*/ v'.follower.log == v.follower.log
            && /*UNCHANGED*/ v'.follower.commitIndex == v.follower.commitIndex
            && send == {}
           )
        || ( // accept request
            && m.term == v.follower.currentTerm
            && v.follower.state.Follower?
            && AppendLogOk(v, m)
            && var index := m.prevLogIndex + 1;
            && (
                || AlreadyDoneWithRequest(k, v, v', m, index, send)
                || Conflict(k, v, v', m, index, send)
                || NoConflict(k, v, v', m, index, send)
               )
           )
       )
    && v'.candidate == v.candidate
    && v'.leader == v.leader
}

// Server i receives an AppendEntries response from server j with
// m.mterm = currentTerm[i].
predicate HandleAppendEntriesResponse(k:Constants, v:Variables, v':Variables, m:Message, send:set<Message>)
    requires WFVars(k, v) && WFVars(k, v')
    requires WFMessage(k, m)
    requires m.AppendEntriesResponse?
{
    && var j := m.source;
    && m.term == v.follower.currentTerm
    && (
        || (
            && m.success
            && v'.leader.nextIndex == v.leader.nextIndex[j := m.matchIndex + 1]
            && v'.leader.matchIndex == v.leader.matchIndex[j := m.matchIndex]
           )
        || (
            && !m.success
            && v'.leader.nextIndex ==
                v.leader.nextIndex[j := Max(v.leader.nextIndex[j] -1, 0)]
            && v'.leader.matchIndex == v.leader.matchIndex
           )
       )
    && v' == v  /* UNCHANGED this? :v) */
    && send == {}
}

predicate UpdateTerm(k:Constants, v:Variables, v':Variables, m:Message, send:set<Message>)
{
    && m.term > v.follower.currentTerm
    && v'.follower.currentTerm == m.term
    && v'.follower.state.Follower?
    && v'.follower.votedFor == None
    && /*UNCHANGED*/ v'.follower.log == v.follower.log
    && /*UNCHANGED*/ v'.follower.commitIndex == v.follower.commitIndex
    && v'.candidate == v.candidate
    && v'.leader == v.leader
    && send == {}
}

// Responses with stale terms are ignored.
predicate DropStaleResponse(k:Constants, v:Variables, v':Variables, m:Message, send:set<Message>)
    requires WFVars(k, v) && WFVars(k, v')
{
    && m.term < v.follower.currentTerm
    && v' == v
    && send == {}
}

// NB source TLA writes:
    // Any RPC with a newer term causes the recipient to advance
    // its term first. Responses with stale terms are ignored.
// ... in a nondeterministic disjunct. What happens if the recipient decides to
// try one of the other actions first? Spurious rejections?

predicate HandleMessage(k:Constants, v:Variables, v':Variables, na:NetworkActivity)
    requires WFVars(k, v) && WFVars(k, v')
{
    && na.receive.Some?
    && var m := na.receive.value;
    && WFMessage(k, m)
    && (
        || UpdateTerm(k, v, v', m, na.send)
        || (
            && m.RequestVoteRequest?
            && HandleRequestVoteRequest(k, v, v', m, na.send)
           )
        || (
            && m.RequestVoteResponse?
            && (
                || DropStaleResponse(k, v, v', m, na.send)
                || HandleRequestVoteResponse(k, v, v', m, na.send)
               )
           )
        || (
            && m.AppendEntriesRequest?
            && HandleAppendEntriesRequest(k, v, v', m, na.send)
           )
        || (
            && m.AppendEntriesResponse?
            && (
                || DropStaleResponse(k, v, v', m, na.send)
                || HandleAppendEntriesResponse(k, v, v', m, na.send)
               )
           )
       )
}

// End of message handlers.

} // module server

module raft {
import opened MissingLibrary
import opened context
import network
import server
type NetworkActivity = network.NetworkActivity

datatype Constants = Constants(
    serverIDs:set<ServerID>,
    network:network.Constants
    )

datatype Variables = Variables(
    server:map<ServerID, server.Variables>,
    network:network.Variables
    )

predicate WFVars(k:Constants, v:Variables)
{
    && v.server.Keys == k.serverIDs
    && (forall s :: s in v.server ==> server.WFVars(server.Constants(k.serverIDs, s), v.server[s]))
}

function ServerConstants(k:Constants, s:ServerID) : server.Constants
{
    server.Constants(k.serverIDs, s)
}

predicate Init(k:Constants, v:Variables)
{
    && WFVars(k, v)
    && (forall s :: s in k.serverIDs ==> server.Init(ServerConstants(k, s), v.server[s]))
    && network.Init(k.network, v.network)
}

predicate UnchangedOtherHosts(k:Constants, v:Variables, v':Variables, s:ServerID)
    requires WFVars(k, v) && WFVars(k, v')
    requires s in k.serverIDs
{
    forall s2 :: s2 in k.serverIDs && s2 != s ==> v'.server[s2] == v.server[s2]
}

datatype Step =
      RestartStep(i:ServerID, na:NetworkActivity)
    | TimeoutStep(i:ServerID, na:NetworkActivity)
    | RequestVoteStep(i:ServerID, na:NetworkActivity, j:ServerID)
    | AppendEntriesStep(i:ServerID, na:NetworkActivity, j:ServerID)
    | BecomeLeaderStep(i:ServerID, na:NetworkActivity)
    | ClientRequestStep(i:ServerID, na:NetworkActivity, v:Value)
    | AdvanceCommitIndexStep(i:ServerID, na:NetworkActivity)
    | HandleMessageStep(i:ServerID, na:NetworkActivity)

predicate NextStep(k:Constants, v:Variables, v':Variables, step:Step)
    requires WFVars(k, v) && WFVars(k, v')
{
    && var i := step.i;
    && var ks := ServerConstants(k, i);
    && i in k.serverIDs
    && UnchangedOtherHosts(k, v, v', i)
    && network.ReceiveAndSend(k.network, v.network, v'.network, step.i, step.na)
    && match step {
        case RestartStep(i, na) =>
            server.Restart(ks, v.server[i], v'.server[i], na)
        case TimeoutStep(i, na) =>
            server.Timeout(ks, v.server[i], v'.server[i], na)
        case RequestVoteStep(i, na, j) =>
            server.RequestVote(ks, v.server[i], v'.server[i], j, na)
        case AppendEntriesStep(i, na, j) =>
            server.AppendEntries(ks, v.server[i], v'.server[i], j, na)
        case BecomeLeaderStep(i, na) =>
            server.BecomeLeader(ks, v.server[i], v'.server[i], na)
        case ClientRequestStep(i, na, value) =>
            server.ClientRequest(ks, v.server[i], v'.server[i], value, na)
        case AdvanceCommitIndexStep(i, na) =>
            server.AdvanceCommitIndex(ks, v.server[i], v'.server[i], na)
        case HandleMessageStep(i, na) =>
            server.HandleMessage(ks, v.server[i], v'.server[i], na)
    }
}

predicate {:opaque} Next(k:Constants, v:Variables, v':Variables)
    requires WFVars(k, v) && WFVars(k, v')
{
    && (exists step :: NextStep(k, v, v', step))
}

// The specification must start with the initial state and transition according
// to Next.
// Spec == Init /\ [][Next]_vars


} // raft
