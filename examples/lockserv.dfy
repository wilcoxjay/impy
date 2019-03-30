// manually translated from lockserv.impy
// not done yet.

type ClientID
function ClientIDs(): set<ClientID>

datatype NodeID = Server | Client(id: ClientID)

datatype Message = Request(client: ClientID)
                 | Grant(client: ClientID)
                 | Release(client: ClientID)

datatype Step = SendRequestStep(client: ClientID)
              | GrantLockStep(client: ClientID)
              | RecvGrantStep(client: ClientID)
              | SendReleaseStep(client: ClientID)
              | RecvReleaseStep(client: ClientID)

datatype HostState = HostState(holds_lock: bool)

datatype Variables = Variables(hosts: map<NodeID, HostState>, network: set<Message>)

predicate SendRequest(v: Variables, v': Variables, c: ClientID)
{
  && v'.hosts == v.hosts
  && v'.network == v.network + {Request(c)}
}

predicate GrantLock(v: Variables, v': Variables, c: ClientID)
  requires Server in v.hosts
{
  var m := Request(c);
  && m in v.network
  && v.hosts[Server].holds_lock
  && v'.hosts == v.hosts[Server := v.hosts[Server].(holds_lock := false)]
  && v'.network == (v.network - {m}) + {Grant(c)}
}

predicate RecvGrant(v: Variables, v': Variables, c: ClientID)
  requires Client(c) in v.hosts
{
  var m := Grant(c);
  var n := Client(c);
  && m in v.network
  && v'.hosts == v.hosts[n := v.hosts[n].(holds_lock := true)]
  && v'.network == v.network - {m}
}

predicate SendRelease(v: Variables, v': Variables, c: ClientID)
  requires Client(c) in v.hosts
{
  var n := Client(c);
  && v.hosts[n].holds_lock
  && v'.hosts == v.hosts[n := v.hosts[n].(holds_lock := false)]
  && v'.network == v.network + {Release(c)}
}

predicate RecvRelease(v: Variables, v': Variables, c: ClientID)
  requires Server in v.hosts
{
  var m := Release(c);
  && m in v.network
  && v'.hosts == v.hosts[Server := v.hosts[Server].(holds_lock := true)]
  && v'.network == v.network - {m}
}

predicate NextStep(v: Variables, v': Variables, step: Step)
  requires WFVariables(v) && WFVariables(v') && WFStep(step)
{
  match step
    case SendRequestStep(c) => SendRequest(v,v',c)
    case GrantLockStep(c) => GrantLock(v,v',c)
    case RecvGrantStep(c) => RecvGrant(v,v',c)
    case SendReleaseStep(c) => SendRelease(v,v',c)
    case RecvReleaseStep(c) => RecvRelease(v,v',c)
}

predicate WFStep(step: Step)
{
  step.client in ClientIDs()
}

predicate WFVariables(v: Variables)
{
  v.hosts.Keys == {Server} + set c | c in ClientIDs() :: Client(c)
}

predicate Next(v: Variables, v': Variables)
  requires WFVariables(v) && WFVariables(v')
{
  exists step | WFStep(step) :: NextStep(v, v', step)
}

predicate Mutex(v: Variables)
  requires WFVariables(v)
{
}
