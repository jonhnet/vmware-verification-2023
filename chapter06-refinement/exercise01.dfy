//#title Two Phase Commit Model
//#desc Model a distributed protocol using compound state machines.

// Your goal is to model a 2-Phase Commit protocol. You're modeling a single
// instance of the problem -- a designated coordinator, no concurrent
// instances. Furthermore, you may assume there are no coordinator or
// participant failures. This is indeed a fairly simplistic setting, but it's
// still nontrivial, and is a nice example for reasoning about the
// state-machine composition framework.
//
// The input to the algorithm is that each participant has a boolean preference.
// The output is that each participant (and the coordinator) learns a decision value.
//
// 2-Phase Commit Protocol english design doc:
//
// 1, Coordinator sends VOTE-REQ to all participants.
// 2. Each participant i sends back vote_i to coordinator according to its preference.
//   If vote_i=No then i sets decision_i := Abort.
// 3. Coordinator collects votes.
//   If all votes are yes then coordinator sets decision_c := Commit and sends
//   Commit to all participants.
//   Else coordinator sets decision_c := Abort and sends Abort to all
//   participants who voted yes.
// 4. Participants receiving Commit set decision_i := Commit
//
// This file provides a lot of helpful framework. You only need to
// define Types.Message and then fill in the state machine types and actions
// in module CoordinatorHost and module ParticipantHost.
//
// Unlike chapter01, where you could work through each file sequentially,
// WE STRONGLY ENCOURAGE YOU to read the entire file before beginning
// work. Later pieces of the file are helpful, for example by explaining
// the network model you're working in, and by helping you understand
// the role the Constants datatypes play.

include "UtilitiesLibrary.dfy"
include "CommitTypes.dfy"
//#extract CommitTypes.template solution CommitTypes.dfy

module Types {
  import opened UtilitiesLibrary
  import opened CommitTypes

  type HostId = nat

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
/*{*/
    | VoteReqMsg                           // from leader
    | VoteMsg(sender: HostId, vote: Vote)  // from participant
    | DecisionMsg(decision: Decision)
/*}*/

  // A MessageOps is a "binding variable" used to connect a Host's Next step
  // (what message got received, what got sent?) with the Network (only allow
  // receipt of messages sent prior; record newly-sent messages).
  // Note that both fields are Option. A step predicate can say recv.None?
  // to indicate that it doesn't need to receive a message to occur.
  // It can say send.None? to indicate that it doesn't want to transmit a message.
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

// There are two host roles in 2PC, Coordinator and Participant. We'll define
// separate state machines for each.
// This state machine defines how a coordinator host should behave: what state
// it records, and what actions it's allowed to take in response to incoming
// messages (or spontaneously by thinking about its existing state).
module CoordinatorHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

/*{*/
  datatype Constants = Constants(participantCount: nat)
/*}*/

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? It needs to have a correct
  // count of the number of participants.
  ghost predicate ConstantsValidForGroup(c: Constants, participantCount: nat)
  {
/*{*/
    && c.participantCount == participantCount
/*}*/
  }

  datatype Variables = Variables(
    decision: Option<Decision>
/*{*/
    ,
    votes: seq<Option<Vote>>
/*}*/
  )
  {
    // WF is for a simple condition that relates every valid Variables state
    // to the Constants.
    ghost predicate WF(c: Constants) {
/*{*/
      && |votes| == c.participantCount
/*}*/
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
/*{*/
    && v.WF(c)
    // No votes recorded yet
    && (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].None?)
    // No decision recorded yet
    && v.decision.None?
/*}*/
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that the coordinator is involved in.
  // Hint: it's probably easiest to separate the receipt and recording of
  // incoming votes from detecting that all have arrived and making a decision.
/*{*/
  ghost predicate SendReq(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps == MessageOps(None, Some(VoteReqMsg))
    && v' == v  // UNCHANGED everything.
  }

  ghost predicate LearnVote(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.VoteMsg?
    && recvMsg.sender < c.participantCount
    // Record sender's vote.
    && v' == v.(votes := v.votes[recvMsg.sender := Some(recvMsg.vote)])
    && msgOps.send.None?
  }

  ghost predicate AllVotesCollected(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].Some?)
  }

  ghost predicate ObservesResult(c: Constants, v: Variables, decision: Decision)
  {
    && v.WF(c)
    && AllVotesCollected(c, v)
    && decision ==
      if (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].value.Yes?)
      then Commit
      else Abort
  }

  ghost predicate Decide(c: Constants, v: Variables, v': Variables, decision: Decision, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.None?
    && ObservesResult(c, v, decision)
    // Record the decision
    && v' == v.(decision := Some(decision))
    // Transmit the decision
    && msgOps.send == Some(DecisionMsg(decision))
  }
/*}*/

  // JayNF
  datatype Step =
/*{*/
    | SendReqStep
    | LearnVoteStep
    | DecideStep(decision: Decision)
/*}*/

  // msgOps is a "binding variable" -- the host and the network have to agree
  // on its assignment to make a valid transition. So the host explains what
  // would happen if it could receive a particular message, and the network
  // decides whether such a message is available for receipt.
  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
/*{*/
      case SendReqStep => SendReq(c, v, v', msgOps)
      case LearnVoteStep => LearnVote(c, v, v', msgOps)
      case DecideStep(decision) => Decide(c, v, v', decision, msgOps)
/*}*/
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

module ParticipantHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? It needs to know its hostId.
  ghost predicate ConstantsValidForGroup(c: Constants, hostId: HostId)
  {
/*{*/
    && c.hostId == hostId
/*}*/
  }

  datatype Variables = Variables(decision: Option<Decision>)
  {
    ghost predicate WF(c: Constants) {
/*{*/
      true
/*}*/
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
/*{*/
    && v.decision.None?
/*}*/
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that participant can take.
/*{*/
  ghost predicate Vote(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.VoteReqMsg?
    && msgOps.send == Some(VoteMsg(c.hostId, c.preference))
    // Infer Abort decision if we're voting No
    && v'.decision == if c.preference.No? then Some(Abort) else v.decision
  }

  ghost predicate LearnDecision(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.DecisionMsg?
    && v'.decision == Some(recvMsg.decision)
    && msgOps.send.None?
  }
/*}*/

  // JayNF
  datatype Step =
/*{*/
    | VoteStep
    | LearnDecisionStep
/*}*/

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
/*{*/
      case VoteStep => Vote(c, v, v', msgOps)
      case LearnDecisionStep => LearnDecision(c, v, v', msgOps)
/*}*/
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

// We define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
// This definition is given to you to clarify how the two protocol roles above
// are pulled together into the ultimate distributed system.
module Host {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Constants =
    | CoordinatorConstants(coordinator: CoordinatorHost.Constants)
    | ParticipantConstants(participant: ParticipantHost.Constants)

  datatype Variables =
    | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
    | ParticipantVariables(participant: ParticipantHost.Variables)
  {
    ghost predicate WF(c: Constants) {
      && (CoordinatorVariables? <==> c.CoordinatorConstants?) // types of c & v agree
      // subtype WF satisfied
      && (match c
            case CoordinatorConstants(_) => coordinator.WF(c.coordinator)
            case ParticipantConstants(_) => participant.WF(c.participant)
          )
    }
  }

  // What property must be true of any group of hosts to run the protocol?
  // Generic DistributedSystem module calls back into this predicate to ensure
  // that it has a well-formed *group* of hosts.
  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // There must at least be a coordinator
    && 0 < |grp_c|
    // Last host is a coordinator
    && Last(grp_c).CoordinatorConstants?
    // All the others are participants
    && (forall hostid:HostId | hostid < |grp_c|-1 :: grp_c[hostid].ParticipantConstants?)
    // The coordinator's constants must correctly account for the number of participants
    && CoordinatorHost.ConstantsValidForGroup(Last(grp_c).coordinator, |grp_c|-1)
    // The participants's constants must match their group positions.
    // (Actually, they just need to be distinct from one another so we get
    // non-conflicting votes, but this is an easy way to express that property.)
    && (forall hostid:HostId | hostid < |grp_c|-1
        :: ParticipantHost.ConstantsValidForGroup(grp_c[hostid].participant, hostid))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_c| :: grp_v[hostid].WF(grp_c[hostid]))
  }

  // Generic DistributedSystem module calls back into this predicate to give
  // the protocol an opportunity to set up constraints across the various
  // hosts.  Protocol requires one coordinator and the rest participants;
  // coordinator must know how many participants, and participants must know
  // own ids.
  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    // constants & variables are well-formed (same number of host slots as constants expect)
    && GroupWF(grp_c, grp_v)
    // Coordinator is initialized to know about the N-1 participants.
    && CoordinatorHost.Init(Last(grp_c).coordinator, Last(grp_v).coordinator)
    // Participants initted with their ids.
    && (forall hostid:HostId | hostid < |grp_c|-1 ::
        ParticipantHost.Init(grp_c[hostid].participant, grp_v[hostid].participant)
      )
  }

  // Dispatch Next to appropriate underlying implementation.
  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case CoordinatorConstants(_) => CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
      case ParticipantConstants(_) => ParticipantHost.Next(c.participant, v.participant, v'.participant, msgOps)
      )
  }
}

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
// This definition is given to you because it's a common assumption you can
// reuse. Someday you might decide to assume a different network model (e.g.
// reliable or at-most-once delivery), but this is a good place to start.
module Network {
  import opened CommitTypes
  import opened Types

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
// This is given to you; it can be reused for just about any shared-nothing-concurrency
// protocol model.
module DistributedSystem {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import Network
  import Host
  import CoordinatorHost
  import ParticipantHost

  datatype Constants = Constants(
    hosts: seq<Host.Constants>,
    network: Network.Constants)
  {
    ghost predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
    && Network.Init(c.network, v.network)
  }

  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.hostid, step.msgOps)
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }

  ghost function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
      case CoordinatorVariables(coordinator) => coordinator.decision
      case ParticipantVariables(participant) => participant.decision
  }

  // Convince us that your model does something
  lemma PseudoLiveness(c: Constants) returns (behavior: seq<Variables>)
    requires c.WF()
    requires |c.hosts| == 2 // There's exactly one voting participant...
    requires c.hosts[0].participant.preference.Yes? // ... who wants a Yes.
    // Exhibit a behavior that satisfies your state machine...
    ensures 0 < |behavior|
    ensures Init(c, behavior[0])
    ensures forall i:nat | i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1])
    // ...and all the participants arrive at a decision.
    ensures Last(behavior).WF(c)
    ensures forall hostid:HostId | c.ValidHostId(hostid)
      :: GetDecisionForHost(Last(behavior).hosts[hostid]) == Some(Commit)
  {
/*{*/
    var v0 := Variables(
      [
        Host.ParticipantVariables(ParticipantHost.Variables(None)),
        Host.CoordinatorVariables(CoordinatorHost.Variables(None, [None]))
      ], Network.Variables({}));
    assert Init(c, v0);

    var v1 := Variables(
      [
        Host.ParticipantVariables(ParticipantHost.Variables(None)),
        Host.CoordinatorVariables(CoordinatorHost.Variables(None, [None]))
      ], Network.Variables({VoteReqMsg}));

    var mops1 := MessageOps(None, Some(VoteReqMsg));
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, v0.hosts[1].coordinator, v1.hosts[1].coordinator, CoordinatorHost.SendReqStep, mops1);
    assert NextStep(c, v0, v1, HostActionStep(1, mops1));

    var v2 := Variables(
      [
        Host.ParticipantVariables(ParticipantHost.Variables(None)),
        Host.CoordinatorVariables(CoordinatorHost.Variables(None, [None]))
      ], Network.Variables({VoteReqMsg, VoteMsg(0, Yes)}));

    var mops2 := MessageOps(Some(VoteReqMsg), Some(VoteMsg(0, Yes)));
    assert ParticipantHost.NextStep(c.hosts[0].participant, v1.hosts[0].participant, v2.hosts[0].participant, ParticipantHost.VoteStep, mops2);
    assert NextStep(c, v1, v2, HostActionStep(0, mops2));

    var v3 := Variables(
      [
        Host.ParticipantVariables(ParticipantHost.Variables(None)),
        Host.CoordinatorVariables(CoordinatorHost.Variables(None, [Some(Yes)]))
      ], Network.Variables({VoteReqMsg, VoteMsg(0, Yes)}));

    var mops3 := MessageOps(Some(VoteMsg(0, Yes)), None);
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, v2.hosts[1].coordinator, v3.hosts[1].coordinator, CoordinatorHost.LearnVoteStep, mops3);
    assert NextStep(c, v2, v3, HostActionStep(1, mops3));

    var v4 := Variables(
      [
        Host.ParticipantVariables(ParticipantHost.Variables(None)),
        Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Commit), [Some(Yes)]))
      ], Network.Variables({VoteReqMsg, VoteMsg(0, Yes), DecisionMsg(Commit)}));

    var mops4 := MessageOps(None, Some(DecisionMsg(Commit)));
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, v3.hosts[1].coordinator, v4.hosts[1].coordinator, CoordinatorHost.DecideStep(Commit), mops4);
    assert NextStep(c, v3, v4, HostActionStep(1, mops4));

    var v5 := Variables(
      [
        Host.ParticipantVariables(ParticipantHost.Variables(Some(Commit))),
        Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Commit), [Some(Yes)]))
      ], Network.Variables({VoteReqMsg, VoteMsg(0, Yes), DecisionMsg(Commit)}));

    var mops5 := MessageOps(Some(DecisionMsg(Commit)), None);
    assert ParticipantHost.NextStep(c.hosts[0].participant, v4.hosts[0].participant, v5.hosts[0].participant, ParticipantHost.LearnDecisionStep, mops5);
    assert NextStep(c, v4, v5, HostActionStep(0, mops5));

    behavior := [v0, v1, v2, v3, v4, v5];
/*}*/
  }
}


