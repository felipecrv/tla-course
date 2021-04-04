------------------------------ MODULE TwoPhase ------------------------------
(***************************************************************************)
(* This specification is based on "Two-Phase Commit", Lecture 6 of the     *)
(* TLA+ Video Course.  It describes the Two-Phase Commit protocol, in      *)
(* which a transaction manager (TM) coordinates the resource managers      *)
(* (RMs) to implement the Transaction Commit specification of module       *)
(* TCommit.  In this specification, RMs spontaneously issue Prepared       *)
(* messages.  We ignore the Prepare messages that the TM can send to the   *)
(* RMs.                                                                    *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by an RM when it  *)
(* decides to abort.  Such a message would cause the TM to abort the       *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.                                                               *)
(***************************************************************************)
CONSTANT RM  \* The set of all Resource Managers (e.g. {"r1", "r2", "r3"}).

VARIABLES
  rmState,    \* rmState[rm] is the state of the Resource Manager rm.
  tmState,    \* Transaction Manager state: "init" or "done".
  tmPrepared, \* The set of resource managers the transaction manager knows are prepared.
  msgs
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  For simplicity, we represent message passing with the    *)
    (* variable msgs whose value is the set of all messages that have been *)
    (* sent.  A message is sent by adding it to the set msgs.  An action   *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the presence of that message in  *)
    (* msgs.  For simplicity, messages are never removed from msgs.  This  *)
    (* allows a single message to be received by multiple receivers.       *)
    (* Receipt of the same message twice is therefore allowed; but in this *)
    (* particular protocol, that's not a problem.                          *)
    (***********************************************************************)

(***************************************************************************)
(* The set of all possible messages. Messages of type "Prepared" are sent  *)
(* from the RM indicated by the message's rm field to the TM. Messages of  *)
(* type "Commit" and "Abort" are broadcast by the TM, to be received by    *)
(* all RMs. The set msgs contains just a single copy of such message.      *)
(***************************************************************************)
Messages == [type: {"Prepared"}, rm: RM] \cup [type: {"Commit", "Abort"}]

TPTypeOK == /\ rmState \in [RM -> {"working", "prepared",
                                   "committed", "aborted"}]
            /\ tmState \in {"init", "done"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages


TPInit == /\ rmState = [r \in RM |-> "working"]
          /\ tmState = "init"
          /\ tmPrepared = {}
          /\ msgs = {}
            
-----------------------------------------------------------------------------

TMRecvPrepared(r) ==   \* The TM receives a "Prepared" message from resource manager r.
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs  \* The message received exists
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>


TMCommit == \* The TM commits the transaction
  /\ tmState = "init"
  /\ tmState' = "done"                        \* TM state transitions
  /\ tmPrepared = RM                          \* TM sees all RMs as prepared
  /\ rmState = [r \in RM |-> "prepared"]      \* All RMs are prepared (nececessary?)
  /\ msgs'= msgs \union {[type |-> "Commit"]} \* Send the Commit message
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort == \* The TM spontaneously aborts the transaction
  /\ tmState = "init" /\ tmState' = "done"   \* TM state transitions
  /\ msgs'= msgs \union {[type |-> "Abort"]} \* Send the Abort message
  /\ UNCHANGED <<rmState, tmPrepared>>
  
-----------------------------------------------------------------------------

RMPrepare(r) == /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
                /\ UNCHANGED <<tmState, tmPrepared>>

(********************************************)
(* RM spontaneously chooses to abort.       *)
(* No message sent in our simplified model. *)
(********************************************)
RMChooseToAbort(r) == /\ rmState[r] = "aborted"
                      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                      /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRecvCommitMsg(r) == \* RM r is told to commit
  /\ [type |-> "Commit"] \in msgs          \* A Commit message should have been sent
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRecvAbortMsg(r) == \* RM is told to abort
  /\ [type |-> "Abort"] \in msgs           \* An Abort message should have been sent
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>


TPNext == \/ TMCommit              \* The transaction is committed by the TM.
          \/ TMAbort               \* The transaction is aborted by the TM.
          \/ \E r \in RM :         \* A message is sent or received by a RM or the TM.
               \/ TMRecvPrepared(r)
               \/ RMPrepare(r)
               \/ RMChooseToAbort(r)
               \/ RMRecvCommitMsg(r)
               \/ RMRecvAbortMsg(r)
               
-----------------------------------------------------------------------------       

\* TODO on Lecture 8            

=============================================================================
\* Modification History
\* Last modified Sun Apr 04 10:00:30 BRT 2021 by felipec
\* Created Sat Apr 03 15:07:14 BRT 2021 by felipec
