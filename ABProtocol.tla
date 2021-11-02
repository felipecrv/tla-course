----------------------------- MODULE ABProtocol -----------------------------
EXTENDS Integers, Sequences, SequencesExercise

CONSTANT Data    \* The set of all possible data objects.

VARIABLES AVar,  \* The last <<value, bit>> pair A decided to send.
          BVar,  \* The last <<value, bit>> pair B received.
          AtoB,  \* Sequence of DATA messages in transit from sender to receiver.
          BtoA   \* Sequence of ACK messages in transit from receiver to sender.


TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})

vars == <<AVar, BVar, AtoB, BtoA>>   \* All variables.

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

\* A sending a data message to B by putting the same message in the channel
\* until an ACK is received.
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BtoA, BVar>>

\* B receiving a data message from A.
BRcv == /\ AtoB # << >>  \* There is at least one message in the channel.
        /\ IF Head(AtoB)[2] # BVar[2]
           THEN BVar' = Head(AtoB)  \* Accept the message if ACK bit is the alternate bit.
           ELSE BVar' = BVar        \* Ignore the message and keep the same local state.
        /\ AtoB' = Tail(AtoB)  \* Remove the received message from the channel.
        /\ UNCHANGED <<AVar, BtoA>>

\* B sending an ACK for the last data value received.
BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

\* A receiving an ACK from B.
ARcv == /\ BtoA # << >>  \* There is at least one message in the channel.
        /\ IF Head(BtoA) = AVar[2]  \* Check the ACK bit.
           THEN \E d \in Data: AVar' = <<d, 1 - AVar[2]>>  \* Alternate bit and send another message.
           ELSE AVar' = AVar  \* Keep sending AVar if ACK bit doesn't match.
        /\ BtoA' = Tail(BtoA)   \* Remove received message from the channel.
        /\ UNCHANGED <<AtoB, BVar>>

\* Lose a message in one of the channels.
LoseMsg == /\ \/ \* Lose a data message.
                 /\ \E i \in 1..Len(AtoB): AtoB' = Remove(i, AtoB)
                 /\ BtoA' = BtoA
              \/ \* Lose an ACK message.
                 /\ \E i \in 1..Len(BtoA): BtoA' = Remove(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED <<AVar, BVar>>

Next == \/ ASnd
        \/ BRcv
        \/ BSnd
        \/ ARcv
        \* \/ CorruptMsg
        \/ LoseMsg

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec

THEOREM Spec => ABS!Spec
-----------------------------------------------------------------------------
FairSpec == Spec /\ SF_vars(ARcv) /\ SF_vars(BRcv)
                 /\ WF_vars(ASnd) /\ WF_vars(ASnd)

THEOREM FairSpec => ABS!FairSpec

(*********************************************************************************)
(* In the first eight lectures, you learned about writing the safety part of a   *)
(* TLA+ spec. Now you know how to specify liveness. You simply add weak and      *)
(* strong fairness conditions. Simple, yes. Easy, no. Liveness is inherently     *)
(* subtle. TLA+ is the simplest way I know to express it, and it’s still hard.   *)
(* But don’t worry if you have trouble with liveness. The safety part is by far  *)
(* the largest part and almost always the most important part of a spec. A major *)
(* reason to add liveness is to catch errors in the safety part. If your         *)
(* fairness conditions don’t imply the eventually or leads-to properties you     *)
(* expect to hold, it could be because the safety part doesn’t allow behaviors   *)
(* that it should.                                                               *)
(*                                                                               *)
(* -- Leslie Lamport                                                             *)
(*********************************************************************************)

=============================================================================
\* Modification History
\* Last modified Sun Oct 31 15:57:20 CET 2021 by felipec
\* Created Sun Oct 31 08:13:45 CET 2021 by felipec
