------------------------------- MODULE ABProtocol2 -------------------------------
EXTENDS Integers, Sequences
CONSTANT Data,    \* The set of all possible data objects.
         Bad     \* The bad message (to model broken/lost messages).

\* Bad must be different from any of the legal messages.
ASSUME Bad \notin (Data \X {0, 1}) \cup {0, 1}

VARIABLES AVar,  \* The last <<value, bit>> pair A decided to send.
          BVar,  \* The last <<value, bit>> pair B received.
          AtoB,  \* Sequence of DATA messages in transit from sender to receiver.
          BtoA   \* Sequence of ACK messages in transit from receiver to sender.


TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1} \cup {Bad})
          /\ BtoA \in Seq({0, 1, Bad})

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
        /\ IF (Head(AtoB) # Bad) /\ (Head(AtoB)[2] # BVar[2])
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

\* Corrupt a message in one of the channels.
CorruptMsg == /\ \/ \* Corrupt a data message.
                    /\ \E i \in 1..Len(AtoB):
                            AtoB' = [AtoB EXCEPT ![i] = Bad]
                    /\ BtoA' = BtoA
                 \/ \* Corrupt an ACK message.
                    /\ \E i \in 1..Len(BtoA):
                            BtoA = [BtoA EXCEPT ![i] = Bad]
                    /\ AtoB' = AtoB
              /\ UNCHANGED <<AVar, BVar>>

Next == \/ ASnd
        \/ BRcv
        \/ BSnd
        \/ ARcv
        \/ CorruptMsg

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec

THEOREM Live == Spec => ABS!Spec
-----------------------------------------------------------------------------
FairSpec == Spec /\ SF_vars(ARcv) /\ SF_vars(BRcv)
                 /\ WF_vars(ASnd) /\ WF_vars(ASnd)

\* NOTE(philix): This doesn't hold (see the last lectures for the fixes)
THEOREM Live2 == FairSpec => ABS!FairSpec
=============================================================================
