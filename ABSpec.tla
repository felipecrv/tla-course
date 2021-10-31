------------------------------- MODULE ABSpec -------------------------------
EXTENDS Integers

CONSTANT Data    \* The set of all possible data objects.

VARIABLES AVar,  \* The last <<value, bit>> pair A decided to send.
          BVar   \* The last <<value, bit>> pair B received.

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}

vars == <<AVar, BVar>>   \* All variables.

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

A == /\ AVar = BVar   \* Pre-condition for sending.
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>  \* Send something and alternate the bit.
     /\ BVar' = BVar  \* BVar remains the same.

B == /\ AVar # BVar   \* Pre-condition for receiving.
     /\ BVar' = AVar  \* BVar is updated with the received data.
     /\ AVar' = AVar  \* AVar remains the same.


Next == A \/ B

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Sun Oct 31 08:19:43 CET 2021 by felipec
\* Created Sun Oct 31 08:13:45 CET 2021 by felipec
