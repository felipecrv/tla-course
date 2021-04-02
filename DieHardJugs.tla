----------------------------- MODULE DieHardJugs -----------------------------
EXTENDS Integers
VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big \in 0..5


Init == /\ small = 0
        /\ big = 0
        
FillSmall == /\ small' = 3
             /\ big' = big
             
FillBig == /\ small' = small
           /\ big' = 5

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ small' = small
            /\ big' = 0
           
SmallToBig == IF big + small =< 5
              THEN /\ big' = big + small
                   /\ small' = 0
              ELSE /\ big' = 5
                   /\ small' = small - (5 - big)
 
BigToSmall == IF big + small =< 3
              THEN /\ small' = big + small
                   /\ big' = 0
              ELSE /\ small' = 3
                   /\ big' = big - (3 - small)


Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

WillDie == /\ big /= 4   \* TLC should find a counter-example to this         

=============================================================================
\* Modification History
\* Last modified Fri Apr 02 00:23:39 BRT 2021 by felipec
\* Created Thu Apr 01 23:53:30 BRT 2021 by felipec
