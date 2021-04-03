------------------------------------ MODULE TCommit ------------------------------- 
CONSTANT RM        \* The set of all Resource Managers (e.g. {"r1", "r2", "r3"})
VARIABLE rmState   \* rmState[rm] is the state of the Resource Manager rm

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

-----------------------------------------------------------------------------------

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"] 
                            (***********************************************)
                            (* [s \in RM |->                               *)
                            (*   IF s = r THEN "prepared" ELSE rmState[s]] *) 
                            (***********************************************)


canCommit == \A r \in RM: rmState[r] \in {"prepared", "comitted"}

notCommited == \A r \in RM: rmState[r] /= "committed"

DecideToCommit(r) == /\ rmState[r] = "prepared"
                     /\ canCommit
                     /\ rmState'= [rmState EXCEPT ![r] = "committed"]                     

DecideToAbort(r) == /\ rmState[r] \in {"working", "prepared"}
                    /\ notCommited
                    /\ rmState'= [rmState EXCEPT ![r] = "aborted"]                     

Decide(r) == \/ DecideToCommit(r) 
             \/ DecideToAbort(r)


TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

-----------------------------------------------------------------------------------

TCConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "commited"

===================================================================================
\* Modification History
\* Last modified Sat Apr 03 14:19:45 BRT 2021 by felipec
\* Created Sat Apr 03 10:13:09 BRT 2021 by felipec