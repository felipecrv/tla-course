-------------------------- MODULE SequencesExercise -------------------------
EXTENDS Integers, Sequences

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < 1
                                               THEN seq[j]
                                               ELSE seq[j+1]]

=============================================================================
\* Modification History
\* Last modified Tue Apr 06 21:23:21 BRT 2021 by felipec
\* Created Tue Apr 06 21:14:03 BRT 2021 by felipec
