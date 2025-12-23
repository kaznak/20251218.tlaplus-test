---- MODULE reader_writer ----
EXTENDS Integers, Sequences, TLC

CONSTANTS
    WRITERS,
    READERS,
    MESSAGES

WRITERS_SET == Permutations(WRITERS)
READERS_SET == Permutations(READERS)
Symmetry == WRITERS_SET \cup READERS_SET

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = <<>>;

process writer \in WRITERS_SET
begin
  AddToQueue:
    with i \in MESSAGES do
        queue := Append(queue, <<self, i>>);
    end with;
end process;


process reader \in READERS_SET
begin
  ReadFromQueue:
    if queue # <<>> then
        total := Append(total, Head(queue));
        queue := Tail(queue);
    end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f7d61858" /\ chksum(tla) = "99c3d36e")
VARIABLES pc, queue, total

vars == << pc, queue, total >>

ProcSet == (WRITERS_SET) \cup (READERS_SET)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in WRITERS_SET -> "AddToQueue"
                                        [] self \in READERS_SET -> "ReadFromQueue"]

AddToQueue(self) == /\ pc[self] = "AddToQueue"
                    /\ \E i \in MESSAGES:
                         queue' = Append(queue, <<self, i>>)
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ total' = total

writer(self) == AddToQueue(self)

ReadFromQueue(self) == /\ pc[self] = "ReadFromQueue"
                       /\ IF queue # <<>>
                             THEN /\ total' = Append(total, Head(queue))
                                  /\ queue' = Tail(queue)
                             ELSE /\ TRUE
                                  /\ UNCHANGED << queue, total >>
                       /\ pc' = [pc EXCEPT ![self] = "Done"]

reader(self) == ReadFromQueue(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in WRITERS_SET: writer(self))
           \/ (\E self \in READERS_SET: reader(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
