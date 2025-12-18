---- MODULE RobustBank ----
EXTENDS Integers, TLC, Sequences

(* --algorithm RobustBank
variable 
    accounts = [p \in {"Alice", "Bob", "Charlie"} |-> 10];

define
    Total == accounts["Alice"] + accounts["Bob"] + accounts["Charlie"]
    MoneyIsConstant == Total = 30
end define;

procedure Transfer(from, to, amount)
begin
  Tx:
    if accounts[from] >= amount then
        accounts[from] := accounts[from] - amount;
        
        Deposit:
        accounts[to]   := accounts[to]   + amount;
    end if;
    
  Ret:
    return;
end procedure;

process Client \in {"Alice", "Bob", "Charlie"}
begin
  Loop:
    while TRUE do
      CallTx:
        with receiver \in {"Alice", "Bob", "Charlie"} \ {self},
             amt      \in 1..5 
        do
           call Transfer(self, receiver, amt);
        end with;

    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES pc, accounts, stack

(* define statement *)
Total == accounts["Alice"] + accounts["Bob"] + accounts["Charlie"]
MoneyIsConstant == Total = 30

VARIABLES from, to, amount

vars == << pc, accounts, stack, from, to, amount >>

ProcSet == ({"Alice", "Bob", "Charlie"})

Init == (* Global variables *)
        /\ accounts = [p \in {"Alice", "Bob", "Charlie"} |-> 10]
        (* Procedure Transfer *)
        /\ from = [ self \in ProcSet |-> defaultInitValue]
        /\ to = [ self \in ProcSet |-> defaultInitValue]
        /\ amount = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Loop"]

Tx(self) == /\ pc[self] = "Tx"
            /\ IF accounts[from[self]] >= amount[self]
                  THEN /\ accounts' = [accounts EXCEPT ![from[self]] = accounts[from[self]] - amount[self]]
                       /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Ret"]
                       /\ UNCHANGED accounts
            /\ UNCHANGED << stack, from, to, amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ accounts' = [accounts EXCEPT ![to[self]] = accounts[to[self]]   + amount[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Ret"]
                 /\ UNCHANGED << stack, from, to, amount >>

Ret(self) == /\ pc[self] = "Ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ from' = [from EXCEPT ![self] = Head(stack[self]).from]
             /\ to' = [to EXCEPT ![self] = Head(stack[self]).to]
             /\ amount' = [amount EXCEPT ![self] = Head(stack[self]).amount]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED accounts

Transfer(self) == Tx(self) \/ Deposit(self) \/ Ret(self)

Loop(self) == /\ pc[self] = "Loop"
              /\ pc' = [pc EXCEPT ![self] = "CallTx"]
              /\ UNCHANGED << accounts, stack, from, to, amount >>

CallTx(self) == /\ pc[self] = "CallTx"
                /\ \E receiver \in {"Alice", "Bob", "Charlie"} \ {self}:
                     \E amt \in 1..5:
                       /\ /\ amount' = [amount EXCEPT ![self] = amt]
                          /\ from' = [from EXCEPT ![self] = self]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Transfer",
                                                                   pc        |->  "Loop",
                                                                   from      |->  from[self],
                                                                   to        |->  to[self],
                                                                   amount    |->  amount[self] ] >>
                                                               \o stack[self]]
                          /\ to' = [to EXCEPT ![self] = receiver]
                       /\ pc' = [pc EXCEPT ![self] = "Tx"]
                /\ UNCHANGED accounts

Client(self) == Loop(self) \/ CallTx(self)

Next == (\E self \in ProcSet: Transfer(self))
           \/ (\E self \in {"Alice", "Bob", "Charlie"}: Client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

====
