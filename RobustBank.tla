---- MODULE RobustBank ----
EXTENDS Integers, TLC, Sequences

(* --algorithm RobustBank
variable 
    accounts = [p \in {"Alice", "Bob", "Charlie"} |-> 10],
    
    \* 【追加】 送金中のため、どこの口座にもないお金
    in_flight = 0;

define
    Total == accounts["Alice"] + accounts["Bob"] + accounts["Charlie"]
    
    \* 【修正】 不変条件：「口座合計」＋「送金中」＝ 30
    MoneyIsConstant == Total + in_flight = 30
end define;

procedure Transfer(from, to, amount)
begin
  Tx:
    if accounts[from] >= amount then
        accounts[from] := accounts[from] - amount;
        
        \* 口座から引くと同時に「送金中」に加算する（これならお金は消えない！）
        in_flight      := in_flight      + amount; 
        
        Deposit:
        in_flight    := in_flight    - amount; \* 送金中から減らして
        accounts[to] := accounts[to] + amount; \* 口座に入れる
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

      LoopEnd:
        skip;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES pc, accounts, in_flight, stack

(* define statement *)
Total == accounts["Alice"] + accounts["Bob"] + accounts["Charlie"]


MoneyIsConstant == Total + in_flight = 30

VARIABLES from, to, amount

vars == << pc, accounts, in_flight, stack, from, to, amount >>

ProcSet == ({"Alice", "Bob", "Charlie"})

Init == (* Global variables *)
        /\ accounts = [p \in {"Alice", "Bob", "Charlie"} |-> 10]
        /\ in_flight = 0
        (* Procedure Transfer *)
        /\ from = [ self \in ProcSet |-> defaultInitValue]
        /\ to = [ self \in ProcSet |-> defaultInitValue]
        /\ amount = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Loop"]

Tx(self) == /\ pc[self] = "Tx"
            /\ IF accounts[from[self]] >= amount[self]
                  THEN /\ accounts' = [accounts EXCEPT ![from[self]] = accounts[from[self]] - amount[self]]
                       /\ in_flight' = in_flight      + amount[self]
                       /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Ret"]
                       /\ UNCHANGED << accounts, in_flight >>
            /\ UNCHANGED << stack, from, to, amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ in_flight' = in_flight    - amount[self]
                 /\ accounts' = [accounts EXCEPT ![to[self]] = accounts[to[self]] + amount[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Ret"]
                 /\ UNCHANGED << stack, from, to, amount >>

Ret(self) == /\ pc[self] = "Ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ from' = [from EXCEPT ![self] = Head(stack[self]).from]
             /\ to' = [to EXCEPT ![self] = Head(stack[self]).to]
             /\ amount' = [amount EXCEPT ![self] = Head(stack[self]).amount]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << accounts, in_flight >>

Transfer(self) == Tx(self) \/ Deposit(self) \/ Ret(self)

Loop(self) == /\ pc[self] = "Loop"
              /\ pc' = [pc EXCEPT ![self] = "CallTx"]
              /\ UNCHANGED << accounts, in_flight, stack, from, to, amount >>

CallTx(self) == /\ pc[self] = "CallTx"
                /\ \E receiver \in {"Alice", "Bob", "Charlie"} \ {self}:
                     \E amt \in 1..5:
                       /\ /\ amount' = [amount EXCEPT ![self] = amt]
                          /\ from' = [from EXCEPT ![self] = self]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Transfer",
                                                                   pc        |->  "LoopEnd",
                                                                   from      |->  from[self],
                                                                   to        |->  to[self],
                                                                   amount    |->  amount[self] ] >>
                                                               \o stack[self]]
                          /\ to' = [to EXCEPT ![self] = receiver]
                       /\ pc' = [pc EXCEPT ![self] = "Tx"]
                /\ UNCHANGED << accounts, in_flight >>

LoopEnd(self) == /\ pc[self] = "LoopEnd"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                 /\ UNCHANGED << accounts, in_flight, stack, from, to, amount >>

Client(self) == Loop(self) \/ CallTx(self) \/ LoopEnd(self)

Next == (\E self \in ProcSet: Transfer(self))
           \/ (\E self \in {"Alice", "Bob", "Charlie"}: Client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

====
