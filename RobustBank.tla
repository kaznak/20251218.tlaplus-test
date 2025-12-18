---- MODULE RobustBank ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT 
    Clients,      \* クライアントの集合 (例: {"A", "B"})
    MaxAmount,    \* 送金額の最大値 (例: 5)
    InitBalance   \* 初期の所持金

\* 集合 S の要素 x について、f[x] の合計を計算する演算子
RECURSIVE SumSet(_, _)
SumSet(S, f) == 
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE  \* 集合から誰か1人選ぶ
       IN  f[x] + SumSet(S \ {x}, f)   \* その人の分 + 残りの人たち

(* --algorithm RobustBank
variable 
    accounts = [p \in Clients |-> InitBalance],
    in_flight = 0;  \* 送金中のため、どこの口座にもないお金

define
    Total == SumSet(Clients, accounts)

    \* 不変条件 : 口座残高と送金中のお金の合計は常に一定
    MoneyIsConstant == Total + in_flight = Cardinality(Clients) * InitBalance
    \* 不変条件 : 口座残高は負にならない
    NoNegativeBalance == \A p \in Clients : accounts[p] >= 0
end define;

procedure Transfer(from, to, amount)
begin
  Tx:
    if accounts[from] >= amount then
        accounts[from] := accounts[from] - amount;
        in_flight      := in_flight      + amount; \* 送金中に加える
        
        Deposit:
            in_flight    := in_flight    - amount; \* 送金中から減らして
            accounts[to] := accounts[to] + amount; \* 口座に入れる
    end if;
    
  Ret:
    return;
end procedure;

process Client \in Clients
begin
  Loop:
    while TRUE do
      CallTx:
        with receiver \in Clients \ {self},
             amt      \in 1..MaxAmount 
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
Total == SumSet(Clients, accounts)


MoneyIsConstant == Total + in_flight = Cardinality(Clients) * InitBalance

NoNegativeBalance == \A p \in Clients : accounts[p] >= 0

VARIABLES from, to, amount

vars == << pc, accounts, in_flight, stack, from, to, amount >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ accounts = [p \in Clients |-> InitBalance]
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
                /\ \E receiver \in Clients \ {self}:
                     \E amt \in 1..MaxAmount:
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
           \/ (\E self \in Clients: Client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
====
