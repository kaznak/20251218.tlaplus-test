---- MODULE RobustBank ----
EXTENDS Integers, TLC, Sequences

(* --algorithm RobustBank
variable 
    accounts = [p \in {"Alice", "Bob", "Charlie"} |-> 10]; \* 3人とも10円持ち

define
    \* 全員の所持金合計を計算する数式
    Total == accounts["Alice"] + accounts["Bob"] + accounts["Charlie"]
    
    \* 不変条件: 3人合わせれば常に30円あるはず
    MoneyIsConstant == Total = 30
end define;

procedure Transfer(from, to, amount)
begin
  Tx:
    \* 原子性を持たせていないため、ここで競合バグが起きる可能性が高い！
    \* (あえてロックをかけない例です)
    if accounts[from] >= amount then
        accounts[from] := accounts[from] - amount;
        accounts[to]   := accounts[to]   + amount;
    end if;
    return;
end procedure;

\* 3人のクライアントプロセスを生成
process Client \in {"Alice", "Bob", "Charlie"}
begin
  Loop:
    while TRUE do \* 無限ループ（停止条件なし）
      
      \* 自分以外のだれか(receiver)に、1～5円のどれか(amt)を送る
      with receiver \in {"Alice", "Bob", "Charlie"} \ {self},
           amt      \in 1..5 
      do
           call Transfer(self, receiver, amt);
      end with;
      
    end while;
end process;

end algorithm; *)
