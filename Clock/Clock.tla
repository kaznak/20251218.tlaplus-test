---- MODULE Clock ----
EXTENDS Integers, TLC, Sequences

\* 時計の時刻の型 (時、分、秒)
ClockType == (0..23) \X (0..59) \X (0..59)

\* 時計の時刻を秒数に変換する演算子
ToSeconds(time) == time[1]*60*60 + time[2]*60 + time[3]

\* 秒数を時計の時刻に変換する演算子
ToClock(seconds) ==
  LET seconds_per_day == 60*60*24 \* 一日の秒数
  IN CHOOSE x \in ClockType: ToSeconds(x) = seconds % seconds_per_day
====
