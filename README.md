# TLA+ test

- TLA+ 用 VSCode 拡張:
    - TLA+ (Temporal Logic of Actions) by TLA+ Foundation
        - https://marketplace.visualstudio.com/items?itemName=tlaplus.vscode-ide
- PlusCal/TLA+ 学習リソース:
    - Learn TLA+
        https://learntla.com/index.html

## TLA+ (Temporal Logic of Actions) 拡張の機能

- TLA+:Parse Module
    - tla ファイルの構文解析と PlusCal コードの変換
- TLA+:Check Model with TLC
    - TLC モデルチェッカーを使用して TLA+ モデルを検証
- TLA+:Evaluate Expression
    - TLA+ 式の評価
    - Learn TLA+ で言及される Scratch.tla の式評価を行う際には、この機能を使用する

## ヒント

### TLA+ の構成要素

- 演算子
- 値
    - プリミティブ（整数、文字列、ブール値、モデル値）
    - 集合
    - 関数

### 直積を積極的に使う

グラフの定義の例

```tla+
---- MODULE scratch ----
EXTENDS Integers, TLC, Sequences
Nodes == 1..3
Edges == { e \in Nodes \X Nodes }
====
```

以下の Edges の定義はエラーを引き起こす事があるほか、フィルタリングをすると面倒くさくなる。

1. `Edges == { <<src, dst>> : src, dst \in Nodes }`
    - どうも vscode 拡張ではエラーが起きるケースがあるっぽい？
2. `Edges == { <<src, dst>> : src \in Nodes, dst \in Nodes }`

直積の場合はフィルタリングを分離出来たりするのでよい。

```tla+
---- MODULE scratch ----
EXTENDS Integers, TLC, Sequences
Nodes == 1..3
NoLoop(src, dst) == src # dst
Edges == { e \in Nodes \X Nodes : NoLoop(e[1], e[2]) }
====
```

### 関数と集合を意識して記述する

例えば、長さが 1 から 3 までの整数列の集合を定義したい場合、以下のように記述できる。

```tla+
---- MODULE scratch ----
EXTENDS Integers, TLC, Sequences

S == 1..3
SeqLens == 1..3
BoundedSeqs(s, seqLens) == UNION { [ 1..k -> s ] : k \in seqLens }
MySeqs == BoundedSeqs(S, SeqLens)
====
```

- 配列は` <index> -> <value>`の関数として定義されることを意識すると、様々な長さの配列を簡単に扱うことができる。
- DOMAIN 演算子は様々な型に対して適用できるので、特に理由がなければ DOMAIN を使う方がよい
    - Len は配列にしか使えない
    - DOMAIN は `A -> B` 型の関数に対してであればなんでも使える。
        - そして TLA+ では配列も構造体も関数
