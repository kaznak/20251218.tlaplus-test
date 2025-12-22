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
