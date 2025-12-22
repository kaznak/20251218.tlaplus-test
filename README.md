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

### 集合内包表記では複数の変数を使えない

以下は誤り

```tla+
Nodes == 1..3
Edges == { <<src, dst>> | src \in Nodes, dst \in Nodes \ {src} }
```

正しくは以下の通り

```tla+
Nodes == 1..3
Edges == { e \in Nodes \X Nodes : e[1] # e[2] }
```
