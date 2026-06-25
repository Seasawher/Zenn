---
title: "[Lean4] 列挙型に対する `ToString` インスタンスの自動生成"
emoji: "🩰"
type: "tech"
topics: ["Lean", "Lean4"]
published: true
---

:::message
この記事は、筆者が Lean by Example に投稿した記事 [列挙型に対する `ToString` インスタンスの自動生成](https://lean-ja.github.io/lean-by-example/EXTRA/EnumToString.html) のコピーです。今後この記事は更新されず、Lean のバージョン更新等が行われるのは Lean by Example に投稿したほうです。
:::

## やりたいことの説明

帰納型であって、すべてのコンストラクタが一切引数を持たないものを、**列挙型(enumeration type)** と呼びます。
たとえば、以下に示すのは列挙型になっている例です。

```lean
/-- 色 -/
inductive Color where
  | red
  | green
  | blue
```

おおまかに、「有限個の候補からどれか一つを選ぶ」という情報だけを持っているのが列挙型であると言えます。

さて、列挙型に対して `ToString` インスタンスを定義する場合、各コンストラクタに対応する文字列を返したい場合が多いでしょう。
上記の例であれば、次のように定義するわけです。

```lean
protected def Color.toString (c : Color) : String :=
  match c with
  | .red => "red"
  | .green => "green"
  | .blue => "blue"

instance : ToString Color where
  toString := Color.toString
```

これは決まりきったルーチンワークなので、「自動化したい」という欲求が湧いてきます。
自動化するにはどうすればいいでしょうか？

## 列挙型であるか判定する

方針としては、列挙型に対してだけ動作する、`ToString` の deriving handler を定義したいです。
`deriving instance ToString for Color` のように書いたら、`Color` の `ToString` インスタンスが自動生成されるようにしたいわけです。
現状では実装していないので、当然失敗します。
これが成功するようにしましょう。

```lean
/- error: No deriving handlers have been implemented for class `ToString` -/
deriving instance ToString for Color
```

deriving handler が内部で何をするかというと、実は手動で定義するときと同じことを自動でやっているだけです。
以下がおおまかな流れです。

1. まず列挙型かどうか判定して、列挙型でなければ即終了
2. 列挙型だったら `instance` コマンドを生成する
3. 生成したコマンドを実行して、インスタンスを作る

したがってまずやるべきことは、列挙型かどうか判定することです。

これには専用の関数が用意されており、`Lean.isEnumType` という関数で判定することができます。

```lean
import Lean

open Lean Meta

-- Bool は列挙型
run_meta
  let actual ← isEnumType ``Bool
  assert! actual

-- Nat は列挙型ではない
run_meta
  let actual ← isEnumType ``Nat
  assert! !actual
```

## `instance` コマンドを自動生成する

次の目標は、列挙型に対して `instance` コマンドを自動生成することです。
以下のように実装することができます。

```lean
import Lean

open Lean Elab Command
open Parser.Term

/-- 与えられた 列挙型を表す `declName : Name` に対して、
`ToString` のインスタンスを与える `instance` コマンドを自動生成する -/
def mkToStringInstForEnum (declName : Name) : TermElabM Command := do
  if !(← isEnumType declName) then
    throwError "{declName} は列挙型ではありません"

  let indVal ← getConstInfoInduct declName
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let ctorStr := ctorInfo.name.getString!
    let alt ← `(matchAltExpr| | $(mkIdent ctorName):ident => $(quote ctorStr))
    alts := alts.push alt

  let typeIdent := mkIdent declName
  let ToStringIdent := mkIdent `ToString
  `(command|
    instance : $ToStringIdent:ident $typeIdent:ident := ⟨
      fun x => match x with
      $alts:matchAlt*⟩)
```

いま定義した、`instance` コマンドを生成する関数を具体的な列挙型に対して実行して、得られたコマンドを確認してみましょう。
実際に、好ましい `instance` コマンドが生成されていることが確認できます。

```lean
inductive Direction where
  | north
  | south
  | east
  | west

/-
info: instance : ToString Direction :=
  ⟨fun x✝ =>
    match x✝ with
    | Direction.north => "north"
    | Direction.south => "south"
    | Direction.east => "east"
    | Direction.west => "west"⟩
-/
run_cmd
  let cmd ← liftTermElabM <| mkToStringInstForEnum `Direction
  let fmt ← liftCoreM <| PrettyPrinter.ppCommand cmd
  logInfo <| MessageData.ofFormat fmt
```

得られたコマンドを `elabCommand` 関数で実行してやることで、`Direction` に対する `ToString` インスタンスが自動生成できることも確認できます。

```lean
-- 実際にコマンドを実行して、`ToString` インスタンスを生成する
run_cmd
  let cmd ← liftTermElabM <| mkToStringInstForEnum `Direction
  elabCommand cmd

#guard toString Direction.north = "north"
#guard toString Direction.south = "south"
```

## deriving handler を宣言する

ここまで終わったら、後は deriving handler を宣言するだけです。
`initialize` コマンドで登録することができます。

```lean
open Lean Elab Command

private def mkToStringInstForEnumHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then
    throwError "型が指定されていません"

  for declName in declNames do
    let cmd ← liftTermElabM <| mkToStringInstForEnum declName
    elabCommand cmd
  return true

initialize
  registerDerivingHandler ``ToString mkToStringInstForEnumHandler
```

これで、晴れて `deriving ToString` が列挙型に対して使えるようになりました。
`initialize` コマンドの効果はモジュール（ファイルのこと）を跨がないと発生しないのですが、ファイルを跨げばこういう感じで書けるようになっているはずです。

```lean
inductive Hoge where
  | a
  | b
  | c
deriving ToString

#guard toString Hoge.a = "a"
#guard toString Hoge.c = "c"
```
