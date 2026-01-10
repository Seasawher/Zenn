---
title: "List.IsInfix を決定可能にする"
emoji: "🔮"
type: "tech"
topics: ["Lean", "Lean4", "形式証明"]
published: true
---

## List.IsInfix について

リスト `xs : List α` に対して、`xs` が `ys` の連続部分列(infix)であるというのは、Lean では `List.IsInfix` という述語として定義されています。

```lean
-- 標準ライブラリにある定義
#check List.IsInfix
```

ただこれには決定可能(Decidable)インスタンスがなく、`decide` タクティクが使えません。

```lean
example : List.IsInfix [2, 3] [1, 2, 3, 4] := by
  fail_if_success decide
  exists [1], [4]
```

以下のような関数を定義することで、`List.IsInfix` に対して決定可能性インスタンスを与えることができます。

```lean
@[simp, grind]
def List.isInfix [DecidableEq α] (xs ys : List α) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | xs, ys@(_ :: ys') =>
    if isPrefixOf xs ys then
      true
    else
      isInfix xs ys'

#guard [2, 3].isInfix [1, 2, 3, 4]
#guard [1, 2].isInfix [1, 2, 3, 4]
#guard [3, 4].isInfix [1, 2, 3, 4]
#guard ! [2, 4].isInfix [1, 2, 3, 4]

theorem List.IsInfix_iff_isInfix [DecidableEq α] (xs ys : List α) :
    xs.isInfix ys ↔ List.IsInfix xs ys := by
  fun_induction List.isInfix with (simp_all <;> grind [List.infix_cons_iff])

instance [DecidableEq α] (xs ys : List α) : Decidable (List.IsInfix xs ys) :=
  decidable_of_iff _ (List.IsInfix_iff_isInfix xs ys)

example : List.IsInfix [2, 3] [1, 2, 3, 4] := by
  decide
```

## 補足

ここで与えた決定可能インスタンスは素朴で証明しやすいですが、実行効率的には最善ではないです。
（`isPrefixOf`による判定を無策に繰り返すため）
また、Mathlib には既に決定可能性インスタンスがありますね: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Infix.html#List.decidableInfix

こういうパターンの決定には KMP法（Knuth-Morris-Pratt法）のような効率的な方法があります。
KMP法のLeanによる実装は存在します。

* https://github.com/leanprover-community/batteries/blob/main/Batteries/Data/Array/Match.lean
* https://github.com/leanprover-community/batteries/blob/main/Batteries/Data/List/Matcher.lean
* https://github.com/leanprover-community/batteries/blob/main/Batteries/Data/String/Matcher.lean

ただ、正しさの証明がまだないという状況のようです。
(興味がある方は実装してみてPRを送ってみると良いかもしれないですね)
