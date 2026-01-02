---
title: "Lean の部分リスト(Sublist)について"
emoji: "🧺"
type: "tech"
topics: ["Lean", "Lean4", "形式証明"]
published: true
---

## Sublist

リスト`l₁ : List α`が`l₂ : List α`の部分リスト(sublist)であるとは、`l₁`に新たに要素を挿入することを繰り返すことで`l₂`が得られることをいいます。
別な言い方をすれば、`l₂`の中に`l₁`の要素が順序を保ったまま現れる、ということです。
これは Lean では `List.Sublist` という名前で定義されており、`l₁ <+ l₂` という表記が用意されています。

```lean
-- `List`名前空間をopenしないとこの記法は使えない
open List

#check List.Sublist

#guard [1, 3] <+ [0, 1, 2, 3, 4]
```

なお`Sublist l₁ l₂` では `l₁` は `l₂` の中に連続的に現れていなくてもよかったのですが、連続的に現れなければならないという制約を課したものは `List.IsInfix` として定義されています。
これには `l₁ <:+: l₂` という表記が用意されています。

```lean
#check List.IsInfix

#check [1, 2] <:+: [1, 2]
```

## 自前で定義する

部分リストの概念をじかに触ってみたいので、標準ライブラリにすでにあるのですが自前で定義しましょう。
名前は`List.Subseq`とします。

### Bool 値の再帰関数として実装する

帰納的述語としての定義をいきなり書くのはちょっと難しいです。
`Subseq`が満たすべき性質を列挙するのは簡単で、たとえば以下のようなものがすぐ思いつくでしょう。

* 空リストはすべてのリストの部分リスト
* `c`が`l`の部分リストであれば、`c`は`l ++ l'`の部分リストでもある

しかし、「どれを帰納的述語のコンストラクタ（つまり公理）として採用するか」は悩ましい問題です。
公理を採用しすぎて独立でなくなってしまったら証明に無駄な労力がかかりますし、公理が足りなくて証明できない命題が発生するのも困ります。
そこで、まずは計算方法を考えます。次のように定義できます。

```lean
variable {α : Type}

def List.isSubseq [DecidableEq α] (xs ys : List α) : Bool :=
  match xs, ys with
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    if x = y then
      isSubseq xs ys
    else
      isSubseq (x :: xs) ys
```

この段階で定義ミスをするのは嫌なので、テストを用意しておきましょう。

```lean
open List

#guard isSubseq [] [1, 2, 3]
#guard !isSubseq [1, 2] []
#guard isSubseq [1, 2] [1, 2, 3]
#guard isSubseq [1, 2] [0, 1, 2, 3]
#guard isSubseq [1, 3] [0, 1, 2, 3]
#guard !isSubseq [3, 1] [0, 1, 2, 3]
#guard !isSubseq [1, 4] [0, 1, 2, 3]
```

大丈夫そうですね。

### 帰納的述語として定義する

上記の再帰関数としての定義をもとに、帰納的述語としての定義を与えます。
再帰呼び出しをしている部分を帰納的ステップに置き換えることに注意してください。

```lean
inductive List.Subseq : List α → List α → Prop where
  /-- 空リストはすべてのリストの部分リスト -/
  | nil (ys : List α) : Subseq [] ys

  /-- `xs` が `ys` の部分リストなら、`z :: xs` は `z :: ys` の部分リスト -/
  | consEq {xs ys : List α} (h : Subseq xs ys) (z : α) :
    Subseq (z :: xs) (z :: ys)

  /-- `xs` が `ys` の部分リストなら、`xs` は `y :: ys` の部分リスト -/
  | cons {xs ys : List α} (h : Subseq xs ys) (y : α) :
    Subseq xs (y :: ys)
```

### 定義の同値性を示す

同じ概念の二通りの定義が得られたので、これらが同じものであることを示しましょう。

```lean
attribute [grind] List.Subseq List.isSubseq

variable {xs ys : List α}

theorem List.Subseq_of_cons {x : α} (h : Subseq (x :: xs) ys) :
    Subseq xs ys := by
  induction ys generalizing x xs with grind

-- 定理の前提条件が満たされたときにインスタンス化されるように指定する
grind_pattern List.Subseq_of_cons => Subseq (x :: xs) ys

@[simp]
theorem List.Subseq_consEq {z : α} :
    Subseq (z :: xs) (z :: ys) ↔ Subseq xs ys := by grind

theorem List.isSubseq_iff_Subseq [DecidableEq α] (xs ys : List α) :
    xs.isSubseq ys = true ↔ Subseq xs ys := by
  fun_induction isSubseq with grind
```

計算可能な実装を与えて、それが同値だと示したので、決定可能性も得られます。

```lean
/-- 部分リストかどうかは決定可能 -/
instance [DecidableEq α] : Decidable (Subseq xs ys) :=
  decidable_of_iff (xs.isSubseq ys = true) (@List.isSubseq_iff_Subseq _ _ xs ys)

#guard Subseq [1, 3] [0, 1, 2, 3]
```

## 二項関係としての性質を示す

部分リストであるという二項関係は、反射的かつ推移的かつ反対称的です。
これを示していきましょう…といっても、証明は`grind`でしばけばすぐに終わってしまうのですが。

```lean
@[refl, grind ·, simp]
theorem List.Subseq_refl : Subseq xs xs := by
  induction xs with grind

theorem List.Subseq_trans {zs : List α} (h₁ : Subseq xs ys) (h₂ : Subseq ys zs) :
    Subseq xs zs := by
  induction h₂ generalizing xs with grind

-- 定理の前提条件が満たされたときにインスタンス化されるように指定する
grind_pattern List.Subseq_trans => Subseq xs ys, Subseq ys zs

theorem List.Subseq_antisymm (h₁ : Subseq xs ys) (h₂ : Subseq ys xs) : xs = ys := by
  induction xs generalizing ys with grind

-- 定理の前提条件が満たされたときにインスタンス化されるように指定する
grind_pattern List.Subseq_antisymm => Subseq xs ys, Subseq ys xs
```

## 感想

このまま基本的な性質をずんずん示していくのも楽しいと思いますが、この記事ではこの辺でやめておきます。
`grind`が非常に強力で、証明が全部１行で終わってしまったのには少し驚きました。
