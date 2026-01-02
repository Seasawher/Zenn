---
title: "挿入ソートの安定性をLeanで形式化する"
emoji: "😸"
type: "tech"
topics: ["Lean", "Lean4", "形式証明"]
published: true
---

## 挿入ソートを定義して、ソートであることを示す

まず話の前提として、挿入ソートを定義してそれがソート済みのリストを返すことを証明します。

```lean
import Batteries

namespace List

variable {α : Type} [LE α] [DecidableLE α]

/-- リストに要素を挿入する。
引数のリストがそもそもソート済みであれば、
挿入後のリストもソート済みになることが期待される。 -/
@[grind]
def orderedInsert (a : α) (as : List α) : List α :=
  match as with
  | [] => [a]
  | b :: bs =>
    if a ≤ b then
      a :: b :: bs
    else
      b :: orderedInsert a bs

/-- 挿入ソート -/
def insertionSort (as : List α) : List α :=
  match as with
  | [] => []
  | a :: bs => orderedInsert a (insertionSort bs)

abbrev Sorted (as : List α) := as.IsChain (· ≤ ·)

-- この仮定が必要
variable [Std.IsLinearOrder α]

@[grind =>]
theorem sorted_orderedInsert (a : α) (as : List α) (h : Sorted as) :
    Sorted (orderedInsert a as) := by
  induction as with grind [IsChain]

@[grind <=]
theorem sorted_insertionSort (as : List α) : Sorted (insertionSort as) := by
  fun_induction insertionSort as with grind

end List
```

## 安定性を示す

本題は安定性でした。
安定性の表現として、ここでは`key : α → β`という関数を導入し、「`key`の値によってソートする」という関数に書き換えます。
Mathlibでは異なるアプローチをとっていますが、ここでこの方法を採用したのは、`β`が仮に Linear Order であっても意味を失わないようにするためです。

```lean
namespace List

variable {α : Type}
variable {β : Type} [LE β] [DecidableLE β]

@[grind, simp]
def orderedInsertByKey (a : α) (as : List α) (key : α → β) : List α :=
  match as with
  | [] => [a]
  | b :: bs =>
    if key a ≤ key b then
      a :: b :: bs
    else
      b :: orderedInsertByKey a bs key

/-- 挿入ソート(key 付) -/
def insertionSortByKey (as : List α) (key : α → β) : List α :=
  match as with
  | [] => []
  | a :: bs => orderedInsertByKey a (insertionSortByKey bs key) key

/-- 指定された key に従ってソート済みか判定 -/
abbrev SortedByKey (as : List α) (key : α → β) := as.map key |>.IsChain (· ≤ ·)

variable [Std.IsLinearOrder β]

@[grind =>]
theorem sorted_orderedInsertByKey (a : α) (as : List α) (key : α → β) (h : SortedByKey as key) :
    SortedByKey (orderedInsertByKey a as key) key := by
  fun_induction orderedInsertByKey <;> grind [= SortedByKey.eq_def, = orderedInsertByKey.eq_def]

@[grind <=]
theorem sorted_insertionSortByKey (as : List α) (key : α → β) : SortedByKey (insertionSortByKey as key) key := by
  fun_induction insertionSortByKey with grind


variable {β : Type} [LE β] [DecidableLE β]
variable (as : List α) (key : α → β)

@[grind <-]
theorem sublist_orderedInsertByKey (a : α) (c as : List α) (key : α → β)
    (h : c <+ as) : c <+ orderedInsertByKey a as key := by
  induction h with grind

@[grind <-]
theorem cons_sublist_orderedInsertByKey (a : α) (c as : List α) (key : α → β)
    (hc : (a :: c).SortedByKey key) (has : as.SortedByKey key)
    (h : c <+ as) : a :: c <+ orderedInsertByKey a as key := by
  induction h generalizing a with simp <;> grind [IsChain]

/-- 挿入ソートは安定 -/
theorem insertionSort_stable (c l : List α) (hcl : c <+ l) (hc : c.SortedByKey key) [Std.IsLinearOrder β] :
    c <+ insertionSortByKey l key := by
  fun_induction insertionSortByKey l key generalizing c with grind

end List
```

## 感想

* ここではMathlibにおける安定性の定義に文句をつけていますが、もしかしたら私の理解不足で、Mathlibが正しいのかもしれません。
* ここで示している安定性は、「`key`の値が等しい要素が元のリストと等しい順序で並ぶ」という一般的な定義より少し強いものになっています。
  部分リスト(非連続であることに注意)の言葉で書いた方がわかりやすく、しかも強いならそれでいいなと思ってこうしました。
* `insertionSort`の安定性について話をしているにも関わらず、`insertionSortByKey`という別な関数の安定性を証明しているのはちょっともやもやします。
  しかし、`α`が Linear Order であるときには `l : List α` に対するどんなソートも安定になるような気がしている（間違っていたらコメントで教えてください）ので、こういう定義がいいかなと思いました。
