/-
---
title: "挿入ソートの安定性をLeanで形式化する"
emoji: "😸"
type: "tech"
topics: ["Lean", "Lean4", "形式証明"]
published: false
---
-/

/-
## 挿入ソートを定義して、ソートであることを示す
-/
import Lean.LibrarySuggestions.Default

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

/-
## 「ソート済み」を定義する
-/

/-- 二項関係Rがリストの隣接要素に対して成立する。
たとえば、`[a, b, c].IsChain R` は `R a b ∧ R b c` と等しい。-/
@[grind]
inductive IsChain (R : α → α → Prop) : List α → Prop
  | nil : IsChain R []
  | single (a : α) : IsChain R [a]
  | cons {a b : α} {bs : List α} (h₁ : R a b) (h₂ : IsChain R (b :: bs)) :
    IsChain R (a :: b :: bs)

abbrev Sorted (as : List α) := as.IsChain (· ≤ ·)


-- この仮定が必要
variable [Std.IsLinearOrder α]

@[grind =>]
theorem sorted_orderedInsert (a : α) (as : List α) (h : Sorted as) :
    Sorted (orderedInsert a as) := by
  induction as with grind

@[grind <=]
theorem sorted_insertionSort (as : List α) : Sorted (insertionSort as) := by
  fun_induction insertionSort as with grind

end List


-- Key を与えてもう一度
namespace List

variable {α : Type}
variable {β : Type} [LE β] [DecidableLE β]

@[grind]
def orderedInsertByKey (a : α) (as : List α) (key : α → β) : List α :=
  match as with
  | [] => [a]
  | b :: bs =>
    if key a ≤ key b then
      a :: b :: bs
    else
      b :: orderedInsertByKey a bs key

/-- 挿入ソート -/
def insertionSortByKey (as : List α) (key : α → β) : List α :=
  match as with
  | [] => []
  | a :: bs => orderedInsertByKey a (insertionSortByKey bs key) key

/-- 指定された key に従ってソート済みと判定される -/
abbrev SortedByKey (as : List α) (key : α → β) := as.map key |>.IsChain (· ≤ ·)

variable [Std.IsLinearOrder β]

@[grind =>]
theorem sorted_orderedInsertByKey (a : α) (as : List α) (key : α → β) (h : SortedByKey as key) :
    SortedByKey (orderedInsertByKey a as key) key := by
  fun_induction orderedInsertByKey <;> grind [= SortedByKey.eq_def, = orderedInsertByKey.eq_def]

@[grind <=]
theorem sorted_insertionSortByKey (as : List α) (key : α → β) : SortedByKey (insertionSortByKey as key) key := by
  fun_induction insertionSortByKey with grind

end List

/- ## 安定性を形式化する -/
variable {α : Type}
variable {β : Type} [LE β] [DecidableLE β]
variable (as : List α) (key : α → β)

open List

example (c l : List α) (hcl : c <+ l) (hc : c.SortedByKey key) :
    c <+ insertionSortByKey l key := by
  fun_induction insertionSortByKey l key generalizing c with
  | case1 =>
    grind
  | case2 a as ih =>
    -- try?
    -- わかんねぇ
    sorry
