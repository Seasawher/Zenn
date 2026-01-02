---
title: "Leanでリストの「末尾の要素を取得する関数」について"
emoji: "😸"
type: "tech"
topics: ["Lean", "Lean4", "形式証明"]
published: false
---

```lean
import Lean.LibrarySuggestions.Default

namespace List

variable {α : Type}

@[grind]
def last? (as : List α) : Option α :=
  match as with
  | [] => none
  | [a] => some a
  | _ :: bs => last? bs

@[grind =]
theorem last?_isSome {as : List α} (h : as ≠ []) : as.last?.isSome := by
  fun_induction last? with simp_all

@[grind =, simp]
theorem last?_append_singleton (as : List α) (a : α) :
    last? (as ++ [a]) = some a := by
  induction as with grind

@[grind =]
theorem last?_append (as bs : List α) :
  (as ++ bs).last? = if bs = [] then as.last? else bs.last? := by
  fun_induction last? bs generalizing as with try grind
  | case3 b bs hbs ih =>
    have ih := ih (as ++ [b])
    grind

@[simp]
theorem last?_append_not_nil (as bs : List α) (h : bs ≠ []) :
  (as ++ bs).last? = bs.last? := by
  grind

variable {β : Type}

theorem map_last? (as : List α) (f : α → β) :
    (as.map f).last? = (as.last?).map f := by
  fun_induction last? with grind [= last?.eq_def]

example (as : List α) :
    (reverse as).head? = as.last? := by
  fun_induction last? <;> grind [= last?.eq_def]

/-- リストの最後の要素を「落とす」関数 -/
@[grind]
def dropEnd (as : List α) : List α :=
  match as with
  | [] => []
  | [_] => []
  | b :: bs => b :: dropEnd bs

def last (as : List α) (h : as ≠ []) : α :=
  as.last?.get (by grind)

@[grind =, simp]
theorem singleton_last (a : α) :
    [a].last (by grind) = a := by
  dsimp [last]
  grind

example (as : List α) (h : as ≠ []) : as.dropEnd ++ [as.last h] = as := by
  fun_induction dropEnd with grind [= last]

end List
```
