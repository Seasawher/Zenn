/- # Lean の部分リストについて

## Sublist

リスト`l₁ : List α`が`l₂ : List α`の部分リスト(sublist)であるとは、`l₁`に新たに要素を挿入することを繰り返すことで`l₂`が得られることをいいます。
別な言い方をすれば、`l₂`の中に`l₁`の要素が順序を保ったまま現れる、ということです。
これは Lean では `List.Sublist` という名前で定義されており、`l₁ <+ l₂` という表記が用意されています。
-/

-- `List`名前空間をopenしないとこの記法は使えない
open List

#check List.Sublist

#guard [1, 3] <+ [0, 1, 2, 3, 4]

/-
`Sublist l₁ l₂` では `l₁` は `l₂` の中に連続的に現れていなくてもよかったのですが、連続的に現れなければならないという制約を課したものは `List.IsInfix` として定義されています。
これには `l₁ <:+: l₂` という表記が用意されています。
-/

#check List.IsInfix

#check [1, 2] <:+: [1, 2]

/- ## MyList に対して定義する

`MyList` に対してこれらを定義して、基本的な性質を示すことにします。
まずは `MyList` を定義します。
-/

/-- 標準にある List を真似て定義した -/
inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)
