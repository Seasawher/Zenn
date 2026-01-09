/-
---
title: "リストの接頭辞を列挙する関数について"
emoji: "😎"
type: "tech"
topics: ["Lean", "Lean4", "形式証明"]
published: true
---
-/

/-
## isPrefix の定義

リストの接頭辞(prefix)について考えてみましょう。
リスト`xs : List α`が`ys : List α`の接頭辞であるということを判定する再帰関数は次のように書けます。
-/

/-- リスト`xs`が`ys`の接頭辞であるかどうか判定する再帰関数 -/
@[grind =]
def List.isPrefix [DecidableEq α] (xs ys : List α) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => (x = y) && isPrefix xs ys

-- 簡単なテスト
#guard [1, 2].isPrefix [1, 2, 3]
#guard ! [1, 3].isPrefix [1, 2, 3]

/-
Lean の標準ライブラリには、この概念は`List.isPrefixOf`として定義されています。
(探し方: Loogle で `List ?a → List ?a → Bool` で検索すれば見つかります)
ここでは自前で定義して、この概念を少し触ってみましょう。
-/

-- 標準ライブラリにある同様の概念
#check List.isPrefixOf

/-
## Prefix の定義

`isPrefix` には異なる定義を与えることもできます。
単純に、`xs ++ zs = ys` となる `zs : List α` が存在することをもって定義することもできますね。
その方針で定義してみましょう。
-/

/-- リスト`xs`が`ys`の接頭辞であることを主張する帰納的述語 -/
@[grind =]
def List.Prefix (xs ys : List α) : Prop := ∃ zs : List α, ys = xs ++ zs

-- 標準ライブラリにある類似の概念
#check List.IsPrefix

/-
同じ概念の異なる２つの定義が手に入ったので、同値性を示したくなりますね。
示しましょう。
ここでは両者の定義はかなり異なっていますが、同値性は定義に沿って帰納法を使えば示すことができます。
Lean にとってはほとんど明らかです。
-/

@[grind <=]
theorem List.nill_Prefix (ys : List α) : List.Prefix [] ys := by
  exists ys

@[grind =, simp]
theorem List.Prefix_nill_iff (xs : List α) : List.Prefix xs [] ↔ xs = [] := by
  constructor
  · intro h
    rcases h with ⟨zs, hz⟩
    simp_all
  · grind

theorem List.isPrefix_iff_Prefix [DecidableEq α] (xs ys : List α) :
    xs.isPrefix ys ↔ List.Prefix xs ys := by
  -- isPrefix の定義に沿った帰納法を使えば示すことができる
  fun_induction isPrefix with grind

/-
## prefix を列挙する

ここからが本題です。
与えられたリストの接頭辞(prefix)をすべて列挙する関数を定義してみましょう。
(Batteries に `List.inits` として同様の関数があります)
以下のように再帰的に定義することができます。
-/

/-- 与えられたリストの接頭辞(prefix)をすべて列挙する -/
@[simp, grind =]
def List.prefixes (xs : List α) : List (List α) :=
  match xs with
  | [] => [[]]
  | x :: xs => [] :: xs.prefixes.map (x :: ·)

-- 簡単なテスト
#guard [1, 2, 3].prefixes = [[], [1], [1, 2], [1, 2, 3]]

/-
この列挙関数の正しさを示すのがこの記事のテーマです。

### 列挙されるのが確かに prefix であること

まず、列挙されているのが確かに prefix になっていることを示しましょう。
これは帰納法によって直ちに示すことができます。
-/

@[grind ->]
theorem List.isPrefix_of_prefixes [DecidableEq α] (xs : List α) :
    ∀ ys ∈ xs.prefixes, isPrefix ys xs := by
  induction xs with grind

/-
### すべての prefix が列挙されること

続いて、漏れがないことを示しましょう。
つまり、すべての prefix が `prefixes` 関数によって列挙されることを示しましょう。
これも、`isPrefix` の定義に沿った帰納法によって直ちに従います。
-/

@[grind ->]
theorem List.prefixes_of_isPrefix [DecidableEq α] (xs ys : List α) :
    isPrefix ys xs → ys ∈ xs.prefixes := by
  fun_induction isPrefix with grind [prefixes.eq_def]

/-
### 重複が無いこと

最後に、重複が無いことを示しましょう。
リストに重複が無いことは `List.Nodup` で表現することができます。
これも帰納法によって直ちに従います。
-/

theorem List.prefixes_Nodup (xs : List α) :
    xs.prefixes.Nodup := by
  induction xs with grind

/-
## おわりに

最後に多少の感想を書きます。

「～を列挙する」系の関数の正しさの証明は、どうすればいいのかなという問題意識でいろいろ例をいじっているときに浮かんだテーマでした。
だいたいは「漏れがない」ことの証明がいちばん難しいと思うのですが、「接頭辞を列挙する」程度の関数であればシンプルなので一撃で示せるということがわかりました。
意外と簡単ですね。

他の「～を列挙する」系の関数についても同様に考えてみるとおもしろいかもなと思っています。
-/
