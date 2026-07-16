---
title: "[Lean4] CLI バージョンを自動更新するために、まずは suggest を出すようにした"
emoji: "🫠"
type: "tech"
topics: ["Lean", "Lean4"]
published: true
---

この記事は、以前書いた次の記事の続きです。

https://zenn.dev/seasawher/articles/600cf2d889fa40

## おさらい

Lean で作った CLI ツールの、バージョンを表す文字列の更新を忘れるという問題の対処法を考えています。

`Lean.versionString` を参照するという方法を試しましたが、これは上手くいきません。
「ツールのバージョン」ではなくて「ツールを使おうとしているパッケージの Lean バージョン」を参照してしまうためです。

## 今回考えた方法

あれからずっと考えていたのですが、try this suggestion を出すのはどうかと思いました。

具体的にはこうします。

https://github.com/Seasawher/mdgen/blob/c2207016610cf351bbe61a4856421b0ba4a9365e/Mdgen/VersionString.lean

Lean が読める人でも何をしているのかわかる人は少ないと思うので説明すると、次のようなことをしています。

* `version%` という項エラボレータを用意する
* `version% "v4.32.0"` などのようにして使う。
  `v4.32.0` の部分は文字列リテラルを入れる。
  そのときの `Lean.versionString` の値と一致しないとき、try this suggestion を出す。
* ただし try this suggestion というのは、エディタ上で「ワンクリックで適用できる code action」のこと。
  こんな感じに表示されます。

  ![try this](/images/cliver/trythis.png)

## 今後の展望

これで try this suggestion をクリックするだけで更新できるようになりました。

まだ「手動でクリックする」手間が残っているので完全自動ではないですが、次に「try this suggestion を自動で適用する CLI」を書けば自動適用できると思います。

そしてそういう CLI は Lean FRO 公式が用意してくれるかもしれないので、結構期待できると思います。