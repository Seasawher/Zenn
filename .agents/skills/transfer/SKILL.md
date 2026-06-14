---
name: transfer
description: Lean By Example に投稿した記事を Zenn 向けに直すためのスキル。
---

# Lean By Example からの移植

このスキルは、Lean By Example に投稿した記事を Zenn 向けに直すためのスキルです。

## 手順

1. 途中で `*.svg` ファイルを参照している場合は、まず元の `*.typ` ファイルを探す。
  見つけたら、そのファイルを typst でコンパイルして `*.png` ファイルを生成する。
  そのうえで、元の `*.svg` ファイルへの参照を `*.png` ファイルへの参照に置き換える。
  リンク先も `/images/` 配下のリンクに適切に置き換える。

2. 内部リンクを見つけたら、それは Lean by Example 内への記事へのリンクであるはず。
  そこで `https://lean-ja.github.io/` を付けることで正しいリンクへ書き換える。