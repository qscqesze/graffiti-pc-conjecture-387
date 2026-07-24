# Graffiti.pc 猜想 387 的一个证明

本仓库收录 JunQing 对 Graffiti.pc 猜想 387 的证明，以及该证明的中文翻译，方便阅读和引用。

## 主要结论

设 $G$ 是一个非空有限简单图，阶为 $n$。将它的度序列按非降序排列为

$$
d_1\le d_2\le\cdots\le d_n,
$$

并定义上中位度

$$
m(G)=d_{\lfloor n/2\rfloor+1}.
$$

若 $\gamma_2(G)$ 表示 $G$ 的 2-支配数，则

$$
\boxed{\gamma_2(G)\le n-m(G)+1}.
$$

这个结论证明了 Graffiti.pc 猜想 387，并且不需要原猜想中的连通性假设。

## 文件

- [中文证明](./proof_zh.md)
- [英文原稿 PDF](./paper/graffiti387_JunQing.pdf)

## 如何引用

GitHub 会读取仓库根目录下的 [`CITATION.cff`](./CITATION.cff)。在仓库页面点击 **Cite this repository**，即可生成 BibTeX 或 APA 格式的引用。

建议题名：

> JunQing. *The 2-Domination Number and the Upper Median Degree: A Proof of Graffiti.pc Conjecture 387*. 2026.

## 关键词

2-支配、支配数、度序列、上中位度、Graffiti.pc、图论。
