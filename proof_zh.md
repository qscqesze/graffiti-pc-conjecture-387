# 2-支配数与上中位度：Graffiti.pc 猜想 387 的一个证明

作者：JunQing

## 摘要

设 $G$ 是一个阶为 $n$ 的非空有限简单图，$m(G)$ 是其度序列的上中位度。我们证明

$$
\gamma_2(G)\le n-m(G)+1,
$$

其中 $\gamma_2(G)$ 是集合 $D\subseteq V(G)$ 的最小基数，使得 $D$ 外的每个顶点在 $D$ 中至少有两个邻点。这证明了 Graffiti.pc 猜想 387。事实上，论证还表明原表述中的连通性假设并非必要。证明使用补图，以及一族对选定非邻点集进行编码的极小线性相关多项式。

**2020 数学主题分类：** 05C69<br>
**关键词：** 2-支配、支配数、度序列、上中位度、Graffiti.pc。

## 1. 引言

本文中的图均为有限简单图。若集合 $D\subseteq V(G)$ 满足：$V(G)\setminus D$ 中的每个顶点在 $D$ 中至少有两个邻点，则称 $D$ 为一个 **2-支配集**。这种集合的最小基数称为 **2-支配数**，记作 $\gamma_2(G)$。关于图支配理论的一般背景，参见文献 [2]。

将一个 $n$ 阶图 $G$ 的度序列按非降序排列为

$$
d_1\le d_2\le\cdots\le d_n.
$$

它的 **上中位度** 定义为

$$
m(G)=d_{\lfloor n/2\rfloor+1}.
$$

由 Graffiti.pc 生成并由 DeLaViña、Larson、Pepper 与 Waller 记录的一个猜想 [1, Conjecture 1] 预言：对于连通图，有上界

$$
\tag{1}\gamma_2(G)\le n-m(G)+1.
$$

文献 [1] 中该猜想的展示公式写成了相反的不等号；然而，紧接在它前面的句子明确陈述了上界 (1)，其后的讨论与部分结果也都采用上界方向。因此，展示公式中的符号是排版错误。

我们将对每个非空有限简单图证明这一猜想中的不等式，而不假设图是连通的。

**定理 1.** 设 $G$ 是一个阶为 $n$ 的非空有限简单图，则

$$
\gamma_2(G)\le n-m(G)+1.
$$

证明所需的唯一代数工具，是下面关于多项式之间极小线性相关性的初等引理。

## 2. 一个多项式引理

**引理 1.** 设 $B$ 是有限集合，$t\ge 0$，并为每个 $z\in B$ 选取两两不同的实数 $a_z$。设 $A_1,\ldots,A_r$ 是 $B$ 的 $t$ 元子集，并定义

$$
p_i(X)=\prod_{z\in A_i}(X-a_z)\qquad(1\le i\le r).
$$

假设带指标族 $(p_i)_{i=1}^r$ 在 $\mathbb R$ 上极小线性相关。令

$$
P=\bigcap_{i=1}^r A_i,\qquad s=|P|.
$$

则：

1. $2\le r\le t+2$；
2. $B\setminus P$ 中的每个元素至多属于集合 $A_1,\ldots,A_r$ 中的 $r-2$ 个；
3. $s\le t+2-r$。

**证明.** 每个 $p_i$ 都非零，所以 $r\ge 2$。极小相关性意味着其中任意 $r-1$ 个多项式都线性无关。所有 $p_i$ 都属于次数至多为 $t$ 的实多项式所构成的 $(t+1)$ 维向量空间，因此

$$
r-1\le t+1,
$$

从而 $r\le t+2$。

选取一个非平凡线性关系

$$
\tag{2}\sum_{i=1}^r c_i p_i=0.
$$

由极小性可知，对每个 $i$ 都有 $c_i\ne 0$。如果某个 $z\in B$ 恰好属于 $A_i$ 中的 $r-1$ 个，那么在 (2) 中令 $X=a_z$，就只会剩下一个非零项。事实上，若 $z\notin A_j$，则

$$
p_j(a_z)=\prod_{u\in A_j}(a_z-a_u)\ne 0,
$$

因为各个 $a_u$ 两两不同。这就产生矛盾。因此，一个至少出现在 $r-1$ 个集合中的元素必然出现在全部 $r$ 个集合中。于是，$P$ 外的每个元素至多出现在 $r-2$ 个集合中。

最后，定义

$$
g(X)=\prod_{z\in P}(X-a_z),
$$

并写成 $p_i=g\widetilde p_i$。乘以非零多项式 $g$ 是一个单射，所以带指标族 $(\widetilde p_i)_{i=1}^r$ 仍然极小线性相关。每个 $\widetilde p_i$ 的次数为 $t-s$，故其中任意 $r-1$ 个都在一个维数为 $t-s+1$ 的向量空间中线性无关。因此

$$
r-1\le t-s+1.
$$

等价地，$s\le t+2-r$。证毕。

## 3. 主定理的证明

**定理 1 的证明.** 记 $m=m(G)$。若 $m=0$，则 $V(G)$ 是一个 2-支配集，并且

$$
\gamma_2(G)\le n<n+1=n-m+1.
$$

因此以下设 $m\ge 1$。令 $F=\overline G$，并设

$$
t=n-1-m,\qquad q=t+2=n-m+1.
$$

特别地，$0\le t\le n-2$ 且 $2\le q\le n$。

定义

$$
H=\{x\in V(G):d_F(x)\le t\},\qquad B=V(G)\setminus H,
$$

并记 $h=|H|$、$k=|B|$。由于

$$
d_F(x)=n-1-d_G(x),
$$

一个顶点属于 $H$，当且仅当它在 $G$ 中的度至少为 $m$。根据上中位度的定义，至少有 $\lceil n/2\rceil$ 个顶点的度不小于 $m$。因此

$$
\tag{3}h\ge\left\lceil\frac n2\right\rceil,\qquad
k\le\left\lfloor\frac n2\right\rfloor,\qquad h\ge k.
$$

先设 $k\le t+1$。由于 $k<q\le n$，可以选取一个包含 $B$ 的 $q$ 元集合 $D$。每个 $v\notin D$ 都属于 $H$，所以

$$
d_F(v,D)\le d_F(v)\le t.
$$

因为 $v\notin D$，它在 $F$ 中位于 $D$ 内的邻点，恰好是在 $G$ 中位于 $D$ 内的非邻点。因此

$$
d_G(v,D)=|D|-d_F(v,D)\ge q-t=2.
$$

故 $D$ 是一个 2-支配集。

下面只需考虑

$$
\tag{4}k\ge t+2
$$

的情形。对于每个 $x\in H$，都有

$$
|N_F(x)\cap B|\le d_F(x)\le t.
$$

利用 (4)，将 $N_F(x)\cap B$ 扩充为 $B$ 的一个 $t$ 元子集 $A_x$。为每个 $z\in B$ 选取两两不同的实数 $a_z$，并定义

$$
p_x(X)=\prod_{z\in A_x}(X-a_z)\qquad(x\in H),
$$

其中当 $t=0$ 时空乘积定义为 $1$。

次数至多为 $t$ 的实多项式构成一个 $t+1$ 维向量空间。由 (3) 和 (4)，

$$
h\ge k\ge t+2,
$$

所以带指标族 $(p_x)_{x\in H}$ 线性相关。从中选取一个关于包含关系极小的相关子族，并以集合 $C\subseteq H$ 为其指标集，记 $r=|C|$。把引理 1 用于集合族 $(A_x)_{x\in C}$。令

$$
P=\bigcap_{x\in C}A_x,\qquad s=|P|.
$$

由引理可得

$$
\tag{5}s\le t+2-r,
$$

并且 $B\setminus P$ 中的每个元素至多属于 $r-2$ 个集合 $A_x$（$x\in C$）。

由于 $2\le r\le t+2$，所以 $0\le t+2-r\le t$。结合 (5) 与 $|B|=k\ge t+2$，可以选取 $Y\subseteq B$，使得

$$
P\subseteq Y,\qquad |Y|=t+2-r.
$$

令

$$
D=C\cup Y.
$$

由于 $C\subseteq H$ 且 $Y\subseteq B$，这个并是不交的，并且

$$
|D|=r+(t+2-r)=t+2=q.
$$

任取 $v\notin D$。若 $v\in H$，则直接有

$$
d_F(v,D)\le d_F(v)\le t.
$$

再设 $v\in B$。由于 $P\subseteq Y$ 且 $v\notin Y$，可知 $v\notin P$。于是由引理 1，$v$ 至多属于 $r-2$ 个集合 $A_x$（$x\in C$）。又因为对每个 $x\in C$ 都有 $N_F(x)\cap B\subseteq A_x$，且 $F$ 是无向图，所以

$$
d_F(v,C)=|\{x\in C:v\in N_F(x)\cap B\}|\le r-2.
$$

从而

$$
d_F(v,D)=d_F(v,C)+d_F(v,Y)\le(r-2)+|Y|=t.
$$

我们已经证明，每个 $v\notin D$ 都满足 $d_F(v,D)\le t$。因此

$$
d_G(v,D)=|D|-d_F(v,D)\ge(t+2)-t=2.
$$

所以 $D$ 是一个 2-支配集，并且

$$
|D|=q=n-m+1.
$$

定理得证。

**注 1.** 对每个 $n\ge 2$，这个界都是紧的：对于完全图 $K_n$，有 $m(K_n)=n-1$ 且 $\gamma_2(K_n)=2$。

**注 2.** 整个证明没有使用连通性。因此，这一结论严格加强了 Graffiti.pc 猜想 387 的原始表述。

## 参考文献

[1] E. DeLaViña, C. E. Larson, R. Pepper, and B. Waller, *Graffiti.pc on the 2-domination number of a graph*, Congressus Numerantium 203 (2010), 15-32.

[2] T. W. Haynes, S. T. Hedetniemi, and P. J. Slater, *Fundamentals of Domination in Graphs*, Monographs and Textbooks in Pure and Applied Mathematics, vol. 208, Marcel Dekker, New York, 1998.
