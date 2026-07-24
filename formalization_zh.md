# Lean 机器验证说明

本仓库已经补充完整的 Lean 4 + mathlib 形式化证明。验证对象不是若干有限图的
计算实验，而是对任意非空有限简单图的统一证明；形式化定理同样不需要连通性。

## 验证的命题

在 `Graffiti387/Main.lean` 中：

- `TwoDominates G D` 表示 $D$ 外每个顶点在 $D$ 中至少有两个邻点；
- `twoDominationNumber G` 表示所有 2-支配集基数的下确界；
- `upperMedianDegree G` 用等价的次序统计量刻画：它是满足“至少
  $\lceil n/2\rceil$ 个顶点的度不小于 $m$”的最大整数 $m$。这正是将度序列
  非降排列后第 $\lfloor n/2\rfloor+1$ 项；
- `graffiti_pc_387` 构造满足
  $|D|\le n-m(G)+1$ 的 2-支配集；
- `twoDominationNumber_le` 推出
  $\gamma_2(G)\le n-m(G)+1$。

## 证明如何对应原文

`Graffiti387/Polynomial.lean` 完整形式化了原证明的代数核心：

1. 用根集合构造多项式；
2. 从线性相关族中取关于包含关系极小的相关子族；
3. 证明极小关系的每个系数都非零；
4. 证明公共根因子可以约去，且公共根数满足精确的维数界；
5. 得到图论部分需要的 `polynomialCircuitSelection` 选择引理。

原文把不同根选在实数中；形式化证明直接把有限集合嵌入有理数，因而在
$\mathbb Q[X]$ 上完成全部论证。这不会减弱结论，反而给出了更具体的代数模型。

`Graffiti387/Main.lean` 随后处理图论部分：

1. 证明一个顶点的邻点数与自身以外的非邻点数之和为 $n-1$；
2. 当低度顶点较少时，把它们扩充成所需大小的集合；
3. 当低度顶点较多时，调用多项式选择引理构造 $C\cup Y$；
4. 分别验证集合外的高度、低度顶点至多有 $t$ 个非邻点落在构造集合中；
5. 由集合大小为 $t+2$ 推出至少有两个邻点。

## 如何复核

工具链版本已经固定为 Lean 4.32.1 和 mathlib v4.32.1。在仓库根目录执行：

```bash
lake exe cache get
lake build
```

`Graffiti387/Verification.lean` 会让 Lean 输出两个最终定理的基础依赖。目前输出
只有 mathlib 通常使用的 `propext`、`Classical.choice` 和 `Quot.sound`，没有项目
自行声明的公理。

GitHub Actions 还会在每次推送和拉取请求时：

1. 扫描并拒绝 `sorry`、`admit` 和自定义 `axiom`；
2. 重新下载匹配版本的依赖；
3. 从源码构建整个 Lean 项目。

因此，“证明文字完整”和“机器能够从源码重复检查”是两条独立的核验链。
