# Sondow-Pudlak 程序中的 Euler 常数形式化碰撞定理

作者：James

## 摘要

本文证明一个关于 Euler-Mascheroni 常数的 Lean 4 形式化碰撞定理。在一个固定
的证明检查器测度坐标中，若同一测度函数配备了形式化的多项式上界提供者，则
有理性分支中计算出的碰撞数等于上界尾部 cutoff 与尾部间隙阈值的最大值。在
这个同一自然数处，Lean 证明上界证书与严格尾部间隙证书给出互相矛盾的不等式。
因此，相对于该形式化输入包，Lean 得到
`¬ is_rational euler_mascheroni`。主定理的 Lean 名称为
`cleanUpperProvider_submissionRoute`，其源码和审计记录均可公开复核。

关键词：Euler-Mascheroni 常数；Sondow 判据；Pudlak 下界；证明复杂度；
形式化数学；Lean。

## 1. 引言

设

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac{1}{k}-\log n\right)
```

为 Euler-Mascheroni 常数。`γ` 的无理性是经典而困难的问题。Sondow 的判据
把 `γ` 的有理性假设转化为一类算术证书；证明复杂度中的有限一致性下界则从
另一侧限制这些证书能够被短证明检查的方式。若这两部分能够被放入同一个证明
代码测度坐标，就可以在一个自然数处比较上界和严格下界，并寻求碰撞。

本文完成的是这一方案的形式化碰撞核心。我们不把不同来源的估计放在各自独立
的非形式化叙述中，而是在 Lean 中固定一个共同的检查器测度坐标。给定同一
测度函数上的上界提供者后，Lean 计算有理性分支的碰撞数，并证明该点同时满足
上界证书和严格尾部间隙证书，从而推出矛盾。

更具体地，令 `input` 表示检查器侧输入，令 `upper_provider` 表示同一坐标中
的上界提供者。对任意

```lean
h : is_rational euler_mascheroni
```

记

```lean
N(h) = computedCollisionNOfRationality h.
```

由 `upper_provider` 得到一个上界尾部 cutoff，记为 `upperN(h)`；由同一上界
尾部经过 `input` 中的 tail-gap 结构得到阈值，记为 `threshold(h)`。本文的
主定理可以概括为

```lean
N(h) = max upperN(h) threshold(h)
```

并且同一形式化输入包推出

```lean
¬ is_rational euler_mascheroni.
```

这个结论是条件性的形式化碰撞定理：它精确说明一旦共同测度坐标和上界提供者
作为 Lean 输入给出，碰撞点如何被计算，以及矛盾如何在同一点发生。本文不把
十进制数值阈值抽取作为本稿目标。

## 2. 形式化设定

### 2.1 共同测度坐标

主定理使用的检查器侧对象为

```lean
ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data
```

该对象把 PA Hilbert 风格的证明检查语义、有限搜索、拒绝提取器和 tail-gap
证书组织在同一个测度函数上。共同测度坐标是定理能够成立的关键：上界和严格
下界必须作用于同一个函数，才可能在同一个自然数处相互冲突。

### 2.2 上界尾部和尾部间隙

第二个输入是同一测度坐标上的上界提供者，记为 `UpperProvider(input)`。
在有理性分支 `h` 下，它返回一个上界尾部证书。该证书包含一个多项式有界函数
`U`、一个 cutoff `upperN(h)`，以及从该 cutoff 以后测度函数受 `U` 控制的
形式化证明。精确 Lean 类型见第 4 节给出的源码链接。

同一 `input` 还把这个 `U` 送入 tail-gap 结构，产生阈值 `threshold(h)`。
因此自然的碰撞候选点不是额外选择的参数，而是

```lean
max upperN(h) threshold(h).
```

## 3. 从两侧证书到碰撞点

本节把证明写成普通数学论文中的推导形式。为避免把形式化细节隐藏在 Lean
名称后面，我们记

```math
M(n)
```

为共同测度坐标中的证明代码测度函数。在 Lean 中，这个函数对应
`month9_month10_checkedProofCodeMeasured`。证明的两侧都作用在同一个 `M`
上，这是产生碰撞的必要条件。

### 3.1 Sondow 侧：有理性分支给出上界尾部

从有理性分支

```lean
h : is_rational euler_mascheroni
```

出发，形式化的上界提供者给出一个上界尾部证书

```lean
upper(h) = checkedSearchUpperTail candidate upper_provider h.
```

该证书包含三个主要数据：

```lean
upper(h).U
upper(h).polynomial
upper(h).upperN
```

其中 `upper(h).U` 是一个多项式有界函数，`upper(h).upperN` 是上界开始生效的
cutoff。它的数学内容可以写为

```math
n\geq upperN(h)\quad\Longrightarrow\quad M(n)\leq U(n).
```

这就是本文中使用的 Sondow 侧输出：在有理性分支下，同一测度函数 `M` 最终受
一个多项式上界 `U` 控制。

### 3.2 Pudlak/检查器侧：同一上界触发尾部间隙

现在把同一个 `U` 送入检查器侧的 tail-gap 证书。Lean 中对应对象为

```lean
input.tail_gap.gap_for_polynomial_upper upper(h).U upper(h).polynomial
```

它给出一个阈值

```lean
threshold(h).
```

其数学内容是：一旦自然数越过该阈值，证明复杂度下界会在同一个测度函数 `M`
上严格超过上界函数 `U`。也就是说，

```math
n\geq threshold(h)\quad\Longrightarrow\quad U(n)<M(n).
```

这一步是 Pudlak/检查器侧的贡献：它不是产生另一个测度函数，而是在同一个 `M`
上给出严格的反向不等式。

### 3.3 选择同一个自然数

为了让两侧同时适用，Lean 选择的碰撞候选点是

```math
N(h)=\max\{upperN(h),threshold(h)\}.
```

于是显然有

```math
N(h)\geq upperN(h),\qquad N(h)\geq threshold(h).
```

把 `N(h)` 代入 3.1 节的上界尾部，得到

```math
M(N(h))\leq U(N(h)).
```

把 `N(h)` 代入 3.2 节的 tail-gap 证书，得到

```math
U(N(h))<M(N(h)).
```

这两个不等式发生在同一个自然数 `N(h)` 和同一个测度函数 `M` 上，因此给出

```math
M(N(h))\leq U(N(h))<M(N(h)),
```

矛盾。Lean 中的 `not_rational` 字段正是把这个同点矛盾封装为

```lean
¬ is_rational euler_mascheroni.
```

### 3.4 形式化证明流程图

Lean 本身给出的对象不是自然语言证明图，而是一组可检查定义和定理。将
`#check`、`#print` 以及主定理体展开后，本文使用的证明流可概括如下：

```text
h : is_rational euler_mascheroni
  -> upper = checkedSearchUpperTail candidate upper_provider h
  -> upper supplies U, polynomial, upperN,
     and n >= upperN -> M(n) <= U(n)
  -> gap = input.tail_gap.gap_for_polynomial_upper U polynomial
  -> gap supplies threshold,
     and n >= threshold -> U(n) < M(n)
  -> N = max upperN threshold
  -> M(N) <= U(N) and U(N) < M(N)
  -> False
  -> ¬ is_rational euler_mascheroni
```

在 Lean 文件中，`cleanComputedBigN_eq_tailGapMax` 证明计算出的 `N` 正是
`max upperN threshold`；`cleanProvider_not_rational` 给出有理性分支的矛盾；
`cleanUpperProvider_submissionRoute` 把这两个结论合并为本文的主定理。

## 4. 主定理

主定理在 Lean 中的名称为

```lean
cleanUpperProvider_submissionRoute
```

源码位置为：

[integration/SondowProjectBigNCleanSubmissionRoute.lean](https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean)

省略 namespace 和若干 projection 后，主定理的形式为

```lean
theorem cleanUpperProvider_submissionRoute
    (input : ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (upper_provider : UpperProvider input) :
    (∀ hrat : is_rational euler_mascheroni,
      computedCollisionNOfRationality hrat =
        max upperN threshold) ∧
      ¬ is_rational euler_mascheroni
```

精确 Lean 语句把 `upperN` 展开为 `checkedSearchUpperTail` 返回的 cutoff，并把
`threshold` 展开为 `input.tail_gap.gap_for_polynomial_upper` 返回的阈值。
定理第一部分给出碰撞点的公式，第二部分给出有理性分支的矛盾。

## 5. 证明

证明由上一节的推导和两个 Lean 定理合成。

**引理 5.1（碰撞数计算）。** 对任意有理性分支证明 `h`，

```lean
computedCollisionNOfRationality h =
  max upperN(h) threshold(h).
```

Lean 中对应名称为

```lean
cleanComputedBigN_eq_tailGapMax
```

它说明形式化程序计算出的自然数正是上界尾部 cutoff 与 tail-gap 阈值的最大值。

**引理 5.2（同点矛盾）。** 令 `N = computedCollisionNOfRationality h`。由
引理 5.1 可知 `N ≥ upperN(h)` 且 `N ≥ threshold(h)`。第一个不等式使上界
尾部证书适用于 `N`，给出 `M(N) ≤ U(N)`；第二个不等式使 tail-gap 证书也适用
于同一个 `N`，给出 `U(N) < M(N)`。于是同一测度函数在同一点满足
`M(N) ≤ U(N) < M(N)`，得到矛盾。

Lean 中该矛盾由

```lean
cleanProvider_not_rational
```

以及检查器输入包中的 `not_rational` 字段给出。将引理 5.1 和引理 5.2 组合，
即得 `cleanUpperProvider_submissionRoute`。

## 6. 形式化资料和复核方式

仓库地址：

<https://github.com/james130012/sondow-pudlak-collision-box>

随本文整理的 release：

<https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/clean-bigN-submission-polished-20260708>

主定理源码：

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean>

审计记录：

- 中文：<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_zh.md>
- English：<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_en.md>

复现命令为：

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

主定理和相关引理可用以下命令检查：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNCleanSubmissionRoute
open SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute

#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#print axioms cleanUpperProvider_submissionRoute
#print axioms cleanComputedBigN_eq_tailGapMax
#print axioms cleanProvider_not_rational
EOF
```

主定理观察到的公理输出为

```text
[propext, Classical.choice, Quot.sound]
```

## 7. 结论

本文给出一个可复核的 Lean 形式化碰撞定理：在共同的证明检查器测度坐标中，
有理性分支的碰撞数为 `max upperN threshold`，并且在该同一自然数处产生上界
与严格下界的矛盾。该结果把 Sondow-Pudlak 程序中的核心碰撞机制整理成一个
清楚、可检查、可引用的形式化定理。

阈值数值抽取可以作为后续工作继续推进；本文的投稿贡献是已经完成并可由
Lean 复核的形式化碰撞核心。

## 参考文献

1. J. Sondow, Criteria for irrationality of Euler's constant, *Proceedings of
   the American Mathematical Society* 131 (2003), 3335-3344.
2. S. R. Buss, On Godel's theorems on lengths of proofs I: Number of lines and
   speedup for arithmetics, *Journal of Symbolic Logic* 59 (1994), 737-756.
3. P. Pudlak, On the lengths of proofs of finitistic consistency statements in
   first order theories, in *Logic Colloquium 1984*, North-Holland, 1986.
4. L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming
   language, in *Automated Deduction - CADE 28*, 2021.
