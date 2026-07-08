# Sondow-Pudlak 程序中的一个参数闭合形式化碰撞定理

作者：James

## 摘要

本文给出一个 Lean 4 形式化的 Sondow-Pudlak 型碰撞定理。设
`minCheckedCodeSize n` 表示同一 PA-Hilbert 检查器坐标中的最小已检查证明码
长度。本文的主定理把旧路线中显式出现的 `upper_provider`、`tail_gap` 和
`eventually_strict_length` 全部从定理表面移除，剩余输入压缩为一个清楚的
单项式增长下界：对任意自然数 `coeff, degree`，存在显式阈值
`thresholdOfMonomial coeff degree`，使得阈值以后

```lean
coeff * (n + 1)^degree < minCheckedCodeSize n.
```

在该输入下，Lean 证明碰撞指标具有公式

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree
```

并在同一指标处推出上界侧与检查器侧的形式化矛盾，从而得到
`¬ is_rational euler_mascheroni`。主定理名称、复现命令和 residual-constant
审计见第 4、5 节；观察到的 axiom profile 只含标准 Lean/Mathlib 逻辑依赖。

关键词：Euler-Mascheroni 常数；Sondow 判据；Pudlak 下界；证明长度；
形式化数学；Lean。

## 1. 引言

Euler-Mascheroni 常数

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac{1}{k}-\log n\right)
```

的无理性是经典困难问题。Sondow 的判据从有理性假设出发产生可计算的算术上界
结构；Pudlak 型证明复杂度下界则从证明长度方向给出反向限制。若两侧能够在
同一个检查器测度坐标中相遇，便可在某个自然数处形成

```math
M(N)\le U(N)<M(N)
```

式的碰撞。

本文的贡献是把这一碰撞机制整理成一个参数表面更干净的 Lean 定理。旧的
中间路线把 `upper_provider` 与 `tail_gap` 直接暴露在主定理中；本文使用
项目长度端点，把它们上移并合并到更具体的单项式增长输入中。这样，审稿人需要
检查的核心数学义务不再是不透明的证书对象，而是如下明确命题：

```math
T(c,d)\le n\quad\Longrightarrow\quad
c(n+1)^d<\operatorname{minCheckedCodeSize}(n).
```

这里 `T(c,d)` 即 Lean 中的 `thresholdOfMonomial c d`。

本文不声称已经给出十进制数值 `N`，也不把旧 half-denominator 精细公式作为
本稿主结果。本文主张的是：在上述明确增长输入下，Lean 已经验证了公式级
碰撞指标、同点矛盾以及干净 axiom profile。

## 2. 形式化对象

固定一个 PA-Hilbert 检查器坐标。对左右两个形式化证明族 `left_family` 和
`right_family`，Lean 构造合取引入后再右合取消去的证明族，并定义

```lean
M n =
  ((left_family.conjIntro right_family)
    |>.rightConjElim
    |>.minCheckedCodeSize n)
```

这就是本文的 `minCheckedCodeSize n`。

Sondow 侧的上界数据被压缩为一个自然数幂上界数据

```lean
upper_data =
  projectLengthConjIntroLengthAddTwoNatPowerUpperData
    left_family right_family left_data right_data
```

其中 `upper_data.coeff` 和 `upper_data.degree` 给出生成上界的自然数单项式
包络。于是本文的碰撞指标定义为

```lean
bigN =
  thresholdOfMonomial upper_data.coeff upper_data.degree.
```

主输入是单项式增长证书：

```lean
monomial_lt_lengthCodeAt_after :
  ∀ coeff degree n : Nat,
    thresholdOfMonomial coeff degree ≤ n →
      coeff * (n + 1)^degree < M n
```

它是当前定理的真正数学承重部分。

## 3. 推导

令

```math
c=\texttt{upper\_data.coeff},\qquad
d=\texttt{upper\_data.degree},\qquad
N=T(c,d).
```

由单项式增长输入，因 `T(c,d) ≤ N`，得到

```math
c(N+1)^d<M(N).
```

另一方面，Sondow 侧的形式化上界构造保证生成的上界函数在 `N` 处被同一个
单项式包络控制。用 Lean 端点的记号写，就是

```math
U(N)\le c(N+1)^d.
```

合并二者得到

```math
U(N)<M(N).
```

同时，检查器端点把同一个 `N` 放回到共同测度坐标中，得到反向的已检查上界

```math
M(N)\le U(N).
```

于是

```math
M(N)\le U(N)<M(N),
```

矛盾。Lean 中的主证书还记录了 `N` 的程序化公式：

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree.
```

这正是本文保留的公式级大 `N`。

## 4. 主定理

主定理 Lean 名称为

```lean
singletonMonomialLowerBound_submissionRoute
```

源码：

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNParameterClosureAudit.lean>

省略 namespace 后，其数学内容可写为：

```lean
theorem singletonMonomialLowerBound_submissionRoute
    -- other explicit arguments are shown in the source file
    (thresholdOfMonomial : Nat → Nat → Nat)
    (monomial_lt_lengthCodeAt_after :
      ∀ coeff degree n : Nat,
        thresholdOfMonomial coeff degree ≤ n →
          coeff * (n + 1)^degree < minCheckedCodeSize n) :
    bigN = thresholdOfMonomial upper_data.coeff upper_data.degree ∧
      ¬ is_rational euler_mascheroni
```

注释行所指的显式参数包括左右证明族、严格时间界、自然数幂上界数据以及这些长度函数
为多项式有界的 Lean 证书。它们都是显式 Lean 参数；主定理表面不再出现
`upper_provider`、`tail_gap` 或 `eventually_strict_length`。

## 5. 形式化审计

复现命令如下：

```bash
lake exe cache get
lake build integration.SondowProjectBigNParameterClosureAudit
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNParameterClosureAudit
open SondowMainCheckedCodeBridge.SondowProjectBigNParameterClosureAudit

#check singletonMonomialLowerBound_submissionRoute
#print axioms singletonMonomialLowerBound_submissionRoute
EOF
```

观察到的输出为：

```text
[propext, Classical.choice, Quot.sound]
```

未出现以下项目级 residual constants：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

审计报告：

- 中文：<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/parameter_closure_audit_20260708_zh.md>
- English：<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/parameter_closure_audit_20260708_en.md>

仓库：

<https://github.com/james130012/sondow-pudlak-collision-box>

## 6. 结论

本文给出一个参数表面闭合的 Lean 形式化碰撞定理。旧路线中的
`upper_provider`、`tail_gap` 和 `eventually_strict_length` 不再作为主定理
表面参数出现；当前主定理只暴露一个清楚的单项式增长下界，并在该输入下证明
公式级大 `N` 与同点矛盾。

后续工作是关闭该单项式增长下界本身，并在需要时继续构造 half-denominator
精细公式和十进制数值阈值。

## 参考文献

1. J. Sondow, Criteria for irrationality of Euler's constant, *Proceedings of
   the American Mathematical Society* 131 (2003), 3335-3344.
2. S. R. Buss, On Godel's theorems on lengths of proofs I: Number of lines and
   speedup for arithmetics, *Journal of Symbolic Logic* 59 (1994), 737-756.
3. P. Pudlak, On the lengths of proofs of finitistic consistency statements in
   first order theories, in *Logic Colloquium 1984*, North-Holland, 1986.
4. L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming
   language, in *Automated Deduction - CADE 28*, 2021.
