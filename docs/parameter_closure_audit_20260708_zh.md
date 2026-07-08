# 参数闭合审计报告

日期：2026-07-08

## 结论

本轮审计新增了参数闭合文件：

```text
integration/SondowProjectBigNParameterClosureAudit.lean
```

当前最干净的投稿定理为：

```lean
singletonMonomialLowerBound_submissionRoute
```

它把旧主线表面上的三个显式对象

```text
upper_provider
tail_gap
eventually_strict_length
```

全部从 theorem surface 中去掉。剩余的核心数学输入被压缩为一个可审计的
单项式增长下界：

```lean
thresholdOfMonomial coeff degree <= n ->
  coeff * (n + 1)^degree < minCheckedCodeSize n
```

在该输入下，Lean 证明公式级碰撞指标满足

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree
```

并推出：

```lean
¬ is_rational euler_mascheroni
```

## Lean 审计输出

复现命令：

```bash
lake build integration.SondowProjectBigNParameterClosureAudit
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNParameterClosureAudit
open SondowMainCheckedCodeBridge.SondowProjectBigNParameterClosureAudit

#check singletonMonomialLowerBound_submissionRoute
#print axioms singletonMonomialLowerBound_submissionRoute
EOF
```

观察到的 axiom profile：

```text
[propext, Classical.choice, Quot.sound]
```

未出现以下项目级 residual constants：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

## 三条路线的含义

文件中保留三条审计路线。

```lean
cleanTailGapFrontier_submissionRoute
```

这条路线把旧的 `input` 和 `upper_provider` 合并为一个 upstream frontier
对象。它关闭的是 theorem surface 的分散参数问题，但 frontier 内部仍含
`tail_gap`。

```lean
eventuallyStrictLength_noTailGap_submissionRoute
```

这条路线不再要求裸 `tail_gap`，而是用
`ComputableGapCertificate.ofEventuallyStrict` 从
`eventually_strict_length` 构造 tail-gap。它说明 `tail_gap` 可以下沉为
最终严格增长定理，但该增长定理本身仍是强输入。

```lean
singletonMonomialLowerBound_submissionRoute
```

这是当前最适合投稿表述的路线。它不暴露 `upper_provider`、`tail_gap` 或
`eventually_strict_length`，并保留干净公式
`bigN = thresholdOfMonomial upper_data.coeff upper_data.degree`。剩余义务是
证明 `minCheckedCodeSize` 最终支配任意自然数单项式。

## 不能过度声称的内容

当前结果不应表述为已经无条件证明 Euler 常数无理性。原因是
`singletonMonomialLowerBound_submissionRoute` 仍然需要单项式增长下界输入。
这不是 Lean 技术包装，而是 Pudlak/证明长度侧真正的数学力量所在。

正确表述应为：项目已经把原先不透明的 `tail_gap` 和 `upper_provider` 参数
压缩为一个清楚、公式级、可审计的增长义务；在该义务下，Lean 给出干净的
碰撞指标公式和矛盾结论。
