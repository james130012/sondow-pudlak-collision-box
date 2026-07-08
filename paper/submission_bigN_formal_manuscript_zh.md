# Sondow-Pudlak 程序中的干净 Lean 检查碰撞阈值

## 摘要

本文给出一个 Lean 4 检查的 Sondow-Pudlak proof-complexity collision theorem，
目标对象是 Euler-Mascheroni 常数。本文不声称已经无条件证明
Euler-Mascheroni 常数无理。本文的正式贡献是：在 clean checker input 和
clean measured upper provider 给定后，Lean 证明 rational branch 中计算出的
碰撞阈值满足

```lean
N = max upperN threshold
```

其中 `upperN` 是 clean upper tail 的 cutoff，`threshold` 是同一 clean checked
route 上的 tail-gap threshold。随后 Lean 在同一路线上推出 rational branch
的矛盾，即相对于该 clean input package 得到

```lean
¬ is_rational euler_mascheroni
```

投稿主 theorem 的 axiom profile 已审计为

```text
[propext, Classical.choice, Quot.sound]
```

并且不含以下三个旧项目级 residual constants：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

精确 half-denominator 公式级大 `N` 和十进制数值 `N` 抽取不作为本文主张，
而作为后续 refinement。

## 1. 引言

Euler-Mascheroni 常数定义为

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac{1}{k}-\log n\right).
```

它的无理性是经典公开问题。Sondow criterion 给出一种从 rationality
hypothesis 出发构造算术 certificate family 的路线；另一方面，Pudlak、
Friedman、Buss 相关的 proof-complexity lower-bound 传统提供了有限一致性
语句的证明长度下界机制。Sondow-Pudlak 程序试图把这两侧放入同一个
proof-code measurement coordinate 中，并在 rational branch 中形成 upper
bound 与 lower strict gap 的碰撞。

本文聚焦的是该程序中已经可以干净审计的核心碰撞定理。它不是一个终局无理性
证明，也不是一个数值计算报告。它证明的是：如果上界侧和 tail-gap 下界侧都以
clean proof-length-free checker coordinate 的形式提供，那么 Lean 中的
rational branch 会计算出一个明确的 collision number，并且这个 number 同时
触发上下界冲突。

本文中最重要的对象不是十进制自然数，而是形式化路线本身给出的阈值：

```lean
N = max upperN threshold
```

这里 `upperN` 和 `threshold` 都来自同一 clean checked route。因此，本文的
主结果是 proof-level/collision-level 的干净定理，而不是旧 half-denominator
公式路线的包装。

## 2. 形式化制品

本文审计基准 release 为：

```text
bigN-halfden-full-20260708
commit 2a7458c253aae4050a0a3a18424abea952d26bc3
```

release 地址：

```text
https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-halfden-full-20260708
```

当前 clean submission route 被隔离在文件：

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

主 theorem 为：

```lean
cleanUpperProvider_submissionRoute
```

该 theorem 依赖 proof-length-axiom-free checker endpoint。相关基础文件为：

```text
integration/SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint.lean
```

## 3. 主定理

忽略 namespace 和部分 projection 细节后，Lean 中主 theorem 的形状如下：

```lean
theorem cleanUpperProvider_submissionRoute
    (input : ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (upper_provider :
      input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    (∀ hrat : is_rational euler_mascheroni,
      computedCollisionNOfRationality hrat =
        max upperN threshold) ∧
      ¬ is_rational euler_mascheroni
```

精确 Lean statement 会把 `upperN` 展开为 `checkedSearchUpperTail` 返回的 cutoff，
并把 `threshold` 展开为同一 clean upper tail 上
`input.tail_gap.gap_for_polynomial_upper` 返回的 threshold。

因此，该 theorem 同时完成两件事：

1. 识别 rational branch 中的 computed collision number：

```lean
N = max upperN threshold
```

2. 在同一个 clean input package 下证明 rational branch 不可能成立：

```lean
¬ is_rational euler_mascheroni
```

这是本文应作为主结果呈现的 theorem。它的优势在于：阈值的定义清楚，证明路线
可复现，axiom profile 不含旧项目级 residual constants。

## 4. 为什么旧 half-denominator 公式路线不是本文主结果

release 中还保留了旧 half-denominator formula-level 工作，其中可见表达式为：

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

这个表达式很漂亮，也有后续研究价值。但是，现有旧 formula-level endpoints
的 axiom profile 仍然包含：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

如果把旧公式路线作为本文 headline theorem，会削弱论文信用。本文因此采取更
严格的投稿策略：主文只使用已经审计干净的
`cleanUpperProvider_submissionRoute`，把 formula-level half-denominator
refinement 和 numerical extraction 都列为后续工作。

当前 Lean 文件中已经保留 clean downstream interface：

```lean
cleanHalfDenUpperProvider_submissionRoute
```

这个 theorem 本身也是 clean 的；但它需要一个 clean upstream
half-denominator upper provider。旧 formula endpoints 目前不能无污染地提供
该 upstream provider，因此本文不把它们作为主证明来源。

## 5. 公理审计

核心审计命令如下：

```bash
lake build integration.SondowProjectBigNCleanSubmissionRoute
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

观察到的 axiom output 为：

```text
[propext, Classical.choice, Quot.sound]
```

主 theorem 未出现以下项目级 residual constants：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

因此，本文主路线可表述为 clean Lean-checked collision theorem，而不是带旧
project-level assumptions 的 formula-level checkpoint。

## 6. 可复现性

复现 clean route 可运行：

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

详细审计报告位于：

```text
docs/clean_submission_route_audit_20260708_zh.md
```

验证日志位于：

```text
docs/bigN_validation_log_20260708_zh.md
```

正式 release 位于：

```text
https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/clean-bigN-submission-route-20260708
```

## 7. 本文主张与非主张

本文已经证明：

1. 一个 clean Lean-checked collision route。
2. rational branch 中形式化计算出的碰撞数：

```lean
N = max upperN threshold
```

3. 在同一 clean input package 下推出 rational branch contradiction。
4. 主 theorem 的 axiom profile 清除了三个旧项目级 residual constants。

本文不主张：

1. 已经无条件证明 Euler-Mascheroni 常数无理。
2. 已经给出十进制自然数 `N`。
3. 已经完成 clean upstream half-denominator formula-level cutoff 的构造。

这一区分是本文投稿可信度的核心。当前成果的强点不在于把未完成的公式级工作
说成已经完成，而在于把已经干净通过 Lean 审计的 proof-level/collision-level
定理清楚呈现出来。
