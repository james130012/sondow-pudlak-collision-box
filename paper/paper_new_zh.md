# Sondow-Pudlak 程序中的干净 Lean-checked 碰撞阈值

## 摘要

本文稿对应当前干净投稿路线：

```lean
cleanUpperProvider_submissionRoute
```

所在文件：

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

在 clean checker input 和 clean measured upper provider 给定后，Lean 证明
rational branch 中计算出的碰撞数满足：

```lean
N = max upperN threshold
```

并且同一路线推出：

```lean
¬ is_rational euler_mascheroni
```

该 theorem 的 axiom profile 为：

```text
[propext, Classical.choice, Quot.sound]
```

不含以下三个项目级依赖：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

因此，本稿把 proof-level/collision-level 的干净 `max upperN threshold`
路线作为主结果。旧 half-denominator 精细公式路线和数值 `N` 抽取作为后续
工作，不作为本轮投稿 claim。

## 1. 目标与边界

Euler-Mascheroni 常数 `gamma` 的无理性仍是公开问题。本文不声称已经给出
无条件证明。本文的目标是给出一个机器检查的干净碰撞核心：如果上界侧和
下界侧都在同一个 proof-length-free checker coordinate 中给出，那么 Lean
计算 rational branch 的碰撞数，并在同一路线上推出矛盾。

这使得当前成果有清楚边界：

1. `N` 不是十进制数值输出。
2. `N` 是 Lean route 中的 formal computed collision number。
3. 当前可引用公式是 `N = max upperN threshold`。
4. 主 theorem 不依赖旧项目级 residual constants。

## 2. 主定理

主 theorem：

```lean
cleanUpperProvider_submissionRoute
```

它的数学内容可以概括为：

给定 clean input 和 clean upper provider，对每个 rational branch witness
`hrat`，Lean 中的 computed collision number 等于：

```lean
max upperN threshold
```

其中：

1. `upperN` 来自 `checkedSearchUpperTail` 的 clean upper-tail cutoff。
2. `threshold` 来自同一 clean upper tail 的 `tail_gap.gap_for_polynomial_upper`。
3. 同一路线给出 `¬ is_rational euler_mascheroni`。

这就是当前投稿要呈现的“可信证明”：不是追求漂亮但带污染的公式，而是把
能被 Lean 干净审计的碰撞结论作为主贡献。

## 3. 审计结果

复现命令：

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

axiom probe：

```lean
import integration.SondowProjectBigNCleanSubmissionRoute
open SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute

#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#print axioms cleanUpperProvider_submissionRoute
#print axioms cleanComputedBigN_eq_tailGapMax
#print axioms cleanProvider_not_rational
```

输出的项目级依赖：无。

输出的普通 Lean/Mathlib 逻辑依赖：

```text
[propext, Classical.choice, Quot.sound]
```

## 4. 为什么不把旧 half-den 公式作为主结果

旧路线中有漂亮公式：

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

但旧 formula-level endpoints 经过 `#print axioms` 审计后仍然出现：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

这三个依赖会削弱论文信用。因此本轮投稿不把旧 half-den formula theorem
作为主结论。正确做法是：

1. 当前主论文使用 clean `max upperN threshold` 碰撞路线。
2. half-denominator formula-level upper provider 作为后续 clean upstream
   construction。
3. 数值级 `N` 抽取也作为后续 refinement。

## 5. 论文表述

当前稿件应该强调：

1. 这是一个 Lean-checked clean collision theorem。
2. rational branch 中 `N` 由 `max upperN threshold` 明确定义。
3. 同一路线推出 contradiction。
4. 主 theorem 的 axiom profile 已经清除了三个项目级依赖。

当前稿件不应声称：

1. 已经无条件证明 `gamma` 无理。
2. 已经给出十进制 `N`。
3. 旧 half-den formula theorem 是投稿主 theorem。

审计报告见：

```text
docs/clean_submission_route_audit_20260708_zh.md
```
