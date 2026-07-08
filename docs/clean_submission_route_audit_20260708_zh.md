# Clean Submission Route 审计报告

日期：2026-07-08  
审计对象：`bigN-halfden-full-20260708` release copy  
Release URL：<https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-halfden-full-20260708>  
Release commit：

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

## 结论

本轮投稿主线应使用干净 checker/collision 路线：

```lean
cleanUpperProvider_submissionRoute
```

所在文件：

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

该 theorem 的作用是：在 clean input 和 clean upper provider 给定后，Lean
证明 rational branch 中计算出的碰撞数满足

```lean
N = max upperN threshold
```

并且同一路线推出：

```lean
¬ is_rational euler_mascheroni
```

这是当前最可信的投稿主结果。它保留了明确的 `N` 生成公式
`max upperN threshold`，并把证明路线放在已经通过 axiom audit 的 clean
checker/collision core 上。

## 三个项目级依赖是否已经清除

对当前投稿主线，结论是：已经清除。

实际检查命令：

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

观察到的 axiom profile：

```text
[propext, Classical.choice, Quot.sound]
```

未出现：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

因此，当前 clean submission theorem 不依赖这三个项目级 residual constant。

## 旧 half-denominator 公式路线审计

旧路线中的漂亮公式包括形如：

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

但对旧 half-denominator formula endpoints 做 `#print axioms` 后发现，从
canonical formula、checked-prefix formula、recognition formula 到
semantic-strong/existence formula，均仍然带有项目级依赖：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

这说明旧公式路线不能作为本轮投稿主定理。若把它作为主结果，会把论文信用
绑定到尚未清除的项目级 residual constants 上。

## 当前采取的处理方式

本次修正没有删除公式级方向，而是把它下沉为后续工作。新增 clean downstream
接口：

```lean
CleanHalfDenUpperProvider
cleanComputedBigN_eq_halfDenFormulaMax
cleanHalfDenUpperProvider_submissionRoute
```

这些 theorem 的 axiom profile 同样为：

```text
[propext, Classical.choice, Quot.sound]
```

含义是：如果未来能在 clean upstream route 中构造 half-denominator upper
provider，并证明其 `upperN = 17 * max 3 ((rat.q.den + 1) / 2) + 8`，那么
下游碰撞主定理会立即得到干净公式级版本。

但这个 upstream construction 目前不能从旧 projectLength formula theorem
直接拿来用，因为旧 theorem 本身已经污染。因此本轮论文不把 half-den 精细
公式或数值 `N` 当作必要成果。

## 投稿表述建议

主论文应这样表述：

1. 本文给出 Lean-checked clean collision theorem。
2. 在 clean upper provider 输入下，rational branch 的碰撞数是明确的
   `max upperN threshold`。
3. 同一 clean route 推出 rational branch contradiction。
4. 主 theorem 的 axiom profile 不含 `partial_consistency_payload`、
   `proof_length`、`strengthened_partial_consistency_payload`。
5. half-denominator formula-level 和 decimal numerical extraction 是后续
   refinement，不是本轮投稿 claim。

不应这样表述：

1. 不应说旧 `projectLength...halfDen...thresholdFormula` 是当前主 theorem。
2. 不应说已经无条件给出 `gamma` irrationality。
3. 不应说已经从 rational parameter 自动构造了 clean half-den formula-level
   upper provider。

## 复现摘要

本轮已通过：

```bash
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

并重新导入模块检查：

```lean
#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#check CleanHalfDenUpperProvider
#check cleanHalfDenUpperProvider_submissionRoute
```

核心 axiom 输出全部为标准 Lean/Mathlib 逻辑依赖：

```text
[propext, Classical.choice, Quot.sound]
```

这是本轮“可信证明版本”的审计结论。
