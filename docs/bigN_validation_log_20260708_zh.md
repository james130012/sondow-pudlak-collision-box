# big-N clean route 复现与验证日志

日期：2026-07-08  
工作目录：

```text
/home/james/code/sondow-pudlak-bigN-audit-20260708/sondow-pudlak-collision-box-bigN-halfden-full-20260708
```

Release tag：

```text
bigN-halfden-full-20260708
```

Release commit：

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

## 构建检查

已运行：

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

结果：

```text
Build completed successfully (8720 jobs).
```

构建过程中存在历史文件的 long-line/flexible tactic linter warnings；未观察到
proof failure。

## clean 主线 probe

运行：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNCleanSubmissionRoute
open SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute

#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#check CleanHalfDenUpperProvider
#check cleanHalfDenUpperProvider_submissionRoute
#print axioms cleanUpperProvider_submissionRoute
#print axioms cleanComputedBigN_eq_tailGapMax
#print axioms cleanProvider_not_rational
#print axioms cleanComputedBigN_eq_halfDenFormulaMax
#print axioms cleanHalfDenUpperProvider_submissionRoute
EOF
```

关键 `#check` 结果：

```lean
cleanUpperProvider_submissionRoute
```

给出：

```lean
(∀ hrat : is_rational euler_mascheroni,
  computedCollisionNOfRationality hrat =
    max upperN threshold) ∧
  ¬ is_rational euler_mascheroni
```

其中完整 Lean statement 将 `upperN` 展开为 `checkedSearchUpperTail` 的
cutoff，将 `threshold` 展开为 `tail_gap.gap_for_polynomial_upper` 的输出。

## axiom 输出

以下 theorem 的 axiom profile 均为：

```text
[propext, Classical.choice, Quot.sound]
```

已检查 theorem：

```lean
cleanUpperProvider_submissionRoute
cleanComputedBigN_eq_tailGapMax
cleanProvider_not_rational
cleanComputedBigN_eq_halfDenFormulaMax
cleanHalfDenUpperProvider_submissionRoute
```

未出现：

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

## 旧 half-den formula route 的处理

旧 formula-level half-denominator theorem 经过审计仍带三个项目级依赖。因此
本轮投稿不使用旧公式路线作为主 theorem。

当前主 theorem 是：

```lean
cleanUpperProvider_submissionRoute
```

当前可引用 big-`N` 形态是：

```lean
N = max upperN threshold
```

formula-level half-denominator 和 numerical `N` extraction 留作后续 refinement。
