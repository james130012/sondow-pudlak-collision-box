# big-N 论文与证明路线审计计划

本文件用于审计 release `bigN-nature-paper-20260708` 中的大 `N` 论文成果。它与论文正文分开：论文负责陈述定理和证明结构，本文件负责复现、检查和发现问题后的修正路线。

## 1. 基准信息

- 本地工作副本：`/home/james/code/sondow-pudlak-collision-box-bigN-nature-paper-20260708`
- GitHub release：`bigN-nature-paper-20260708`
- 基准提交：`c26cd1d2b3abbc6c3584ab5c2afbd1e953d3cacd`
- Lean：`leanprover/lean4:v4.31.0`
- Mathlib：`v4.31.0`

核对命令：

```bash
git status --short --branch
git rev-parse HEAD
git tag --points-at HEAD
cat lean-toolchain
rg -n 'rev = "v4.31.0"' lakefile.toml
```

## 2. 主成果复现

主成果入口：

```text
integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

主 theorem：

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

最低复现命令：

```bash
lake exe cache get
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

targeted theorem probe 需要先构建模块：

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
```

然后运行：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

#check projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
EOF
```

审计目标：

1. theorem 是否存在且能 elaboration。
2. theorem 是否真的给出 `∃ N : Nat`。
3. theorem 是否证明 `endpointN = N`。
4. theorem 是否证明同一个 `N` 满足 source-side strict gap。
5. `SemanticStrongNatLowerBound` 是否由 `source_minChecked_calibration` 和 `buss_pudlak_rescaling` 导出，而非作为主 theorem 的外部输入。

## 3. 证明路线检查

### 3.1 finite-prefix / MiniHilbert rewrite

入口：

```lean
s21SondowMiniHilbertMinProofCodeSizePrefixMax
S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
```

命令需要先构建模块：

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
```

然后运行：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

#check s21SondowMiniHilbertMinProofCodeSizePrefixMax
#check S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
EOF
```

审计目标：

1. prefix 是否来自 `natPrefixMax`。
2. `minProofCodeSize` 是否来自 recognition theorem 的 MiniHilbert semantics。
3. 论文是否没有把该 prefix 误写成已计算十进制常数。

### 3.2 half-denominator obstruction

入口：

```lean
mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

命令需要先构建模块：

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
```

然后运行：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

#check mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
#check not_sondowCheckedHalfDenPrefix_of_rationalParameter
EOF
```

审计目标：

1. tail threshold 是否为 `max 3 ((rat.q.den + 1) / 2)`。
2. prefix premise 是否明确不是 automatic。
3. 论文是否保留该 obstruction，避免把路线写成无条件 prefix closure。

### 3.3 numerical handoff

入口：

```text
integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

定理：

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

命令：

```bash
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

targeted theorem probe 需要先构建模块：

```bash
lake build integration.SondowProjectMonth11Month12HardResidualElimination
```

然后运行：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12HardResidualElimination

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12HardResidualElimination

#check finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
EOF
```

审计目标：

1. C-line final computed index 是否确实化为 `max upper.upperN (thresholdOf upper.U upper.polynomial)`。
2. 后续十进制 `N` 是否被正确表述为 `thresholdOf` 或 executable witness 的计算问题。
3. 论文是否没有把 existential witness 冒充为 printed decimal value。

## 4. Axiom 边界检查

主论文 theorem 的 `#print axioms` 可在先构建模块后用以下命令审计：

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
```

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

#print axioms projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
#print axioms S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
EOF
```

解释原则：

1. 常规 Lean/Mathlib 依赖如 `Classical.choice` 不等于项目数学漏洞，但要如实记录。
2. 项目级 external input 必须在论文中以 assumption package 或 boundary 形式出现。
3. 若出现论文未说明的依赖，先修论文；若依赖不应出现，再查 Lean 证明路线。

## 5. 论文一致性检查

检查对象：

```text
paper/paper_new_en.md
paper/paper_new_zh.md
paper/world_class_revision_plan_zh.md
docs/bigN_audit_plan_zh.md
```

检查规则：

1. release tag 必须写作 `bigN-nature-paper-20260708`。
2. commit 必须写作 `c26cd1d2b3abbc6c3584ab5c2afbd1e953d3cacd`。
3. 主 theorem 名不得拼错。
4. `N` 必须表述为 existential threshold，除非后续真的完成 executable extraction。
5. `gamma` irrationality 必须表述为 non-claim。
6. 中文稿不得比英文稿声称更强。

## 6. 代码修正触发条件

出现以下情况时，应修改 Lean 或文档接口：

1. targeted `#check` 失败且不是缓存或导入环境问题。
2. theorem type 与论文主张不匹配。
3. theorem 名、namespace 或入口太隐蔽，妨碍复现审计。
4. `#print axioms` 暴露出未记录的项目级依赖。
5. source-file elaboration 失败。

修正原则：

1. 优先最小补丁。
2. 优先增加审计入口、alias theorem 或注释，不做无关重构。
3. 修正后重新运行相关 `#check` 或 source-file elaboration。
4. 所有代码修正必须同步到论文或审计文档。

## 7. 当前完成标准

本轮达到可交付状态需要：

1. 新 release 副本建立完成，并确认 tag/commit。
2. 论文中英文稿完成 theorem-driven 改写。
3. 审计计划文档完成。
4. `git diff --check` 通过。
5. 至少 targeted `#check` 能覆盖主 theorem、MiniHilbert rewrite、half-denominator obstruction 和 numerical handoff。
6. 若 source-file elaboration 因耗时无法全部完成，需要记录已运行命令、输出状态和下一步。
