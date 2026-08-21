# 世界级数学论文改造规划单

工作副本：`/home/james/code/sondow-pudlak-collision-box-bigN-nature-paper-20260708`

基准版本：GitHub release `bigN-nature-paper-20260708`

基准提交：`c26cd1d2b3abbc6c3584ab5c2afbd1e953d3cacd`

本规划的目标不是把草稿包装得更响亮，而是把论文、代码和审计材料一起改造成可被顶级数学期刊审稿人审计的研究制品：主定理清楚，假设清楚，证明链清楚，形式化证据清楚，未完成边界清楚，复现路径清楚。如果复现或审计中发现 Lean 接口、证明陈述、命名、文档或论文表达存在问题，应在这个 release 副本中修正，而不是只做文字润色。

## 一、论文总目标

把当前草稿从“项目进展说明”改写为“定理驱动的形式化数学论文”。论文应围绕一个中心结论展开：

在明确列出的 Sondow 侧识别数据、partial-consistency 数据、source-minChecked calibration、Buss-Pudlak rescaling 与 half-denominator tail 输入下，Lean 4 证明存在自然数阈值 `N`，并且该 `N` 同时是项目 endpoint 返回值和 source-side strict gap 的见证。

必须保持以下边界：

1. 已证明：大 `N` 的存在性和该点上的严格 source-side gap。
2. 已证明：相关有限前缀可改写到 MiniHilbert `minProofCodeSize` 语义。
3. 已证明：tail-gap 数值入口可规约到 `max upper.upperN (thresholdOf upper.U upper.polynomial)`。
4. 未证明：十进制自然数 `N = ...`。
5. 未声称：Euler-Mascheroni 常数无理性的无条件证明。

## 一点五、总体交付物

本项目本轮推进至少包含五类交付物：

1. 成果复制：在本地新建的 release 副本中确认 tag、commit、Lean/Mathlib 版本、核心文件和核心 theorem 均可定位。
2. 证明路线检验：对主 theorem、finite-prefix rewrite、half-denominator obstruction、numerical handoff theorem 做 targeted `#check` 或 source-file elaboration；必要时补充 `#print axioms` 审计入口。
3. 论文表述修改：把中英文论文从项目报告式文本改为 theorem-driven manuscript，使结果、假设、证明结构、非主张和复现命令一一对应。
4. 代码问题修正：如果审计发现 theorem 命名、namespace、可复现命令、证明接口、注释或辅助定义有错，应在 Lean 或文档中修正；不得用论文文本掩盖代码问题。
5. 成果呈现：最终给出一个清晰目录，说明主成果在哪里、如何复现、如何审计、哪些部分已经证明、哪些部分仍是后续数值或外部输入工作。

## 二、写作标准

参考顶级数学论文的通用形态，而不是模仿宣传性科学新闻：

1. 开篇要先给出问题、已有路线、本文贡献和精确边界。
2. 主定理必须在引言中以数学形式陈述，不能只在 prose 中描述。
3. 所有输入应组织为 assumption package，不应散落在叙述段落中。
4. 证明部分要按 lemma/proposition/theorem 的依赖链展开。
5. 机器检查事实要逐条绑定到 Lean 文件、定理名和可复现命令。
6. 对未完成部分要写成 theorem-boundary 或 future computation problem，而不是弱化为“工程细节”。
7. 中文稿和英文稿必须语义一致，英文稿优先达到投稿级别，中文稿作为完整对照稿。

参考样式依据：

- Annals of Mathematics 在线期卷结构：https://annals.math.princeton.edu/
- Journal of the AMS / AMS 论文页面：https://pubs.ams.org/JAMS
- Inventiones Mathematicae 论文常见结构示例：https://link.springer.com/article/10.1007/s00222-025-01346-9
- Annals of Formalized Mathematics 对 formalized mathematics 论文的定位：https://afm.episciences.org/
- AMS author/style guide：https://www.ams.org/publications/authors/AMS-StyleGuide-online.pdf

## 三、拟定论文结构

英文主稿 `paper/paper_new_en.md`：

1. Title
2. Abstract
3. Introduction
   - Euler-Mascheroni problem
   - Sondow criterion and proof-length lower-bound route
   - Main contribution
   - Explicit non-claims
4. Formal Framework
   - proof-code measurement
   - source length
   - Sondow finite prefix
   - endpoint `N`
5. Main Theorem
   - theorem statement in mathematical prose
   - exact Lean theorem name
   - assumption package
6. Proof Architecture
   - Sondow half-denominator tail
   - finite-prefix maximum and MiniHilbert rewrite
   - source-minChecked calibration
   - Buss-Pudlak rescaling
   - existential witness extraction
7. Numerical Endpoint and the Remaining Computation
   - `thresholdOf` route
   - why existential `N` is not a printed decimal
8. Formal Verification and Axiom Boundary
   - commands
   - `#check`/`#print axioms` expectations
   - release tag and commit hash
9. References
10. Methods / Code Availability / Data Availability

中文稿 `paper/paper_new_zh.md`：

与英文主稿保持同构结构，术语采用中英并列，避免中文自然语言把形式化主张写强。

## 四、核心证据清单

重写时必须从当前 release 副本核对以下入口：

1. `integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean`
   - `projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax`
   - `S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax`
   - `s21SondowMiniHilbertMinProofCodeSizePrefixMax`
   - `not_sondowCheckedHalfDenPrefix_of_rationalParameter`
2. `integration/SondowProjectMonth11Month12HardResidualElimination.lean`
   - `finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf`
3. Project boundary files:
   - `README.md`
   - `STATUS.md`
   - `AXIOM_LEDGER.md`
   - `lakefile.toml`
   - `lean-toolchain`

## 五、执行顺序

### 第一阶段：论文主结构重写

1. 把摘要改成数学论文摘要：问题、方法、定理、边界各一句。
2. 把主文前半部分改成 Introduction + Main theorem。
3. 删除或下沉过早出现的工程式 release 说明。
4. 增加 notation/assumption package，统一 `sourceLength`、`sondowThreshold`、`sondowPrefixCoeff`、`endpointN` 的解释。
5. 把表格改成 theorem-boundary table，表述为 claims and non-claims。

### 第二阶段：证明架构重写

1. 把 proof route 写成四个 proposition 级模块。
2. 每个模块附 Lean theorem name。
3. 明确哪些是 formal theorem，哪些是 external root input，哪些是 remaining numerical computation。
4. 明确 half-denominator prefix obstruction 不能被省略。

### 第三阶段：审计材料准备

1. 增加 release tag、commit hash 和本地复现命令。
2. 增加 targeted `#check` 命令。
3. 增加可选 `#print axioms` 命令。
4. 记录可能很慢的 build 命令和轻量 source-file elaboration 命令。

### 第四阶段：质量门槛

1. `git diff --check` 必须通过。
2. Markdown 中 Lean 定理名、文件名不得拼错。
3. release tag、commit hash、branch 说明不得互相矛盾。
4. 对 `N` 的表述必须始终是 existential threshold，除非后续真的抽取出 decimal value。
5. 对 Euler-Mascheroni irrationality 的表述必须始终是 non-claim。
6. 中文稿不能比英文稿更强。

## 六、后续全面审计路线

论文初稿达到上述结构后，再进入全面审计。审计不是泛泛阅读，而是按依赖图逐层查：

1. 主 theorem type 审计。
2. Main theorem assumption package 审计。
3. `#print axioms` 审计。
4. `sourceLength` 来源审计。
5. finite-prefix / MiniHilbert rewrite 审计。
6. `thresholdOf` 数值入口审计。
7. `proof_length`、payload truth、Pudlak literature residual 审计。
8. release artifact 与论文文字一致性审计。

审计输出应单独形成 `docs/bigN_audit_plan_zh.md` 和审计记录，不混入论文正文。

## 六点五、代码修正原则

审计过程中如发现代码问题，按以下顺序处理：

1. 定理能检查但论文引用不准：优先修论文、规划单和审计文档。
2. 定理名或 namespace 不利于审计：增加轻量 alias theorem 或审计入口文件，避免大规模重构。
3. theorem statement 与论文所需数学主张不完全一致：先判定是论文写强、写弱，还是 Lean 端缺少桥接定理；论文写错则改论文，Lean 缺桥则补最小桥。
4. source-file elaboration 失败：定位失败模块，区分依赖缓存问题、导入问题、真实 proof breakage；真实 breakage 必须修 Lean。
5. `#print axioms` 暴露出未说明依赖：不得隐藏，必须写入论文边界或审计文档。

代码修正应保持局部、可审计、可复现。除非证明确实需要，不做大型结构重排。

## 七、本轮立即推进项

1. 先核对并记录核心 Lean theorem type。
2. 重写英文稿。
3. 同步重写中文稿。
4. 增加 `docs/bigN_audit_plan_zh.md`，把成果复现、证明路线检验、代码修正触发条件写清楚。
5. 运行 `git diff --check`。
6. 尽量运行 targeted `#check` 和两个核心 Lean source-file elaboration 命令；若耗时过长，则保留命令和已完成的轻量检查结果。
7. 对发现的问题进行最小必要代码或文档修正。
