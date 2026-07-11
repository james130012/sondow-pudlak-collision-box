# 并行任务提示词：语法变换执行轨迹

将下面代码块整段发给新的 Codex 终端。

```text
工作目录：
/home/james/code/sondow-pudlak-bigN-audit-20260708/sondow-pudlak-collision-box-bigN-halfden-full-20260708

目标：
独立完成 shift / free / substitution / axiom-generation trace
（移位/自由化/代入/公理公式生成执行轨迹）的真实执行成本形式化。
这里只证明语法变换执行轨迹，不推进证书诚实位权、Buss-Pudlak 下界或论文。

先阅读：
1. docs/short_checked_minproof_growth_proof_zh.md
2. docs/checked_minproof_theorem_dependency_graph_zh.dot
3. integration/FoundationCompactSyntaxTransformationBounds.lean
4. integration/FoundationCompactSyntaxTransformationCodeBounds.lean
5. integration/FoundationCompactListedCertificateVerifier.lean
6. integration/FoundationCompactVerifierFormulaListChecks.lean
7. integration/FoundationCompactVerifierBitCostPrimitives.lean
8. integration/FoundationCompactPAAxiomCertificate.lean
9. integration/FoundationCompactNatDecoderCost.lean
10. .lake/packages/Foundation/Foundation/FirstOrder/Basic/Syntax/Rew.lean
11. .lake/packages/Foundation/Foundation/Syntax/Predicate/Rew.lean
12. .lake/packages/Foundation/Foundation/FirstOrder/Arithmetic/Schemata.lean

文件边界：
- 主要新增：
  integration/FoundationCompactSyntaxTransformationTrace.lean
- 如确实需要，可再新增同前缀的一个辅助 Lean 文件。
- 不要修改以下正在被另一终端编辑的文件：
  integration/FoundationCompactListedProofHonestWeight.lean
  integration/FoundationCompactListedCertifiedHonestWeight.lean
  docs/short_checked_minproof_growth_proof_zh.md
  docs/checked_minproof_theorem_dependency_graph_zh.dot
- 不要修改论文、README 或旧路线文件。
- 不要撤销工作区中任何已有改动。

必须证明的端点：
1. 为 term/formula shift（项/公式移位）定义递归 costed trace（带成本轨迹）。
2. 为 formula free（公式自由化）定义递归轨迹。
3. 为 one-variable substitution（单变量代入，含 qpow 量词下重写）
   定义递归轨迹。
4. 为 List.map Rewriting.shift（公式列表逐项移位）定义总轨迹。
5. 为 PAAxiomCertificate.sentence（PA 公理证书生成公式）定义轨迹；
   必须覆盖 23 个标签，尤其 induction body（归纳公理体）
   `(succInd body).univCl` 的真实生成过程。
6. 每个轨迹都要有：
   - result theorem（结果定理）：轨迹结果精确等于当前执行定义；
   - cost theorem（成本定理）：成本受输入完整二进制码长的一个显式固定多项式控制；
   - `#print axioms` 审计。

严格要求：
- 不得用 `sorry`、新增 `axiom`、非空输入结构或外部成本参数。
- 不得只证明输出码长；必须证明递归执行轨迹成本。
- 不得写成 `(原函数结果, 1)` 再宣称成本为 1；每次构造、递归调用、
  列表遍历、变量索引运算和生成的语法节点都必须计费。
- 可取较宽但固定的多项式，不要求最优常数。
- 成本坐标必须使用 `binaryTermCode`、`binaryFormulaCode`、
  `binaryPAAxiomCertificateCode` 的长度，不能退回 raw Gödel code（原始哥德尔码）。
- 复用
  `FoundationCompactSyntaxTransformationCodeBounds.lean`
  中已经通过的输出码长界，不重复包装为假设。
- 对 `qpow` 必须显式处理量词深度；不能留下 depth/budget（深度/预算）参数到公开定理。
- 对公理生成，固定公理可给显式常数界；归纳公理必须真正展开并计入
  shift/substitution/universal-closure（移位/代入/全称闭包）成本。
- 最终公开定理的公理画像只允许
  `propext`、`Classical.choice`、`Quot.sound`，不得有 `sorryAx`。

公理生成的首要可行性审计：
- 先检查 `Semiformula.univCl`（全称闭包）。当前 Foundation 定义使用
  `phi.fvSup` 次量词，而自由变量编号在 `binaryFormulaCode` 中按二进制计长。
  因此稀疏大编号可能使小证书生成指数长的 `(succInd body).univCl`。
- 先给出严格判断：是否存在长度为 `O(k)` 但 `fvSup >= 2^k` 的归纳体公式族。
  若存在，明确记录反例，不得声称
  `axiomCertificateSentenceTrace certificate` 仅关于证书码长有多项式界。
- 若确认上述指数风险，在新轨迹文件中实现
  `axiomSentenceEqTrace certificate sentence`（公理证书与候选句子等值轨迹）之类的
  guarded verifier（带守卫验证器）：先由已在输入中的候选句子码长检查
  `fvSup` 上界，守卫失败则立即拒绝，只在守卫通过后生成闭包。
- 该守卫不得破坏完备性；必须证明
  `certificate.sentence = sentence` 时守卫必然通过，并证明新轨迹返回 `true`
  当且仅当原句子相等。成本界应关于证书与候选句子两个诚实输入码长的固定多项式。
- 如需要替换现有 `listedCertificateValidTrace` 中的 `sentenceEqTrace certificate.sentence sentence`，
  先在新文件中提供完整替代 API 和定理，不直接修改主终端正在使用的文件；
  完成后由主终端统一接入。

建议端点名（可按类型细节调整）：
- binaryTermShiftTrace_result / _cost_le
- binaryFormulaShiftTrace_result / _cost_le
- binaryFormulaFreeTrace_result / _cost_le
- binaryFormulaSubstitutionOneTrace_result / _cost_le
- formulaListShiftTrace_result / _cost_le
- axiomSentenceEqTrace_result_eq_true_iff / _cost_le

验证方式：
- 开发时只运行：
  nice -n 10 lake env lean integration/FoundationCompactSyntaxTransformationTrace.lean
- 新模块需要 `.olean` 时，只定向运行：
  nice -n 10 lake build integration.FoundationCompactSyntaxTransformationTrace
- 不跑完整 `lake build`。
- 完成后报告：通过的端点、显式多项式、`#print axioms` 输出、
  尚未覆盖的真实义务。不要自行更新 DOT，主终端统一更新。
```
