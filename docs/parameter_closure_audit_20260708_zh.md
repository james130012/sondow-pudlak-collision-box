# 参数闭合审计报告

日期：2026-07-08

## 结论

本轮审计新增了参数闭合文件：

```text
integration/SondowProjectBigNParameterClosureAudit.lean
```

参数闭合层当前最干净的条件化定理为：

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

## 增长义务复审

2026-07-09 的增长义务复审新增了：

```text
integration/SondowProjectBigNGrowthObligationAudit.lean
```

该文件已经由 Lean 检查通过，并给出五条关键结论：

```lean
conjRightMinCheckedCodeSize_le_explicitLength
conjRightMinCheckedCodeSize_polynomial_of_component_polynomial
monomialDomination_impossible_of_polynomial_bound
singletonMonomialLowerBound_conjSource_obligation_impossible
eventuallyStrictLength_conjSource_impossible
```

含义是：当前 `singletonMonomialLowerBound_submissionRoute` 中的
`minCheckedCodeSize` 来自
`(left_family.conjIntro right_family).rightConjElim`。因为
`left_family` 与 `right_family` 是显式证明族，且二者长度被假设为多项式，
Lean 证明了这个 `minCheckedCodeSize` 本身也有多项式上界。因此它不能承担
“最终支配任意单项式”的 Pudlak 下界义务。若把
`eventually_strict_length` 强行接到同一个 `lengthCodeAt` 上，Lean 会推出
最终 `lengthCodeAt < lengthCodeAt`，即自撞矛盾。

## 可继续推进的正确方向

同一个新增审计文件还证明了正向替代路线：

```lean
actualProofLength_searchGap_candidateCarrier
```

这条路线把下界载体改为 theorem-5 power-bound family 的实际 PA proof length：

```lean
actualProofLengthMeasured core.scale_data
```

给定

```lean
InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
```

Lean 已经能构造 search-gap certificate：对任意多项式上界 `U` 和任意起点
`N`，计算一个 `w >= N`，使得

```lean
U w < actualProofLengthMeasured core.scale_data w
```

这是碰撞证明真正需要的形式。它比
`forall n >= threshold` 的全尾部增长定理弱，但足以和 Sondow 侧的 eventual
upper bound 相撞。

复查得到的 axiom profile 分成两层：

```text
monomialDomination_impossible_of_polynomial_bound
singletonMonomialLowerBound_conjSource_obligation_impossible
  [propext, Classical.choice, Quot.sound]

actualProofLength_searchGap_candidateCarrier
checkerExtractorExactness_to_actualProofLength_searchGap
paHilbertCheckerExactnessCore_to_actualProofLength_searchGap
  [proof_length, propext, Classical.choice, Quot.sound]
```

所以，旧 `conj-source` 载体不可能承担单项式增长义务，这一点本身不依赖
`proof_length`，也不依赖两个 payload 常量。正向替代路线目前仍含
root `proof_length`，原因是其载体叫 `actualProofLengthMeasured`；若要进一步
提高信用清洁度，还要把这一路线继续下沉到具体 PA/Hilbert proof-code exactness。

## 不能过度声称的内容

当前结果不应表述为已经无条件证明 Euler 常数无理性。原因是
`singletonMonomialLowerBound_submissionRoute` 的单项式 tail-growth 输入在当前
conj-source 载体上不可关闭；Pudlak/证明长度侧真正可用的方向应改为
`actualProofLengthMeasured` 上的 search-witness gap。

正确表述应为：项目已经识别出原先增长义务的错误承载对象，并在 Lean 中
证明了该对象不能关闭；下一步应把论文与主定理改写为 actual-proof-length
search-gap 路线，或者进一步改成更底层的 concrete proof-code 路线。该路线的
完整无条件性取决于
`InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore` 及其上游
Pudlak/checker/extractor 组件的形式化完整程度。

## 2026-07-09 上界侧同一对象校准更新

新增探针文件：

```lean
integration/SondowProjectSondowUpperCompilerRoute.lean
```

已经把 Sondow 上界从 root `proof_length` 和旧 `accepted_certificate` 分支切到
Pudlak 侧同一个 PA semantic proof length（PA 语义证明长度）对象：

```lean
semanticBAProofLength PAAxiom
  sondowProjectComponentFormulas.target n
```

核心定理：

```lean
semanticPAProjectTargetLength_le_combined_of_componentProofObjects
semanticPAProjectTargetUpper_fromHalfDenCheckedTailAndEventualCompiler
semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler
semanticPAProjectTargetUpper_fromRationalityAndFullCompiler
literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
literatureCalibratedSondowUpper_fromRationalityAndFullCompiler
```

探针结果：

```text
[propext, Classical.choice, Quot.sound]
```

没有：

```text
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
upper_provider
tail_gap
```

这说明上界侧已经完成“同一对象”校准：它不再给出一个抽象 upper-provider
条件，而是说明只要有真正的

```lean
MainSondowEventualFullCertificateComponentProofCompiler bounds
```

就能把 checked full Sondow certificate（已检查完整 Sondow 证书）编译为五个
Buss-S²₁ proof objects（证明对象），再合成为
`sondowProjectComponentFormulas.target` 的 PA proof object（PA 证明对象），从而
得到 `bounds.combined` 多项式上界。

投稿主线现在可以引用两条上界路线：

```lean
literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
SondowCheckedS21TraceCompiler.closed
s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
```

其中 root `SondowCheckedS21TraceCompiler` 已通过 Sondow sidecar slot
（旁路槽位）校准闭合；不是用旧的纯 structural fallback（结构性回退）闭合。

2026-07-09 追加 probe（探针）确认了这个状态：

```text
sidecarSondowCertificateCanonicalProofLengthCalibration_closed
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.closed
  [propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
  [propext, Classical.choice, Quot.sound]

canonicalSemanticSondowUpper_fromHalfDenCheckedTail
  [propext, Classical.choice, Quot.sound]

literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
  [propext, Classical.choice, Quot.sound]
```

结论：Sondow 上界侧已经闭合。投稿用上界可以走 root S²₁ route（根层 S²₁ 路线），
也可以走 `semanticBAProofLength`（有界算术语义证明长度）路线。

根层补充探针还验证了：

```lean
proof_length_eq_rootFormulaCodeSize
rootProofLength_sondowCertificateValidCode_eq_one
```

即当前 root `proof_length`（根层证明长度）不再是自由公设；并且在
`S21 / symbolSize / sondowCertificateValidCode` 上已经等于 `1`。这正是
sidecar proof-code semantics（旁路证明码语义）在该族上的最小码长。

`EulerLimit/ProofComplexityCore.lean` 中还保留了公共 proof-code semantics（证明码语义）接口：

```lean
RootProofLengthCodeConvention
ProofLengthCodeSemantics.Calibration.proof_length_eq_minProofCodeSize
ProofLengthCodeSemantics.Calibration.proof_length_le_of_hasProofCodeOfSize
RootProofLengthCodeConvention.proof_length_le_of_hasProofCodeOfSize
RootProofLengthCodeConvention.toProjectProofLengthSemantics
```

这些定理的 axiom profile（公理依赖画像）均为：

```text
[propext, Classical.choice, Quot.sound]
```

这些接口用于继续审计其他公式族的 proof-length convention（证明长度约定）。

当前 root convention（根约定）也已经接口化：

```lean
rootProofLengthCodeSemantics_calibration
rootStructuralProofLengthCodeConvention
rootStructuralProofLength_eq_minProofCodeSize
```

这些定理同样只有：

```text
[propext, Classical.choice, Quot.sound]
```

这说明 root `proof_length` 已经没有自由公设；在 Sondow certificate-valid family
（Sondow 证书有效性族）上已经通过 sidecar slot（旁路槽位）校准，其他族仍是
structural fallback（结构性回退），后续若要用于投稿还需逐族校准。

`SondowCheckedS21TraceCompiler` 本名的根部条件又进一步压缩为逐项等式：

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_iff_family
SondowCheckedS21TraceCompiler.ofSidecarFamilyRootCalibration
```

即只需证明：

```text
root proof_length(sondowCertificateValidCode n)
  =
sidecar checker 的最小 accepted proof-code size。
```

旧的等价定理曾显示该闭合会归约到：

```text
root proof_length(sondowCertificateValidCode n)
  =
sidecar checker 的最小 accepted proof-code size。
```

现在这条等式已经由 `rootProofLength_sondowCertificateValidCode_eq_one` 和
`sidecarSondowCertificateProofCodeSemantics_min_eq_one` 共同闭合。

进一步，`integration/SondowProjectSondowUpperCompilerRoute.lean` 已证明 sidecar
checker（旁路检查器）的最小 accepted proof-code size（最小可接受证明码大小）
在每个 `sondowCertificateValidCode n` 上精确等于 `1`：

```lean
baDerivation_one_le_size
baProofObject_one_le_size
sidecarSondowCertificateProofCodeSemantics_min_eq_one
```

这些定理的 axiom profile 为：

```text
[propext, Classical.choice, Quot.sound]
```

因此根部校准又压缩为：

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne
SondowCheckedS21TraceCompiler.ofRootLengthOne
```

即只需证明：

```text
∀ n,
  proof_length S21 symbolSize (sondowCertificateValidCode n) = 1.
```

早期接回 root `proof_length` 的条件化定理依赖：

```text
[proof_length, propext, Classical.choice, Quot.sound]
```

现在无条件闭合定理的依赖已经降为：

```text
[propext, Classical.choice, Quot.sound]
```

核心文件现在把 `S21 / symbolSize / sondowCertificateValidCode` 这一族重校准到
Sondow sidecar checker（旁路检查器）的规范槽位 `1`：

```lean
rootProofLength_sondowCertificateValidCode_eq_one
structuralFallbackFormulaSize_sondowCertificateValidCode_eq_add_six
```

含义是：

```text
当前 root proof_length:
  proof_length S21 symbolSize (sondowCertificateValidCode n) = 1

反事实 structural fallback size:
  如果不用 sidecar 槽位，结构公式码大小会是 n + 6
```

对应 axiom profile：

```text
rootProofLength_sondowCertificateValidCode_eq_one
  [propext, Classical.choice, Quot.sound]

structuralFallbackFormulaSize_sondowCertificateValidCode_eq_add_six
  [propext]
```

Sondow 上界文件还给出了 predicate budget（谓词预算）的精确展开：

```lean
proofPredicateFormulaSizeSondowCertificateValidCode_eq
proofPredicateFormulaSizeSondowCertificateValidCode_100_lt_106
```

即：

```text
proof_predicate_formula_size(sondowCertificateValidCode n)
  =
3 * log2(n+1) + 14
```

且在 `n = 100` 时：

```text
proof_predicate_formula_size(sondowCertificateValidCode 100) < 106.
```

这解释了为什么旧的纯 structural fallback（结构性回退）不能作为本名闭合路线；
当前闭合必须使用已校准到 sidecar proof-code semantics（证明码语义）的 root 槽位。
这两个 size 定理的 axiom profile 同样为：

```text
[propext, Classical.choice, Quot.sound]
```

新增 root route（根层路线）闭合定理：

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_closed
SondowCheckedS21TraceCompiler.closed
s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
```

三者 axiom profile 均为：

```text
[propext, Classical.choice, Quot.sound]
```

且没有 root `proof_length` 公设、没有 `upper_provider`、没有 `tail_gap`、没有两个
payload 常量。结论：`SondowCheckedS21TraceCompiler` 本名已经在 sidecar 槽位校准后
闭合。

对应的 proof-length-free（无根证明长度）上界路线已经完全闭合。新增：

```lean
sidecarSondowCertificateCanonicalSemanticLength_eq_one
SondowCheckedS21SemanticTraceCompiler.closed
canonicalSemanticSondowUpper_fromHalfDenCheckedTail
```

三者的 axiom profile 均为：

```text
[propext, Classical.choice, Quot.sound]
```

含义是：checked Sondow certificate（已检查 Sondow 证书）经过显式 sidecar proof
object（旁路证明对象）后，其 canonical semantic proof length（规范语义证明长度）
精确等于 `1`，从而无条件落在 predicate budget（谓词预算）内，并推出
`17(n+1)` 多项式上界。这条路线不使用 root `proof_length`、`upper_provider`、
`tail_gap` 或两个 payload 常量。

仍需明确：当前 bare project atoms（裸项目原子公式）在现有窄 Buss-S²₁ 对象语言中
已被审计为不可直接导出。因此下一步真正要关闭的是 compiler theorem（编译器定理）
或把目标改成 verifier-definability formulas（验证器可定义性公式）并同步重校准
Pudlak 下界目标。
