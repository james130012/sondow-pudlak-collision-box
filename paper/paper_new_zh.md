# 一个 Lean 4 验证的 Sondow-Pudlak 存在性阈值定理

James^1,*

^1 独立研究者。

*通讯：在正式投稿地址确定前，通过公开仓库 issue tracker 联系。*

## 摘要

Euler-Mascheroni 常数的无理性仍是公开问题。本文不声称解决该问题。
本文从 Sondow-Pudlak 路线中抽取一个精确的 proof-complexity threshold
命题，并在 Lean 4 中验证它：在显式给出的 S21 proof-length recognition
数据、Sondow 与 partial-consistency families 的 verifier traces、rational
branch 上的 Sondow 参数、partial-consistency truth、source-minChecked
calibration 以及 Buss-Pudlak time-constructible rescaling theorem 之下，
Lean 证明最终 project-length endpoint 返回某个自然数 `N`，并且同一个
`N` 满足所需的 source-side strict gap。本文还记录了 Sondow finite
prefix 到 MiniHilbert `minProofCodeSize` prefix 的改写，以及后续数值路线
的 handoff theorem：
`max upper.upperN (thresholdOf upper.U upper.polynomial)`。本文结论是关于
大阈值的存在性形式化定理；它不是 `N` 的十进制展开，也不是 `gamma` 无理
性的无条件证明。

## 1. 引言

Euler-Mascheroni 常数定义为

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

Sondow 判据可把 `gamma` 的有理性假设转化为结构化的算术证书。Pudlak-
Friedman-Buss 的 proof-complexity 路线则给出有限一致性语句的证明长度
下界。Sondow-Pudlak 对撞论证只有在两侧进入同一个 proof-length coordinate
之后才有严格意义：必须是同一类被测证明对象、同一套 proof-code semantics、
同一组 finite-prefix conventions。

本文制品的贡献，是在这个坐标问题中给出一个机器检查的 endpoint。大 `N`
公式已经不再只是路线图中的目标：本 release 中有 Lean theorem 证明该阈值
存在，并证明该阈值处的严格不等式。该 theorem 是条件性的，条件以显式
input packages 的形式出现在 theorem statement 中；这些输入不是隐藏的
无条件可得性断言。

边界必须说清楚。本文证明的是当前形式化路线中的大阈值存在性 theorem。
本文不抽取十进制自然数，不消除整个项目中的每一个残余 proof-complexity
输入，也不证明 `gamma` 的无理性。

## 2. 形式化坐标

主源文件是

```text
integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

本文审计的 release 是

```text
bigN-nature-paper-20260708
```

对应提交为

```text
c26cd1d2b3abbc6c3584ab5c2afbd1e953d3cacd
```

令

```lean
h := hrec.toLocalProofCodeSemanticsPackage.toCanonicalCalibrationPackage
```

为从 `S21GraftProofLengthRecognitionTheorem` 得到的 canonical calibration
package。主 theorem 中的 source measurement 为

```lean
sourceLength m :=
  ((h.sondow_proofs.conjIntro h.partial_proofs)
    |>.rightConjElim
    |>.minCheckedCodeSize m)
```

因此，下界侧不是任意数值函数。它是把 Sondow proof family 与
partial-consistency proof family 先作 conjunction introduction，再作
right-conjunction elimination 后得到的 MiniHilbert checked-code measurement。

对 rational branch 参数

```lean
rat : MainSondowRationalParameter
```

half-denominator tail threshold 是

```lean
sondowThreshold := max 3 ((rat.q.den + 1) / 2)
```

Sondow finite-prefix coefficient 是

```lean
sondowPrefixCoeff :=
  natPrefixMax h.sondow_proofs.length sondowThreshold
```

最终 endpoint 中生成的 target upper coefficient 是

```lean
max 17 sondowPrefixCoeff + 8
```

次数为 `1`。这正是 source-side strict gap 中出现的线性项系数。

## 3. 主定理

本文使用的主形式化 endpoint 是

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

其数学内容如下。

**定理 1（source-calibrated existential big-N endpoint）。** 固定 internal
Pudlak scale data。假设给定：

1. `S21GraftProofLengthRecognitionTheorem`；
2. `sondowCertificateValidCode` 的 verifier-trace soundness；
3. `partialConsistencyCode` 的 verifier-trace soundness；
4. rational-branch 参数 `rat : MainSondowRationalParameter`；
5. `PartialConsistencyAcceptedTruth`；
6. time-constructible bound 的严格单调性；
7. Pudlak exponent 非零；
8. conjunction proof family 的
   `MiniHilbert.PartialConsistencySourceMinCheckedCalibration`；
9. `BussPudlakTimeConstructibleRescalingTheorem`。

则在上述 `sourceLength`、`sondowThreshold` 和 `sondowPrefixCoeff` 记号下，
最终 project-length search endpoint 返回某个自然数 `N`，并且

```lean
∃ N : Nat,
  endpointN = N ∧
  N =
    semanticStrongNatLowerBoundClassicalMonomialSearchWitness
      sourceLength hsource (max 17 sondowPrefixCoeff + 8) 1 0 ∧
  (max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

其中 `hsource : SemanticStrongNatLowerBound sourceLength` 不是一个额外
外部输入，而是在 theorem 内部由 source-minChecked calibration 和
Buss-Pudlak rescaling theorem 推出。

该 theorem 在当前阶段是存在性、非计算性的：witness 是 classical object

```lean
semanticStrongNatLowerBoundClassicalMonomialSearchWitness
```

这足以得到形式化的 `∃ N : Nat` theorem 和该点处的 strict inequality；
但它不提供可执行的十进制 `N`。

## 4. 证明架构

Lean 证明把 endpoint 分解为四个可审计组件。

**Sondow tail。** 从 rational-branch 参数出发，reproof Sondow tail 在

```lean
max 3 ((rat.q.den + 1) / 2)
```

之后被接受。对应构造为

```lean
mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
```

**Finite prefix。** 剩余 prefix 没有被忽略，而是由 `natPrefixMax` 测量，
并进入线性 upper coefficient `max 17 sondowPrefixCoeff + 8`。

**MiniHilbert rewrite。** finite prefix 通过下列 theorem 改写到真实的
MiniHilbert proof-code semantics：

```lean
S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
```

其中

```lean
s21SondowMiniHilbertMinProofCodeSizePrefixMax hrec threshold
```

是在 recognition theorem 生成的 Sondow certificate-valid codes 上取
`minProofCodeSize` prefix maximum。

**Source lower bound。** 主 theorem 不假设裸的 `SemanticStrongNatLowerBound`。
它从

```lean
PartialConsistencySourceMinCheckedCalibration
BussPudlakTimeConstructibleRescalingTheorem
```

构造该 lower bound，然后把 semantic-strong search witness theorem 应用到
生成的线性单项式上。

这些组件合在一起证明：endpoint 和 source lower-bound witness 命名同一个
自然数；并且在该自然数处，生成的线性单项式严格小于 `sourceLength`。

## 5. Half-denominator 边界

half-denominator threshold 相对于 full-denominator tail 是实质改进，但它仍
留下真实的 finite-prefix 边界。项目证明了 obstruction

```lean
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

它说明在当前 accepted-code semantics 下，低于

```lean
max 3 ((rat.q.den + 1) / 2)
```

的 checked-prefix premise 不能由 rational parameter 自动推出。特别是，
prefix 包含 index `0`，而 rational-parameter full Sondow certificate 在该处
不可能 accepted，因为分母为正。

这个 obstruction 是数学陈述的一部分。把它从论文中移除，会把一个已经检查
的 theorem 改写成一个未证明的更强断言。

## 6. 数值 handoff

 companion numerical handoff theorem 位于

```text
integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

定理名为

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

它证明：一旦 tail-gap threshold function 满足

```lean
(proof_length_tail_gap.gap_for_polynomial_upper U hU).threshold =
  thresholdOf U hU
```

则 C-line root route 中的 final computed collision index 为

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

这才是后续打印自然数 `N` 的正确入口。十进制 `N` 需要真实计算
`thresholdOf upper.U upper.polynomial`，或给出等价的 executable witness。
再增加一个自然语言层面的 endpoint 并不能解决数值问题。

## 7. 主张与非主张

| 陈述 | 状态 | Lean 证据 |
| --- | --- | --- |
| source-calibrated endpoint 存在 `N : Nat` | 已证明 | `projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax` |
| 同一个 `N` 满足 source-side strict gap | 已证明 | 同上 |
| 从 source-minChecked calibration 与 Buss-Pudlak rescaling 推出 `SemanticStrongNatLowerBound` | 已在主 theorem 内证明 | 同上 |
| Sondow finite prefix 改写到 MiniHilbert `minProofCodeSize` | 已证明 | `S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax` |
| half-denominator checked-prefix premise 自动成立 | 在当前 semantics 下为假 | `not_sondowCheckedHalfDenPrefix_of_rationalParameter` |
| C-line 数值 endpoint 化为 `max upper.upperN (thresholdOf ...)` | 已证明 | `finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf` |
| `N` 的十进制值 | 未完成 | 需要 executable `thresholdOf` 或 witness extraction |
| `gamma` 无理性的无条件证明 | 未声称 | 不属于本文 theorem |

## 8. 复现与审计协议

仓库固定 Lean 与 Mathlib 版本：

```text
leanprover/lean4:v4.31.0
mathlib v4.31.0
```

从公开 release 复现的基本命令为：

```bash
git clone https://github.com/james130012/sondow-pudlak-collision-box.git
cd sondow-pudlak-collision-box
git checkout bigN-nature-paper-20260708
lake exe cache get
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

若审稿人希望做 targeted theorem probe，应先构建相应模块，使 `.olean`
文件可被 `lake env lean --stdin` 导入：

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
lake build integration.SondowProjectMonth11Month12HardResidualElimination
```

然后运行：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

#check projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
#check S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
#check not_sondowCheckedHalfDenPrefix_of_rationalParameter
EOF
```

以及：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12HardResidualElimination

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12HardResidualElimination

#check finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
EOF
```

论文源文件还应通过：

```bash
git diff --check
```

更大项目中较早的 conditional collision endpoints 的 axiom boundary 记录在
`AXIOM_LEDGER.md`。本文主 theorem 更具体：它从可发表的大 `N` endpoint 中
移除了抽象 `SemanticStrongNatLowerBound` 前提，但仍依赖定理 1 中列出的
recognition、verifier-trace、rational-branch、partial-truth、calibration
和 rescaling 输入。

## 9. 数据与代码可得性

本文不使用经验数据集。数学制品由 Lean 源码树、固定的 Lake 配置和本文
paper sources 组成。

代码仓库为：

```text
https://github.com/james130012/sondow-pudlak-collision-box
```

本文审计的 release 为：

```text
https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-nature-paper-20260708
```

正式投稿时，应把最终接受的 commit 和生成的论文制品归档到可生成 DOI 的
平台。GitHub release 适合公开审计，但不能替代永久归档。

## 10. 参考文献

1. Sondow, J. Criteria for irrationality of Euler's constant. *Proceedings of
   the American Mathematical Society* **131**, 3335-3344 (2003).
2. Buss, S. R. On Godel's theorems on lengths of proofs I: number of lines and
   speedup for arithmetics. *Journal of Symbolic Logic* **59**, 737-756 (1994).
3. Pudlak, P. On the lengths of proofs of finitistic consistency statements in
   first order theories. In *Logic Colloquium 1984* (1986).
4. Pudlak, P. Improved bounds to the lengths of proofs of finitistic
   consistency statements. In *Logic and Combinatorics* (1987).
5. Krajicek, J. and Pudlak, P. The number of proof lines and the size of proofs
   in first-order logic. *Archive for Mathematical Logic* (1988).
6. de Moura, L. and Ullrich, S. The Lean 4 theorem prover and programming
   language. In *Automated Deduction - CADE 28* (2021).

## 11. 声明

本草稿未声明外部资助。作者声明不存在竞争性利益。本文使用 AI-assisted
editing 重组文本；所有数学主张均绑定到上文列出的 Lean 源文件和 theorem
names，不以 AI 生成文本替代 Lean 证明。
