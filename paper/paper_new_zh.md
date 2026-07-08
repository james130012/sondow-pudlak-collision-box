# 一个 Lean 检查的 Sondow-Pudlak 存在性阈值证书

James^1,*

^1 Independent researcher.
*Correspondence: through the public repository issue tracker unless a journal
submission address is supplied.

## 摘要

Euler-Mascheroni constant 的无理性仍是公开问题。Sondow 判据把有理性假设转化为一族可检查的算术证书，Pudlak-Friedman-Buss 方向则给出有限一致性语句的证明长度下界。这里我们报告一个 Lean 4 机器检查的 Sondow-Pudlak 证明长度制品：在显式列出的 S21 proof-length recognition、Sondow/partial verifier trace、half-denominator tail、partial-consistency truth、source-minChecked calibration 和 Buss-Pudlak rescaling 输入下，Lean 证明最终 project-length endpoint 返回某个自然数阈值 `N`，并且该 `N` 满足所需的 source-side strict gap。结果不是 Euler 常数无理性的无条件证明，也不是十进制自然数 `N` 的抽取；它把此前路线图中的“存在大 N”推进为可复现、可审计的形式化定理。

## 主文

### 问题

Euler-Mascheroni constant 定义为

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

项目的目标不是把这个公开问题用自然语言断言解决，而是把 Sondow 侧的证书上界和 Pudlak 侧的证明长度下界放到同一个可检查坐标中。本文报告的是一个中间但实质的形式化结论：在当前 source-calibrated proof-length route 中，存在最终阈值 `N`。

这个表述有三个边界。

1. 已证明的是条件性形式化证书：给定论文列出的根输入，Lean 构造 `N : Nat` 并证明目标不等式。
2. 未证明的是展开成十进制的自然数 `N = ...`。
3. 未声称的是 `¬ is_rational euler_mascheroni` 的无条件定理。

这一区分是审计的核心。一个存在性阈值定理可以是严肃的机器检查成果，但它不能被包装成最终数值抽取或最终无理性证明。

### 形式化结果

主形式化入口位于

```text
integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

定理名为

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

其结论的审计形状为

```lean
∃ N : Nat,
  endpointN = N ∧
  N =
    semanticStrongNatLowerBoundClassicalMonomialSearchWitness
      sourceLength hsource (max 17 sondowPrefixCoeff + 8) 1 0 ∧
  (max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

这里 `sourceLength` 不是任意函数，而是从 Sondow proof family 与 partial-consistency proof family 的 conjunction/right-elimination checker measurement 中得到：

```lean
sourceLength m :=
  ((h.sondow_proofs.conjIntro h.partial_proofs)
    |>.rightConjElim
    |>.minCheckedCodeSize m)
```

`sondowPrefixCoeff` 也不是人为常数，而是有限前缀的真实最大值：

```lean
sondowThreshold := max 3 ((rat.q.den + 1) / 2)
sondowPrefixCoeff := natPrefixMax h.sondow_proofs.length sondowThreshold
```

因此，Lean 证明的是一个带来源的阈值存在性结果：最终 endpoint 返回的 `N` 与 lower-bound witness 同一，并在该点满足严格下界。

### 两个根输入

该构造从两个根输入出发。

第一根是 S21/Sondow proof-length recognition side。它由

```lean
S21GraftProofLengthRecognitionTheorem
```

提供，并通过 `toLocalProofCodeSemanticsPackage` 与 `toCanonicalCalibrationPackage` 进入 project-length route。最新桥接把有限前缀最大值接到了 MiniHilbert proof-code semantics：

```lean
s21SondowMiniHilbertMinProofCodeSizePrefixMax

S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
```

这一步很重要，因为它把残余有限前缀从抽象 proof-family length 改写到 `minProofCodeSize` 上。它不是最终十进制计算，但它把数值任务推进到真实证明码语义。

第二根是原 proof-length tail-gap model。最终 C-line root route 中的数值入口位于

```text
integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

定理名为

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

它把最终 computed collision index 化为

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

这给出了后续十进制 `N` 的真实入口：必须构造并计算 `thresholdOf`，而不是再增加外层接口。

### 结果边界

表 1 列出本文主张与非主张。

| 项目 | 状态 | 机器检查入口 |
| --- | --- | --- |
| 存在 `N : Nat` | 已证明 | `projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax` |
| `N` 满足 source-side strict gap | 已证明 | 同上 |
| Sondow finite prefix 改写到 MiniHilbert `minProofCodeSize` | 已证明 | `S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax` |
| tail-gap 数值入口化为 `max upper.upperN (thresholdOf ...)` | 已证明 | `finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf` |
| 打印十进制自然数 `N` | 未完成 | 需要可计算 `thresholdOf` 或 executable witness |
| 无条件证明 `gamma` 无理 | 未声称 | 不属于本文结论 |

### Half-denominator 残余

half-denominator Sondow tail 给出阈值

```lean
max 3 ((rat.q.den + 1) / 2)
```

在更强的 checked-prefix 条件下，相关 endpoint 可进一步化为

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

但 `rat.q.den` 来自 rationality branch，不能在没有额外构造的情况下当作已知外部常数消去。项目中还证明了真实的 finite-prefix obstruction：

```lean
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

这说明 checked-prefix premise 不能从 rational parameter 自动推出。该障碍必须保留在论文中；把它包装成“显然成立”会改变定理含义。

### 可复现性

本研究制品固定 Lean 与 Mathlib 版本：

```text
leanprover/lean4:v4.31.0
mathlib v4.31.0
```

最小复现步骤如下。

```bash
git clone https://github.com/james130012/sondow-pudlak-collision-box.git
cd sondow-pudlak-collision-box
git checkout codex/month9-10-internal-lower-machine-continuation
lake exe cache get
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

旧公开对撞入口可用轻量 probe 检查：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#check SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

论文中的新 Month 11/12 定理以源文件 type-check 为主复现方式。若审稿人需要通过 `#check` 直接打印新定理类型，应先运行：

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
lake build integration.SondowProjectMonth11Month12HardResidualElimination
```

然后再用 `lake env lean --stdin` 导入相应模块。完整构建会重放大量 integration 依赖，耗时显著长于源文件直检。

### 为什么还没有十进制 N

存在性结果使用的是 Prop-level strong lower bound：

```lean
SemanticStrongNatLowerBound
```

Lean 通过

```lean
semanticStrongNatLowerBoundClassicalMonomialSearchWitness
```

抽取满足目标不等式的 witness。这足以证明 `∃ N : Nat`，但不是可执行搜索程序。要打印自然数，必须进一步构造以下二者之一。

1. 一个可计算的 `thresholdOf upper.U upper.polynomial`，并证明它等于 tail-gap threshold。
2. 一个 executable rejection extractor，给出真实 `extractor.witness` 与 `extractor.cutoff`。

本文的贡献是把存在性阈值闭合，并把数值路线压到这两个真实入口上。

## 参考文献

1. Sondow, J. Criteria for irrationality of Euler's constant. *Proceedings of the American Mathematical Society* **131**, 3335-3344 (2003).
2. Buss, S. R. On Godel's theorems on lengths of proofs I: number of lines and speedup for arithmetics. *Journal of Symbolic Logic* **59**, 737-756 (1994).
3. Pudlak, P. On the lengths of proofs of finitistic consistency statements in first order theories. In *Logic Colloquium 1984* (1986).
4. Pudlak, P. Improved bounds to the lengths of proofs of finitistic consistency statements. In *Logic and Combinatorics* (1987).
5. Krajicek, J. & Pudlak, P. The number of proof lines and the size of proofs in first-order logic. *Archive for Mathematical Logic* (1988).
6. de Moura, L. & Ullrich, S. The Lean 4 theorem prover and programming language. *Automated Deduction - CADE 28* (2021).

## Methods

### Formal environment

All formal claims are checked in Lean 4 with the repository-pinned toolchain:

```text
leanprover/lean4:v4.31.0
```

The Lake package is `euler_limit`; the relevant dependency is Mathlib at revision `v4.31.0`. The file `lakefile.toml` fixes these dependencies.

### Verification protocol

The primary verification protocol is source-file elaboration with Lean:

```bash
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

The first command checks the existential big-`N` endpoint and the MiniHilbert prefix bridges. The second command checks the tail-gap `thresholdOf` handoff theorem.

Whitespace and patch-integrity checks are run with:

```bash
git diff --check
```

### Axiom and assumption audit

The manuscript separates formal composition from remaining mathematical inputs. The older public collision endpoint still depends on explicitly listed external or abstract inputs, including literature Pudlak lower-bound content, payload truth, and root `proof_length`. These dependencies are documented in `AXIOM_LEDGER.md`.

The existential big-`N` theorem removes the abstract `SemanticStrongNatLowerBound` premise from the publishable endpoint by deriving it from:

```lean
PartialConsistencySourceMinCheckedCalibration
BussPudlakTimeConstructibleRescalingTheorem
```

It does not remove all global project assumptions. In particular, the recognition theorem and verifier traces remain explicit inputs.

### AI-assisted manuscript preparation

AI-assisted editing was used to reorganize the manuscript text and to prepare reproducibility instructions. The mathematical and formal claims reported here are tied to Lean source files and are checked by the commands above; no AI-generated mathematical assertion is used as a substitute for a Lean theorem.

## Data Availability

No empirical datasets were generated or analysed. The minimum material needed to verify the claims is the Lean source tree, the pinned Lake configuration, and the paper source files in this repository.

## Code Availability

The source code is available at:

```text
https://github.com/james130012/sondow-pudlak-collision-box
```

The current audit branch is:

```text
codex/month9-10-internal-lower-machine-continuation
```

For journal submission, the exact accepted commit should be archived in a DOI-minting repository such as Zenodo or Code Ocean, and this section should be updated with the DOI. A GitHub branch or tag is sufficient for immediate public audit, but it is not a substitute for a permanent journal archive.

## Acknowledgements

No external funding is declared in this draft.

## Author Contributions

J. designed the formal route, implemented the Lean development, prepared the manuscript, and is responsible for the repository release unless additional contributors are added before submission.

## Competing Interests

The author declares no competing interests in this draft.

## Additional Information

Correspondence and requests for materials should be directed through the public repository until a journal submission address is supplied. Supplementary information should include the exact release tag, commit hash, `#print axioms` transcript, and generated PDF/HTML audit artifacts for the submitted version.
