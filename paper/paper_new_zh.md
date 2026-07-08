# Lean 检查的 Sondow-Pudlak 存在性大 N 证书

## 摘要

本文报告一个 Lean 4 检查的 Sondow-Pudlak 存在性大 `N` 证书。当前机器检查版本已经不只是给出外层接口或路线图，而是在 proof-length recognition package、Sondow/partial verifier trace、half-denominator Sondow tail、partial-consistency truth、source-minChecked calibration 和 Buss-Pudlak rescaling 等真实根输入下，证明最终 project-length endpoint 确实计算出某个自然数 `N`，并且该 `N` 满足所需的 source-side strict gap。

核心 Lean 定理是：

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

其结论形如：

```lean
∃ N : Nat,
  endpointN = N ∧
  N =
    semanticStrongNatLowerBoundClassicalMonomialSearchWitness
      sourceLength hsource (max 17 sondowPrefixCoeff + 8) 1 0 ∧
  (max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

这说明：存在性大 `N` 已经在 Lean 中闭合。当前尚未完成的是把这个 `N` 展开为一个显式十进制自然数。换言之，已完成的是 existence theorem（存在性定理），未完成的是 numeric extraction（数值抽取）。

本文还记录数值路线的最新 normal form：在旧 proof-length tail-gap 模型和 S²₁/PudlakPA root proof-length inputs 下，最终 computed collision index 可化为

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

因此后续自然数 `N` 的真实任务不是重新包装接口，而是计算或构造这个 `thresholdOf`，以及消去仍依赖 rational-parameter denominator 和 finite prefix 的残余。

关键词：Euler-Mascheroni constant；Sondow criterion；Pudlak finite consistency；proof length；Lean 4；existential big N；formal verification。

## 1. 问题与结论边界

欧拉-马歇罗尼常数定义为

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

γ 是否有理仍是公开问题。Sondow 的判据把 γ 的有理性与一族可验证的证书条件联系起来；Pudlak-Friedman-Buss 方向则提供有限一致性陈述的 proof-length lower bounds。项目目标是把二者放到同一个形式化测量坐标中，使上界侧和下界侧在同一个大 `N` 上相遇。

本文主张的边界如下。

1. 已证明：在当前 source-calibrated proof-length recognition route 内，存在一个自然数 `N`，最终 endpoint 正是该 `N`，并且 source-side strict inequality 在该 `N` 上成立。
2. 已证明：该 `N` 的定义来源不是任意占位符，而是 `semanticStrongNatLowerBoundClassicalMonomialSearchWitness` 或在更显式 tail-gap 路线中化为 `max upperN thresholdOf(...)`。
3. 未证明：一个完全展开的十进制自然数 `N = ...`。
4. 未声称：无条件证明 γ 无理。

这一区分很重要。存在性大 `N` 已经是可审计的 Lean 结果；显式自然数 `N` 是下一阶段的计算/构造任务。

## 2. 形式化主定理

当前 proof checkpoint 的主入口是：

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

该定理的主要输入包括：

1. `hrec : S21GraftProofLengthRecognitionTheorem`，给出 S²₁ proof-length recognition package；
2. `sondowTrace` 和 `partialTrace`，给出两个 verifier trace soundness；
3. `rat : MainSondowRationalParameter`，表示 rationality branch 中的 Sondow rational parameter；
4. `partialTruth : PartialConsistencyAcceptedTruth`；
5. `time_bound_strict` 与 `exponent_ne_zero`；
6. `source_minChecked_calibration`，把 partial-consistency source proof length 校准到 `minCheckedCodeSize`；
7. `buss_pudlak_rescaling`，把 Buss-Pudlak rescaling 输入转成 semantic strong lower bound。

定理内部构造：

```lean
h :=
  hrec.toLocalProofCodeSemanticsPackage.toCanonicalCalibrationPackage

sondowThreshold :=
  max 3 ((rat.q.den + 1) / 2)

sondowPrefixCoeff :=
  natPrefixMax h.sondow_proofs.length sondowThreshold

sourceLength m :=
  ((h.sondow_proofs.conjIntro h.partial_proofs)
    |>.rightConjElim
    |>.minCheckedCodeSize m)
```

然后证明存在 `N : Nat`，使最终 endpoint 返回该 `N`，并且

```lean
(max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

这个结论是实际 proof object 上的结论，不是自然语言中的“应当存在”。

## 3. 两个根输入

当前构造不是从空接口开始，而是从两个根输入出发。

第一根是 S²₁ / Sondow proof-length side。相关桥接定理包括：

```lean
SondowReflectionGraftRootProofLengthConvention.ofRootS21AndPudlakPA

sondowReflectionGraftRootProofLengthConvention_nonempty_of_rootS21_pudlakPA

sondowReflectionGraftTailVerificationBridge_of_mainEventualCompiler_rootS21_pudlakPA_and_rationalParameter
```

这些结果把 Sondow reflection-graft route 的 proof-length convention 拆成 S²₁ root calibration 和 Pudlak/PA root calibration，而不是把整块根假设隐藏成一个不透明包。

第二根是原有 proof-length tail-gap model。它在最终 C-line root route 中给出：

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max
```

该定理把最终 computed collision index 化为：

```lean
max upper.upperN
  (proof_length_tail_gap.gap_for_polynomial_upper
    upper.U upper.polynomial).threshold
```

最新自然数路线进一步把这个 threshold 暴露为显式函数：

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

其目标形状是：

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

这就是后续要真正计算的自然数入口。

## 4. 存在性大 N 与数值大 N

存在性大 `N` 和数值大 `N` 是不同层级。

存在性定理已经闭合，因为 `SemanticStrongNatLowerBound` 给出的是 `∃ᶠ n in atTop` 形式的强下界。Lean 用 classical witness 抽出满足目标多项式不等式的某个 `N`：

```lean
semanticStrongNatLowerBoundClassicalMonomialSearchWitness
```

这足以证明：

```lean
∃ N : Nat, endpointN = N ∧ ...
```

但它不直接给出一个可打印的自然数。原因是 `SemanticStrongNatLowerBound` 是 Prop-level lower bound，而不是 executable search procedure。

要得到数值大 `N`，必须走更强的可计算路线，例如：

1. 给出 explicit tail-gap provider，并计算 `thresholdOf upper.U upper.polynomial`；
2. 或给出 executable rejection extractor，并计算

```lean
extractor.witness upper.U upper.polynomial upper.upperN
```

当前 Lean 已经把最终自然数路线压缩到这些真实计算入口；剩余工作是构造这些入口，而不是再建立外层包装。

## 5. Half-Denominator 路线的残余

half-denominator Sondow tail 给出了更尖锐的阈值：

```lean
max 3 ((rat.q.den + 1) / 2)
```

在 one-higher-power 或 checked-prefix 条件下，相关 endpoint 可化成：

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

但是这个式子仍依赖 `rat.q.den`。由于 `rat : MainSondowRationalParameter` 来自 rationality branch，而最终目标正是推出 rationality branch 矛盾，不能把 `rat.q.den` 当作一个已知外部常数随意消去。

项目中还证明了 prefix obstruction：

```lean
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

这说明 accepted/checked prefix premise 不能从 rational parameter 自动获得。它是一个真实的有限前缀障碍，不应被包装成“显然成立”。

## 6. 可复刻版本

Lean proof checkpoint 已发布为：

```text
bigN-existence-20260708
```

对应提交：

```text
69f5ef28b0f1b62ff7276314423ce4f806c50d0c
```

该版本包含存在性大 `N` 的 Lean 证明，并经过以下检查：

```bash
git diff --check
lake env lean integration/SondowProjectS21Kernel.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

其中 `ProjectLengthTargetUpperEndpoint.lean` 只有两个既有 `unnecessarySimpa` linter warning，没有 Lean 错误。

本文修订版对应的审计发布标签为：

```text
bigN-existence-paper-20260708
```

该标签用于下载更新后的论文源文件与 PDF/HTML 资产。它不改变上一段 Lean 证明 checkpoint 的边界，而是把论文说明和最新 `thresholdOf` 数值交接口同步到存在性大 `N` 状态。

## 7. 审计清单

专家审计时应优先检查以下点。

1. 主 theorem 是否确实返回 `∃ N : Nat`，而不是只声明外层 interface 非空。
2. `source_minChecked_calibration.semanticStrongNatLowerBound_of_rescaling` 是否确实把 Buss-Pudlak rescaling 接到 `sourceLength`。
3. `sondowThreshold` 和 `sondowPrefixCoeff` 是否来自真实 proof-family length，而不是人为常数。
4. S²₁ root calibration 与 Pudlak/PA root calibration 是否通过 split-root constructor 合成。
5. 数值路线中 `thresholdOf` 或 `extractor.witness` 是否是实际算法，而不是再次使用 `Classical.choose`。

这些审计点能把“存在性大N”与“数值大N”严格分开，避免把已证明部分和未完成部分混在一起。

## 8. 后续自然数 N 路线

后续工作应集中在两个真实残余上。

第一，构造 explicit tail-gap provider。若能给出

```lean
thresholdOf :
  ∀ U : Nat → Real, is_polynomial_bound U → Nat
```

并证明它等于旧 proof-length tail-gap threshold，则最终自然数就是：

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

第二，构造 executable rejection extractor。若能给出真实的 `extractor.witness` 和 `extractor.cutoff`，并证明 finite candidate rejection，则最终自然数可直接由 witness 函数计算。

这两条路线都是从真实结构出发。它们不会通过新增接口本身解决问题；真正的工作是给出可计算 threshold 或 witness 的内容。

## 9. 结论

当前 Lean 项目已经证明存在性大 `N`：最终 project-length endpoint 返回某个自然数 `N`，该 `N` 是 source-calibrated lower-bound witness，并在该点满足严格 source-side gap。

这已经足以作为一个独立的 formal checkpoint：存在性大 `N` 已机器检查。下一步不是重复包装该结果，而是沿 `thresholdOf` 或 executable `extractor.witness` 路线计算具体自然数 `N`。

因此，当前版本应公开表述为：一个 Lean 检查的 Sondow-Pudlak source-calibrated existential big-N certificate。它不是 γ 无理性的最终无条件证明，也不是数值 `N` 的最终输出；但它已经把“存在大N”从路线图推进到可复刻的机器检查定理。

## 参考文献

1. Jonathan Sondow, “Criteria for Irrationality of Euler's Constant,” *Proceedings of the American Mathematical Society*, 131(11), 3335-3344, 2003. arXiv:math/0209070.
2. Samuel R. Buss, “On Gödel's Theorems on Lengths of Proofs I: Number of Lines and Speedup for Arithmetics,” *Journal of Symbolic Logic*, 59(3), 737-756, 1994.
3. Pavel Pudlak, “On the lengths of proofs of finitistic consistency statements in first order theories,” in *Logic Colloquium 1984*.
4. Pavel Pudlak, “Improved bounds to the lengths of proofs of finitistic consistency statements,” in *Logic and Combinatorics*, 1987.
5. Jan Krajicek and Pavel Pudlak, “The Number of Proof Lines and the Size of Proofs in First-Order Logic,” *Archive for Mathematical Logic*, 1988.
6. The Lean 4 and Mathlib projects, project documentation and source libraries.
