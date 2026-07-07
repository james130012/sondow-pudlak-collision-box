# Lean 检查的 Sondow-Pudlak 符号对撞证书

## 摘要

本文报告一个 Lean 4（证明器）检查的 Sondow-Pudlak symbolic collision certificate（符号对撞证书）。在 checked lower bound（检查下界）、explicit target upper（显式目标上界）、scale data（尺度数据）和 checker/project-length semantics（检查器/项目长度语义）按形式化接口给定时，Lean 已经把上下两侧推进到同一个 no-fallback bigN（无后备大阈值）上，并证明

```lean
upper.U bigN < measured bigN
measured bigN ≤ upper.U bigN
False
```

这不是一个只在自然语言中描述的对撞：`bigN`（大阈值）、`measured`（被测函数）、`upper.U`（上界函数）和两条不等式都出现在同一个 Lean theorem（Lean 定理）中。进一步的 computation-facing normal form（面向计算的规范形）证明该 `bigN` 正是

```lean
rejectionExtractor.witness upper.U upper.polynomial 0
```

因此，当前成果的核心不是“假设存在某个很大的 N”，而是把同一个形式化见证压缩到 checker rejection extractor（检查器拒绝抽取器）的阈值 0 见证。

本文不声称已经给出 Euler-Mascheroni constant（欧拉-马歇罗尼常数）γ 的无条件无理性证明，也不声称已经输出 numeric N（数值阈值）。当前主张是更精确的：在项目的 checked lower bound（检查下界）接口内，Sondow 上界侧和 Pudlak 型下界侧的形式化对撞核心已经闭合，并且有可复刻的 public checkpoint（公开检查点）。

关键词：Euler-Mascheroni constant（欧拉-马歇罗尼常数）；Sondow criterion（Sondow 判据）；Pudlak finite consistency（Pudlak 有限一致性）；proof complexity（证明复杂度）；Peano Arithmetic（皮亚诺算术）；Lean 4（证明器）；symbolic collision（符号对撞）。

## 1. 问题与目标

欧拉常数定义为

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

γ 是否有理仍是公开问题。Sondow 的判据把 γ 的有理性与某些积分、乘积和小数部分条件联系起来；Pudlak-Friedman-Buss 方向的结果则给出 finite consistency statements（有限一致性陈述）的 proof-length lower bounds（证明长度下界）。本项目研究的是这两类信息能否在同一个 formal measurement coordinate（形式化测量坐标）上发生 collision（对撞）。

一个有效对撞需要同时满足三件事。

1. 上界侧必须给出某个 measured function（被测函数）的 eventual upper bound（最终上界）。
2. 下界侧必须给出同一个 measured function（被测函数）的 strict lower/gap statement（严格下界/间隙陈述）。
3. 两侧必须落在同一个 `bigN`（大阈值）和同一个 checker/project-length semantics（检查器/项目长度语义）上。

前两点单独成立并不够。若上界和下界测量的是不同对象，就不会推出矛盾。本文的形式化重点正是把“同一对象”从直觉说法变成可检查的 Lean theorem（Lean 定理）。

## 2. 共同测量对象

项目中的共同测量对象由三层组成。

第一层是 formula/code layer（公式/编码层）。所有要比较的公式族必须进入同一个 local code family（本地编码族），否则 Pudlak 侧下界和 Sondow 侧证书不能共同计量。

第二层是 checker layer（检查器层）。项目使用本地 Hilbert/PA-style proof checker（Hilbert/PA 风格证明检查器）把 proof object（证明对象）和 formula code（公式编码）连接起来。这里的关键量不是抽象文字长度，而是 checker 可以识别的 minCheckedCodeSize（最小已检查码长）或 projectLength（项目长度）。

第三层是 gap/search layer（间隙/搜索层）。对每个 polynomial upper bound（多项式上界），lower-side rejection extractor（下界侧拒绝抽取器）给出一个 witness（见证），在该见证处严格间隙成立。当前最新对接把目标阈值固定为 0，从而得到 no-fallback（无后备）的搜索见证。

在这个坐标中，对撞的核心形状是：

```math
U(N) < M(N) \quad\text{and}\quad M(N) \le U(N).
```

这里 `M` 是形式化中的 `measured`（被测函数），`U` 是 `upper.U`（上界函数），`N` 是同一个 `bigN`（大阈值）。两条不等式合在一起给出 `False`（矛盾）。

## 3. 当前主结果

当前主结果可以用下面的 Lean theorem（Lean 定理）概括：

```lean
projectLengthExplicitTargetUpperSearchBigNCertificate_of_checkedLowerBound_noFallback
```

它从 `InternalPudlakTheorem5CheckedPowerBoundLowerBound`（内部 Pudlak 第五定理检查幂界下界输入）直接构造 target-upper search bigN certificate（目标上界搜索大阈值证书）。该定理要求的主要输入包括：

1. `scale_data`（尺度数据）：包含缩放函数、幂界编码和相关单调性数据；
2. `left_family` / `right_family`（左右证明族）：用于构造 conjunction/introduction route（合取引入路线）和右侧目标族；
3. `lengthCodeAt`（长度编码函数）：把下界侧测量连接到项目中的 minCheckedCodeSize（最小已检查码长）；
4. `checked_lower`（检查下界）：Pudlak 型幂界下界的已检查接口；
5. polynomial bound certificates（多项式界证书）：证明左右证明族长度受多项式控制；
6. `time_bound_strict`（时间界严格单调性）和 `exponent_ne_zero`（指数非零性）。

在这些输入下，定理返回同一个 `bigN` 上的完整 certificate package（证书包）：

```lean
upper.upperN = 0
concreteFrontier.lower_search.rejectionExtractor.witness
  upper.U upper.polynomial upper.upperN = bigN
PAHilbertAcceptedProofCodeForFormulaCode
  (concretePAHilbertPowerBoundChecker scale_data)
  (scale_data.powerBoundRawCode bigN)
  bigN
scale_data.powerBoundRawCode bigN =
  strengthenedPartialConsistencyCode (scale_data.scale bigN)
upper.U bigN < measured bigN
measured bigN ≤ upper.U bigN
False
```

这个 theorem（定理）说明：checked lower bound（检查下界）已经不是停在外层假设或叙述接口上，而是被接到了 explicit target upper（显式目标上界）的 no-fallback（无后备）证书上。

## 4. `bigN` 的规范形

后续定理

```lean
projectLengthExplicitTargetUpperSearchBigN_of_checkedLowerBound_noFallback_eq_rejectionExtractorWitness_zero
```

给出 computation-facing exactness（面向计算的精确性）：

```lean
bigN =
  concreteFrontier.lower_search.rejectionExtractor.witness
    upper.U upper.polynomial 0
```

这一步很重要。它排除了“形式上有一个存在见证，但不知道和计算路线是否一致”的残留。当前 `bigN`（大阈值）就是 lower search rejection extractor（下界搜索拒绝抽取器）对 `upper.U`（上界函数）和 `upper.polynomial`（上界多项式证书）在阈值 0 处给出的 witness（见证）。

换言之，当前尚未完成的是 numeric evaluation（数值求值），不是 symbolic identification（符号识别）。要输出具体自然数 `N`，还需要把 `upper.U`、`upper.polynomial`、`scale_data` 和 rejection extractor（拒绝抽取器）的可执行表示全部展开到可计算数据；但形式化对象已经被校准到唯一的计算入口。

## 5. 可复刻检查点

仓库发布了 prerelease（预发布）：

```text
fcce697-symbolic-collision-checkpoint
```

该 release（发布）固定到 commit（提交）

```text
fcce697c60adfe87d4d33515ff965322962fc994
```

这个 checkpoint（检查点）可用于复刻“同一个 `bigN` 上出现两条相反不等式并推出 `False`”这一事实。它不是 numeric N checkpoint（数值阈值检查点），也不是 γ irrationality theorem（γ 无理性定理）；它是 symbolic collision checkpoint（符号对撞检查点）。

专家审计时应把这个检查点理解为：

1. collision kernel（对撞核心）已经机器检查；
2. checked lower route（检查下界路线）已经对接到 no-fallback target upper route（无后备目标上界路线）；
3. `bigN` 的后续计算目标已经规范化到 rejection extractor witness（拒绝抽取器见证）；
4. 尚未输出具体自然数 `N`。

## 6. 与 γ 无理性路线的关系

本文不把当前结果包装成无条件的 γ 无理性证明。更准确的关系如下。

Sondow side（Sondow 侧）负责从 rationality assumption（有理性假设）产生短证书或短验证路线。Pudlak side（Pudlak 侧）负责提供 finite-consistency/reflection family（有限一致性/反射族）的下界。项目中的 checker/project-length route（检查器/项目长度路线）负责证明二者确实作用于同一个 measured function（被测函数）。

当前已经完成的是第三部分中最容易出逻辑漏洞的核心：同一个 `bigN`（大阈值）、同一个 `measured`（被测函数）、同一个 `upper.U`（上界函数）上的形式化对撞。尚未完成的是把所有外部数学输入都变成 parameter-free internal witnesses（无参数内部见证），并把最终 `bigN`（大阈值）求值成具体自然数。

因此，当前成果对完整 γ 路线的意义是：它把后续工作从“证明整个对撞是否能闭合”压缩为更具体的两个任务：

1. 构造或引用足够强的 external mathematical inputs（外部数学输入），并在 Lean 中对齐到当前 checked lower interface（检查下界接口）；
2. 展开 rejection extractor witness（拒绝抽取器见证）以得到 numeric N（数值阈值）。

## 7. 公理和输入边界

当前成果的信用边界应分成两类。

第一类是 Lean/Mathlib（Lean 库）常规逻辑依赖，例如 `propext`、`Classical.choice` 和 `Quot.sound`。这类依赖来自 Lean 的标准数学基础。

第二类是项目接口输入，包括 checked lower bound（检查下界）、scale data（尺度数据）、证明族、长度编码等。它们不是被隐藏的结论，而是在 theorem type（定理类型）中显式出现。对专家来说，关键审计问题不是“论文是否口头承诺这些输入存在”，而是：

1. 输入是否准确表达对应的 Sondow/Pudlak 数学内容；
2. 输入是否足够强，能够产生当前 theorem（定理）需要的 checked lower bound（检查下界）；
3. 输入是否能进一步构造成 parameter-free witness（无参数见证）；
4. rejection extractor witness（拒绝抽取器见证）是否能被有效求值。

## 8. 剩余工作

剩余工作不应再表述为“对撞核心是否成立”。更准确的清单如下。

第一，numeric N extraction（数值阈值抽取）。当前 `bigN` 已经被证明等于 rejection extractor witness（拒绝抽取器见证），但还没有把该见证展开成具体自然数。

第二，external-to-internal calibration（外部到内部校准）。Sondow 判据、Pudlak 型下界和 payload semantics（载荷语义）需要继续从文献陈述或项目接口推进到无参数、可审计的 Lean witnesses（Lean 见证）。

第三，publication-grade audit（发表级审计）。正式论文需要把当前 theorem names（定理名）、release tag（发布标签）、axiom audit（公理审计）和可复刻步骤整理为稳定附录，并避免使用内部施工标签作为数学结构。

这些剩余任务都很重，但它们与“当前是否已经形成同一 `bigN` 上的形式化对撞”不是同一个问题。后者已经由上述 Lean theorem（Lean 定理）和 checkpoint（检查点）支持。

## 9. 结论

当前项目已经取得一个明确的形式化成果：checked lower bound（检查下界）可以直接导出 no-fallback target-upper bigN certificate（无后备目标上界大阈值证书），并在同一个 `bigN` 上给出

```lean
upper.U bigN < measured bigN
measured bigN ≤ upper.U bigN
False
```

随后，`bigN` 又被证明等于 rejection extractor witness（拒绝抽取器见证）在阈值 0 处的值。这把符号对撞核心和未来的数值求值入口接到了一起。

因此，当前版本适合被公开表述为：一个可复刻、Lean 检查的 Sondow-Pudlak symbolic collision checkpoint（符号对撞检查点）。它不是 γ 无理性的最终无条件证明，但它已经把对撞核心从概念路线推进到机器检查的同对象矛盾证书。

## 参考文献

1. Jonathan Sondow, “Criteria for Irrationality of Euler's Constant,” *Proceedings of the American Mathematical Society*, 131(11), 3335-3344, 2003. arXiv:math/0209070.
2. Samuel R. Buss, “On Gödel's Theorems on Lengths of Proofs I: Number of Lines and Speedup for Arithmetics,” *Journal of Symbolic Logic*, 59(3), 737-756, 1994.
3. Pavel Pudlak, “On the lengths of proofs of finitistic consistency statements in first order theories,” in *Logic Colloquium 1984*.
4. Pavel Pudlak, “Improved bounds to the lengths of proofs of finitistic consistency statements,” in *Logic and Combinatorics*, 1987.
5. Jan Krajicek and Pavel Pudlak, “The Number of Proof Lines and the Size of Proofs in First-Order Logic,” *Archive for Mathematical Logic*, 1988.
6. The Lean 4 and Mathlib projects, project documentation and source libraries.
