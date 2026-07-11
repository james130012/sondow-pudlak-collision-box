# 单项式增长义务的纸面推理

日期：2026-07-09

## 0. 2026-07-09 当前指导结论

最新下界输入边界复审见：

```text
docs/pudlak_tail_gap_lower_bound_paper_proof_zh.md
integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

当前方向以这里为准：

1. Sondow upper side（Sondow 上界侧）已经闭合，不再是本文件的主要负债。
2. Pudlak lower/search-gap side（Pudlak 下界/搜索间隙侧）仍是核心负债。
3. clean axiom profile（干净公理画像）只能说明抽象接口干净；不能说明
   `tail_gap`（尾部间隙证书）已经从标准数学无条件推出。
4. `ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput` 明确含有
   `tail_gap` 字段，`computed N`（计算碰撞指标）公式明确读取
   `input.tail_gap.gap_for_polynomial_upper`。
5. `singletonMonomialLowerBound_submissionRoute` 的当前 conj-source carrier
   （合取来源载体）已经被 Lean 证明不能承担单项式超多项式增长义务。
6. 下一步目标不能再包装 `tail_gap`，而应关闭当前已经完全打开的
   no-accepted-code target（无接受证明码目标）：

```text
lengthCodeAt（校准长度函数）
size-filtered enumeration（按大小过滤的枚举）
noAcceptedBelowCodeBound（界内无接受证明码）
```

并由它们推出：

```text
checked measured minimum proof-code size gap
  （检查测量的最小证明码大小间隙）
  -> collision（碰撞）.
```

Lean 中已经把这个目标命名为：

```lean
SizeFilteredNoAcceptedCodeSearchClosureTarget
```

2026-07-09 的最新打开层又把这个目标压低了一步。新增 Lean 探针证明：

```lean
calibratedSingletonFiniteEnumeration_of_injective
canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
canonicalLengthGap_to_noAcceptedCodeSearchTarget_of_injective
canonicalLengthGap_and_rootExactness_to_actualProofLengthGap
no_canonicalLengthGap_and_rootExactness_currentRoot
```

含义是：

```text
如果 powerBoundRawCode（幂界公式码）是 injective（单射），
那么 concrete PA/Hilbert checker（具体 PA/Hilbert 检查器）
接受的 proof code（证明码）唯一，只能是 canonical code（规范码）n。

如果再给出 lengthCodeAt（校准长度函数）的 search-gap（搜索间隙），
Lean 可以直接构造 noAccepted search（无接受码搜索）。
```

所以 `rejection_search`（拒绝搜索）已经不是黑盒。它被打开成更根本的一句话：

```text
真实的 canonical proof-code length（规范证明码长度）
必须可搜索地超过任意 polynomial upper（多项式上界）。
```

但这也暴露出最终硬点：`lengthCodeAt` 不能任意挑一个超多项式函数。它必须等于
真实 proof-code semantics（证明码语义）给出的 proof length（证明长度）或
minimum proof-code size（最小证明码大小）。Lean 已经证明，如果再要求

```text
proof_length(PA, symbolSize, powerBoundRawCode n) = lengthCodeAt n
```

那么 `lengthCodeAt` 的 gap 会转成 `actualProofLengthMeasured`（实际证明长度测量）
的 gap；但当前 root `proof_length`（根证明长度）下这个目标不可能，因为
`actualProofLengthMeasured(n) = scale(n) + 12` 且 `scale` 是 polynomially bounded
（多项式有界）的。

因此当前真正的根任务不是构造一个任意 `lengthCodeAt`，而是替换/重构 root
proof-code semantics（根证明码语义），使它不再退化为公式码大小 `scale+12`，
并在这个真实语义上证明 no-small-code theorem（无小证明码定理）。

本轮还加入了一个 growth-only model probe（只测试增长层的模型探针）：

```lean
def superPolynomialCanonicalLength (n : Nat) : Nat :=
  (n + 1) ^ n

superPolynomialCanonicalLength_searchGap
superPolynomialCanonicalLength_to_noAcceptedCodeSearchTarget
superPolynomialCanonicalLength_to_checkedMeasuredSearchGap
```

Lean 已证明 `(n+1)^n` 可搜索地超过任意 polynomial upper（多项式上界）。给定
`U(n) <= c(n+1)^k`，取 `C >= c` 和

```text
w = max N (C + k + 1),
```

即可得到

```text
U(w) < (w+1)^w.
```

然后，由 `powerBoundRawCode` injective（幂界公式码单射）可直接构造
`SizeFilteredNoAcceptedCodeSearchClosureTarget`（按大小过滤的无接受码搜索闭合目标）
和 checked-measured search-gap（检查测量搜索间隙）。这些探针通过，并且 axiom
profile（公理画像）为：

```text
[propext, Classical.choice, Quot.sound]
```

这说明：

```text
如果真实 proof-code length（证明码长度）具有超多项式 search-gap，
后续 Lean 适配层已经能完全闭合。
```

但它还不是投稿下界证明，因为 `(n+1)^n` 目前只是模型 carrier（载体），没有从
PA/Hilbert verifier/checker（验证器/检查器）和 proof syntax（证明语法）推出。
下一步真正要做的是证明真实 minimum proof-code size（最小证明码大小）等于或
至少支配这样的超多项式 carrier，而不是把这个 carrier 当作自由选择。

当前通过的无 `proof_length`（证明长度）探针为：

```lean
concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow
calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap
sizeFilteredNoAcceptedCodeSearchTarget_to_checkedMeasuredSearchGap
```

探针输出显示这些定理的 axiom profile（公理画像）只有：

```text
[propext, Classical.choice, Quot.sound]
```

因此下一刀不是继续打包 `tail_gap`，也不是回到 root actual proof length
（根实际证明长度），而是直接证明 `noAcceptedBelowCodeBound`
（界内无接受证明码）。

2026-07-09 的最新 Lean 探针进一步证明了一个负结论：

```lean
actualProofLengthMeasured_currentRoot_eq_scale_add_twelve
actualProofLengthMeasured_currentRoot_polynomial
no_actualProofLengthSearchGapTarget_currentRoot
no_actualProofLengthPointwiseSearchGapTarget_currentRoot
```

含义是：在当前 root `proof_length`（根层证明长度）定义下，

```text
actualProofLengthMeasured(n) = scale(n) + 12.
```

而 `scale(n)` 已经是 polynomial bound（多项式有界）。所以当前 root
measurement（根层测量）不可能支撑 `tail_gap/search-gap`（尾部间隙/搜索间隙）。
这说明任务不是“把剩余参数继续下沉一下”即可完成；必须替换 Pudlak 侧的根测量
对象，让它变成具体 PA/Hilbert proof-code semantics（具体 PA/Hilbert 证明码语义）
诱导的 minimum proof-code size（最小证明码大小），然后在那里证明
no-small-code theorem（无小证明码定理）。

同一次探针还证明了 final residual/by-index route（最终残余/按指标路线）不能
作为替代闭合：

```lean
no_finalResidualInput_cutoffSelfCollision
no_finalByIndexResidualInput_cutoffSelfCollision
no_finalScaleInjectiveByIndexResidualInput_cutoffSelfCollision
no_finalStrictScaleByIndexResidualInput_cutoffSelfCollision
no_finalBoundedStrictScaleByIndexResidualInput_cutoffSelfCollision
```

反证取 `f(n)=n+1`。`cutoff_gt`（截断界严格超过）会推出
`witness < cutoff`，于是 `scaleNoCollisionBelow`（截断以下无尺度碰撞）可以对
`code = witness` 使用，得到 `scale(witness) != scale(witness)`。所以 numeric-code
cutoff（数值码截断）路线也不能承担所有多项式的下界目标。

下一步唯一可信方向是：

```text
concrete proof-code semantics（具体证明码语义）
size-filtered finite enumeration（按大小过滤的有限枚举）
real no-small-code theorem（真实无小证明码定理）
```

也就是说，枚举对象必须是 `size(code) < K` 的证明码，而不是 `numeric code < K`
的自然数码；同时必须证明在 Pudlak 目标公式处不存在小 size（小大小）的接受
证明码。

Lean 中已经把这个方向压缩成最小正向入口：

```lean
calibratedRejectionSearch_checkedMeasuredSearchGap
calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
calibratedRejectionSearch_checkedMeasured_gt_at_witness
calibratedRejectionSearch_acceptedCodeSize_gt_at_witness
calibratedRejectionSearch_toCanonicalSearchCore
SizeFilteredRejectionSearchClosureTarget
sizeFilteredRejectionSearchClosureTarget_to_checkedMeasuredSearchGap
```

其中 `calibratedRejectionSearch_checkedMeasuredSearchGap` 的 axiom profile（公理画像）
为：

```text
[propext, Classical.choice, Quot.sound]
```

这说明从

```text
lengthCodeAt（校准长度函数）
enumeration（按 size(code) < K 完备的有限枚举）
rejection_search（可执行拒绝搜索）
```

到 checked-measured search-gap（检查测量搜索间隙）的 Lean 接口已经是干净的。
剩余硬义务就是构造这个 `rejection_search`，也就是实际证明 Pudlak 目标公式处
没有小 proof-code size（证明码大小）的接受证明码。

本轮新增的关键澄清是：`rejection_search` 的数学内容已经被 Lean 展开为
accepted-code lower bound（被接受证明码下界）：

```text
对任意 polynomial upper U 和起点 N，
令 w = rejection_search.witness U hU N。
若 code 被 concrete PA/Hilbert checker 接受为
scale_data.powerBoundRawCode w 的证明码，
则 U(w) < lengthCodeAt(code)。
```

并且 Lean 证明了这个 accepted-code 版本与 checked measured minimum
proof-code size（检查测量的最小证明码长度）版本等价：

```text
(forall accepted code, U(n) < lengthCodeAt(code))
  <-> U(n) < month9_month10_checkedProofCodeMeasured(n).
```

所以当前不是在把 `tail_gap`（尾部间隙）改名成 `rejection_search`（拒绝搜索）。
正确理解是：

```text
tail_gap 被下沉为一个真实 no-small-code lower bound（无小证明码下界）
的可执行搜索版本。
```

但还不能说全消，因为 `rejection_search` 仍需从上游构造。它还包含 Boolean
rejection sweep（布尔拒绝扫描）和 finite enumeration rejection（有限枚举拒绝）
数据，强于单纯的存在性下界陈述。下一步若要“全消”，必须证明这个可执行搜索包
来自具体 PA/Hilbert checker（检查器）、decoder/extractor（解码/抽取器）和
proof-code size semantics（证明码大小语义），而不是把它作为输入给出。

本文件下面的旧单项式分析仍有价值，但应读作“为什么旧载体不可能成功”的
反证说明，不应再读作最终投稿主线。

本文档给出 `thresholdOfMonomial` 增长义务的纸面证明设计，并说明它在
当前 Lean 项目中应如何内化。结论是：该义务不能放在当前
`conj-source` 的 `minCheckedCodeSize` 上；正确的下界载体应改为
theorem-5 power-bound family 的实际 PA proof length，或者至少改为由
checker/extractor/exactness 给出的 finite-search witness gap。若要进一步消去
root `proof_length`，还必须把该载体继续下沉到具体 PA/Hilbert proof-code
exactness。

## 1. 当前目标义务

`singletonMonomialLowerBound_submissionRoute` 试图把所有外露的
`tail_gap`、`upper_provider`、`eventually_strict_length` 压缩成一个自然数
单项式下界：

```lean
thresholdOfMonomial : Nat -> Nat -> Nat

monomial_lt_lengthCodeAt_after :
  forall coeff degree n : Nat,
    thresholdOfMonomial coeff degree <= n ->
      coeff * (n + 1)^degree < minCheckedCodeSize n
```

在数学语言中，这要求某个自然数值函数 `L(n)` 最终支配每一个自然系数
单项式：

```text
forall C,d, exists N(C,d), forall n >= N(C,d),
  C (n+1)^d < L(n).
```

这是一个超多项式增长要求。它不是普通的接线条件。

## 2. 当前 conj-source 载体

当前路线把

```text
L(n)
```

具体取为

```lean
((left_family.conjIntro right_family).rightConjElim).minCheckedCodeSize n
```

这里 `left_family` 与 `right_family` 是两个显式 Hilbert 证明族。其连接证明
族先做 conjunction introduction，再做 right conjunction elimination。

因此该证明族在第 `n` 项已经有一个显式证明，其长度不超过

```text
left_length(n) + right_length(n) + 3.
```

最小 checked code size 不可能大于已有证明的长度，所以有点态上界：

```text
L(n) <= left_length(n) + right_length(n) + 3.
```

如果 `left_length` 与 `right_length` 都有多项式上界，那么右侧也有多项式
上界。因此 `L` 本身有多项式上界。

## 3. 关键纸面引理

**引理。** 设 `L : Nat -> Nat`。如果 `L` 有多项式上界，则不存在函数
`T : Nat -> Nat -> Nat` 满足

```text
forall C,d,n, T(C,d) <= n -> C(n+1)^d < L(n).
```

**证明。**

因为 `L` 有多项式上界，存在实数 `c >= 0` 和自然数 `k`，使得对所有 `n`，

```text
L(n) <= c (n+1)^k.
```

取自然数 `C` 满足 `C >= c`。这是 Archimedean 性质给出的。

现在把假设中的单项式下界用于这对参数 `(C,k)`，并取

```text
n = T(C,k).
```

于是得到

```text
C(n+1)^k < L(n).
```

另一方面，多项式上界给出

```text
L(n) <= c(n+1)^k.
```

又因为 `C >= c` 且 `(n+1)^k >= 0`，所以

```text
c(n+1)^k <= C(n+1)^k.
```

合并得到

```text
C(n+1)^k < L(n) <= c(n+1)^k <= C(n+1)^k,
```

即

```text
C(n+1)^k < C(n+1)^k,
```

矛盾。故这样的 `T` 不存在。

## 4. 当前路线的结论

将上面的引理应用到当前 `conj-source` 载体：

```text
L(n) =
  ((left_family.conjIntro right_family).rightConjElim).minCheckedCodeSize n
```

由于 Lean 已证明

```text
L(n) <= left_length(n) + right_length(n) + 3,
```

并且当前路线假设 `left_length` 和 `right_length` 有多项式上界，所以该
`L` 不可能最终支配任意单项式。

因此：

```text
thresholdOfMonomial / monomial_lt_lengthCodeAt_after
```

不能在这个 `minCheckedCodeSize` 上关闭。继续在这个对象上寻找
`thresholdOfMonomial` 会导致数学矛盾，而不是工程缺口。

## 5. 正确替代目标

碰撞证明真正需要的不是“同一个 `L(n)` 对所有足够大 `n` 超过所有多项式”，
而是以下 search-witness gap：

```text
forall polynomial upper U, forall lower cutoff N,
  exists w >= N, U(w) < M(w).
```

这里 `M(n)` 不应再取当前 root `actualProofLengthMeasured`（根实际证明长度测量）。
在当前 root coordinate（根坐标）下，Lean 已经证明它等于 `scale(n)+12`，
因而是 polynomial bound（多项式有界）。正确的替代对象应取 checked measured
minimum proof-code size（检查测量的最小证明码大小）：

```lean
month9_month10_checkedProofCodeMeasured
  scale_data
  (concretePAHilbertPowerBoundCalibratedCheckerSemantics
    scale_data lengthCodeAt).toProofCodeSemantics
  n
```

也就是在 concrete PA/Hilbert checker（具体 PA/Hilbert 检查器）接受的所有证明码
中，取 calibrated length（校准长度）的最小值。

如果 Sondow 侧在假设 `gamma` 有理时给出 eventual upper bound：

```text
forall n >= N0, M(n) <= U(n),
```

而 Pudlak/checker 侧给出 search-witness gap，那么对 `N0` 运行 gap 得到
`w >= N0` 且

```text
U(w) < M(w).
```

Sondow 上界又给出

```text
M(w) <= U(w).
```

两者合并即矛盾：

```text
U(w) < M(w) <= U(w).
```

这就是 collision 所需的核心逻辑。它比 full tail domination 弱，但足以
推出碰撞。

## 6. Lean 内化对应

纸面证明已经对应到以下 Lean 定理：

```lean
conjRightMinCheckedCodeSize_le_explicitLength
```

内化第 2 节的显式长度上界：

```text
L(n) <= left_length(n) + right_length(n) + 3.
```

```lean
conjRightMinCheckedCodeSize_polynomial_of_component_polynomial
```

内化“两个 component proof family 长度多项式有界，则当前 `L` 多项式有界”。

```lean
monomialDomination_impossible_of_polynomial_bound
```

内化第 3 节的抽象反证：任何已经多项式有界的自然数值函数，都不能最终
支配所有自然系数单项式。

```lean
singletonMonomialLowerBound_conjSource_obligation_impossible
```

把抽象反证专门应用到 `singletonMonomialLowerBound_submissionRoute` 当前使用
的 `rightConjElim.minCheckedCodeSize`。

```lean
calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
calibratedRejectionSearch_acceptedCodeSize_gt_at_witness
concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow
SizeFilteredNoAcceptedCodeSearchClosureTarget
sizeFilteredNoAcceptedCodeSearchTarget_to_checkedMeasuredSearchGap
```

内化第 5 节的替代方向：`rejection_search`（拒绝搜索）已经被打开成
no accepted proof code below a bound（界内无接受证明码），并且这个命题等价于
checked measured minimum proof-code size（检查测量的最小证明码大小）超过给定
多项式上界。

这一层的 axiom profile（公理画像）只有：

```text
[propext, Classical.choice, Quot.sound]
```

所以当前真正剩余的不是 `proof_length`（证明长度）包装，而是构造
`SizeFilteredNoAcceptedCodeSearchClosureTarget`（按大小过滤的无接受证明码搜索闭合目标）。

## 7. 不能声称的内容

不能声称已经在当前 `conj-source` 的 `minCheckedCodeSize` 上构造出了
`thresholdOfMonomial`。Lean 现在证明的是相反事实：在 component proof
length 多项式有界的条件下，这样的对象不存在。

可以声称的是：项目已经把原增长义务的错误载体识别出来，并给出形式化反证；
后续主线已经改为 concrete proof-code semantics（具体证明码语义）上的
size-filtered no-accepted-code lower bound（按大小过滤的无接受证明码下界）。

该方向的无条件完成，取决于能否真正构造：

```text
lengthCodeAt（校准长度函数）
enumeration（按大小过滤的有限枚举）
noAcceptedBelowCodeBound（界内无接受证明码证明）
```

这三件事必须来自 theorem-5 checker/verifier（第五定理检查器/验证器）和
Pudlak proof-complexity lower-bound argument（Pudlak 证明复杂性下界论证），不能
再作为 `tail_gap`（尾部间隙）或 `rejection_search`（拒绝搜索）黑盒输入。

## 8. 本轮新增的模型闭合与反证

本轮把 growth obligation（增长义务）拆成两个问题：

```text
1. 如果给定的 lengthCodeAt（长度函数）真的超多项式，后端能不能推出 gap？
2. 当前 root proof_length（根证明长度）能不能被证明等于这样的 lengthCodeAt？
```

第一个问题已经由 Lean 正面验证。定义：

```text
superPolynomialCanonicalLength(n) = (n+1)^n.
```

Lean 证明：

```lean
superPolynomialCanonicalLength_searchGap
superPolynomialCanonicalLength_to_noAcceptedCodeSearchTarget
superPolynomialCanonicalLength_to_checkedMeasuredSearchGap
```

纸面推导是：若 polynomial upper（多项式上界）满足

```text
U(n) <= c (n+1)^k,
```

取自然数 `C >= c`，并令

```text
w = max(N, C+k+1).
```

则

```text
U(w) <= c(w+1)^k <= C(w+1)^k
     < (w+1)(w+1)^k = (w+1)^(k+1) <= (w+1)^w.
```

因此 `(n+1)^n` 对任意多项式上界给出 search-gap（搜索间隙）。这一层的
axiom profile（公理画像）只有：

```text
[propext, Classical.choice, Quot.sound]
```

第二个问题由 Lean 给出负结论。新增定理：

```lean
rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_direct
no_superPolynomialCanonicalLength_rootExactness_currentRoot
no_superPolynomialCalibratedCheckerExactness_currentRoot
```

含义是：calibrated checker exactness（校准检查器精确性）会直接推出

```text
proof_length(PA, symbolSize, powerBoundRawCode n) = lengthCodeAt(n).
```

所以如果把 `lengthCodeAt` 取为 `(n+1)^n`，就要求当前 root `proof_length`
（根证明长度）等于超多项式载体。但当前 root coordinate（根坐标）下 Lean 已经证明：

```text
actualProofLengthMeasured(n) = scale(n) + 12,
```

而 `scale` 是 polynomial bound（多项式有界）。因此当前 root `proof_length`
不能承载 Pudlak lower bound（Pudlak 下界）。这不是工程接线问题，而是逻辑反证。

结论：

```text
增长层本身可以闭合；
checked-measured adapter（检查测量适配器）可以闭合；
旧 proof_length/exactness（证明长度/精确性）路线不能闭合；
剩余任务只能是证明真实 PA/Hilbert proof-code semantics（证明码语义）上的
no-small-proof theorem（无小证明定理），或者重构 root proof_length 为该真实语义。
```

## 9. 本轮新增：native checker 不能承载增长义务

本轮继续检查旧工作后，得到比 root `proof_length`（根证明长度）反证更底层的
结论：当前 concrete PA/Hilbert checker（具体 PA/Hilbert 检查器）的 native size
（原生大小）路线本身也不能证明增长义务。

原因是当前 proof object semantics（证明对象语义）给每个 `n` 一个 canonical
accepted proof code（规范接受证明码）：

```text
proof code n proves powerBoundRawCode(n),
and native size(n) = n.
```

Lean 形式化为：

```lean
nativePowerBoundCheckedMeasured_le_index
nativePowerBoundCheckedMeasured_polynomial
no_nativePowerBoundCheckedMeasuredSearchGap
no_nativeIdentityNoAcceptedCodeSearchTarget
```

其中核心不等式是：

```text
M(n) <= n.
```

所以当前 native checked measured object（原生检查测量对象）是 polynomially
bounded（多项式有界）的。它不可能 eventually dominate every polynomial
（最终支配任意多项式），也不可能产生 `ComputableSearchGapCertificate`
（可计算搜索间隙证书）。

这不是一个可以继续通过 adapter theorem（适配定理）解决的缺口。当前 checker
（检查器）把目标公式族做成了一步可接受对象：

```text
steps = [code],
conclusion = powerBoundRawCode(code).
```

因此，若目标是完全打开 Pudlak lower bound（Pudlak 下界），下一步必须重构
checker/proof-object semantics（检查器/证明对象语义），把它替换成真正的
PA/Hilbert proof-code semantics（证明码语义）。在旧 native checker（原生检查器）
上，增长义务不是暂时没证出，而是已经被短证明通道形式化反证。

## 10. 修正目标：canonical CnBox 的语义 PA 证明长度

本轮新增的正确替代对象不是另一个 calibrated lengthCodeAt（校准长度函数），
而是 bounded arithmetic sidecar（有界算术侧库）里的 canonical CnBox PA box
（规范 CnBox PA 盒子）。Lean 新增：

```lean
correctedCanonicalCnBoxPABox_length_eq_semanticFiniteConsistency
```

其内容是：

```text
canonicalCnBoxPABox.length(n)
  = semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n).
```

这一步很关键，因为它把增长义务放回真实 proof-object semantics
（证明对象语义）上：长度是 PA 证明对象达到 `finiteConsistencyFormula(n)`
（有限一致性公式）的 semantic minimum proof length（语义最小证明长度），而不是
旧 `code n` 一步接受的 native numeric size（原生数值大小）。

因此当前修正闭合目标是：

```lean
CorrectedCanonicalCnBoxLowerBoundClosureTarget
```

也就是存在：

```text
lower_source : BussPudlakTheorem5PALowerBoundSource
calibration : CanonicalRelabeledPudlakCalibration lower_source
```

Lean 已证明：

```lean
correctedCanonicalCnBoxLowerBoundClosureTarget_to_gap
correctedCanonicalCnBoxLowerBoundClosureTarget_to_eventualLowerBound
```

所以 corrected closure target（修正闭合目标）一旦给出，就能机械推出 canonical
CnBox proof-length gap（规范 CnBox 证明长度间隙）和 collision kernel（碰撞核）
需要的 `EventualLowerBound`（最终下界）。这些桥接本身的 axiom profile
（公理画像）只有：

```text
[propext, Classical.choice, Quot.sound]
```

本轮也证明：

```lean
no_correctedCanonicalExactConstructorCalibration
```

说明 exact constructor equality（精确构造子相等）路线不可行：
`externalPudlakCode`（外部 Pudlak 码）和 `partialConsistencyCode`（部分一致性码）
是不同 constructors（构造子）。所以真正路线必须是：

```text
SemanticFormulaRelabeling（语义公式重标定）
+ length_eq（长度相等）
+ Buss/Pudlak theorem-5 lower source（Buss/Pudlak 第五定理下界来源）。
```

这把增长义务重新定位为一个单一硬缺口：

```text
构造或内化 BussPudlakTheorem5PALowerBoundSource
并证明它与 canonical CnBox semantic PA length（规范 CnBox 语义 PA 长度）
通过 CanonicalRelabeledPudlakCalibration（规范重标定校准）相接。
```

换句话说，后续不能再修旧 native checker（原生检查器）。那条路已经反证。真正
闭合路线必须形式化或可靠导入 Buss/Pudlak/Friedman no-small-proof theorem
（无小证明定理）。

本轮还把 lower-source（下界来源）本身从抽象字段向 root literature theorem
（根侧文献定理）推进了一步。Lean 新增：

```lean
boundedPolynomialBound_to_rootPolynomialBound
boundedLowerSourceOfRootStrongRescaled
boundedLowerSourceFromRootLiterature
boundedLowerSourceFromRootLiterature_scale_eq
boundedLowerSourceFromRootLiterature_pa_length_eq
```

其中 `boundedLowerSourceFromRootLiterature`（从根侧文献构造的有界下界来源）把
EulerLimit 侧已有的：

```text
literaturePudlakTheorem5ExternalScaleData
literaturePudlakTheorem5ExternalRescaledLowerBound
```

读成 bounded sidecar（有界算术侧库）的：

```text
BussPudlakTheorem5PALowerBoundSource.
```

这一步没有证明文献 Pudlak theorem 5（Pudlak 第五定理）本身；它把已有文献输入
转换为 corrected CnBox route（修正 CnBox 路线）可消费的 lower-source interface
（下界来源接口）。探针显示它依赖：

```text
[literaturePudlakTheorem5ExternalRescaledLowerBound,
 literaturePudlakTheorem5ExternalScaleData,
 proof_length,
 propext,
 Classical.choice,
 Quot.sound]
```

因此当前真正剩余目标进一步缩成：

```lean
RootLiteratureCanonicalCnBoxCalibrationTarget
```

也就是存在：

```text
CanonicalRelabeledPudlakCalibration boundedLowerSourceFromRootLiterature.
```

Lean 已证明：

```lean
rootLiteratureCanonicalCalibration_to_correctedClosureTarget
rootLiteratureCanonicalCalibration_to_gap
```

所以从现在开始，增长义务的根问题不是“再找一个 gap certificate（间隙证书）”，而是
证明 root literature proof length（根侧文献证明长度）与 canonical CnBox semantic
PA proof length（规范 CnBox 语义 PA 证明长度）的 relabeling/length equality
（重标定/长度相等）。

## 11. 进一步打开后的 no-go：当前 CnBox 语义长度塌成 0

继续检查第 10 节的剩余目标后，Lean 证明了一个关键反向结论：

```lean
currentToySemanticBAProofLength_finiteConsistency_eq_zero
currentToyCanonicalCnBoxPABox_length_eq_zero
no_currentToyCanonicalCnBoxProofLengthGap
```

这说明当前 `finiteConsistencyFormula n`（有限一致性公式）在 bounded arithmetic
sidecar（有界算术侧库）里还只是 uninterpreted atom（未解释原子标签），而不是已经
展开成真实 PA formula（PA 公式）的有限一致性句子。当前 `PAAxiom`（PA 公理谓词）
没有推出该原子的公理或推理路径，所以不存在
`BAProofObject PAAxiom`（PA 证明对象）证明它：

```lean
no_currentToyPADerivation_finiteConsistencyFormula
no_currentToyPAProofObject_finiteConsistencyFormula
```

同时，当前 toy calculus（玩具演算）也证明：

```lean
no_currentToyPADerivation_contradictionFormula
currentToyPAFiniteConsistencyStatement_all
```

也就是说，`PAFiniteConsistencyStatement n`（PA 有限一致性命题）在现在的对象语言里是
平凡成立的：toy PA（玩具 PA）没有任何推导能推出 `falsum`（假）。这只说明 toy proof
predicate（玩具证明谓词）一致；它不是 Pudlak theorem 5（Pudlak 第五定理）里那个
真实 PA proof-length lower bound（真实 PA 证明长度下界）。

因此，在当前 toy PA calculus（玩具 PA 演算）里：

```text
semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n) = 0.
```

这不是 Pudlak lower bound（Pudlak 下界）的候选对象。一个恒等于 0 的长度函数不可能
eventually dominate every polynomial upper（最终支配任意多项式上界）。Lean 已经
形式化为：

```lean
no_rootLiteratureCanonicalCnBoxCalibrationTarget_currentToySemantics
```

所以现在的结论更清楚：

```text
旧 native checker（原生检查器）路线因短接受码失败；
修正 CnBox 路线因 finiteConsistencyFormula 仍是 toy atom（玩具原子）而不能闭合。
```

下一步不应再包装 `tail_gap`（尾部间隙）或 `length_eq`（长度相等），而必须补上对象级
PA semantics（PA 语义）：

```text
finiteConsistencyFormula 的真实 PA 公式展开
+ PA proof-code semantics（PA 证明码语义）
+ checker / enumeration / extractor / proof-length exactness
  （检查器 / 枚举 / 抽取器 / 证明长度精确性）
+ 与文献 Pudlak theorem 5（Pudlak 第五定理）的长度校准。
```

这才是下界盒子的根部。当前 Lean 探针已经排除了“现有 CnBox toy endpoint 可以直接
接入文献下界”的可能性。

## 12. 根证明长度的 no-go：文献下界与当前 proof_length 定义冲突

继续检查 EulerLimit root side（EulerLimit 根侧）后，增长义务又被向下推进一层。
当前 root `proof_length`（根证明长度）在 `ProofComplexityCore.lean` 中已经定义为
`rootFormulaCodeSize`（根公式码大小）诱导的最小码长，而不是 PA minimum proof
length（PA 最小证明长度）。

Lean 证明：

```lean
rootLiteratureRescaledPudlak_currentRootLength_eq_scale_add_twelve
```

即对文献 Pudlak theorem 5（Pudlak 第五定理）使用的 rescaled external Pudlak family
（重标定外部 Pudlak 族），当前 root 证明长度满足：

```text
proof_length(PA, symbolSize, target(n)) = scale(n) + 12.
```

而 `literaturePudlakTheorem5ExternalScaleData`（文献尺度数据）自带
`scale_polynomial_bound`（尺度多项式有界）。所以 Lean 又证明：

```lean
rootLiteratureRescaledPudlak_currentRootLength_polynomial
```

即该 measured family（测量族）本身 polynomially bounded（多项式有界）。

这与文献输入：

```lean
literaturePudlakTheorem5ExternalRescaledLowerBound
```

断言的 `StrongProofLengthLowerBound`（强证明长度下界）不相容。Lean 新增：

```lean
no_strongProofLengthLowerBound_of_currentMeasuredPolynomial
no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot
literaturePudlakTheorem5External_currentRoot_contradiction
```

其含义是：在当前 root `proof_length` 定义下，文献下界输入会与公式码大小定义直接推出
`False`。这不是数学定理失败，而是当前 formal target（形式化目标）选错：

```text
root proof_length（根证明长度）
  现在 = formula-code size（公式码大小）
  应该 = minimum PA proof-code length（最小 PA 证明码长度）。
```

因此，增长义务的真正下一步是重构 `EulerLimit/ProofComplexityCore.lean`：

```text
1. 引入真实 PA proof-code semantics（PA 证明码语义）；
2. 用 minProofCodeSize（最小证明码大小）定义 PA/symbolSize 的 proof_length；
3. 保留 Sondow sidecar（Sondow 侧旁路）只能作为局部校准，不可覆盖 PA theorem-5 族；
4. 再把 literature Pudlak theorem 5（文献 Pudlak 第五定理）接到这个真实 PA 长度对象上。
```

在这一步完成前，不能把任何 `literaturePudlakTheorem5External...` 作为当前
root `proof_length` 上的无条件干净下界来使用。

## 13. 对旧 rejection-search 工作的复查：硬缺口不是 tail_gap，而是最小证明码增长

重新审计旧 Month 11/12 路线后，结论是：许多文件已经把 `tail_gap`（尾部间隙）
从外层 theorem（定理）表面移开，但没有自动证明 Pudlak lower bound（Pudlak 下界）。
它们通常把证明义务换成：

```text
rejectionExtractor（拒绝抽取器）
proofLengthExactness（证明长度精确性）
canonical calibrated core（规范校准核心）
eventually_strict_length（最终严格长度下界）
```

这些名字中，真正不可绕开的数学内容是：

```text
checker.minProofCodeSizeAt(n)
最终超过任意 polynomial upper（多项式上界）。
```

如果这个最小接受证明码长度是 polynomially bounded（多项式有界），那么任何
rejectionExtractor 都不可能存在。Lean 已经新增了通用定理：

```lean
no_checkerRejectionExtractor_of_checkedMeasured_polynomial
no_checkerRejectionExtractor_of_minProofCodeSizeAt_polynomial
```

它们说明：

```text
checked measured gap（检查侧测量间隙）
rejectionExtractor（拒绝抽取器）
eventually beats every polynomial（最终超过任意多项式）
```

三者都要求同一个底层事实：最小接受证明码长度必须不是多项式有界。否则可取

```text
U(n) = measured(n) + 1
```

直接得到：

```text
measured(w) + 1 < measured(w),
```

矛盾。

这也解释了旧 native powerBound checker（原生 powerBound 检查器）为什么不能用。
项目已经有 Lean 定理：

```lean
concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
nativePowerBoundCheckedMeasured_le_index
nativePowerBoundCheckedMeasured_polynomial
no_nativePowerBoundCheckedMeasuredSearchGap
```

含义是：对每个 `n`，该 checker 接受 code `n` 来证明 `powerBoundRawCode n`，所以
最小接受码长度至多是 `n`，当然是多项式有界。这样的 checker 不可能支撑
Pudlak theorem 5（Pudlak 第五定理）要求的 super-polynomial growth（超多项式增长）。

因此，当前目标必须改写为根部目标：

```text
构造真实 PA proof-code semantics（PA 证明码语义）；
在这个语义中定义 theorem-5 formula family（第五定理公式族）；
证明其 minProofCodeSizeAt(n)（最小证明码大小）最终超过任意多项式；
再把 root proof_length（根证明长度）定义为这个最小证明码长度。
```

只有完成这四步，`rejectionExtractor` 才不再是黑盒；否则它只是 `tail_gap` 的改名或
下沉版本。

对 `SondowProjectMonth11Month12HardResidualElimination.lean`（第 11-12 月硬残留消除）
的复查也支持这个结论。该文件已经正确排除了错误方向：

```lean
checked_eq_scale_blocker_impossible
hard_residual_blockers_impossible
finalThreeCertificateEndpoint_exactScale_impossible
```

这些定理说明不能把 checked minimum proof-code size（检查侧最小证明码大小）强行等同于
polynomial scale（多项式尺度），否则会给多项式有界的 scale 构造 search gap
（搜索间隙），直接矛盾。但该文件的 positive route（正向路线）仍然保留：

```text
extractor（抽取器）
actual_transport（实际证明长度传输）
proof_length family exactness（证明长度族精确性）
```

所以它是一个很好的定位文件，但不是最终闭合文件。真正还要完成的是：

```text
1. 造出真实 PA checker/extractor（PA 检查器/抽取器），不是 native short-code checker；
2. 证明这个 extractor 来自真实 no-small-proof-code theorem（无小证明码定理）；
3. 证明 root proof_length（根证明长度）就是该真实 PA 最小证明码长度。
```

## 14. external PA/Hilbert 桥在当前 root identity 下会退化成线性长度

进一步检查 `ProjectionBridge.lean`（投影桥）里的旧接口后，发现还有一个看起来像闭合
校准的命名公设：

```lean
externalPAHilbertProofLength_eq_localChecked
```

它声称 project-level PA `proof_length`（项目级 PA 证明长度）等于某个 local checked
code proof length（本地已检查码证明长度）。但是在当前
`proof_length = rootFormulaCodeSize`（证明长度等于根公式码大小）的 root definition
（根定义）下，这个桥不会产生真实 PA 长度；它只会强迫本地 checked length
（已检查长度）等于公式码大小。

Lean 已新增：

```lean
externalPAHilbertProofLength_eq_localChecked_forces_rootFormulaCodeSize
```

其内容是：

```text
localCheckedCodeProofLength(code)
= rootFormulaCodeSize(PA, symbolSize, code).
```

并且对两个核心族具体化为：

```lean
externalPAHilbertProofLength_eq_localChecked_forces_partialConsistency_linear
externalPAHilbertProofLength_eq_localChecked_forces_reflectionGraft_linear
```

即：

```text
partialConsistencyCode(m)    的本地 checked 长度 = m + 11,
sondowReflectionGraftCode(m) 的本地 checked 长度 = m + 13.
```

这两个都是 linear（线性）函数，不可能承载 Pudlak theorem 5（Pudlak 第五定理）要求的
super-polynomial lower bound（超多项式下界）。

因此：

```text
externalPAHilbertProofLength_eq_localChecked
```

不是闭合根缺口的答案。它只是一个外部校准公设；而且只要 root `proof_length` 仍是公式码
大小，它会把所有本地 PA/Hilbert 证明码语义压回线性公式码大小。

下一步必须先改 root `proof_length` 的语义来源：

```text
错误路线：
  root proof_length = rootFormulaCodeSize
  + externalPAHilbertProofLength_eq_localChecked
  -> local checked length = linear formula-code size.

正确路线：
  root proof_length = minimum size accepted by real PA proof-code checker
  （真实 PA 证明码检查器接受的最小大小）
  + literature/theorem-5 lower bound calibrated to that checker.
```

这一步是根定义替换，不是新增 wrapper（包装器）。

## 15. 复查旧工作后的总诊断

这轮重新检查旧工作后，结论可以压缩成一句话：

```text
旧工作已经打开了 adapter layer（适配层），但没有完成 theorem-5
no-small-proof-code theorem（第五定理无小证明码定理）。
```

具体说，以下部分是真正已经被 Lean 证明并且可继续使用的：

```text
tail_gap（尾部间隙）可以被改写成 search gap（搜索间隙）；
search gap 可以由 rejection_search（拒绝搜索）给出；
rejection_search 可以打开成 noAcceptedBelowCodeBound（界内无接受码）；
若给定超多项式 canonical length（规范长度），size-filtered search
（按大小过滤的搜索）可以机械地产生 checked measured gap（检查测量间隙）。
```

这些是有效的工程和形式化成果。它们说明 collision kernel（碰撞核心）吃到一个真实下界
以后，后续链条能顺利推出矛盾。

但是，旧工作没有完成、也不能靠包装完成的是下面这个根命题：

```text
对真实 PA/Hilbert proof-code checker（PA/Hilbert 证明码检查器），
theorem-5 target family（第五定理目标公式族）的
minimum accepted proof-code size（最小接受证明码大小）
eventually beats every polynomial（最终超过任意多项式）。
```

Lean 已经把几个错误闭合方向排除了：

```lean
actualProofLengthMeasured_currentRoot_polynomial
no_actualProofLengthSearchGapTarget_currentRoot
no_checkerRejectionExtractor_of_minProofCodeSizeAt_polynomial
no_currentToyCanonicalCnBoxProofLengthGap
no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot
externalPAHilbertProofLength_eq_localChecked_forces_partialConsistency_linear
externalPAHilbertProofLength_eq_localChecked_forces_reflectionGraft_linear
```

这些定理的共同含义是：

```text
1. 当前 root proof_length（根证明长度）是 formula-code size（公式码大小），太小；
2. 当前 native checker（原生检查器）有短接受码，太小；
3. 当前 toy CnBox PA semantics（玩具 CnBox PA 语义）没有真实有限一致性公式证明码，
   长度反而塌成 0；
4. external PA/Hilbert bridge（外部 PA/Hilbert 桥）在当前 root 定义下只会推出线性长度；
5. rejectionExtractor（拒绝抽取器）只有在最小接受证明码长度已经超多项式时才可能存在。
```

因此，下一刀不能再是：

```text
tail_gap -> rejection_search -> exactness -> lengthCodeAt
```

这种继续换名字的路线。真正要做的是把根对象换成：

```text
real PA proof-code semantics（真实 PA 证明码语义）
  = proof code syntax（证明码语法）
  + checker relation（检查器关系）
  + size measure（大小测度）
  + target formula interpretation（目标公式解释）
  + theorem-5 no-small-code lower bound（第五定理无小码下界）
```

然后再让：

```text
root proof_length(PA, symbolSize, code)
```

定义为该 checker 接受 `code` 的最小证明码大小。只有这一步完成，Pudlak 侧下界才会从
paper-level theorem（纸面定理）变成项目内部 proof object（证明对象），而不是
`tail_gap`、`rejection_search` 或 `exactness` 的改名。

## 16. 本轮新增：当前 root 下 theorem-5 core 全部不可能

继续把旧工作向根部压缩后，Lean 现在证明了更强的结论：在当前
`proof_length = rootFormulaCodeSize`（证明长度等于根公式码大小）的定义下，不只是
`tail_gap`（尾部间隙）不能无条件关闭，连所有 theorem-5 lower-bound core
（第五定理下界核心）对象本身也不能存在。

新增探针：

```lean
no_internalPudlakTheorem5PowerBoundLowerBound_currentRoot
no_internalPudlakTheorem5LowerBoundCore_currentRoot
no_nonempty_internalPudlakTheorem5LowerBoundCore_currentRoot
no_internalPudlakTheorem5CheckedLowerBoundCore_currentRoot
no_internalPudlakTheorem5ProofCodeSemanticsCore_currentRoot
no_internalPudlakTheorem5ProofLengthCodeSemanticsCore_currentRoot
no_internalPudlakTheorem5NoSmallCodeSemanticsCore_currentRoot
no_internalPudlakTheorem5FiniteSearchNoSmallCore_currentRoot
no_internalPudlakTheorem5ComputableFiniteSearchNoSmallCore_currentRoot
```

证明逻辑很短：

```text
1. 当前 root 定义给出：
   proof_length(PA, symbolSize, powerBoundRawCode(n)) = scale(n) + 12.

2. scale(n) 已经在 scale_data（尺度数据）中带有 polynomial bound（多项式上界）。

3. 因此该 proof_length family（证明长度族）本身是 polynomially bounded
   （多项式有界）。

4. StrongProofLengthLowerBound（强证明长度下界）要求它 frequently beats every
   polynomial（频繁超过每个多项式）。

5. 取这个 family 自己作为 polynomial upper（多项式上界），立刻得到
   length(n) > length(n)，矛盾。
```

所以当前项目里的这些 core/checklist（核心/清单）不是“只差一点接线”的闭合对象。
它们在当前 root proof-length semantics（根证明长度语义）下是不可存在对象。

这把剩余义务进一步精确成：

```text
必须先替换 root proof_length 的语义来源。

旧根：
  proof_length = rootFormulaCodeSize

新根必须是：
  proof_length(PA, symbolSize, code)
    = min size of real PA/Hilbert proof code accepted for code
      （真实 PA/Hilbert 证明码被接受的最小大小）
```

替换根定义后，再去证明 theorem-5 no-small-proof-code theorem（第五定理无小证明码定理）。
如果不先换根，任何把 Pudlak theorem 5（Pudlak 第五定理）塞进现有 core 的尝试都会被
上述 no-go theorem（不可能定理）反杀。

## 17. PA/Hilbert concrete checker 也不能直接作为 root replacement

进一步检查 `SondowProjectMonth11PAHilbertCheckerSurface.lean`（第 11 月 PA/Hilbert
检查器表面）后，确认项目里确实已经有：

```text
PAHilbertProofObject（PA/Hilbert 证明对象）
PAHilbertChecker（PA/Hilbert 检查器）
PAHilbertProofObjectDecoder（证明对象解码器）
PAHilbertNoSmallProofCode（无小证明码）
```

但是当前 concrete power-bound checker（具体幂界检查器）不能作为新的 root proof-code
semantics（根证明码语义），因为它内置了短接受码：

```lean
concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
```

该定理给出：对每个 `n`，编号 `n` 的证明码已经被接受为
`powerBoundRawCode n` 的 PA/Hilbert 证明码。

本轮新增两个 PA/Hilbert 层 no-go probe（不可能探针）：

```lean
no_concretePAHilbertPowerBound_noSmallAccepted_at_succ
no_concretePAHilbertPowerBound_noSmallProofCodeForFormulaCode_at_succ
```

它们说明：

```text
对当前 concrete power-bound checker，
不可能证明在 bound = n + 1 以下没有接受证明码；
也不可能证明按 formula code（公式码）看的 no-small-proof-code statement
（无小证明码陈述）。
```

所以现有 checker 层的用途是 audit/prototype（审计/原型），不是最终 root replacement
（根替换）。真正可用的 root proof-code semantics 必须满足：

```text
1. proof code syntax（证明码语法）不是公式索引本身；
2. decoder（解码器）不能把每个 n 直接解成 powerBoundRawCode n 的短证明；
3. checker acceptance（检查器接受）必须对应真实 PA/Hilbert 推导；
4. theorem-5 no-small-proof-code theorem（第五定理无小证明码定理）
   必须对这个 checker 成立。
```

这一步把剩余任务从“接现有 PA/Hilbert checker”进一步收窄为：

```text
构造真实 PA/Hilbert proof-code semantics，
并替换当前短码 concrete checker。
```

## 18. 根替换目标已经命名：但当前 root 下它也不可能存在

为了避免“真实 root replacement（根替换）”停留在口头层面，本轮把目标直接对齐到项目中
最强的 Month 11-12 对象：

```lean
PAHilbertCheckerExactnessCore
```

这个 core（核心）已经包含：

```text
PAHilbertChecker（PA/Hilbert 检查器）
PAHilbertDerivabilitySemantics（PA/Hilbert 可导出语义）
ProofCodeSemantics（证明码语义）
PAHilbertProofCodeSemanticsBridge（PA/Hilbert 证明码语义桥）
PAHilbertSmallCodeEnumeration（小证明码枚举）
ComputableFiniteSearchExclusion（可计算有限搜索排除）
InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
（内部 Pudlak 第五定理可计算有限搜索无小码核心）
```

因此新增命名目标：

```lean
RealPAHilbertRootReplacementTarget
```

定义为：

```text
Nonempty PAHilbertCheckerExactnessCore
```

这不是新增数学包装，而是把最终要构造的真实根对象锁定到现有最强接口。

Lean 同时证明：

```lean
no_paHilbertCheckerExactnessCore_currentRoot
no_realPAHilbertRootReplacementTarget_currentRoot
```

含义是：

```text
在当前 proof_length = rootFormulaCodeSize（证明长度等于根公式码大小）下，
PAHilbertCheckerExactnessCore 不可能存在；
因此 RealPAHilbertRootReplacementTarget 也不可能存在。
```

这一步把工程顺序固定下来：

```text
错误顺序：
  先构造 PAHilbertCheckerExactnessCore，再接当前 root proof_length。

正确顺序：
  1. 先替换 root proof_length 的定义；
  2. 让 root proof_length 由真实 PA/Hilbert proof-code semantics 诱导；
  3. 再构造 PAHilbertCheckerExactnessCore；
  4. 再由该 core 生成 theorem-5 computable finite-search no-small-code core。
```

如果不先做第 1 步，`PAHilbertCheckerExactnessCore` 会投影到已经被 Lean 反证的
`InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore`（内部第五定理可计算有限搜索
无小码核心），从而直接矛盾。

## 19. 本轮复核后的最小增长义务

本轮把 previous lower-bound work（此前下界工作）重新拆开检查后，得到更精确的结论。
过去的工作已经打开了很多 adapter layer（适配器层），但真正的增长义务仍然不能靠这些
adapter layer（适配器层）解决。

Lean 新增：

```lean
ProofLengthFreeLowerGapClosureTarget
proofLengthFreeLowerGapClosureTarget_to_checkedMeasuredSearchGap
```

这说明：

```text
如果已经有 proof-code semantics（证明码语义）、
small-code search（小码搜索）、
computable finite-search exclusion（可计算有限搜索排除），
那么 checked measured search gap（检查测量搜索间隙）会自动出来。
```

所以增长义务不是：

```text
从 tail_gap（尾部间隙）造 gap（间隙）；
从 rejection_search（拒绝搜索）造 gap（间隙）；
从 adapter theorem（适配器定理）造 gap（间隙）。
```

这些已经能由 Lean 机械完成。

真正剩余义务是：

```text
证明真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）上，
theorem-5 family（第五定理公式族）的最小接受证明码长度
eventually beats every polynomial（最终超过任意多项式）。
```

形式上，就是要构造：

```text
ProofCodeSemantics（证明码语义）
SmallCodeSearch（小码搜索）
ComputableFiniteSearchExclusion（可计算有限搜索排除）
RootExactness（根精确性）
```

其中前三项给出 proof-length-free checked gap（无根证明长度检查间隙）；最后一项把它接回
project root proof_length（项目根证明长度）。

## 20. 旧路线为什么必须停止

Lean 现在有一个合成台账：

```lean
currentLowerBoundRouteObstructionLedger
```

它同时记录：

```text
current root actualProofLengthMeasured（当前根实际证明长度测量）是多项式有界；
native concrete checker（原生具体检查器）有短 accepted code（接受码）；
current toy CnBox semantics（当前玩具 CnBox 语义）长度为 0，因此没有
EventualLowerBound（最终下界）。
```

这三条把旧路线全部截断：

```text
不能在当前 root proof_length（根证明长度）上证明 Pudlak growth（Pudlak 增长）；
不能把当前 concrete power-bound checker（具体幂界检查器）当真实 PA proof checker
（PA 证明检查器）；
不能把 current toy CnBox semantics（当前玩具 CnBox 语义）当真实 finite-consistency
proof-length model（有限一致性证明长度模型）。
```

因此，下一步只能是根定义替换：

```text
把 root proof_length（根证明长度）从 formula-code size（公式码大小）
替换为真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）诱导的
minimum accepted proof-code size（最小接受证明码大小）。
```

本轮新增的反证：

```lean
no_proofLengthFreeSourceRootExactness_currentRoot
```

说明如果不替换当前 root proof_length（根证明长度），即使已经有 proof-length-free source
（无根证明长度源），也不可能把它 root-exact（根精确）地接回项目实际证明长度。

本轮进一步新增：

```lean
no_currentToyCanonicalCnBoxEventualLowerBound
no_canonicalRelabeledPudlakCalibration_currentToySemantics
no_correctedCanonicalCnBoxLowerBoundClosureTarget_currentToySemantics
```

这说明 canonical CnBox route（规范 CnBox 路线）在当前 toy BAProofObject PAAxiom
（玩具 PA 证明对象）语义下也被彻底排除：

```text
canonicalCnBoxPABox.length(n) = 0
```

所以它不可能最终超过任意 polynomial bound（多项式上界）。因此，增长义务不能再表述为
“补一个 canonical calibration（规范校准）”；必须表述为：

```text
替换 toy BA proof object semantics（玩具有界算术证明对象语义），
给出真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义），
并在该语义上证明 theorem-5 lower bound（第五定理下界）。
```

## 21. root-closed theorem-5 目标：增长义务的最终精确形状

本轮新增 Lean 目标：

```lean
RootClosedTheorem5LowerBoundWitness
RootClosedTheorem5LowerBoundTarget
```

它把增长义务压缩成两个不可再隐藏的字段：

```text
PAHilbertProofLengthFreeLowerGapSource
（PA/Hilbert 无根证明长度下界源）

ProofLengthFreeSourceRootExactness
（无根源和项目根 proof_length 的精确相等）
```

Lean 已证明：

```lean
rootClosedTheorem5LowerBoundTarget_to_actualProofLengthSearchGapTarget
rootClosedTheorem5LowerBoundTarget_to_actualProofLengthPointwiseSearchGapTarget
```

因此，只要 root-closed target（根闭合目标）成立，就能推出 actual proof-length
search gap（实际证明长度搜索间隙）以及逐点 witness（见证）。这说明 adapter layer
（适配层）已经足够；缺口不在 `tail_gap`（尾部间隙）或 `rejection_search`
（拒绝搜索）的格式上。

Lean 同时证明：

```lean
no_rootClosedTheorem5LowerBoundTarget_currentRoot
```

这条反证的意义是：

```text
当前 root proof_length（根证明长度）等于 formula-code size（公式码大小），
所以在 theorem-5 family（第5定理公式族）上是 polynomially bounded
（多项式有界）的；
多项式有界的测量不可能 eventually beat every polynomial（最终超过任意多项式）；
因此当前根定义不可能闭合 Pudlak lower bound（Pudlak 下界）。
```

所以后续增长证明的真实目标不是再构造一个包装，而是：

```text
构造真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）；
证明 finite small-code search（有限小码搜索）是完整的；
证明 computable finite-search exclusion（可计算有限搜索排除）；
把 project root proof_length（项目根证明长度）精确校准为该真实语义的
minimum accepted proof-code size（最小接受证明码大小）。
```

这就是现在的“完全打开”状态：所有旧接口层已经被 Lean 压扁成一个根部增长命题。
如果不替换当前 root proof_length（根证明长度），Lean 已经证明该命题不可能成立。

## 22. 旧 final exact input 不是闭合证明

继续复查旧 `ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput`
（最终精确检查器核心输入）后，Lean 新增：

```lean
finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundWitness
finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundTarget
no_finalExactCheckerCoreInput_currentRoot
```

结论是：

```text
旧 final exact input（最终精确输入）如果存在，
就直接给出 RootClosedTheorem5LowerBoundTarget（根闭合第5定理目标）。
```

原因是它已经把增长义务放入字段：

```text
proof_length_gap
（root proof_length 已经有搜索间隙）

proof_length_eq_lengthCodeAt
（root proof_length 等于校准长度）
```

所以它不是从 checker（检查器）和 enumeration（枚举）中推出下界，而是把下界作为输入
带进来。当前 root proof_length（根证明长度）仍是 formula-code size（公式码大小），
因此 Lean 证明：

```text
Nonempty ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput -> False
```

这对增长义务的意义是：

```text
不能把 FinalExactCheckerCoreInput（最终精确检查器核心输入）
当作已经完成的 theorem-5 lower bound（第5定理下界）；
它只是 root-closed target（根闭合目标）的旧包装。
```

后续真正要构造的是没有预置 `proof_length_gap`（证明长度间隙）字段的对象：

```text
真实 PA/Hilbert proof-code semantics（证明码语义）
finite small-code search completeness（有限小码搜索完备性）
computable finite-search exclusion（可计算有限搜索排除）
root proof_length exactness（根证明长度精确性）
```

其中第三项必须是 theorem-5 lower-bound proof（第5定理下界证明）本身，而不是字段输入。

## 23. gap-free theorem-5 closure target

本轮进一步新增：

```lean
GapFreeTheorem5ClosureTarget
computableFiniteSearchNoSmallCore_toRootClosedTheorem5LowerBoundWitness
gapFreeTheorem5ClosureTarget_to_rootClosedTheorem5LowerBoundTarget
no_gapFreeTheorem5ClosureTarget_currentRoot
```

`GapFreeTheorem5ClosureTarget`（无 gap 字段第5定理闭合目标）的定义是：

```text
Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
```

这个目标比旧 `FinalExactCheckerCoreInput`（最终精确检查器核心输入）更正确，因为它不把
`proof_length_gap`（证明长度间隙）作为字段。它要求的是：

```text
proof_length_model（证明长度模型）
small_code_search（小码搜索）
computable_search_exclusion（可计算搜索排除）
calibration（校准）
```

其中真正的增长证明义务集中在：

```text
computable_search_exclusion
（可计算有限搜索排除）
```

也就是：

```text
对任意 polynomial bound（多项式上界）f 和任意起点 N，
构造 witness n >= N（见证 n 不小于 N）和 cutoff K（截断 K），
并证明所有 size < K（大小小于 K）的候选证明码都不能检查通过
powerBoundRawCode n（幂界原始公式码 n）。
```

Lean 已证明：

```text
GapFreeTheorem5ClosureTarget
  -> RootClosedTheorem5LowerBoundTarget
```

并且当前 root proof_length（根证明长度）下：

```text
GapFreeTheorem5ClosureTarget -> False
```

所以现在的证明路线已经很窄：

```text
不能再使用 proof_length_gap（证明长度间隙）字段；
不能使用当前 formula-code size root（公式码大小根定义）；
必须构造真实 PA/Hilbert proof-code semantics（证明码语义）上的
computable finite-search exclusion（可计算有限搜索排除）。
```

## 24. 把 computable_search_exclusion 打开成 NoAcceptedBelowCutoff

本轮对旧工作继续向下复查，结论是：

```text
computable_search_exclusion（可计算搜索排除）
仍然不是最底层数学命题。
```

它里面的 `rejects_candidates`（拒绝候选）依赖候选列表。候选列表的旧接口
`InternalPudlakTheorem5SmallCodeSearch`（第5定理小码搜索）只保证：

```text
accepted code（被接受码）且 size < K
  -> 出现在 candidates(n,K) 里。
```

这叫 completeness（完备性）。

但它不保证：

```text
出现在 candidates(n,K) 里
  -> size < K。
```

这叫 size-filter / soundness（尺寸过滤/健全性）。

所以，真正的增长证明义务应当写成更直接的形式：

```text
对任意 polynomial bound（多项式上界）f 和起点 N，
构造 n >= N 和 K > f(n)，
并证明所有 size < K 的 proof code（证明码）
都不会被 checker（检查器）接受为 powerBoundRawCode(n) 的证明。
```

本轮新增 Lean 对象：

```lean
ComputableNoAcceptedBelowCutoff
```

以及直接推导：

```lean
ComputableNoAcceptedBelowCutoff.noSmallAtWitness
ComputableNoAcceptedBelowCutoff.minProofCodeSize_gt_at_witness
ComputableNoAcceptedBelowCutoff.toCheckedMeasuredSearchGap
```

这说明：

```text
NoAcceptedBelowCutoff（截断界以下无接受码）
  -> 任意 accepted proof code 的 size 大于 f(n)
  -> minProofCodeSize（最小证明码尺寸）大于 f(n)
  -> checked measured gap（检查器测量间隙）
```

这一段的 axiom profile（公理剖面）为：

```text
[propext, Classical.choice, Quot.sound]
```

不含 `proof_length`（证明长度），也不含 `tail_gap`（尾部间隙）或 `proof_length_gap`（证明长度间隙）。

旧对象也被打开：

```lean
computableFiniteSearchExclusion_toNoAcceptedBelowCutoff
```

这说明旧的 `computable_search_exclusion` 一定蕴含新的直接无小码目标。

反向重建旧对象需要：

```lean
SizeFilteredSmallCodeSearch
noAcceptedBelowCutoff_toComputableFiniteSearchExclusion
```

也就是候选列表必须确实只列出 cutoff 以下的小码。

本轮还新增：

```lean
OpenedGapFreeTheorem5ClosureCore
OpenedGapFreeTheorem5ClosureTarget
```

它把 gap-free theorem-5 closure（无 gap 字段第5定理闭合）写成：

```text
proof_length_model（证明长度模型）
sizeFilteredSearch（尺寸过滤搜索）
noAcceptedBelow（截断界以下无接受码）
calibration（校准）
```

并证明：

```text
OpenedGapFreeTheorem5ClosureTarget
  -> GapFreeTheorem5ClosureTarget
  -> RootClosedTheorem5LowerBoundTarget
```

当前 root proof_length（根证明长度）下仍有：

```lean
no_openedGapFreeTheorem5ClosureTarget_currentRoot
```

含义是：

```text
当前 formula-code size root（公式码大小根定义）不可能承载这个下界。
```

复查旧路线还确认了一个硬障碍：当前 concrete power-bound checker（具体幂界检查器）
已经有短 accepted code（被接受码）：

```lean
concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
```

所以 Lean 已证明：

```lean
no_concretePAHilbertPowerBound_noSmallAccepted_at_succ
nativePowerBoundCheckedMeasured_le_index
no_nativePowerBoundCheckedMeasuredSearchGap
```

这说明不能靠当前 toy / fallback checker（玩具/回退检查器）证明 theorem-5 lower bound。

当前最短剩余目标是：

```text
为真实 PA/Hilbert proof-code semantics（证明码语义）证明
ComputableNoAcceptedBelowCutoff（截断界以下无接受码）；
然后证明 root proof_length exactness（根证明长度精确性）。
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 最终当前指导结论：缺口的根和突破口

当前要证明的不是 `tail_gap`（尾部间隙），也不是 `rejection_search`（拒绝搜索），而是：

```lean
ShortestCheckedMinProofCodeGrowthObligation
```

它等价于：

```lean
CheckedMinProofCodeStrongLowerBound
```

并且 Lean 已证明它等价于：

```lean
InternalPudlakTheorem5NoSmallProofCodes
```

所以真正目标是：

```text
在真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）中证明：
minProofCodeSize(powerBoundRawCode n)
最终超过任意 polynomial bound（多项式上界）。
```

已经完成的形式化突破：

```text
tail_gap
-> NoAcceptedBelowCutoff（截断界以下无接受码）
-> checked minProofCodeSize strong lower bound（检查后最小证明码强下界）
<-> NoSmallProofCodes（无小证明码）
```

卡点：

```text
1. 当前 native power-bound checker（原生幂界检查器）有短接受码：
   minProofCodeSize(powerBoundRawCode n) <= n。
   Lean 已证明：
   no_nativePowerBoundShortestCheckedMinProofCodeGrowthObligation。

2. 当前 root proof_length（根证明长度）等于 formula-code size（公式码大小），
   是多项式有界的，不能承载 theorem-5 下界。

3. bounded_arithmetic 的 BussPudlakTheorem5PALowerBoundSource
   仍是下界接口，不是内部证明。

4. literaturePudlakTheorem5ExternalScaleData /
   literaturePudlakTheorem5ExternalRescaledLowerBound
   仍是外部公设路线，不是 Lean 内部闭合。
```

突破口：

```text
必须构造真实 PA/Hilbert proof-code semantics（证明码语义），
并在它上面证明 InternalPudlakTheorem5NoSmallProofCodes。
```

下一步的最小正确方向：

```text
真实 proof-code syntax（证明码语法）
+ verified PA/Hilbert checker（已验证 PA/Hilbert 检查器）
+ completion / soundness（完备性 / 可靠性）
+ Pudlak theorem-5 no-small-proof-code proof（第5定理无小证明码证明）
-> ShortestCheckedMinProofCodeGrowthObligation
```

不能再做的事：

```text
不能把下界义务继续改名或包装；
不能把当前 native checker 当真实 PA checker；
不能把当前 root proof_length 当真实证明长度；
不能把外部 Pudlak 公设当内部证明完成。
```

## 当前证明指导：要证明什么，卡在哪里，怎么突破

这一节是当前下界工作的作战图。以后推进时优先按本节判断方向，避免再在
`tail_gap`（尾部间隙）、`rejection_search`（拒绝搜索）和 root `proof_length`
（根证明长度）之间循环展开。

### 1. 真正要证明什么

当前最短目标已经在 Lean 中命名为：

```lean
ShortestCheckedMinProofCodeGrowthObligation
```

它不是新公设，只是下面命题的别名：

```lean
CheckedMinProofCodeStrongLowerBound
```

数学内容是：

```text
给定真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）sem，
对任意 polynomial bound（多项式上界）U，
对任意起点 N，
存在 n >= N，使得

sem.minProofCodeSize(powerBoundRawCode n) > U(n).
```

也就是说，必须证明 theorem-5 family（第5定理公式族）的最小接受证明码尺寸
最终超过任意多项式。这就是下界盒子的根，不是 `tail_gap` 的另一个名字。

Lean 已经证明：

```lean
shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
```

即：

```text
ShortestCheckedMinProofCodeGrowthObligation
  <-> InternalPudlakTheorem5NoSmallProofCodes
```

所以目标也可以等价写成：

```text
证明 theorem-5 的 NoSmallProofCodes（无小证明码）标准形式。
```

### 2. 已经打开了什么

当前 Lean 已经完成的不是下界定理本身，而是“把缺口定位到唯一根部”：

```text
tail_gap（尾部间隙）
  -> NoAcceptedBelowCutoff（截断界以下无接受码）
  -> CheckedMinProofCodeStrongLowerBound（检查后最小证明码强下界）
  <-> InternalPudlakTheorem5NoSmallProofCodes（第5定理无小证明码）
```

相关 Lean 名称：

```lean
checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes
shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
```

这条链的关键 axiom profile（公理剖面）只有：

```text
[propext, Classical.choice, Quot.sound]
```

没有：

```text
proof_length（根证明长度）
tail_gap（尾部间隙）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（加强部分一致性载荷）
```

### 3. 卡在哪里

卡点一：当前 native power-bound checker（原生幂界检查器）太弱，不能作为真实
PA/Hilbert proof-code semantics（证明码语义）。

Lean 已证明：

```lean
no_nativePowerBoundShortestCheckedMinProofCodeGrowthObligation
```

原因很具体：当前 checker 对每个 `n` 已经接受一个大小至多为 `n` 的证明码，
所以：

```text
minProofCodeSize(powerBoundRawCode n) <= n
```

因此它不可能最终超过多项式 `U(n) = n`。这不是小 bug（错误），而是该 checker
的语义不是真实 PA 证明码语义。

卡点二：当前 root `proof_length`（根证明长度）仍等于 formula-code size（公式码大小），
它也是多项式有界的。所有把下界接回当前 root `proof_length` 的路线都会被 Lean 的 no-go
（不可能性定理）打掉。

卡点三：bounded_arithmetic（有界算术）路线里的

```lean
BussPudlakTheorem5PALowerBoundSource
```

现在仍是 lower-bound interface（下界接口）。它提供的是“如果已有第5定理下界源，
就能接到当前最短目标”，但它不是第5定理的内部证明。

卡点四：外部文献路线中的

```lean
literaturePudlakTheorem5ExternalScaleData
literaturePudlakTheorem5ExternalRescaledLowerBound
```

仍是 `axiom`（公设）。这条线只能说明“引用外部 Pudlak 第5定理时如何接入”，
不能算 Lean 内部无条件闭合。

### 4. 不能走的路

不能再做以下事情：

```text
把 tail_gap 改名为 rejection_search；
把 rejection_search 改名为 computable_search_exclusion；
把 proof_length_gap 放进输入结构；
把当前 native checker 当真实 PA checker；
把当前 root proof_length 当真实最小证明码长度；
把外部文献公设当成内部证明完成。
```

这些都会保留信用负债，因为它们没有证明 `NoSmallProofCodes`（无小证明码）。

### 5. 应该怎么突破

突破必须集中在一个点：

```text
构造真实 PA/Hilbert proof-code semantics（证明码语义），
并在该语义上证明 InternalPudlakTheorem5NoSmallProofCodes。
```

具体分四步：

```text
第一步：定义真实 proof code syntax（证明码语法）。
  证明码必须编码 PA/Hilbert proof（PA/Hilbert 证明），不能像当前 native checker 那样
  直接把 index n 当成 powerBoundRawCode n 的接受证明码。

第二步：定义 verified checker（已验证检查器）。
  checker 必须逐步检查 Hilbert axiom（Hilbert 公理）、modus ponens（分离规则）、
  substitution / instantiation（代换/实例化）和目标公式编码。

第三步：证明 completion（完备性）与 sound rejection（可靠拒绝）。
  completion（完备性）保证如果目标公式确实有证明，则某个证明码会被接受；
  sound rejection（可靠拒绝）保证有限搜索拒绝的小码确实不是证明。

第四步：形式化 Pudlak theorem-5 no-small-proof-code argument
  （Pudlak 第5定理无小证明码论证）。
  这一步才是核心数学下界：证明若存在最终多项式大小的 PA 证明族，
  就会违反第5定理所依赖的有界算术/有限一致性下界。
```

### 6. 下一步最小可执行任务

下一次 Lean 推进不要先改论文，也不要继续扩展 wrapper（包装器）。应先在 Lean 中建立
一个新的真实语义目标文件或区域，最小目标是：

```lean
structure RealPAHilbertProofCodeSemanticsTarget where
  sem :
    ProofCodeSemantics
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  no_native_short_code :
    ¬ ShortestCheckedMinProofCodeGrowthObligation scale_data
        (concretePAHilbertPowerBoundCheckerSemantics scale_data).toProofCodeSemantics
  target :
    ShortestCheckedMinProofCodeGrowthObligation scale_data sem
```

但注意：这个 `target` 字段不能作为最终公设留下。它只是临时工作靶。真正要把它消掉，
必须继续把 `target` 展开成：

```text
proof-code syntax（证明码语法）
+ checker correctness（检查器正确性）
+ Pudlak theorem-5 lower-bound proof（第5定理下界证明）
```

因此，当前最清醒的判断是：

```text
形式化路线已经有根本性定位突破；
下界定理本身尚未闭合；
唯一可接受的突破口是内部证明 NoSmallProofCodes，
而不是再下沉或改名已有输入。
```

## 最新工作基准：最短增长义务已经固定

本轮复查旧的 lower-bound（下界）工作后，Lean 中已经把任务压缩到一个更短、
更干净的 root-free（不依赖根证明长度）目标：

```lean
ShortestCheckedMinProofCodeGrowthObligation
```

它只是以下命题的命名别名，不是新公设：

```lean
CheckedMinProofCodeStrongLowerBound
```

其数学含义是：

```text
对任意 polynomial bound（多项式上界）f，
对任意起点 N，
存在 n >= N，
使得真实 checker（检查器）语义中的

minProofCodeSize(powerBoundRawCode n)

严格大于 f(n)。
```

这就是当前最短增长义务：

```text
checked minProofCodeSize strong lower bound
（检查后最小证明码尺寸强下界）
```

Lean 已证明它和 theorem-5（第5定理）内部标准形式等价：

```lean
shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
```

等价右边是：

```lean
InternalPudlakTheorem5NoSmallProofCodes
```

也就是：任何 polynomial bound（多项式界）以下都不能最终覆盖 accepted proof code
（被接受证明码）。这说明现在不是在换名字，而是在把 `tail_gap`（尾部间隙）
真正下沉到 proof-code semantics（证明码语义）的最小证明码增长命题。

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

关键 axiom profile（公理剖面）：

```text
shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
depends on axioms: [propext, Classical.choice, Quot.sound]
```

这里没有：

```text
proof_length（根证明长度）
tail_gap（尾部间隙）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（加强部分一致性载荷）
```

所以本轮的根本性突破是：

```text
下界黑盒的最短形式已经被 Lean 固定为
checked minProofCodeSize 强下界，
且它与 theorem-5 NoSmallProofCodes 标准形式等价。
```

但这还不是无条件完成。仍未完成的硬数学证明是：

```text
在真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）上，
证明 InternalPudlakTheorem5NoSmallProofCodes
或等价地证明 ShortestCheckedMinProofCodeGrowthObligation。
```

下一步不能再沿 `tail_gap -> rejection_search -> proof_length` 展开，而应直接攻击：

```text
real PA/Hilbert proof-code syntax（真实 PA/Hilbert 证明码语法）
+ verifier correctness（验证器正确性）
+ small-code enumeration（小证明码枚举）
+ no-small-proof-code lower theorem（无小证明码下界定理）
-> ShortestCheckedMinProofCodeGrowthObligation
```

## 本轮修正：最终增长义务必须是完备的强下界

上一轮的正向目标：

```lean
BAProofObjectStrongSizeLowerBound
```

表达的是：

```text
对任意多项式上界 U 和起点 N，
存在 n >= N，
使所有证明 target(n) 的证明对象都大于 U(n)。
```

但单独使用它有一个逻辑漏洞：如果 `target(n)` 没有任何证明对象，那么“所有证明对象都大于
U(n)”会真空成立。因此它不能单独作为最终下界闭合目标。

本轮将最终目标升级为：

```lean
BACompleteProofObjectStrongSizeLowerBound
```

它包含两个字段：

```text
complete:
  BAProofObjectCompleteness Ax target

strong_lower:
  BAProofObjectStrongSizeLowerBound Ax target
```

也就是：

```text
每个 target(n) 都确实有证明对象；
但对于任意多项式 U，总能找到足够晚的 n，
使每一个证明 target(n) 的证明对象都大于 U(n)。
```

这才是不真空的 Pudlak 侧增长义务。

Lean 已证明：

```lean
BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_option
BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_no_eventual
BACompleteProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
BACompleteProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
BACompleteProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
```

同时 Lean 已证明当前 toy finite-consistency target（玩具有限一致性目标）不能实例化它：

```lean
no_currentToyBACompleteProofObjectStrongSizeLowerBound_finiteConsistency
```

原因是当前 toy PA proof-object semantics（玩具 PA 证明对象语义）没有
`finiteConsistencyFormula n` 的证明对象。这个反证是好事：它说明新的目标不会被“没有证明对象”
偷渡成真。

因此现在真正要做的纸面证明和 Lean 内化证明是：

```text
构造真实 PA/Hilbert proof-object semantics（证明对象语义），
证明每个 target(n) 有证明对象，
并证明这些证明对象的最小大小超越任意多项式。
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean > /tmp/pudlak_lower_complete_strong_probe24.log 2>&1
```

结果：

```text
无 error（错误）
无 warning（警告）
```

新增非真空目标的公理剖面仍为：

```text
[propext, Classical.choice, Quot.sound]
```

未出现：

```text
proof_length
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

## 本轮新增：增长义务改写为正向证明对象强下界

为了避免最终目标继续停留在否定型表述，本轮新增：

```lean
BAProofObjectStrongSizeLowerBound
```

中文含义：

```text
BA 证明对象强大小下界。
```

完整展开：

```text
对任意 polynomial upper bound U（多项式上界 U），
对任意起点 N，
存在 n >= N，
使得每一个证明 target(n) 的 BAProofObject（BA 证明对象）
都满足：

U(n) < proof.size.
```

这个命题是现在最适合作为纸面证明和 Lean 内化目标的形式。它不是包装，不是 `tail_gap`
（尾部间隙），也不是 `proof_length`（根证明长度）公设；它直接说“小证明对象不存在”。

Lean 中已经证明如下等价：

```lean
BAProofObjectStrongSizeLowerBound_iff_no_eventual_polynomial_proof_family
BAProofObjectStrongSizeLowerBound_iff_BAOptionMinProofSizeBeatsPolynomial
boundedEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
bussPudlakEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
```

并证明它足够推出下游搜索/碰撞所需下界：

```lean
BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
BAProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
```

因此，下界缺口现在被压缩成一个正向 theorem-5 证明目标：

```text
证明真实 PA/Hilbert target family 满足
BAProofObjectStrongSizeLowerBound。
```

纸面证明要做的事情也因此明确：

1. 固定任意多项式上界 `U` 和起点 `N`。
2. 构造某个 `n >= N`。
3. 证明任何 PA/Hilbert proof object（证明对象）若证明 `target(n)`，其 size（大小）都大于 `U(n)`。

如果这一步完成，下游 Lean 已经能自动推出：

```text
无最终多项式证明对象族；
可空最小证明大小超多项式；
checked minProofCodeSize 强下界；
NoAcceptedBelowCutoff。
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean > /tmp/pudlak_lower_strong_proof_object_probe23.log 2>&1
```

结果：

```text
无 error（错误）
无 warning（警告）
```

新增定理的公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

未出现：

```text
proof_length
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

## 本轮新增：下界增长义务的最终形态是无多项式证明族定理

继续复查旧工作后，可以把问题分成两类：

第一类是已经打开的接口层：

```text
tail_gap（尾部间隙）
rejection_search（拒绝搜索）
ComputableNoAcceptedBelowCutoff（截断界以下无接受码）
EventualLowerBound（最终下界）
```

这些现在都能被接到 proof-code semantics（证明码语义）或 BA proof-object semantics
（有界算术证明对象语义）上，不再是模糊的黑盒。

第二类是还没有被数学证明关闭的根命题：

```text
¬ BAEventuallyPolynomialProofObjectFamily(Ax, target)
```

中文意思是：

```text
不存在一个最终多项式大小的证明对象族。
```

展开为：

```text
不存在 U : Nat -> Real 和 N : Nat，
其中 U 是 polynomial bound（多项式上界），
并且对所有 n >= N，
target(n) 都有一个 BAProofObject（有界算术证明对象）
其 size（大小） <= U(n)。
```

本轮 Lean 已证明，在 option-valued minimum proof size（可空最小证明大小）校准下：

```lean
boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family
```

也就是：

```text
EventualLowerBound(box)
<->
¬ BAEventuallyPolynomialProofObjectFamily(Ax, target).
```

对 Buss-Pudlak source（Buss-Pudlak 下界源）也有专门版本：

```lean
bussPudlakEventualLowerBound_iff_no_eventual_polynomial_proof_family
```

因此旧 `BussPudlakTheorem5PALowerBoundSource.lower_bound` 字段现在的准确含义是：

```text
只要 source.pa_length(n) 被校准为 target(n) 的真实最小证明对象大小，
它就等价于“target 没有最终多项式大小证明对象族”。
```

这一步解决了一个关键审计问题：旧路线不是因为 Lean 能神奇地产生下界，而是因为
`lower_bound` 字段本身承载了完整的 proof-complexity lower bound（证明复杂度下界）。
现在这个承载内容已经被 Lean 等价展开，不再是名称层面的包装。

本轮新增 Lean 位置：

```text
integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

核心定理：

```lean
boundedArithmeticPolynomialBound_to_rootPolynomialBound_opened
boundedEventualLowerBound_to_no_eventual_polynomial_proof_family
no_eventual_polynomial_proof_family_to_boundedEventualLowerBound
boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family
bussPudlakLowerSource_to_no_eventual_polynomial_proof_family
bussPudlakEventualLowerBound_iff_no_eventual_polynomial_proof_family
```

Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean > /tmp/pudlak_lower_source_no_poly_probe22.log 2>&1
```

结果：

```text
无 error（错误）
无 warning（警告）
```

新增定理的公理剖面均只含 Lean/mathlib 常规项：

```text
[propext, Classical.choice, Quot.sound]
```

没有引入：

```text
proof_length（根证明长度公设）
tail_gap（尾部间隙输入）
partial_consistency_payload（部分一致性负载）
strengthened_partial_consistency_payload（强化部分一致性负载）
```

另外复查旧 `PAHilbertCheckerExactnessCore`（PA/Hilbert 检查器精确性核心）后，确认它不是
当前最干净入口。虽然名字像 checker/exactness（检查器/精确性）层，但其结构字段含有
`computable_finite_search_no_small_core`，而该 core 内部有 `proof_length_model`
（证明长度模型）路径。因此：

```text
paHilbertCheckerExactnessCore_to_checkedMinProofCodeStrongLowerBound
```

的公理剖面仍会出现 `proof_length`。这说明旧 core 路线还没有真正从根证明长度公设中脱身；
当前更干净的目标应停在：

```text
option-valued semantic minimum proof size
（可空语义最小证明大小）

和

¬ BAEventuallyPolynomialProofObjectFamily
（不存在最终多项式证明对象族）
```

所以现在的增长义务可以非常清楚地写成：

```text
必须证明真实 PA/Hilbert target family
没有最终多项式大小证明对象族。
```

如果这个定理完成，那么下游会自动得到：

```text
BAOptionMinProofSizeBeatsPolynomial
CheckedMinProofCodeStrongLowerBound
ComputableNoAcceptedBelowCutoff
checked measured search gap
```

如果这个定理不能完成，那么再包装成 `tail_gap`、`rejection_search` 或 `lower_source`
都不会增加论文信用度，因为它们只是这个命题的不同外观。

## 39. 增长义务的根部校正：必须增长的是真实最小证明对象大小

本轮复查了此前围绕 `tail_gap`（尾部间隙）、`rejection_search`（拒绝搜索）、
`proof_length`（证明长度）做过的工作。结论是：旧路线已经把很多接口拆开了，
但仍有两个根部风险必须先切掉。

第一，`semanticBAProofLength`（实数值语义证明长度）使用 `sInf`
（下确界）。如果某个目标没有任何证明对象，那么对应集合为空；这时实数层面的
empty-infimum convention（空下确界约定）会把“没有证明”变成一个实数值。这种
定义不适合承载 Pudlak lower bound（Pudlak 下界）的根语义。

第二，如果为了“存在证明”而把每个目标公式直接放进 axiom predicate（公理谓词），
就会产生 one-step proof（一步证明）。这会使最小证明大小常数有界，直接与
super-polynomial lower bound（超多项式下界）矛盾。

因此，本轮把增长义务改写到：

```lean
semanticBAMinProofSizeOption
```

这个对象是 option-valued minimum（可空最小值）：

```text
none     没有证明对象；
some k   存在证明对象，并且最小证明对象大小为 k。
```

Lean 新增了反推定理：

```lean
semanticBAMinProofSizeOption_some_to_hasProofOfSize
semanticBAMinProofSizeOption_some_to_exists_proof
semanticBAMinProofSizeOption_some_iff_exists_proof
```

这些定理保证：

```text
只要下界见证使用 some k，就已经承诺真实 BAProofObject（有界算术证明对象）存在。
```

在此基础上，审计文件定义了：

```lean
BAOptionMinProofSizeBeatsPolynomial
```

这就是当前最干净的增长目标：

```text
对每个 polynomial bound U（多项式界）和每个起点 N，
找到 n >= N 与真实最小证明大小 k，
使 U(n) < k。
```

Lean 已证明：

```lean
BAOptionMinProofSizeBeatsPolynomial_to_frequently_exists_proof
no_BAOptionMinProofSizeBeatsPolynomial_of_polynomial_upper_bound
no_currentToyBAOptionMinProofSizeBeatsPolynomial_finiteConsistency
no_BAOptionMinProofSizeBeatsPolynomial_of_target_axioms
```

这些定理把增长义务固定成下面的形式：

```text
不能靠 empty proof set（空证明集）；
不能靠 target-as-axiom（目标即公理）；
不能靠 polynomial-size proof family（多项式大小证明族）。
```

这一步的数学意义是：后续如果要真正关闭 Pudlak lower bound（Pudlak 下界），
必须证明真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）下的
minimum proof-object size（最小证明对象大小）本身超多项式增长。任何只给出多项式
长度证明构造、或只给出空证明集解释、或把目标塞进公理的路线，都会被新增 Lean 定理
直接排除。

本轮验证：

```text
lake env lean bounded_arithmetic_lab/BoundedArithmeticLab/SemanticProofLength.lean
lake build BoundedArithmeticLab.SemanticProofLength
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
新增增长边界定理 axiom profile（公理剖面）：
[propext, Classical.choice, Quot.sound]
```

没有新增：

```text
proof_length（证明长度公设）
tail_gap（尾部间隙）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（强化部分一致性载荷）
```

所以，当前任务的下一步不是继续包装 `tail_gap`，也不是把 `rejection_search`
换一个名字，而是构造真实 PA/Hilbert proof object layer（PA/Hilbert 证明对象层），
并在该层证明 `BAOptionMinProofSizeBeatsPolynomial` 所要求的超多项式增长。

## 40. Option 增长目标已经正向接入下界管线

本轮新增了从 option-valued minimum（可空最小值）到 checked proof-code lower bound
（检查证明码下界）的正向桥：

```lean
baProofObjectRootCodeSemantics_minProofCodeSize_eq_option
BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound
BAOptionMinProofSizeBeatsPolynomial_toNoAcceptedBelowCutoff
```

这三条定理完成了一个关键校准：

```text
semanticBAMinProofSizeOption = some k
  => root ProofCodeSemantics.minProofCodeSize = k
```

因此，一旦能证明：

```lean
BAOptionMinProofSizeBeatsPolynomial Ax target
```

Lean 现在会自动给出：

```text
CheckedMinProofCodeStrongLowerBound（检查最小证明码强下界）
ComputableNoAcceptedBelowCutoff（截断以下无接受码）
```

这意味着下界增长义务已经从“接口接线问题”推进为“真实增长定理问题”：

```text
要证明的不是 tail_gap（尾部间隙）；
要证明的也不是 rejection_search（拒绝搜索）；
而是具体 target family（目标公式族）的真实最小 proof object size
（证明对象大小）超过任意 polynomial bound（多项式界）。
```

这条桥没有使用 `proof_length`（证明长度公设）。它也没有使用
`partial_consistency_payload`（部分一致性载荷）或
`strengthened_partial_consistency_payload`（强化部分一致性载荷）。探针输出显示新增定理
的 axiom profile（公理剖面）为：

```text
[propext, Classical.choice, Quot.sound]
```

当前剩余硬义务可以写成最短形式：

```text
构造真实 Ax 与 target；
证明每个 target(n) 有真实 BAProofObject（有界算术证明对象）；
证明 semanticBAMinProofSizeOption(Ax, target, n) 的 some k
最终超过任意 polynomial bound（多项式界）。
```

如果这三步完成，Pudlak 侧下界就能经由本轮桥接进入：

```text
NoAcceptedBelowCutoff -> checked measured search gap -> collision route
```

所以后续推进要集中在真实 `Ax/target/proof object` 构造和超多项式增长证明，
不能再回到空下确界、目标即公理、或人工 `tail_gap` 输入。

## 41. 增长定理的等价形：排除最终多项式证明族

本轮将 `BAOptionMinProofSizeBeatsPolynomial`（可空最小证明大小超多项式增长）
改写成更接近纸面证明的等价命题。

新增定义：

```lean
BAEventuallyPolynomialProofObjectFamily
```

含义是：

```text
存在一个 polynomial bound U（多项式界）和 threshold N（阈值），
使得从 N 以后每个 target(n) 都有一个 proof object（证明对象），
并且证明对象大小 <= U(n)。
```

Lean 证明了：

```lean
BAOptionMinProofSizeBeatsPolynomial_iff_no_eventual_polynomial_proof_family
```

在 completeness（每个 target(n) 都有证明对象）前提下：

```text
BAOptionMinProofSizeBeatsPolynomial
等价于
不存在最终多项式大小证明对象族。
```

这把增长义务从“最小值比较”改成了一个更审稿友好的证明复杂度命题：

```text
任何声称从某个 N 以后给出 target(n) 证明的 uniform family（统一证明族），
其大小都不可能被一个固定 polynomial bound（多项式界）控制。
```

同时，Lean 已经把这个等价命题接入下界管线：

```lean
no_eventual_polynomial_proof_family_to_checkedMinProofCodeStrongLowerBound
no_eventual_polynomial_proof_family_toNoAcceptedBelowCutoff
```

所以现在最短闭合路线是：

```text
1. 构造真实 Ax/target/proof object layer
   （公理系统/目标公式族/证明对象层）；

2. 证明 completeness
   （每个 target(n) 有证明对象）；

3. 证明 ¬ BAEventuallyPolynomialProofObjectFamily
   （不存在最终多项式大小证明对象族）；

4. Lean 自动推出 NoAcceptedBelowCutoff
   （截断以下无接受码）；

5. 进入 checked measured search gap（检查测量搜索间隙）和 collision route（碰撞路线）。
```

这一步没有新增 `proof_length`（证明长度公设）依赖，也没有新增 `tail_gap`
（尾部间隙）依赖。新增定理的 axiom profile（公理剖面）仍为：

```text
[propext, Classical.choice, Quot.sound]
```

因此，当前要攻克的不是接线，而是真正的 proof-complexity lower bound
（证明复杂度下界）：

```text
¬ BAEventuallyPolynomialProofObjectFamily
```

## 36. 根部校正：旧 checker 不是可修补对象

本轮新增 Lean 定理：

```lean
no_currentToyBAProofObjectAcceptedNatCodeBridge_concretePowerBound
```

它把旧路线的问题钉死在根定义上：

```text
concretePAHilbertPowerBoundChecker
（具体 PA/Hilbert 幂界检查器）
已经接受短码 n 证明 powerBoundRawCode(n)。
```

如果再要求它满足：

```lean
BAProofObjectAcceptedNatCodeBridge
```

也就是：

```text
每个 accepted nat code（被接受自然数码）
都能抽取为同一目标公式的 BAProofObject
（有界算术证明对象），并且证明对象 size（大小）不超过该 code（码）。
```

那么对 `n = 0` 已经推出：

```text
存在 BAProofObject PAAxiom
证明 finiteConsistencyFormula(0)。
```

但当前 toy PA calculus（玩具 PA 演算）已经由 Lean 证明：

```lean
no_currentToyPAProofObject_finiteConsistencyFormula
```

所以旧 checker 不能作为最终下界语义，也不能靠补一个桥接参数修好。

这说明后续增长义务不能再写成：

```text
给旧 powerBound checker 加 rejection_search（拒绝搜索）
```

而必须写成：

```text
构造真实 proof-code semantics（证明码语义）
或构造真实 BAProofObject encoder/checker（BA 证明对象编码/检查器）。
```

当前最短未闭合义务是：

```text
BAProofObjectAcceptedNatCodeBridge
（自然数证明码到 BA 证明对象桥）

以及

BussPudlakTheorem5PALowerBoundSource.lower_bound
（Buss-Pudlak 第5定理 PA 下界来源中的下界字段）
```

其中第一项是 coding/checker obligation（编码/检查器义务）：

```text
accepted PA/Hilbert nat code
（被接受 PA/Hilbert 自然数证明码）
-> decoded / extracted BAProofObject
（解码/抽取出的 BA 证明对象）
```

第二项是 real theorem-5 obligation（真正第5定理义务）：

```text
semanticBAProofLength(finiteConsistencyFormula n)
（有限一致性公式的语义 BA 证明长度）
eventually beats every polynomial
（最终超过任意多项式）
```

新增探针结果：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
status = 0
```

新增定理公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

没有使用：

```text
proof_length（证明长度）
partial_consistency_payload（部分一致性载荷）
tail_gap（尾部间隙）
```

## 37. 公共证书包路线在当前 toy 语义下不可实例化

本轮把 no-go（不可行结论）继续推出到项目公共证书层。新增 Lean 定理：

```lean
no_projectPublicCollisionCertificateBundle_currentToySemantics
no_projectConcreteCertificateObligation_currentToySemantics
no_nonempty_projectPublicCollisionCertificateBundle_currentToySemantics
no_nonempty_projectConcreteCertificateObligation_currentToySemantics
no_projectPublicCollisionCompletionObligation_currentToySemantics
```

它们共同说明：

```text
ProjectPublicCollisionCertificateBundle
（项目公共碰撞证书包）
ProjectConcreteCertificateObligation
（项目具体证书义务）
ProjectPublicCollisionCompletionObligation
（项目公共碰撞完成义务）

在当前 toy PA semantics（玩具 PA 语义）下都不能存在。
```

证明原因很直接：

```text
公共证书层要求：

lower_source.pa_length(n)
  = semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n)

但当前 toy PA calculus（玩具 PA 演算）中：

semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n) = 0

于是 lower_source.lower_bound（下界字段）
会要求 0 最终超过常数多项式 0，矛盾。
```

这一步排除了一个危险误解：

```text
不能把 public bundle（公共证书包）
或 completion obligation（完成义务）
当作“已经闭合的证明”。

在当前语义下，它们不是未完成，而是不可实例化。
```

新增探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
status = 0
```

新增 no-go 公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

没有使用：

```text
proof_length（证明长度）
partial_consistency_payload（部分一致性载荷）
literaturePudlakTheorem5ExternalRescaledLowerBound
（外部 Pudlak 第5定理下界公设）
```

所以增长义务的下一步不应再是：

```text
填 ProjectPublicCollisionCertificateBundle 的字段。
```

而必须是：

```text
替换 current toy PA semantics（当前玩具 PA 语义），
并构造真实 proof-code semantics / encoder / checker
（证明码语义 / 编码器 / 检查器）。
```

只有在新的真实语义中，才有可能重新证明：

```text
semantic proof length（语义证明长度）
eventually beats every polynomial（最终超过任意多项式）
```

## 38. 增长义务前置条件：先有证明对象，再谈长度增长

本轮在根语义层新增：

```lean
semanticBAMinProofSizeOption
```

它是 option-valued semantic proof size（可空语义证明大小）：

```text
some k  表示存在 BAProofObject（BA 证明对象），且最小大小为 k；
none    表示没有 BAProofObject（BA 证明对象）。
```

这修正了旧 `semanticBAProofLength : Real`（实数值语义证明长度）的一个审计问题：

```text
旧定义使用 sInf（下确界）。
如果证明对象集合为空，Real.sInf_empty 会给出 0。
```

也就是说，旧语义会把：

```text
没有证明对象
```

显示成：

```text
证明长度 0。
```

对 Pudlak 下界来说，这是根部风险。因为真正要证明的是：

```text
最短证明长度最终超过任意多项式。
```

这个命题至少要求：

```text
每个目标公式确实有证明对象，
并且证明对象集合非空。
```

本轮 Lean 已证明当前 toy PA calculus（玩具 PA 演算）中：

```lean
currentToySemanticBAMinProofSizeOption_finiteConsistency_eq_none
```

即：

```text
finiteConsistencyFormula(n)
在当前 toy PA 中没有 BAProofObject（BA 证明对象）。
```

这解释了为什么旧公共证书层会被排除：

```text
它把 lower_source.pa_length 接到旧 Real semanticBAProofLength；
但旧 Real 语义在无证明情形下给出 0；
于是和 lower_source.lower_bound 直接矛盾。
```

新的闭合路线必须改成：

```text
1. 构造真实 PA/Hilbert 或 BA proof object semantics
   （证明对象语义）；
2. 证明 finiteConsistencyFormula(n) 对每个 n 有 proof object
   （证明对象完备性）；
3. 用 semanticBAMinProofSizeOption = some k
   或等价最小证明码语义定义长度；
4. 在这个非空最小长度上证明 theorem-5 lower bound
   （第5定理下界）。
```

本轮探针：

```text
lake build BoundedArithmeticLab.SemanticProofLength
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
status = 0
```

新增定理没有使用：

```text
proof_length（证明长度）
partial_consistency_payload（部分一致性载荷）
tail_gap（尾部间隙）
```

## 34. 旧工作复核后的增长义务重写

旧路线最大的问题不是 Lean 语法问题，而是增长义务没有真正落在证明码下界上。

如果使用 `concretePAHilbertPowerBoundChecker`（具体幂上界检查器），则对每个 `n` 都有
一个显式接受码：

```text
code = n
accepted for powerBoundRawCode n
（数值码 n 被接受为 powerBoundRawCode n 的证明码）
```

所以这个 checker 的最小接受码天然不可能超过所有多项式。特别是取多项式 `U(n)=n`
或 `U(n)=n+1` 时，任何要求 `cutoff > U(witness)` 并拒绝所有
`code < cutoff` 的数据，都会拒绝掉 `code = witness` 这个已接受码。

这说明旧的 powerBound checker 不是 Pudlak 下界 checker。它更像一个测试用壳子，不能放进
最终证明主线。

本轮把增长义务改成下面这个精确目标：

```text
PAHilbertAcceptedNatCodeRejectionExtractorData
（PA/Hilbert 接受数值码拒绝抽取数据）
```

它的数学内容是：

```text
给定任意 polynomial bound（多项式界）U 和起点 N，
构造 witness >= N 与 cutoff，
满足 U(witness) < cutoff，
并证明所有 code < cutoff 都不是
powerBoundRawCode(witness) 的 accepted PA/Hilbert proof code
（已接受 PA/Hilbert 证明码）。
```

本轮新增的关键桥：

```lean
paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor
```

说明如果 finite enumeration（有限枚举）确实枚举的是全部自然数码
`List.range cutoff`，那么旧的 finite-search rejection extractor（有限搜索拒绝抽取器）
就可以变成这个直接的 accepted-code rejection（接受码拒绝）目标。

这一步消除了一个隐藏风险：不能只证明“候选表中的码被拒绝”，还必须证明候选表就是所有小于
`cutoff` 的码。否则可以用空候选表制造一个假下界。

本轮新增的反证：

```lean
no_concretePAHilbertPowerBoundAcceptedNatCodeCheckerExtractor
no_concretePAHilbertPowerBoundRejectionExtractorInput
no_concretePAHilbertPowerBoundFourPiece
```

含义是：旧的 concrete powerBound 路线无法提供这个直接下界数据。这里不是工程没接好，
而是逻辑上会和它自身接受 `code = n` 冲突。

因此现在的增长定理义务可以写成一句话：

```text
必须为真实 PA/Hilbert proof system（证明系统）的数值证明码，
证明 accepted-code no-small theorem（接受码无小证明定理）。
```

完成这条以后，Lean 已经有干净桥把它送到：

```text
CheckedMinProofCodeStrongLowerBound
（检查后最小证明码强下界）
```

再与 Sondow 上界相撞。没有完成这条以前，Pudlak 下界仍不能说已经完全内化。

## 35. 进一步压缩：从 BA proof-object 到 accepted nat-code

本轮把增长义务继续拆开。旧的 `powerBound checker`（幂上界检查器）不行，但
`BAProofObject`（有界算术证明对象）路线是更真实的候选。

已有 Lean 事实：

```lean
baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
```

它说明：

```text
结构化 BA proof object semantics（BA 证明对象语义）
的 minProofCodeSize（最小证明码大小）
等于 semanticBAProofLength（语义 BA 证明长度）。
```

因此，如果 Buss-Pudlak lower source（Buss-Pudlak 下界源）的 `pa_length` 被校准到
`semanticBAProofLength`，就能得到结构化证明对象层面的下界。

本轮新增：

```lean
bussPudlakLowerSource_baProofObjectSemantics_toNoAcceptedBelowCutoff
bussPudlakLowerSource_baProofObjectSemantics_to_checkedMeasuredSearchGap
```

这把：

```text
Buss-Pudlak lower source
+ BAProofObject completeness（BA 证明对象完备性）
+ semantic length calibration（语义长度校准）
```

推进到：

```text
ComputableNoAcceptedBelowCutoff
（截断以下无接受证明）
```

但这还不是最终 PA/Hilbert accepted nat-code（PA/Hilbert 接受自然数码）层。为此新增了
一个精确接口：

```lean
BAProofObjectAcceptedNatCodeBridge
```

它要求：

```text
若 PA/Hilbert checker 接受自然数码 code 作为 powerBoundRawCode n 的证明，
则可以抽取一个 BAProofObject proof，
使 proof.conclusion = target n 且 proof.size <= code。
```

在这个条件下，Lean 已证明：

```lean
baProofObjectNoAcceptedBelow_toPAHilbertAcceptedNatCodeRejectionData
bussPudlakLowerSource_baProofObjectBridge_toPAHilbertAcceptedNatCodeRejectionData
```

所以现在增长义务的根部变成：

```text
证明真实 PA/Hilbert accepted nat-code checker
确实能大小受控地解码/抽取 BAProofObject。
```

这比之前的 `tail_gap`（尾部间隙）或 `rejection_search`（拒绝搜索）更底层、更具体。
它不是一个抽象间隙证书，而是实际 proof-code semantics（证明码语义）和 checker
exactness（检查器精确性）的构造义务。

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
status = 0
BAProofObject -> accepted nat-code rejection 桥通过 Lean 检查
```

当前仍未完全闭合的两件事：

```text
1. BussPudlakTheorem5PALowerBoundSource.lower_bound
   仍是 theorem-5 下界字段；

2. BAProofObjectAcceptedNatCodeBridge
   仍需由真实 PA/Hilbert decoder/checker 构造。
```

下一步真正要砍的是第 2 项：实现或形式化一个 PA/Hilbert proof-code decoder/checker
（证明码解码器/检查器），并证明 accepted code（接受码）能抽取出大小不超过 code 的
BAProofObject。做到这一点后，Pudlak 侧会从结构化证明对象层推进到自然数证明码层。

## 30. 完全打开后的增长义务

本轮复查旧工作后，增长义务已经不能再表述为 `tail_gap`（尾部间隙）或
`proof_length_gap`（证明长度间隙）。这些名字太高层，容易把真正的数学内容藏起来。

当前 Lean 中最干净的打开形式是：

```lean
ComputableNoAcceptedBelowCutoff
```

数学意思是：

```text
给定任意 polynomial bound（多项式上界）f 和任意起点 N，
构造 n >= N 与 cutoff K，
满足 f(n) < K；
并证明每一个 size < K 的 proof code（证明码）
都不会被 checker（检查器）接受为 powerBoundRawCode(n) 的证明。
```

从这个命题出发，Lean 已经证明：

```lean
proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMeasuredSearchGap
proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMinProofCodeStrongLowerBound
```

探针剖面是：

```text
[propext, Classical.choice, Quot.sound]
```

不含：

```text
proof_length
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

因此，增长义务已经被压缩到一个不能再靠包装下沉的核心句子：

```text
在真实 PA/Hilbert proof-code semantics（证明码语义）中，
证明 theorem-5 family（第5定理公式族）没有小接受证明码。
```

旧 native concrete checker（原生具体检查器）不能完成这个任务。Lean 已证明：

```lean
no_nativePowerBoundCheckedMinProofCodeStrongLowerBound
```

含义是：当前 `concretePAHilbertPowerBoundCheckerSemantics`
（具体 PA/Hilbert 幂界检查器语义）对 `powerBoundRawCode n` 有大小至多为 `n`
的 accepted code（接受码），所以最小接受码长度是 polynomially bounded
（多项式有界）的；它不可能推出 super-polynomial lower bound（超多项式下界）。

与此同时，合成模型探针：

```lean
superPolynomialCanonicalLength_to_checkedMinProofCodeStrongLowerBound
```

说明如果 proof-code size（证明码尺寸）本身取为明确的
`(n+1)^n`，则适配链可以干净闭合，剖面同样只有：

```text
[propext, Classical.choice, Quot.sound]
```

这证明 adapter（适配器）没有问题；问题只剩真实 Pudlak 下界本身。

下一步的数学目标必须写成：

```text
构造真实 PA/Hilbert checker（检查器）和 proof-code semantics（证明码语义）；
证明它对 theorem-5 family 满足 NoAcceptedBelowCutoff（截断以下无接受码）；
再由已验证的 Lean 桥接定理推出 CheckedMinProofCodeStrongLowerBound。
```

不能再把当前 root `proof_length = formula-code size`（根证明长度等于公式码大小）拿来用。
只要接回 current root proof_length（当前根证明长度），Lean 已经证明会回到 no-go
（不可能性）：

```lean
no_openedGapFreeTheorem5ClosureTarget_currentRoot
```

该 no-go 的剖面包含 `proof_length`，正是因为它在反证“接回当前 root proof_length”的路线。
这说明当前 root definition（根定义）必须替换，或者投稿主线必须停在 root-free
proof-code semantics（无根证明长度的证明码语义）层。

## 31. 根接口修正：从 full decoder exactness 到 canonical decoder exactness

继续向 checker root（检查器根部）复查后，发现旧目标还存在一个独立于
`proof_length`（证明长度）的矛盾。

旧结构：

```lean
PAHilbertCheckerDecoderExactness
```

要求：

```text
任意 PAHilbertProofObject proof
都满足 decoder.decode proof.code = some proof。
```

但 `PAHilbertProofObject`（PA/Hilbert 证明对象）不是按 code（码）唯一的。两个不同
proof object 可以有同一个 numeric code（数值码）。所以 Lean 已证明：

```lean
no_full_decoder_exactness_for_unrestricted_proof_objects
```

本轮新增审计定理：

```lean
no_paHilbertCheckerInterface_unrestrictedProofObjects
```

剖面：

```text
[propext]
```

这说明旧 `PAHilbertCheckerInterface`（PA/Hilbert 检查器接口）本身不可居住，不是因为
Pudlak lower bound（Pudlak 下界）太难，也不是因为 root proof_length（根证明长度）
定义错，而是因为 decoder exactness（解码器精确性）规格要求了不可能的唯一性。

因此，增长义务的根目标必须改写为：

```lean
PAHilbertCanonicalDecoderExactness
```

它只要求 decoder（解码器）对 canonical proof objects（规范证明对象）精确。Lean 已证明
当前 seed decoder（种子解码器）满足这个修正版接口：

```lean
concretePAHilbertSeedCanonicalDecoderExactness
```

剖面：

```text
[propext]
```

这一步的作用是把一个形式矛盾的目标换成可构造目标。它还没有证明增长下界。

现在真正的最终路线应当是：

```text
1. canonical decoder exactness（规范解码器精确性）；
2. coherent accepts/rejects checker（相容的接受/拒绝检查器）；
3. real PA/Hilbert proof-code semantics（真实 PA/Hilbert 证明码语义）；
4. theorem-5 NoAcceptedBelowCutoff（第5定理截断以下无接受码）；
5. CheckedMinProofCodeStrongLowerBound（已检查最小证明码强下界）。
```

旧 `RealPAHilbertRootReplacementTarget` 不能再作为目标，因为它仍含旧
`PAHilbertCheckerExactnessCore`，而这个 core（核心）包含不可能的 full decoder exactness。

## 32. 文献 theorem-5 输入的状态

复查外部 Pudlak 文件后，当前项目里 theorem-5 lower bound（第五定理下界）仍没有内部证明。

在：

```text
EulerLimit/ExternalPudlakRawEncoding.lean
```

仍有：

```lean
axiom literaturePudlakTheorem5ExternalScaleData
axiom literaturePudlakTheorem5ExternalRescaledLowerBound
```

在：

```text
BoundedArithmeticLab/BussPudlakSource.lean
```

`BussPudlakTheorem5PALowerBoundSource`（Buss/Pudlak 第五定理 PA 下界来源）把
`EventualLowerBound`（最终下界）作为字段 `lower_bound` 保存；文件注释也说明它没有证明
那个 theorem（定理）。

所以不能把这些 source（来源）当作“缺口已闭合”。它们最多是外部文献边界。

当前真正要完成的增长证明仍是：

```lean
ComputableNoAcceptedBelowCutoff
```

但它必须在修正后的 canonical decoder / real checker / real proof-code semantics
（规范解码器 / 真实检查器 / 真实证明码语义）上证明，而不能再通过旧
`PAHilbertCheckerExactnessCore` 或外部 literature axiom（文献公设）获得。

## 33. 最小增长义务：接受数值码拒绝数据

本轮把 `ComputableNoAcceptedBelowCutoff`（截断以下无接受码）继续下沉到 PA/Hilbert
numeric-code layer（数值码层）。新增 Lean 桥：

```lean
paHilbertAcceptedNatCodeRejectionData_toNoAcceptedBelowCutoff
```

说明只要有：

```lean
PAHilbertAcceptedNatCodeRejectionExtractorData
```

就能直接得到：

```lean
ComputableNoAcceptedBelowCutoff
```

再由已经验证的桥得到：

```lean
CheckedMinProofCodeStrongLowerBound
```

新的 corrected core（修正核心）是：

```lean
PAHilbertCanonicalAcceptedNatCodeNoSmallCore
```

它不含：

```text
root proof_length（根证明长度）
calibration（校准）
full decoder exactness（完整解码器精确性）
tail_gap（尾部间隙）
payload axioms（载荷公设）
```

它只保留：

```text
canonical checker interface（规范检查器接口）
completion（目标公式族可被某些码接受）
accepted-nat-code rejection data（接受数值码拒绝数据）
```

Lean 已证明：

```lean
PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_checkedMinProofCodeStrongLowerBound
paHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget_to_checkedMinProofCodeStrongLowerBound
```

剖面：

```text
[propext, Classical.choice, Quot.sound]
```

同时，旧 concrete power-bound checker（具体幂界检查器）被排除：

```lean
no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData
no_concretePAHilbertPowerBoundCanonicalAcceptedNatCodeNoSmallCore
```

原因是它有短接受码：

```text
code n accepts powerBoundRawCode(n)
```

所以它不可能证明：

```text
所有 c < K 的 accepted code 都不存在
```

尤其当 rejection data 对 `f(n)=n` 给出 `K>n` 时立即矛盾。

因此，现在增长义务的最小 Lean 目标是：

```text
构造一个真实 canonical PA/Hilbert checker；
证明 PAHilbertAcceptedNatCodeRejectionExtractorData；
由已验证桥推出 CheckedMinProofCodeStrongLowerBound。
```

这一步已经不是包装问题，而是 theorem-5 no-small-proof theorem（第5定理无小证明定理）
本身。

## 29. 增长义务的干净版本

本轮把增长义务从 root `proof_length`（根证明长度）中剥离出来。现在最干净的增长命题是：

```text
CheckedMinProofCodeStrongLowerBound
```

即：

```text
对任意 polynomial bound（多项式上界）f，
minProofCodeSize(powerBoundRawCode n)
会在任意远处超过 f(n)。
```

Lean 新增并验证：

```lean
proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound
proofLengthFreeLowerGapClosureTarget_to_checkedMinProofCodeStrongLowerBound
checkerComputableSearchProfile_to_checkedMinProofCodeStrongLowerBound
```

它们的 axiom profile（公理剖面）为：

```text
[propext, Classical.choice, Quot.sound]
```

不含：

```text
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
tail_gap
```

这说明增长义务现在已经精确落在 proof-code semantics（证明码语义）的最小证明码长度上。
旧的 `PAHilbertCheckerExactnessCore`（PA/Hilbert 检查器精确性核心）仍含
`proof_length` 依赖，因为它把 proof-length calibration（证明长度校准）绑在 core 里。
所以投稿主线若要最大化可信度，应使用 proof-length-free source（无证明长度来源）作为
Pudlak 下界入口，再单独讨论是否需要、以及如何证明 root proof-length exactness（根证明长度精确性）。

本轮还验证了一个显式增长模型：

```lean
superPolynomialCanonicalLength n = (n + 1)^n
```

Lean 证明：

```lean
superPolynomialCanonicalLength_to_checkedMinProofCodeStrongLowerBound
```

axiom profile（公理剖面）为：

```text
[propext, Classical.choice, Quot.sound]
```

这说明 `(n+1)^n` 这类明确的 super-polynomial carrier（超多项式载体）足以让
checked minimum proof-code lower bound（已检查最小证明码下界）闭合。剩余数学难点已经被
压缩成一句话：

```text
证明真实 PA/Hilbert proof-code semantics（证明码语义）自然给出的最小证明码长度
具有这种超多项式增长。
```

不能把当前模型 carrier 直接当作 root proof_length（根证明长度）。Lean 已证明当前
root proof_length（根证明长度）太小，不能与这个超多项式 carrier 相等。

## 28. pa_length/minProofCodeSize 校准的证明对象化

本轮把增长义务中的一个隐藏校准点打开了：

```text
pa_length(n) = minProofCodeSize(powerBoundRawCode n)
```

原来这句话看起来像一个外部 calibration（校准）条件。现在 Lean 里新增了一个直接的
proof-object semantics（证明对象语义）：

```lean
baProofObjectRootCodeSemantics
```

它把 proof code（证明码）本身定义为：

```text
BAProofObject Ax（BA 证明对象）
```

并把 checks（检查关系）定义为：

```text
该证明对象的 conclusion（结论）等于 rootCode 对应的 target formula（目标公式）。
```

Lean 已证明：

```lean
baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
```

数学内容是：

```text
如果每个 target n 都有真实 BAProofObject，
并且 rootCode 是 injective（单射），
那么：

minProofCodeSize(rootCode n)
  =
semanticBAProofLength(Ax, target, n).
```

于是下界闭合可以走：

```lean
bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
```

它消费的输入是：

```text
source.lower_bound
source.pa_length(n) = semanticBAProofLength(Ax, target, n)
每个 target n 有 BAProofObject
powerBoundRawCode 单射
```

输出是：

```text
CheckedMinProofCodeStrongLowerBound
```

也就是增长义务最短形式：

```text
minProofCodeSize(powerBoundRawCode n)
最终超过任意 polynomial bound（多项式上界）。
```

这一步清掉了一个重要模糊点：`semanticBAProofLength`（语义证明长度）和
`minProofCodeSize`（最小证明码尺寸）之间不再靠口头说明，而是由 Lean 证明对象语义桥连接。

同时，当前 toy PA（玩具 PA）路线被 Lean 直接排除：

```lean
no_currentToyFiniteConsistencyProofObjectCompleteness
no_currentToyBussPudlakLowerSource_semanticFiniteConsistency
```

含义是：

```text
当前 finiteConsistencyFormula（有限一致性公式）在 toy BA 语法中只是原子公式；
当前 PAAxiom / BADerivation 无法给出它的 BAProofObject；
因此 semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n) = 0；
把 lower_source.pa_length 校准到它，会和 lower_source.lower_bound 直接矛盾。
```

所以增长义务现在不是：

```text
继续包装 tail_gap 或 lower_source
```

而是：

```text
替换 toy PA 为真实 PA/Hilbert proof-code semantics（证明码语义），
并在该真实语义上证明 Pudlak/Buss 下界。
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

新增核心定理的 axiom profile（公理剖面）：

```text
[propext, Classical.choice, Quot.sound]
```

没有引入：

```text
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
```

## 27. bounded_arithmetic lower source 的接入条件

本轮新增 bounded_arithmetic_lab（有界算术库）到最短增长义务的桥。

Lean 定理：

```lean
boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound
```

它证明：

```text
BoundedArithmeticLab.EventualLowerBound box
+ ∀ n, box.length(n) = minProofCodeSize(powerBoundRawCode n)
-> CheckedMinProofCodeStrongLowerBound
```

对 Buss-Pudlak 下界源的专门版本是：

```lean
bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
```

它证明：

```text
BussPudlakTheorem5PALowerBoundSource
+ ∀ n, source.pa_length(n) = minProofCodeSize(powerBoundRawCode n)
-> CheckedMinProofCodeStrongLowerBound
```

这把 bounded_arithmetic 的外部下界路线接到当前最短缺口：

```text
CheckedMinProofCodeStrongLowerBound
  <-> InternalPudlakTheorem5NoSmallProofCodes
```

当前状态因此非常清楚：

```text
桥接已经干净；
剩余不是 tail_gap；
剩余不是 cutoff；
剩余不是候选枚举；
剩余是 source.lower_bound 与 pa_length/minProofCodeSize 校准。
```

其中：

```text
source.lower_bound
```

仍是 `BussPudlakTheorem5PALowerBoundSource` 的字段。

校准：

```text
source.pa_length(n) = minProofCodeSize(powerBoundRawCode n)
```

仍需由真实 PA/Hilbert proof-code semantics（证明码语义）证明。

公理剖面：

```text
boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound
  [propext, Classical.choice, Quot.sound]

bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
  [propext, Classical.choice, Quot.sound]
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 26. 剩余缺口等价于 NoSmallProofCodes

本轮把增长义务继续对齐到 theorem-5 internal surface（第5定理内部接口）的标准命题：

```lean
InternalPudlakTheorem5NoSmallProofCodes
```

Lean 已证明：

```lean
checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes
```

因此现在有精确等价链：

```text
InternalPudlakTheorem5NoSmallProofCodes
  <-> CheckedMinProofCodeStrongLowerBound
  <-> ComputableNoAcceptedBelowCutoff
  -> checked measured search gap
```

前三个目标都不使用 root proof_length（根证明长度）。

它们只谈：

```text
proof-code semantics（证明码语义）
accepted proof code（被接受证明码）
size（尺寸）
minProofCodeSize（最小证明码尺寸）
```

公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

这说明：

```text
tail_gap（尾部间隙）已经不是剩余问题；
computable_search_exclusion（可计算搜索排除）已经不是黑盒；
cutoff（截断界）也不是核心数学难点。
```

剩余核心就是：

```text
证明 InternalPudlakTheorem5NoSmallProofCodes
（第5定理无小证明码）。
```

换成数学话就是：

```text
真实 PA/Hilbert proof-code semantics（证明码语义）中，
powerBoundRawCode(n) 的所有 accepted proof code（被接受证明码）
最终都大于任意 polynomial bound（多项式上界）。
```

同时，本轮审计 bounded_arithmetic_lab（有界算术库）：

```lean
BussPudlakTheorem5PALowerBoundSource
```

发现它当前的下界是字段：

```lean
source.lower_bound
```

Lean 记录为：

```lean
bussPudlakTheorem5PALowerBoundSource_lower_bound_is_field
```

这说明 bounded_arithmetic_lab 当前是 theorem-5 lower-bound interface（第5定理下界接口），
不是 theorem-5 lower-bound proof（第5定理下界证明）本身。

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 25. 最短增长义务：checked minProofCodeSize 强下界

本轮继续把增长义务下沉一层。

上一节的最短目标是：

```text
ComputableNoAcceptedBelowCutoff
（截断界以下无接受码）
```

现在 Lean 进一步抽出它背后的 root-free（不依赖根证明长度）强下界命题：

```lean
CheckedMinProofCodeStrongLowerBound
```

它说：

```text
对任意 polynomial bound（多项式上界）f，
checked minProofCodeSize（检查器最小证明码尺寸）
在任意尾部之后都能超过 f。
```

Lean 已证明：

```lean
ComputableNoAcceptedBelowCutoff.toCheckedMinProofCodeStrongLowerBound
checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
```

所以现在有一个明确等价路线：

```text
checked minProofCodeSize strong lower bound
  <-> NoAcceptedBelowCutoff（截断界以下无接受码）
  -> checked measured gap（检查器测量间隙）
```

这个部分不使用 `proof_length`（证明长度）。公理剖面是：

```text
[propext, Classical.choice, Quot.sound]
```

本轮还接上了 proof-length（证明长度）版本：

```lean
strongProofLengthLowerBound_toNoAcceptedBelowCutoff
```

含义是：

```text
StrongProofLengthLowerBound（强证明长度下界）
+ Calibration（校准）
-> NoAcceptedBelowCutoff（截断界以下无接受码）
```

这个桥接说明：

```text
如果文献 Pudlak theorem-5 lower bound（第5定理下界）
已经给出 root proof_length 级强下界，
并且该 root proof_length 已校准到真实 proof-code minimum（证明码最小值），
那么下界盒子可以关闭到 NoAcceptedBelowCutoff。
```

但是当前项目 root 不能用来做这件事。Lean 已证明：

```lean
no_proofLengthCalibratedStrongLowerBoundNoAcceptedCore_currentRoot
```

含义是：

```text
当前 root proof_length = formula-code size（根证明长度等于公式码大小），
它是 polynomially bounded（多项式有界）的；
因此它不可能同时支持 strong proof-length lower bound（强证明长度下界）。
```

复查外部 Pudlak 文件还确认：

```lean
literaturePudlakTheorem5ExternalScaleData
literaturePudlakTheorem5ExternalRescaledLowerBound
```

仍是 `axiom`（公设）。所以文献路线目前最多是“以 Pudlak 第5定理作为外部输入”的路线，
不是 Lean 内部完全证明。

现在增长义务的最短精确表述是：

```text
在真实 PA/Hilbert proof-code semantics（证明码语义）上证明：

CheckedMinProofCodeStrongLowerBound

即 minProofCodeSize(powerBoundRawCode n)
最终超过任意 polynomial bound（多项式上界）。
```

之后若要回到项目级 `proof_length`，还必须证明：

```text
Calibration / root proof_length exactness
（校准 / 根证明长度精确性）。
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 最终当前指导结论：缺口的根和突破口

当前要证明的不是 `tail_gap`（尾部间隙），也不是 `rejection_search`（拒绝搜索），而是：

```lean
ShortestCheckedMinProofCodeGrowthObligation
```

它等价于：

```lean
CheckedMinProofCodeStrongLowerBound
```

并且 Lean 已证明它等价于：

```lean
InternalPudlakTheorem5NoSmallProofCodes
```

所以真正目标是：

```text
在真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）中证明：
minProofCodeSize(powerBoundRawCode n)
最终超过任意 polynomial bound（多项式上界）。
```

已经完成的形式化突破：

```text
tail_gap
-> NoAcceptedBelowCutoff（截断界以下无接受码）
-> checked minProofCodeSize strong lower bound（检查后最小证明码强下界）
<-> NoSmallProofCodes（无小证明码）
```

卡点：

```text
1. 当前 native power-bound checker（原生幂界检查器）有短接受码：
   minProofCodeSize(powerBoundRawCode n) <= n。
   Lean 已证明：
   no_nativePowerBoundShortestCheckedMinProofCodeGrowthObligation。

2. 当前 root proof_length（根证明长度）等于 formula-code size（公式码大小），
   是多项式有界的，不能承载 theorem-5 下界。

3. bounded_arithmetic 的 BussPudlakTheorem5PALowerBoundSource
   仍是下界接口，不是内部证明。

4. literaturePudlakTheorem5ExternalScaleData /
   literaturePudlakTheorem5ExternalRescaledLowerBound
   仍是外部公设路线，不是 Lean 内部闭合。
```

突破口：

```text
必须构造真实 PA/Hilbert proof-code semantics（证明码语义），
并在它上面证明 InternalPudlakTheorem5NoSmallProofCodes。
```

下一步的最小正确方向：

```text
真实 proof-code syntax（证明码语法）
+ verified PA/Hilbert checker（已验证 PA/Hilbert 检查器）
+ completion / soundness（完备性 / 可靠性）
+ Pudlak theorem-5 no-small-proof-code proof（第5定理无小证明码证明）
-> ShortestCheckedMinProofCodeGrowthObligation
```

不能再做的事：

```text
不能把下界义务继续改名或包装；
不能把当前 native checker 当真实 PA checker；
不能把当前 root proof_length 当真实证明长度；
不能把外部 Pudlak 公设当内部证明完成。
```
