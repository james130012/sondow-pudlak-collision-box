# Pudlak 下界与 tail_gap 输入边界的纸面证明

日期：2026-07-09

本文档只处理 Pudlak lower bound（Pudlak 下界）和 tail_gap（尾部间隙证书）
的信用边界。结论先写在前面：

当前 Lean 路线已经严格证明了：

```text
tail_gap / search-gap input + Sondow upper route
  -> computed collision N
  -> upper/lower contradiction.
```

但当前 Lean 路线还没有从标准数学定理、checker（检查器）、
enumeration（枚举）、extractor（抽取器）和 proof-length exactness
（证明长度精确性）完全推出 tail_gap 本身。换句话说，干净的 axiom profile
（公理画像）证明的是抽象接口没有旧项目级公设污染；它不等价于证明 Pudlak
下界已经无条件闭合。

## 1. 需要证明的下界对象

碰撞证明需要一个被测量函数

```text
M(n).
```

Sondow side（Sondow 侧）在有理性假设下给出 eventual upper bound
（最终上界）：

```text
exists U, polynomial(U) and exists upperN,
  forall n >= upperN, M(n) <= U(n).
```

Pudlak side（Pudlak 侧）必须给出相反方向的 lower/gap statement
（下界/间隙命题）。强 tail-gap（尾部间隙）形式是：

```text
forall U, polynomial(U) ->
  exists threshold,
    forall n >= threshold, U(n) < M(n).
```

较弱但足够碰撞的 search-gap（搜索间隙）形式是：

```text
forall U, polynomial(U) ->
  forall N,
    exists w >= N, U(w) < M(w).
```

如果 Sondow 上界从 `upperN` 开始成立，search-gap（搜索间隙）只要在
`N = upperN` 后找到一个 `w`，就得到：

```text
U(w) < M(w) <= U(w),
```

从而矛盾。

## 2. 当前 clean route（干净路线）里 tail_gap 的真实位置

当前 proof-length-free checker route（无证明长度公设的检查器路线）使用的输入
结构是：

```lean
structure ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat -> Nat
  scale_strict :
    forall {a b : Nat}, a < b -> scale_data.scale a < scale_data.scale b
  tail_gap :
    ComputableGapCertificate
      (fun n : Nat => (lengthCodeAt n : Real))
```

这里 `tail_gap` 是结构字段。它不是由该结构内部证明出来的定理，而是作为输入
包的一部分被携带。该结构再通过

```lean
input.tail_gap.toComputableSearchGapCertificate
```

转成 search-gap（搜索间隙）供碰撞核心使用。

因此，以下说法是正确的：

```text
Lean 已经证明：
如果给出 tail_gap，则 clean checker route 能推出碰撞。
```

以下说法目前不正确：

```text
Lean 已经从零证明了 tail_gap。
```

## 3. computed N 为什么仍然读 tail_gap

clean computed N（干净计算碰撞指标）公式是：

```text
computedN =
  max upperN (input.tail_gap.gap_for_polynomial_upper U hU).threshold.
```

这说明 `tail_gap` 不只是文档名词，而是在最终 big-N（大 N）公式里提供
threshold（阈值）。Sondow side（Sondow 侧）给出 `upperN`；Pudlak side
（Pudlak 侧）通过 `tail_gap` 给出 gap threshold（间隙阈值）。两者取最大值，
才是碰撞点。

所以如果论文说 “computed N is clean（计算 N 是干净的）”，必须同步说明：

```text
clean 是指没有旧项目级 residual constants（残留常量）；
不是指 tail_gap 的数学来源已经被无条件证明。
```

## 4. axiom profile 干净不等于下界闭合

Lean 的

```lean
#print axioms cleanUpperProvider_submissionRoute
```

可能只显示：

```text
[propext, Classical.choice, Quot.sound]
```

这只说明 theorem（定理）本身没有依赖额外 global axiom（全局公设）。但是如果
theorem 的参数里有：

```lean
input : ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data
```

那么 `input.tail_gap` 仍然是数学假设的一部分。它不以 global axiom（全局公设）
形式出现，所以 axiom profile（公理画像）不会暴露它；但审稿人会在 theorem
signature（定理签名）里看到它。

因此审计规则是：

```text
axiom profile 检查全局公设；
theorem signature 检查显式参数；
structure field audit 检查参数包内部是否藏有数学义务。
```

三者必须同时看，不能只看 axiom profile。

## 5. parameter closure（参数表面闭合）的含义

`cleanTailGapFrontier_submissionRoute` 把原来的两个显式参数：

```lean
input
upper_provider
```

合并成一个 frontier（前沿包）。这叫 parameter-surface closure（参数表面闭合）。
它让 theorem surface（定理表面）更整洁，但 frontier（前沿包）内部仍有
`tail_gap` 字段。

这类整理是工程上有价值的，但不能在论文里说成：

```text
Pudlak lower bound has been proved unconditionally.
```

它只能说：

```text
The collision theorem is formally proved from a named clean frontier package.
```

## 6. eventually_strict_length 路线的真实含义

另一条路线用：

```lean
eventually_strict_length :
  forall U, is_polynomial_bound U ->
    eventually atTop, U(m) < lengthCodeAt(m)
```

来构造 `tail_gap`。这确实比裸 `tail_gap` 更接近数学命题，但它仍然是一个
proof-complexity lower-bound theorem（证明复杂度下界定理）输入。

如果 `eventually_strict_length` 是参数，那么只是把 tail_gap（尾部间隙证书）
下沉为 growth theorem（增长定理），还没有证明该增长定理。

## 7. singleton monomial route（单项式路线）的硬障碍

当前 `singletonMonomialLowerBound_submissionRoute` 把下界义务写成：

```lean
thresholdOfMonomial coeff degree <= n ->
  coeff * (n + 1)^degree < minCheckedCodeSize n
```

但项目里已经形式化证明了一个关键反证：

```lean
singletonMonomialLowerBound_conjSource_obligation_impossible
```

含义是：如果当前载体是 conjunction-source（合取来源）的
`rightConjElim.minCheckedCodeSize`，并且左右两个 component proof family
（组成证明族）的长度都有多项式上界，那么这个载体本身也有多项式上界。
一个已经多项式有界的函数不可能最终支配所有自然系数单项式。

所以当前 singleton monomial route（单项式路线）不能作为最终下界证明载体。
它适合作为反证审计材料，不适合作为投稿主定理的无条件下界来源。

## 8. 正确的下界闭合路线

要真正拿掉 lower-bound/tail_gap（下界/尾部间隙）信用负债，需要证明下面链条：

```text
checker semantics（检查器语义）
  + finite enumeration（有限枚举）
  + rejection extractor（拒绝抽取器）
  + proof-length exactness（证明长度精确性）
  -> finite-search/no-small-code core（有限搜索/无小证明码核心）
  -> search-gap certificate（搜索间隙证书）
  -> collision.
```

旧路线里，Lean 已经有条件地证明了一个 actual proof-length（实际证明长度）
后半段：

```lean
checkerExtractorExactness_to_actualProofLength_searchGap
paHilbertCheckerExactnessCore_to_actualProofLength_searchGap
```

这些 theorem（定理）的含义是：

```text
一旦 checker/extractor/exactness 这些对象被供应，
Lean 可以推出 actualProofLengthMeasured 上的 search-gap。
```

但这条路线现在只能作为旧路线诊断使用：`actualProofLengthMeasured`
（实际证明长度测量）在当前 root coordinate（根坐标）下已经被 Lean 证明为
`scale + 12`，无法承载超多项式下界。当前真正要关闭的不是这个旧目标，而是
后文第 13 节的 `SizeFilteredNoAcceptedCodeSearchClosureTarget`
（按大小过滤的无接受证明码搜索闭合目标）。

## 9. 当前可投稿表述的安全边界

当前可以安全写：

```text
We formalize a clean collision kernel: from a verified Sondow upper route and a
Pudlak/checker lower-search package in the same measured coordinate, Lean
derives the computed collision index and contradiction.
```

当前不能安全写：

```text
We have unconditionally formalized Pudlak's lower bound from standard
mathematics.
```

更不能只凭 clean axiom profile（干净公理画像）说：

```text
The lower bound has no remaining assumptions.
```

## 10. Lean 探针

本次新增的 Lean 审计文件是：

```text
integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

应运行：

```bash
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

该探针检查三件事：

1. `ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput` 确实含有
   `tail_gap` 字段。
2. `toSearchInput` 确实由 `input.tail_gap.toComputableSearchGapCertificate`
   生成 search-gap。
3. `computedCollisionN_eq_tailGapMax` 的 big-N 公式确实读取
   `input.tail_gap.gap_for_polynomial_upper`。

这个探针的目的不是证明 tail_gap，而是防止把“输入包里的 lower-bound 证书”
误读成“已经无条件证明出的 lower-bound 定理”。

### 10.1 已运行探针结果

已运行：

```bash
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
lake env lean integration/SondowProjectBigNGrowthObligationAudit.lean
```

两者均通过。

`cleanUpperProvider_submissionRoute` 的类型输出显示：

```lean
(input : ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
(upper_provider :
  input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
...
max ... (input.tail_gap.gap_for_polynomial_upper ...).threshold
```

对应 axiom profile（公理画像）为：

```text
[propext, Classical.choice, Quot.sound]
```

这正好验证本文的判断：clean route（干净路线）的全局公设画像是干净的，
但 theorem signature（定理签名）和结构字段仍显示 lower-bound package
（下界包）是输入。

`tailGapInput_toSearchInput_gap_eq_tail_gap` 的探针输出显示：

```lean
input.toSearchInput.gap =
  input.tail_gap.toComputableSearchGapCertificate
```

也就是说，search-gap（搜索间隙）不是另行构造的，而是由输入包中的
`tail_gap` 字段转换而来。

`cleanComputedN_formula_reads_tail_gap` 的探针输出显示：

```lean
computedCollisionNOfRationality hrat =
  max upperN
    (input.tail_gap.gap_for_polynomial_upper U hU).threshold
```

这说明 final big-N（最终大 N）公式仍读取 Pudlak side（Pudlak 侧）的
tail-gap threshold（尾部间隙阈值）。

`singletonMonomialLowerBound_conjSource_obligation_impossible` 的探针输出显示：

```lean
(thresholdOfMonomial : Nat -> Nat -> Nat)
(monomial_lt_lengthCodeAt_after : ...)
  -> False
```

## 10.2 当前 root proof_length 坐标下的 Lean 反证

本轮又加入并通过了一个更根部的探针。Lean 中新增：

```lean
actualProofLengthMeasured_currentRoot_eq_scale_add_twelve
actualProofLengthMeasured_currentRoot_polynomial
no_actualProofLengthSearchGapTarget_currentRoot
no_actualProofLengthPointwiseSearchGapTarget_currentRoot
```

它们证明的内容是：

```text
actualProofLengthMeasured(scale_data)(n)
  = proof_length(PA, symbolSize, scale_data.powerBoundRawCode n)
  = scale_data.scale(n) + 12.
```

由于 `scale_data` 自带：

```lean
scale_polynomial_bound :
  is_polynomial_bound (fun n => (scale n : Real))
```

所以当前 root `actualProofLengthMeasured`（根层实际证明长度测量）本身也是
polynomial bound（多项式有界）。而项目已有并复用的 Lean 定理

```lean
no_computable_search_gap_of_polynomial_bound
```

说明：一个 polynomially bounded measured function（多项式有界测量函数）
不可能携带 `ComputableSearchGapCertificate`（可计算搜索间隙证书），因为可取

```text
U(n) = measured(n) + 1
```

作为 polynomial upper（多项式上界），这会迫使某个见证点满足

```text
measured(w) + 1 < measured(w),
```

矛盾。

因此，Lean 已经证明：

```lean
ActualProofLengthSearchGapTarget scale_data -> False
ActualProofLengthPointwiseSearchGapTarget scale_data -> False
```

在当前 root proof_length（根层证明长度）坐标下成立。

这不是一个普通工程缺口，而是坐标选择上的数学障碍：

```text
当前 proof_length 是 structural fallback code size（结构性后备公式码大小）；
它在 theorem-5 power-bound family（定理 5 幂上界公式族）上只有 scale(n)+12；
而 scale(n) 已被假设为 polynomial bound（多项式有界）。
```

所以不能在这个 root `proof_length` 上继续“接线”来证明 Pudlak tail-gap。
真正的闭合必须把 Pudlak side（Pudlak 侧）换到 concrete PA/Hilbert
proof-code semantics（具体 PA/Hilbert 证明码语义）上的 minimum proof-code
size（最小证明码大小），并在那里证明 no-small-code theorem（无小证明码定理）。

## 10.3 final residual route 的 Lean 反证

本轮还加入并通过了第二组反证：

```lean
linear_succ_real_is_polynomial_bound
no_finalResidualInput_cutoffSelfCollision
no_finalByIndexResidualInput_cutoffSelfCollision
no_finalScaleInjectiveByIndexResidualInput_cutoffSelfCollision
no_finalStrictScaleByIndexResidualInput_cutoffSelfCollision
no_finalBoundedStrictScaleByIndexResidualInput_cutoffSelfCollision
```

这些定理处理的是 Month 11 中的 final residual route（最终残余路线）。
该路线要求：

```lean
witness : forall f, polynomial f -> Nat -> Nat
cutoff  : forall f, polynomial f -> Nat -> Nat
cutoff_gt :
  f (witness f hf N) < cutoff f hf N
scaleNoCollisionBelow :
  forall code < cutoff f hf N,
    scale code != scale (witness f hf N)
```

这个接口看起来像是把 `tail_gap`（尾部间隙）换成了更底层的
finite-search rejection（有限搜索拒绝）。但 Lean 现在证明它本身对
“所有 polynomial f（多项式 f）”不可能成立。

证明只取一个多项式：

```text
f(n) = n + 1.
```

由 `cutoff_gt` 得到：

```text
witness + 1 < cutoff.
```

所以：

```text
witness < cutoff.
```

再把 `code = witness` 代入 `scaleNoCollisionBelow`，得到：

```text
scale(witness) != scale(witness),
```

矛盾。

因此，下面这些 final residual/by-index（最终残余/按指标）路线不能作为
Pudlak lower bound（Pudlak 下界）的闭合路线：

```lean
ConcretePAHilbertPowerBoundFinalResidualInput
ConcretePAHilbertPowerBoundFinalByIndexResidualInput
ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
```

这进一步收窄了正确路线：

```text
不能用 numeric-code cutoff（数值码截断）排除所有 code < cutoff，
因为 witness 自己会落入被排除区间。

必须使用真正的 proof-code size（证明码大小）枚举：
只枚举 size(code) < K 的证明码，而不是简单枚举 numeric code < K。
```

换句话说，可信闭合必须发生在 concrete proof-code semantics
（具体证明码语义）和 size-filtered finite enumeration（按大小过滤的有限枚举）
上；不能回退到 by-index/id-size（按指标/恒等大小）路线。

## 10.4 当前最小正向闭合入口

在排除错误路线后，本轮 Lean 探针还固定了一个正向入口：

```lean
calibratedRejectionSearch_checkedMeasuredSearchGap
calibratedRejectionSearch_checkedMeasuredSearchGap_witness_eq
calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
calibratedRejectionSearch_checkedMeasured_gt_at_witness
calibratedRejectionSearch_acceptedCodeSize_gt_at_witness
calibratedRejectionSearch_toCanonicalSearchCore
calibratedRejectionSearch_toCanonicalSearchCore_witness_eq
SizeFilteredRejectionSearchClosureTarget
sizeFilteredRejectionSearchClosureTarget_to_checkedMeasuredSearchGap
```

其中最关键的是：

```lean
def calibratedRejectionSearch_checkedMeasuredSearchGap
    {lengthCodeAt : Nat -> Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
```

这个定理说明：

```text
calibrated size（校准大小）
+ size-filtered finite enumeration（按大小过滤的有限枚举）
+ executable rejection search（可执行拒绝搜索）
  -> checked-measured search-gap（检查测量搜索间隙）.
```

它不读取 `tail_gap`（尾部间隙），也不需要 four-piece（四件套）里的
`proof_length` exactness（证明长度精确性）字段。探针输出显示它的 axiom profile
（公理画像）为：

```text
[propext, Classical.choice, Quot.sound]
```

更具体地，Lean 证明了 witness（见证点）路径：

```lean
((calibratedRejectionSearch_checkedMeasuredSearchGap rejection_search)
  |>.gap_for_polynomial_upper U hU).witness N
  = rejection_search.witness U hU N
```

因此，当前最小剩余义务不再是抽象 `tail_gap`，而是：

```text
构造 lengthCodeAt（校准长度函数）；
构造 enumeration（对 size(code) < K 完备的有限枚举）；
构造 rejection_search（对这些枚举证明码的可执行拒绝搜索）；
证明 rejection_search 对任意 polynomial U 和起点 N 产生 witness。
```

本轮进一步把 `rejection_search`（拒绝搜索）的数学含义完全展开成
accepted proof-code size（被接受证明码大小）的下界。

Lean 证明了固定 `n` 处的等价式：

```lean
calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
```

其含义是：

```text
对所有被 concrete PA/Hilbert checker 接受的 code，
  U(n) < lengthCodeAt(code)

等价于

U(n) < month9_month10_checkedProofCodeMeasured(n).
```

也就是说，all accepted code calibrated sizes（所有被接受码的校准长度）下界
和 checked measured minimum proof-code size（检查测量的最小证明码长度）下界
不是两个不同目标，而是同一个目标的两种表述。

随后 Lean 证明了 `rejection_search` 在其选出的 witness（见证点）处推出这两个
下界版本：

```lean
calibratedRejectionSearch_checkedMeasured_gt_at_witness
calibratedRejectionSearch_acceptedCodeSize_gt_at_witness
```

第二个定理的实际数学内容是：

```text
给定任意 polynomial upper U 和起点 N，
令 w = rejection_search.witness U hU N。
如果某个 code 被 concrete PA/Hilbert checker 接受为
scale_data.powerBoundRawCode w 的证明码，
那么 U(w) < lengthCodeAt(code)。
```

这些探针的 axiom profile（公理画像）同样只有：

```text
[propext, Classical.choice, Quot.sound]
```

所以这里没有重新引入 `tail_gap`（尾部间隙）或 `proof_length`（证明长度公设）。

需要准确区分的是：上述等价是

```text
accepted-code-size lower bound
  <-> checked-measured lower bound
```

而不是说任意一个下界陈述都自动反向构造出
`ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput`。
后者还包含 executable Boolean rejection sweep（可执行布尔拒绝扫描）和
finite enumeration rejection（有限枚举拒绝）数据，因此它是更强、更可审计的
构造包。剩余硬义务仍然是从上游真正构造这个 `rejection_search`，不是把它改名。

最后，Lean 还证明了这个 `rejection_search` 能直接构造
`PAHilbertCanonicalSearchCore`（PA/Hilbert 规范搜索核心），并且 witness 不变：

```lean
calibratedRejectionSearch_toCanonicalSearchCore
calibratedRejectionSearch_toCanonicalSearchCore_witness_eq
```

这关闭的是 adapter layer（适配层）：一旦有真实的 size-filtered rejection search，
它可以无缝进入 proof-length-free Month 12 endpoint（无证明长度公设的 Month 12
端点）。

这就是下一步真正要闭合的 Pudlak/checker lower-bound（Pudlak/检查器下界）
核心。

## 10.5 本轮真正打开的 lower box（下界盒子）

本轮新增的 Lean 探针把 `rejection_search`（拒绝搜索）再向下打开了一层。关键
新增定理是：

```lean
calibratedSingletonFiniteEnumeration_of_injective
canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
canonicalLengthGap_to_noAcceptedCodeSearchTarget_of_injective
canonicalLengthGap_and_rootExactness_to_actualProofLengthGap
no_canonicalLengthGap_and_rootExactness_currentRoot
```

第一步，Lean 使用已有定理

```lean
concretePAHilbertPowerBound_acceptedProofCode_to_code_eq_of_injective
```

证明：只要 `powerBoundRawCode`（幂界公式码）是 injective（单射），那么任何被
concrete PA/Hilbert checker（具体 PA/Hilbert 检查器）接受为
`powerBoundRawCode n` 的 proof code（证明码）都必须等于 canonical code（规范码）
`n`。这说明接受码结构已经不是黑盒。

第二步，Lean 构造了 singleton finite enumeration（单例有限枚举）：

```lean
calibratedSingletonCodeBound lengthCodeAt n K =
  if lengthCodeAt n < K then n + 1 else 0
```

含义是：如果规范码 `n` 的 calibrated size（校准大小）低于 cutoff（截断界）
`K`，枚举区间包含 `n`；否则枚举区间为空。由于所有接受码都等于 `n`，这个
枚举对 `size(code) < K` 是 complete（完备）的。

第三步，Lean 证明：

```lean
canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
```

也就是说，只要已经有

```text
powerBoundRawCode injective（幂界公式码单射）
ComputableSearchGapCertificate(lengthCodeAt)
  （校准长度函数的可计算搜索间隙证书）
```

就能直接构造

```text
ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
  （校准无接受证明码搜索输入）
```

这个构造没有使用 `tail_gap` 字段，也没有使用 root `proof_length`（根证明长度）。
在 witness（见证点）`w` 处，cutoff（截断界）被定义为
`lengthCodeAt w`，所以枚举区间为空；`noAcceptedBelowCodeBound`
（界内无接受证明码）变成空枚举上的命题。真正承担增长力量的是

```text
U(w) < lengthCodeAt(w)
```

也就是 `lengthCodeAt` 自身的 search-gap（搜索间隙）。

这一步非常重要：它说明旧的 `rejection_search` 不是不可理解的黑盒。它可以被
压到一个更根本的命题：

```text
规范证明码长度 lengthCodeAt(n) 最终/可搜索地超过任意多项式。
```

但是这也同时暴露了真正风险：如果 `lengthCodeAt` 是任意挑出来的超多项式函数，
那么下界没有论文信用。要有数学信用，必须证明 `lengthCodeAt` 是真实 proof-code
semantics（证明码语义）诱导的 proof length（证明长度）或 minimum proof-code
size（最小证明码大小）。

第四步，Lean 证明了根层精确性的后果：

```lean
canonicalLengthGap_and_rootExactness_to_actualProofLengthGap
```

它说如果同时有

```text
ComputableSearchGapCertificate(lengthCodeAt)
proof_length(PA, symbolSize, powerBoundRawCode n) = lengthCodeAt n
```

那么立刻得到 `actualProofLengthMeasured`（实际证明长度测量）的 search-gap。

第五步，Lean 又证明：

```lean
no_canonicalLengthGap_and_rootExactness_currentRoot
```

也就是说，在当前 root proof_length（根证明长度）定义下，上面两个条件不可能
同时成立。原因是当前 root `actualProofLengthMeasured` 已经被证明等于
`scale + 12`，而 `scale` 是 polynomially bounded（多项式有界）的。

所以，本轮完全打开后的准确结论是：

```text
checker 接受码唯一性：已打开。
size-filtered singleton enumeration（按大小过滤的单例枚举）：已构造。
lengthCodeAt gap -> noAccepted search：已由 Lean 证明。
noAccepted search -> checked-measured gap：已由 Lean 证明。

剩余硬点：
  证明真实 proof-code length（证明码长度）本身具有这个 gap；
  并且不能使用当前 root proof_length，因为它已经被证明太小。
```

旧工作的主要问题也因此被定位清楚：很多路线把 `tail_gap`（尾部间隙）下沉成
`rejection_search`（拒绝搜索）、`lengthCodeAt`（长度函数）或 `proof_length`
exactness（证明长度精确性），但没有证明真实证明码长度超多项式。现在 Lean
已经证明：如果 `lengthCodeAt` 是多项式有界，noAccepted 目标不可能；如果把
`lengthCodeAt` 接回当前 root `proof_length`，同样不可能。

## 10.6 超多项式 carrier（载体）的闭合探针

为了确认剩余缺口确实只在“真实证明码长度增长”本身，本轮又加入了一个模型探针：

```lean
def superPolynomialCanonicalLength (n : Nat) : Nat :=
  (n + 1) ^ n
```

Lean 已证明：

```lean
superPolynomialCanonicalLength_searchGap
superPolynomialCanonicalLength_to_noAcceptedCodeSearchTarget
superPolynomialCanonicalLength_to_checkedMeasuredSearchGap
```

第一条定理证明：

```text
(n+1)^n 可搜索地超过任意 polynomial upper（多项式上界）。
```

证明方式是显式的。若

```text
U(n) <= c (n+1)^k,
```

取自然数 `C >= c`，再取

```text
w = max N (C + k + 1).
```

则 `w >= N`，并且

```text
U(w) <= c (w+1)^k
     <= C (w+1)^k
      < (w+1) (w+1)^k
     <= (w+1)^w.
```

这给出了 `ComputableSearchGapCertificate`（可计算搜索间隙证书）。探针输出显示
其 axiom profile（公理画像）为：

```text
[propext, Classical.choice, Quot.sound]
```

没有 `proof_length`（证明长度），也没有 `tail_gap`（尾部间隙）。

第二、三条定理说明：如果再有

```text
powerBoundRawCode injective（幂界公式码单射）
```

那么这个超多项式 carrier（载体）可以直接生成：

```text
SizeFilteredNoAcceptedCodeSearchClosureTarget
checked-measured search-gap（检查测量搜索间隙）
```

这验证了适配层已经完全闭合：一旦真实 proof-code semantics（证明码语义）给出
这种增长，Lean 后续路线不再需要额外黑盒。

但这不是投稿可用的无条件 Pudlak 下界。原因很明确：

```text
superPolynomialCanonicalLength 目前只是模型 carrier；
还没有证明它等于真实 PA/Hilbert proof-code length
（PA/Hilbert 证明码长度）或 minimum proof-code size（最小证明码大小）。
```

因此，本探针的论文信用含义是：

```text
增长 -> noAccepted -> checkedMeasuredGap 这条 Lean 通路已闭合；
剩余唯一硬缺口是：
  把真实 PA/Hilbert 证明码语义的最小证明码大小
  证明为具有这种超多项式 search-gap。
```

它也排除了一个误解：问题已经不是 Lean 接口不会接，而是数学上必须证明真实
proof-code length（证明码长度）本身足够大。任意定义一个超多项式长度函数可以
通过探针，但不能提升论文信用；只有把该长度函数从 verifier/checker
（验证器/检查器）和 PA/Hilbert proof syntax（PA/Hilbert 证明语法）中推出，
才算真正闭合。

在 component proof family（组成证明族）长度多项式有界的条件下，当前
conj-source carrier（合取来源载体）上的单项式增长义务会导出矛盾。

`lowerGap_from_extractor_exactness_is_conditional` 的探针输出显示：

```lean
(extractor : InternalPudlakTheorem5CheckerComputableRejectionExtractor ...)
(exactness : InternalPudlakTheorem5CheckerProofLengthExactness checker) :
  Nonempty (ComputableSearchGapCertificate ...)
```

这说明 checker/extractor/exactness（检查器/抽取器/精确性）可以推出
search-gap（搜索间隙），但它们仍是定理输入，不是已经自动消失的对象。

`axiomatizedSubmissionRoute` 的 axiom profile（公理画像）输出为：

```text
[partial_consistency_payload,
 proof_length,
 propext,
 strengthened_partial_consistency_payload,
 Classical.choice,
 Quot.sound,
 pudlakAdditiveProjection,
 pudlakChecker,
 pudlakEnumeration,
 pudlakExtractor,
 pudlakProofLengthExactness,
 sondowProjectUpper,
 submissionScaleData]
```

这个输出说明：axiomatized route（公设化路线）不是投稿最终信用路线。它有用处是
把剩余义务命名暴露出来；但从信用角度看，Pudlak side（Pudlak 侧）仍必须继续
向上游关闭，不能停在这些命名公设上。

## 11. 结论

Pudlak 下界目前的准确状态是：

```text
Sondow upper side（Sondow 上界侧）：已闭合。

Pudlak lower/search-gap side（Pudlak 下界/搜索间隙侧）：
  已经有 clean collision kernel（干净碰撞核心）和若干条件化转接定理；
  但在当前 root proof_length（根层证明长度）坐标下，Lean 已证明
  actualProofLengthMeasured 是 polynomial bound（多项式有界），
  因而 search-gap 目标反而不可能成立。

  同时，final residual/by-index（最终残余/按指标）路线也已被 Lean 反证：
  它会在 f(n)=n+1 时要求 witness 自己不与自己碰撞。
```

因此，下一步不能再包装 tail_gap；也不能继续在当前 root `proof_length` 坐标
上寻找 Pudlak 下界，也不能使用 numeric-code cutoff（数值码截断）的 final
residual/by-index 路线。必须把目标迁移到 concrete proof-code semantics
（具体证明码语义）上的 minimum proof-code size（最小证明码大小），并使用
size-filtered finite enumeration（按大小过滤的有限枚举）直接证明
`noAcceptedBelowCodeBound`（界内无接受证明码）。checker（检查器）、
decoder（解码器）、enumeration（枚举）和 Pudlak proof-complexity argument
（Pudlak 证明复杂性论证）都应服务于这一个目标。

## 12. 旧工作的问题诊断

这次重新读旧路线后，可以把以前围绕 Pudlak lower bound（Pudlak 下界）的工作
分成四类。

第一类是 external literature boundary（外部文献边界），例如
`PudlakTheorem5ExternalInputBoundarySurface` 和
`PudlakTheorem5ExactMinimalFieldPackageSurface`。这些文件做得有价值：
它们把 literature raw code（文献原始码）、rescaled raw code（重标度原始码）、
powerBoundRawCode（幂界公式码）和 rescaled Pudlak strengthened code
（重标度 Pudlak 强化码）对齐。问题是它们只关闭 code identity（编码同一性）
和 source boundary（来源边界），没有构造 checker-side no-small-code theorem
（检查器侧无小证明码定理）。所以它们能说明“目标公式是谁”，不能说明“为什么
没有小证明”。

第二类是 Month 6/7/8 的 proof-length model（证明长度模型）工作，例如
`ProofLengthCalibrationInternalizationSurface` 和
`SondowProjectMonth8ProofLengthInstantiationSurface`。这些文件已经把
proof code semantics（证明码语义）、local checker exactness（局部检查器精确性）
和 project proof-length semantics（项目证明长度语义）之间的等价关系写得很细。
问题是核心对象仍是 certificate / recognition / calibration field
（证书/识别/校准字段）。也就是说，它证明了：

```text
如果给出 local recognition（局部识别）
或 project checked semantics（项目检查语义），
则 proof_length（证明长度）可以转到 minProofCodeSize（最小证明码大小）。
```

它没有从 PA/Hilbert syntax（PA/Hilbert 语法）、decoder（解码器）和 verifier
（验证器）无条件构造这个 recognition（识别）。所以这部分不是错，而是还停在
proof-length calibration residual（证明长度校准残差）。

第三类是 Month 9/10/11/12 的 corrected route（修正路线），例如
`SondowProjectMonth11Month12HardResidualElimination` 和
`SondowProjectMonth11Month12ActualTransportExactness`。这部分已经发现并修正了
一个重要错误：不能要求 checked minProofCodeSize（检查最小证明码大小）等于
`scale`（尺度），因为 `scale` 是 polynomial bound（多项式有界），而 lower-gap
（下界间隙）要求超过任意 polynomial upper（多项式上界）。Lean 中已有反证：

```text
checked_eq_scale_blocker_impossible
finalThreeCertificateEndpoint_exactScale_impossible
```

这说明旧的 exact-scale route（精确等于尺度路线）逻辑上走不通。正确方向是
checked measured route（检查测量路线）或 checker projectLength route（检查器项目
长度路线），而不是把下界对象强行设为 polynomial scale（多项式尺度）。

第四类是 current calibrated route（当前校准路线）。这次新增的 Lean 探针已经把
`rejection_search`（拒绝搜索）打开到 no accepted code（无接受证明码）层：

```lean
concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow
ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
calibratedRejectionSearch_toNoAcceptedCodeSearch
calibratedNoAcceptedCodeSearch_toRejectionSearch
SizeFilteredNoAcceptedCodeSearchClosureTarget
sizeFilteredNoAcceptedCodeSearchTarget_to_checkedMeasuredSearchGap
```

这部分是当前最干净的入口，因为它不再依赖 root `proof_length`（根证明长度），
也不再把 `tail_gap`（尾部间隙）当字段读入。探针输出显示这一层的 axiom profile
（公理画像）只有：

```text
[propext, Classical.choice, Quot.sound]
```

## 13. 当前完全打开后的精确定理目标

现在真正要闭合的对象不是旧的 `ActualProofLengthPointwiseSearchGapTarget`
（实际证明长度逐点搜索间隙目标）。那条目标仍读 `actualProofLengthMeasured`
（实际证明长度测量），而当前 root coordinate（根坐标）下它已经被 Lean 证明为
`scale + 12`，所以无法承载超多项式下界。

当前目标应写成：

```lean
def SizeFilteredNoAcceptedCodeSearchClosureTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (Sigma lengthCodeAt : Nat -> Nat,
      Sigma enumeration :
        ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
          scale_data lengthCodeAt,
        ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
          scale_data lengthCodeAt enumeration)
```

展开成数学语言，就是要构造：

```text
1. lengthCodeAt（校准长度函数）：
   给每个 numeric proof code（数值证明码）一个真正的 proof-code size
   （证明码大小）。

2. enumeration（大小过滤枚举）：
   对每个 n 和 K，给出一个 numeric code bound（数值码界），保证所有
   accepted code（被接受码）中满足 lengthCodeAt(code) < K 的 code 都在
   这个有限界内。

3. noAcceptedBelowCodeBound（界内无接受证明码）：
   对任意 polynomial U（多项式 U）和起点 N，构造 witness w >= N 和 cutoff K，
   使得 U(w) < K，并证明所有 code < enumeration.codeBound(w,K) 都不是
   scale_data.powerBoundRawCode(w) 的 accepted proof code（可接受证明码）。
```

Lean 已经证明：

```text
上述三件事
  -> checked-measured search-gap（检查测量搜索间隙）
  -> canonical search core（规范搜索核心）
  -> 可进入 proof-length-free Month 12 endpoint（无证明长度公设端点）。
```

所以现在的硬点已经完全打开成一句话：

```text
必须证明 Pudlak theorem-5 target formula（Pudlak 第五定理目标公式）
在每个足够强的 witness w 处不存在 size < K 的 accepted PA/Hilbert proof code
（小于 K 的可接受 PA/Hilbert 证明码）。
```

这不是包装问题，而是真正的 proof-complexity lower bound（证明复杂性下界）问题。
后续工作不能再新增 `tail_gap`（尾部间隙）字段，也不能把它改名为
`rejection_search`（拒绝搜索）。必须从 checker（检查器）、decoder（解码器）、
proof object semantics（证明对象语义）、finite enumeration（有限枚举）和 Pudlak
lower-bound argument（Pudlak 下界论证）本身推出 `noAcceptedBelowCodeBound`
（界内无接受证明码）。

## 14. 本轮新增：把旧 calibrated route 的坑打开

本轮重新检查旧工作后，关键问题已经进一步定位到 calibrated checker
（校准检查器）和 root exactness（根层精确性）的连接处。

在 `concretePAHilbertPowerBoundCalibratedCheckerSemantics`（校准 PA/Hilbert
幂界检查器语义）里，`size`（大小函数）定义为外部给定的
`lengthCodeAt`（长度函数）。因此，只要 `powerBoundRawCode`（幂界原始码）
是 injective（单射），Lean 能证明：

```lean
concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
```

也就是该 calibrated checker（校准检查器）的最小证明码大小等于传入的
`lengthCodeAt`。这一步本身是干净的，axiom profile（公理画像）只有：

```text
[propext, Classical.choice, Quot.sound]
```

但这也说明旧 route（路线）的风险：如果 `lengthCodeAt` 可以任意给，
那么把它取成超多项式函数并不等于证明真实 PA/Hilbert proof length
（证明长度）超多项式。真正的数学内容必须体现在 root exactness
（根层精确性）或一个替代的真实 proof-code semantics（证明码语义）里。

本轮新增的直接桥接定理是：

```lean
rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_direct
```

它证明：如果 calibrated checker exactness（校准检查器精确性）成立，
那么必然得到

```text
proof_length(PA, symbolSize, powerBoundRawCode n) = lengthCodeAt(n).
```

所以 exactness（精确性）不是一个小技术条件，而正是把 `lengthCodeAt`
认定为真实 root `proof_length`（根证明长度）的硬条件。该定理的 axiom profile
（公理画像）为：

```text
[proof_length, propext, Classical.choice, Quot.sound]
```

随后本轮用显式模型载体

```text
superPolynomialCanonicalLength(n) = (n+1)^n
```

证明：

```lean
superPolynomialCanonicalLength_searchGap
superPolynomialCanonicalLength_to_noAcceptedCodeSearchTarget
superPolynomialCanonicalLength_to_checkedMeasuredSearchGap
```

这说明 growth layer（增长层）和 adapter layer（适配层）可以完全闭合：一旦
`lengthCodeAt` 本身真的超多项式，就能得到 checked-measured search-gap
（检查测量搜索间隙）。这些模型定理没有 `proof_length`（证明长度）依赖，
axiom profile（公理画像）只有：

```text
[propext, Classical.choice, Quot.sound]
```

但是，本轮也证明了负结论：

```lean
no_superPolynomialCanonicalLength_rootExactness_currentRoot
no_superPolynomialCalibratedCheckerExactness_currentRoot
```

含义是：不能把这个超多项式模型载体接回当前 root `proof_length`
（根证明长度）。当前 root `proof_length` 在 theorem-5 power-bound family
（第五定理幂界族）上已经等于 `scale(n)+12`，是 polynomial bound
（多项式有界）。因此，任何试图让它等于 `(n+1)^n` 的 root exactness
（根层精确性）都会推出矛盾；任何试图让当前 calibrated checker
（校准检查器）对这个超多项式载体 exact（精确）的证明也会推出矛盾。

这就是旧工作的根本问题：

```text
旧路线证明了很多 adapter theorem（适配定理）；
但它没有证明真实 PA/Hilbert proof-code length（证明码长度）超多项式；
它把关键义务停在 lengthCodeAt / exactness / rejection_search 这些接口上。
```

现在已经打开到不能再下沉的形式：

```text
要么重构 root proof_length（根证明长度），把它替换为真实的 PA/Hilbert
minimum proof-code size（最小证明码大小），并证明该真实长度有 Pudlak
super-polynomial lower bound（超多项式下界）；

要么保持 proof-length-free checked-measured route（无证明长度公设的检查测量路线），
直接从 checker/verifier/extractor（检查器/验证器/抽取器）证明
SizeFilteredNoAcceptedCodeSearchClosureTarget（按大小过滤的无接受证明码搜索闭合目标）。
```

这不是已经完成无条件 Pudlak lower bound（Pudlak 下界）的证明；但它把旧包装
完全拆开了：adapter（适配）已经干净，growth model（增长模型）已经干净，
剩余唯一硬核义务是真实 PA/Hilbert no-small-proof theorem
（无小证明定理）。

## 15. 本轮新增：当前 concrete checker 的 native-size 反证

上一节只说明：不能把任意给定的超多项式 `lengthCodeAt`（长度函数）接回当前
root `proof_length`（根证明长度）。本轮又把旧工作再向下查了一层，得到一个更
硬的结论：当前 concrete PA/Hilbert checker（具体 PA/Hilbert 检查器）的
native size（原生大小）本身也不能承载 Pudlak lower bound（Pudlak 下界）。

代码中的关键定义是：

```lean
concretePAHilbertPowerBoundProofObject scale_data code
```

它把任意 `code` 解码成一个 proof object（证明对象）：

```text
steps      = [code],
conclusion = powerBoundRawCode(code).
```

因此对每个 `n`，Lean 已经有显式接受证明码：

```lean
concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
```

含义是：

```text
code n is an accepted proof code for powerBoundRawCode(n)
（代码 n 是 powerBoundRawCode(n) 的可接受证明码）。
```

同时，native checker semantics（原生检查器语义）定义为：

```text
Code = Nat,
checks = accepted proof code relation,
size = id.
```

也就是说，proof code（证明码）`n` 的 size（大小）就是 `n`。于是当前对象的
checked measured minimum（检查测量最小值）满足：

```lean
nativePowerBoundCheckedMeasured_le_index
```

即：

```text
M(n) <= n.
```

所以它是 polynomially bounded（多项式有界）的：

```lean
nativePowerBoundCheckedMeasured_polynomial
```

进一步，Lean 证明：

```lean
no_nativePowerBoundCheckedMeasuredSearchGap
```

意思是：当前 native checked measured object（原生检查测量对象）不可能拥有
`ComputableSearchGapCertificate`（可计算搜索间隙证书）。原因很直接：一个
已经满足 `M(n) <= n` 的函数，不可能 eventually dominate every polynomial
（最终支配任意多项式）。

同一件事也在 size-filtered no-accepted-code route（按大小过滤的无接受证明码
路线）里被证明为不可能：

```lean
no_nativeIdentityNoAcceptedCodeSearchTarget
```

含义是：如果 calibrated size（校准大小）取 native numeric size（原生数值大小）
`id`，那么 no accepted code below every polynomial cutoff（每个多项式截断以下
无接受证明码）这个目标直接矛盾。因为 canonical accepted proof code（规范接受
证明码）就是 `n`，它总在大小 `n` 处出现。

这说明旧工作的根本问题比“缺一个参数闭合”更深：

```text
当前 concrete checker 把 theorem-5 power-bound formula family
（第五定理幂界公式族）做成了可由 code n 一步接受的对象；
因此它不是一个能表达真实 PA/Hilbert no-small-proof theorem
（无小证明定理）的 proof-code semantics（证明码语义）。
```

所以不能在这个 native checker（原生检查器）上继续寻找下界证明。真正要关闭
Pudlak 侧黑盒，只剩一个可行方向：

```text
重构 checker/proof-object semantics（检查器/证明对象语义），
去掉 steps = [code] 这种直接接受目标公式的短证明通道；
然后在新的真实 PA/Hilbert proof-code semantics（证明码语义）上，
形式化 Pudlak no-small-proof theorem（无小证明定理）。
```

换句话说，本轮已经完全打开了旧路线的问题：adapter（适配器）不是主要障碍，
`tail_gap`（尾部间隙）也不是单纯缺少下沉；当前底层 concrete checker
（具体检查器）自身有短证明通道。若不替换这层语义，Pudlak lower bound
（Pudlak 下界）在该对象上不是未证明，而是形式上为假。

## 16. 修正后的闭合目标：canonical CnBox 语义 PA 长度

本轮继续检查 bounded arithmetic sidecar（有界算术侧库）后，找到了比旧
`concretePAHilbertPowerBoundChecker`（具体 PA/Hilbert 幂界检查器）更正确的
下界承载对象：

```text
canonicalCnBoxPABox.length(n)
  = semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n).
```

Lean 中新增定理：

```lean
correctedCanonicalCnBoxPABox_length_eq_semanticFiniteConsistency
```

它说明 corrected target（修正目标）测量的是 finite-consistency formula family
（有限一致性公式族）在 PA proof-object semantics（PA 证明对象语义）下的 semantic
minimum proof length（语义最小证明长度），不是旧 native checker（原生检查器）
的 `code n` 一步接受长度。

因此，本轮把真正应该闭合的 Pudlak lower-bound target（Pudlak 下界目标）改写为：

```lean
CorrectedCanonicalCnBoxLowerBoundClosureTarget
```

展开后就是：

```text
存在 lower_source : BussPudlakTheorem5PALowerBoundSource
以及 calibration : CanonicalRelabeledPudlakCalibration lower_source.
```

其中：

```text
BussPudlakTheorem5PALowerBoundSource（Buss/Pudlak 第五定理 PA 下界来源）
  承载真正的 EventualLowerBound（最终下界）；

CanonicalRelabeledPudlakCalibration（规范重标定 Pudlak 校准）
  把外部 Pudlak 公式族按语义重标定到 canonical CnBox PA box
  （规范 CnBox PA 盒子）上，并给出长度相等。
```

Lean 已经证明：

```lean
correctedCanonicalCnBoxLowerBoundClosureTarget_to_gap
correctedCanonicalCnBoxLowerBoundClosureTarget_to_eventualLowerBound
```

也就是说，一旦这个 corrected closure target（修正闭合目标）给出，canonical
proof-length gap（规范证明长度间隙）和 collision kernel（碰撞核）所需的
`EventualLowerBound`（最终下界）都会机械推出。该层 axiom profile（公理画像）为：

```text
[propext, Classical.choice, Quot.sound]
```

没有 `proof_length`（证明长度）公设，也没有旧项目级 `tail_gap`
（尾部间隙）输入。

同时，Lean 也证明：

```lean
no_correctedCanonicalExactConstructorCalibration
```

含义是：不能要求 exact constructor equality（精确构造子相等）

```text
rescaledExternalPudlakCode(...) = partialConsistencyCode(n).
```

因为 bounded sidecar（有界算术侧库）里 `externalPudlakCode`（外部 Pudlak 码）
和 `partialConsistencyCode`（部分一致性码）是故意不同的 constructors（构造子）。
所以可行路线不是“构造子硬相等”，而是：

```text
SemanticFormulaRelabeling（语义公式重标定）
+ length_eq（长度相等）
+ Buss/Pudlak lower source（Buss/Pudlak 下界来源）。
```

当前状态因此更加精确：

```text
旧 concrete checker route（具体检查器路线）已经被反证；
修正后的 canonical CnBox route（规范 CnBox 路线）已经接出正确目标；
剩余硬缺口是构造或内化
  BussPudlakTheorem5PALowerBoundSource
  + CanonicalRelabeledPudlakCalibration。
```

如果允许引用文献 Pudlak theorem 5（Pudlak 第五定理）作为外部数学输入，那么这
一层可以作为清晰的 paper assumption（论文假设）或 literature theorem import
（文献定理导入）来写；如果目标是 Lean 内部完全无外部下界输入，那么后续必须
形式化 Buss/Pudlak/Friedman no-small-proof theorem（无小证明定理）本身。

本轮随后又把这个目标再缩小了一步。Lean 新增：

```lean
boundedLowerSourceOfRootStrongRescaled
boundedLowerSourceFromRootLiterature
boundedLowerSourceFromRootLiterature_scale_eq
boundedLowerSourceFromRootLiterature_pa_length_eq
```

其作用是：把 EulerLimit root side（EulerLimit 根侧）已有的

```text
literaturePudlakTheorem5ExternalScaleData
literaturePudlakTheorem5ExternalRescaledLowerBound
```

转换成 bounded sidecar（有界算术侧库）里的

```text
BussPudlakTheorem5PALowerBoundSource.
```

这不是证明文献 theorem 5（第五定理）本身；它只是把已有 root literature lower
bound（根侧文献下界）读成 bounded sidecar 的 lower-source interface
（下界来源接口）。探针显示该桥的 axiom profile（公理画像）正是：

```text
[literaturePudlakTheorem5ExternalRescaledLowerBound,
 literaturePudlakTheorem5ExternalScaleData,
 proof_length,
 propext,
 Classical.choice,
 Quot.sound]
```

因此当前剩余缺口进一步变成：

```lean
RootLiteratureCanonicalCnBoxCalibrationTarget
```

也就是：

```text
存在 CanonicalRelabeledPudlakCalibration
  boundedLowerSourceFromRootLiterature.
```

Lean 已证明：

```lean
rootLiteratureCanonicalCalibration_to_correctedClosureTarget
rootLiteratureCanonicalCalibration_to_gap
```

所以只要完成这一条 canonical relabeling/length calibration（规范重标定/长度校准），
Pudlak 下界侧就会沿 corrected CnBox route（修正 CnBox 路线）闭合。现在的真实硬点
不再是抽象 `lower_source`（下界来源），而是以下等式/语义对应：

```text
root literature proof length on the rescaled external Pudlak family
（根侧文献重标定外部 Pudlak 族证明长度）

=

semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n)
（PA 公理下有限一致性公式的语义证明长度）。
```

这就是下一刀的位置。

## 17. 下一刀后的结论：当前 CnBox 终点仍是玩具语义，不能直接承载下界

继续向下打开 `RootLiteratureCanonicalCnBoxCalibrationTarget`（根文献到规范
CnBox 校准目标）后，Lean 探针给出了一个更根本的结论：当前
`semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n)`（PA 公理下有限一致性
公式的语义证明长度）还不是文献意义上的 PA 最短证明长度。

原因是 bounded arithmetic sidecar（有界算术侧库）里的

```lean
finiteConsistencyFormula n
```

目前定义为一个 uninterpreted atom（未解释原子标签）：

```text
BAFormula.atom FormulaFamily.partialConsistency n.
```

而当前 `PAAxiom`（PA 公理谓词）只包含若干玩具结构公理，例如等号自反、加零、
乘零、长度零、smash 单调、归纳模式占位、polytime definability（多项式时间可定义性）
占位等；它没有把这个原子标签解释成真正的 finite consistency sentence（有限一致性
句子），也没有任何公理能直接推出该原子。

本轮新增一个 audit truth interpretation（审计真值解释）：

```lean
currentToyBAFormulaAuditTruth
currentToyPAAxiom_auditTruth
currentToyPADerivation_auditTruth
```

它把所有当前 PA 结构公理解释为真，同时把 project atom（项目原子标签）解释为假。
Lean 由此严格证明：

```lean
no_currentToyPADerivation_finiteConsistencyFormula
no_currentToyPAProofObject_finiteConsistencyFormula
```

含义是：在当前 toy PA calculus（玩具 PA 演算）里，不存在
`finiteConsistencyFormula n` 的 `BAProofObject PAAxiom`（PA 证明对象）。

同一组探针还证明：

```lean
no_currentToyPADerivation_contradictionFormula
currentToyPAFiniteConsistencyStatement_all
```

这揭示了 same-object bridge（同一对象桥）里的另一层误读风险：
`PAFiniteConsistencyStatement n`（PA 有限一致性命题）在当前 toy calculus（玩具演算）
中只是

```text
没有大小 <= n 的 toy PA proof object（玩具 PA 证明对象）证明 falsum（假）。
```

由于当前 toy PA axioms（玩具 PA 公理）本来就不能推出 `falsum`，这个命题对所有
`n` 都平凡成立。它并不等价于“PA 证明了有限一致性公式”，更不提供 Pudlak theorem
5（Pudlak 第五定理）需要的 proof-length lower bound（证明长度下界）。

进一步，Lean 证明：

```lean
currentToySemanticBAProofLength_finiteConsistency_eq_zero
currentToyCanonicalCnBoxPABox_length_eq_zero
no_currentToyCanonicalCnBoxProofLengthGap
```

也就是说，当前语义下

```text
canonicalCnBoxPABox.length(n) = 0,
```

所以它不可能满足 Pudlak 所需的 all-polynomial proof-length gap（对任意多项式上界
的证明长度间隙）。这些 no-go probe（反向探针）的 axiom profile（公理画像）为：

```text
[propext, Classical.choice, Quot.sound]
```

没有使用外部 Pudlak theorem 5（Pudlak 第五定理）输入，也没有使用项目级
`tail_gap`（尾部间隙）或 `proof_length`（证明长度）黑盒。

于是 Lean 又得到：

```lean
no_rootLiteratureCanonicalCnBoxCalibrationTarget_currentToySemantics
```

含义是：只要 CnBox 终点仍解释为当前 toy `BAProofObject PAAxiom`（玩具 PA 证明对象）
语义，根侧文献下界就不能校准到该终点。这里不是缺一个 wrapper（包装器），而是目标
公式语义没有真正接到 PA proof-code semantics（PA 证明码语义）。

因此，旧工作的真实问题现在被完全打开为两层：

```text
1. old native checker route（旧原生检查器路线）
   有 code n 的短接受通道，形式上不可能承载 Pudlak 下界；

2. corrected canonical CnBox route（修正规范 CnBox 路线）
   避开了短接受通道，但当前 finiteConsistencyFormula 只是未解释原子，
   toy PA semantics 下没有证明对象，语义长度塌成 0。
```

真正要闭合下界黑盒，必须重构或补全以下对象之一：

```text
A. 把 finiteConsistencyFormula n 细化成真实 PA 语言中的有限一致性公式，
   并给出 PA proof-code semantics（证明码语义）、编码、验证器和长度定义；

B. 或者建立一个严谨的 bridge theorem（桥定理），证明 bounded sidecar 的
   semanticBAProofLength 与文献 PA proof_length 是同一个最短证明长度对象。
```

在这一步完成前，不能把 `RootLiteratureCanonicalCnBoxCalibrationTarget` 写成已关闭。
它现在已经被精确定位为：真实 PA 有限一致性公式语义与当前 CnBox toy endpoint
之间的对象级语义缺口。

## 18. 更根部的 no-go：当前 root proof_length 与文献下界输入不相容

继续向 EulerLimit root side（EulerLimit 根侧）下钻后，Lean 又证明了一个更严重的
审计结论：当前 root `proof_length`（根证明长度）定义本身也不能承载文献 Pudlak
theorem 5（Pudlak 第五定理）输入。

当前 `ProofComplexityCore.lean` 中：

```text
proof_length(T, measure, code)
  = rootSemanticProofLength(T, measure, code)
  = rootFormulaCodeSize(T, measure, code).
```

对于文献输入的 rescaled external Pudlak family（重标定外部 Pudlak 族），Lean 新增：

```lean
rootLiteratureRescaledPudlak_currentRootLength_eq_scale_add_twelve
```

其内容是：

```text
proof_length(PA, symbolSize,
  rescaledExternalStrengthenedLowerBoundCode(rawCode, scale, n))
  = scale(n) + 12.
```

由于 `literaturePudlakTheorem5ExternalScaleData`（文献 Pudlak 第五定理尺度数据）自身
包含：

```text
scale_polynomial_bound
```

Lean 进一步证明：

```lean
rootLiteratureRescaledPudlak_currentRootLength_polynomial
```

即该 root proof_length measured family（根证明长度测量族）是 polynomially bounded
（多项式有界）的。

但是 `literaturePudlakTheorem5ExternalRescaledLowerBound`（文献重标定下界）断言同一个
测量族满足：

```text
StrongProofLengthLowerBound
```

也就是 eventually beats every polynomial（最终超过任意多项式）。这与多项式有界性
直接冲突。Lean 已证明通用引理：

```lean
no_strongProofLengthLowerBound_of_currentMeasuredPolynomial
```

并由此得到：

```lean
no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot
literaturePudlakTheorem5External_currentRoot_contradiction
```

第二个定理的 axiom profile（公理画像）为：

```text
[literaturePudlakTheorem5ExternalRescaledLowerBound,
 literaturePudlakTheorem5ExternalScaleData,
 proof_length,
 propext,
 Classical.choice,
 Quot.sound]
```

这不是证明数学上 Pudlak theorem 5（Pudlak 第五定理）错误，而是证明当前项目里的
root `proof_length` 定义太弱：它只是 formula-code size（公式码大小），不是 PA
minimum proof length（PA 最小证明长度）。

因此，当前下界缺口已经被压到真正根部：

```text
必须先重构 EulerLimit/ProofComplexityCore.lean：

proof_length
  不能定义为 rootFormulaCodeSize；
  必须由真实 PA proof-code semantics（PA 证明码语义）诱导的最小证明长度给出。
```

换句话说，下一步不是补 `tail_gap`（尾部间隙）、不是补 CnBox `length_eq`
（长度相等），也不是继续加 wrapper（包装器）。下一步必须替换 root proof_length
（根证明长度）的定义，使文献 Pudlak theorem 5 输入落在真实 PA proof-length object
（真实 PA 证明长度对象）上。否则文献下界输入与当前 root 定义会直接推出 `False`。

## 19. 旧 proof-length-free 路线的问题：rejectionExtractor 不是自动闭合

对之前围绕 `tail_gap`（尾部间隙）替换做过的工作重新检查后，核心问题可以更精确地
说成：

```text
tail_gap 被移出 theorem surface（定理表面）
≠ Pudlak lower bound（Pudlak 下界）已经被证明。
```

旧的 Month 12 proof-length-free candidate（无证明长度候选）把对象换成：

```text
checkerSemantics（检查器语义）
finiteEnumeration（有限枚举）
rejectionExtractor（拒绝抽取器）
acceptedCodeExactness（接受码精确性）
```

其中真正承载下界力量的是 `rejectionExtractor`。它要求：对任意 polynomial upper
（多项式上界）`U`，找到 witness（见证）和 cutoff（截断），使 cutoff 大于
`U(witness)`，并且所有枚举到的 cutoff 以下证明码都不能接受目标公式。这已经等价于
一种 no-small-proof-code theorem（无小证明码定理），不是普通工程接线。

为避免继续被 wrapper（包装器）绕住，Lean 新增了两个通用 no-go probe（反向探针）：

```lean
no_checkerRejectionExtractor_of_checkedMeasured_polynomial
no_checkerRejectionExtractor_of_minProofCodeSizeAt_polynomial
```

第一个定理说：

```text
如果 checker 侧 measured minimum accepted proof-code size
（测量后的最小接受证明码大小）
是 polynomially bounded（多项式有界），
那么不存在 InternalPudlakTheorem5CheckerComputableRejectionExtractor
（Pudlak 第五定理检查器可计算拒绝抽取器）。
```

第二个定理把同一结论改写成旧代码里更常见的形式：

```text
如果 checker.minProofCodeSizeAt(n) 是多项式有界，
那么 rejectionExtractor 不可能存在。
```

这两个定理的 axiom profile（公理画像）都是：

```text
[propext, Classical.choice, Quot.sound]
```

没有 `tail_gap`，没有 `proof_length`，没有文献 Pudlak 输入，也没有项目级残留公设。

因此，旧工作的实际问题已经完全打开：

```text
1. proof-length-free candidate 只是把 root proof_length 暂时拿掉；
2. 它仍然需要 rejectionExtractor；
3. rejectionExtractor 本身只有在最小接受证明码长度超多项式时才可能存在；
4. 对 native powerBound checker（原生 powerBound 检查器），存在短接受码 n，
   所以它的 measured minimum 至多为 n，必然多项式有界；
5. 因此 native checker 不能承载 Pudlak 下界。
```

这说明“把 tail_gap 换成 rejection_search”不是闭合，而只是把证明义务移到了更清楚的
位置。现在这个位置已经被 Lean 形式化为：

```text
必须证明真实 PA theorem-5 formula family（真实 PA 第五定理公式族）的
minimum accepted proof-code size（最小接受证明码大小）
不是多项式有界，并且最终超过任意多项式。
```

换成一句话：

```text
下界盒子不能靠接口关闭，只能靠真实 PA proof-code semantics（PA 证明码语义）和
真实 no-small-proof-code theorem（无小证明码定理）关闭。
```

## 20. external PA/Hilbert 校准桥的当前退化

继续审计后，Lean 又打开了一个旧路线里容易误判的点：

```lean
externalPAHilbertProofLength_eq_localChecked
```

这个命名公设把 root PA `proof_length`（根 PA 证明长度）接到 local checked proof length
（本地已检查证明长度）。但当前 root `proof_length` 已经被定义成
`rootFormulaCodeSize`（根公式码大小）。因此该桥并不会产生真实 PA proof-code semantics
（PA 证明码语义），而是会把本地 checked length（已检查长度）压成公式码大小。

Lean 新增：

```lean
externalPAHilbertProofLength_eq_localChecked_forces_rootFormulaCodeSize
externalPAHilbertProofLength_eq_localChecked_forces_partialConsistency_linear
externalPAHilbertProofLength_eq_localChecked_forces_reflectionGraft_linear
```

具体结论是：

```text
partialConsistencyCode(m)    的 checked 长度 = m + 11,
sondowReflectionGraftCode(m) 的 checked 长度 = m + 13.
```

这两个是线性的，不能承载 Pudlak theorem 5（Pudlak 第五定理）的超多项式下界。

所以，`externalPAHilbertProofLength_eq_localChecked` 不是闭合证明缺口；它只是暴露了
同一个根问题：

```text
必须把 root proof_length 从 formula-code size（公式码大小）
换成真实 PA proof-code semantics 诱导的最小证明码长度。
```

## 21. 旧路线复查后的最终边界

现在可以把旧路线的问题分成三类。

第一类是已经打开并且可信的 adapter theorem（适配定理）：

```text
tail_gap -> search gap（搜索间隙）
rejection_search -> no accepted code below cutoff（截断以下无接受码）
no accepted code search -> checked measured gap（检查测量间隙）
super-polynomial canonical carrier -> size-filtered search closure
（超多项式规范载体推出按大小过滤的搜索闭合）
```

这些部分可以留下。它们不是漏洞，而是把 collision proof（碰撞证明）需要的接口做清楚。

第二类是已经被 Lean 反证的错误闭合路线：

```text
当前 root proof_length（根证明长度）路线：太小，只有 formula-code size（公式码大小）；
native concrete checker（原生具体检查器）路线：太小，有 code n 这种短接受码；
toy CnBox PA semantics（玩具 CnBox PA 语义）路线：太弱，有限一致性公式不是真实可导出对象；
external PA/Hilbert bridge（外部 PA/Hilbert 桥）路线：在当前 root 定义下退化成线性长度。
```

对应 Lean 探针已经通过：

```lean
no_actualProofLengthSearchGapTarget_currentRoot
no_nativePowerBoundCheckedMeasuredSearchGap
no_currentToyCanonicalCnBoxProofLengthGap
no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot
externalPAHilbertProofLength_eq_localChecked_forces_partialConsistency_linear
externalPAHilbertProofLength_eq_localChecked_forces_reflectionGraft_linear
```

第三类才是尚未完成的根证明：

```text
构造真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义），
并证明 theorem-5 target family（第五定理目标公式族）的
minimum accepted proof-code size（最小接受证明码大小）
最终超过任意 polynomial upper（多项式上界）。
```

这不是 Lean 接口问题，而是核心数学下界。所有旧包装最终都回到它：

```text
tail_gap（尾部间隙）需要它；
rejectionExtractor（拒绝抽取器）需要它；
proof_length exactness（证明长度精确性）需要它；
root theorem-5 lower bound（根第五定理下界）也需要它。
```

所以后续推进的硬目标应写成：

```text
RealPAProofCodeSemantics + Theorem5NoSmallProofCode
  -> ComputableSearchGapCertificate(real PA min proof-code size)
  -> collision contradiction.
```

其中 `Theorem5NoSmallProofCode`（第五定理无小证明码）不能再作为裸参数出现；它必须
要么被 Lean 内部证明，要么被明确标注为外部文献定理并给出可审计的 calibration
（校准）到本项目的 proof-code semantics（证明码语义）。

## 22. 进一步压实：现有 theorem-5 core 在当前 root 下不可存在

本轮新增 Lean 探针把边界再往根部推进了一层。以前可以说：

```text
tail_gap（尾部间隙）还没有关闭；
rejectionExtractor（拒绝抽取器）仍是下界内容；
proof_length exactness（证明长度精确性）仍是硬条件。
```

现在可以更强地说：

```text
在当前 root proof_length（根证明长度）定义下，
任何 theorem-5 lower-bound core（第五定理下界核心）都不可能存在。
```

新增 Lean 定理包括：

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

这些 theorem（定理）覆盖从最抽象的 `LowerBoundCore`（下界核心），到
`ProofCodeSemanticsCore`（证明码语义核心），再到
`ComputableFiniteSearchNoSmallCore`（可计算有限搜索无小码核心）的整条旧包装链。

证明依赖的关键事实是：

```lean
actualProofLengthMeasured_currentRoot_eq_scale_add_twelve
actualProofLengthMeasured_currentRoot_polynomial
no_strongProofLengthLowerBound_of_currentMeasuredPolynomial
```

含义是：

```text
当前 root proof_length 在 theorem-5 power-bound raw family（第五定理幂界原始公式族）
上只是 scale(n) + 12。

scale(n) 是 polynomially bounded（多项式有界）。

所以这个长度族不可能同时满足 StrongProofLengthLowerBound（强证明长度下界）。
```

这说明旧工作最大的问题不是缺少某个小 lemma（小引理），而是 root semantics
（根语义）选错了：当前 root 把证明长度压成公式码大小，天然杀死 Pudlak 下界。

后续真正闭合路线必须先完成：

```text
root proof_length semantic replacement（根证明长度语义替换）
```

然后再证明或严格导入：

```text
real PA/Hilbert theorem-5 no-small-proof-code lower bound
（真实 PA/Hilbert 第五定理无小证明码下界）
```

否则任何 core/checklist（核心/清单）形式的“闭合”都会和当前 root 定义矛盾。

## 23. 现有 concrete PA/Hilbert checker 的短码障碍

为了确认是否能直接用项目里已有的 PA/Hilbert checker（PA/Hilbert 检查器）替换 root
`proof_length`（根证明长度），本轮继续审计了 Month 11 checker surface
（第 11 月检查器表面）。

结论是：不能直接用。

原因是当前 concrete power-bound checker（具体幂界检查器）已经证明：

```lean
concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
```

即：

```text
对每个 n，numeric code（数字码）n 已经是 powerBoundRawCode(n) 的 accepted proof code
（接受证明码）。
```

因此新增 Lean 定理：

```lean
no_concretePAHilbertPowerBound_noSmallAccepted_at_succ
no_concretePAHilbertPowerBound_noSmallProofCodeForFormulaCode_at_succ
```

第一条说明：

```text
bound = n + 1 时，不可能说没有 accepted proof code（接受证明码）低于 bound，
因为 code n 已经被接受。
```

第二条说明同一事实在 decoded proof-object level（解码证明对象层）也成立：

```text
按 formula code（公式码）看的 no-small-proof-code（无小证明码）也不可能成立。
```

这一步很关键：它排除了一个看似自然的修补方案：

```text
把 root proof_length 直接接到当前 concretePAHilbertPowerBoundChecker。
```

这个方案会失败，因为该 checker 的最小接受码长度至多是 `n`，仍然多项式有界。

所以真正 root replacement（根替换）不能复用这个短码 checker。它必须换成真实
PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）：

```text
proof object（证明对象）必须编码完整 PA/Hilbert 推导；
acceptance（接受）必须表示该推导真的推出目标公式；
size（大小）必须测量完整证明码大小；
theorem-5 lower bound（第五定理下界）必须证明这些完整证明码没有多项式上界。
```

## 24. 根替换目标的精确定义

现在 root replacement（根替换）不再只是口头方向。Lean 中新增：

```lean
RealPAHilbertRootReplacementTarget
```

它被定义为：

```text
Nonempty PAHilbertCheckerExactnessCore
```

这里 `PAHilbertCheckerExactnessCore`（PA/Hilbert 检查器精确性核心）已经是项目当前
最强的真实检查器目标。它同时包含：

```text
checker（检查器）
semantics（语义）
proof-code semantics（证明码语义）
bridge from semantic proof code to accepted PA/Hilbert numeric code
（从语义证明码到 PA/Hilbert 接受数字码的桥）
finite small-code enumeration（有限小码枚举）
computable search exclusion（可计算搜索排除）
theorem-5 computable finite-search no-small-code core
（第五定理可计算有限搜索无小码核心）
```

但 Lean 同时证明：

```lean
no_paHilbertCheckerExactnessCore_currentRoot
no_realPAHilbertRootReplacementTarget_currentRoot
```

也就是说：

```text
在当前 root proof_length = formula-code size（根证明长度等于公式码大小）下，
这个最强 root replacement target（根替换目标）也不可能存在。
```

这说明下一步的工程顺序已经不能再颠倒：

```text
必须先改 root proof_length（根证明长度）的定义；
不能先构造 PAHilbertCheckerExactnessCore 再接当前 root。
```

改完 root 之后，`PAHilbertCheckerExactnessCore` 才是正确目标；它一旦构造出来，就能通过
已有 Lean 接口投影到：

```lean
InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
```

再给出 collision proof（碰撞证明）需要的 lower-search gap（下界搜索间隙）。

## 25. 本轮复核：旧工作的问题和已经完全打开的层

本轮重新检查此前围绕 lower-bound（下界）、tail_gap（尾部间隙）、
rejection_search（拒绝搜索）、proof_length（证明长度）做过的工作后，结论更清楚：

```text
旧工作不是完全无效；
旧工作的问题是把若干真正硬义务推进到了更底层名字里，
但有些名字仍被误读成已经完成的证明。
```

Lean 中新增：

```lean
currentLowerBoundRouteObstructionLedger
```

它把三条独立障碍合成一个可检查台账：

```text
1. 当前 actualProofLengthMeasured（实际证明长度测量）是 polynomially bounded
   （多项式有界），所以不能有 all-polynomial search gap（任意多项式搜索间隙）；

2. 当前 concrete power-bound checker（具体幂界检查器）有短 accepted code（接受码）n，
   所以它不能承载 theorem-5 no-small-code lower bound（第五定理无小码下界）；

3. 当前 toy CnBox PA semantics（玩具 CnBox PA 语义）上 canonical CnBox length
   （规范 CnBox 长度）为 0，所以也不能承载 EventualLowerBound（最终下界）。
```

这三条说明：不能再把问题归结为“tail_gap 还没有接线”。真正的问题是 root proof-length
semantics（根证明长度语义）和 checker semantics（检查器语义）还没有替换成真实
PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）。

本轮又把第三条进一步压实为三条 Lean 反证：

```lean
no_currentToyCanonicalCnBoxEventualLowerBound
no_canonicalRelabeledPudlakCalibration_currentToySemantics
no_correctedCanonicalCnBoxLowerBoundClosureTarget_currentToySemantics
```

含义是：

```text
当前 toy BAProofObject PAAxiom（玩具 PA 证明对象）语义下，
canonicalCnBoxPABox（规范 CnBox PA 盒子）的 length（长度）恒等于 0；
因此它不仅没有 proof-length gap（证明长度间隙），
连 EventualLowerBound（最终下界）本身也没有。
```

更强地说，任何 `CanonicalRelabeledPudlakCalibration`
（规范重标定 Pudlak 校准）都不能在当前 toy semantics（玩具语义）上成立。
所以问题不在于换一个 lower_source（下界来源），而在于必须替换 toy PA proof-code
semantics（玩具 PA 证明码语义）本身。

## 26. 正向层：proof-length-free lower-gap 已经打开

本轮也新增了一个正向的最小目标：

```lean
ProofLengthFreeLowerGapClosureTarget
```

它只包含：

```text
ProofCodeSemantics（证明码语义）
SmallCodeSearch（小码搜索）
ComputableFiniteSearchExclusion（可计算有限搜索排除）
```

然后 Lean 证明：

```lean
proofLengthFreeLowerGapClosureTarget_to_checkedMeasuredSearchGap
```

含义是：

```text
只要给出 proof-code semantics（证明码语义）、
finite small-code search（有限小码搜索）、
computable finite-search exclusion（可计算有限搜索排除），
Lean 就能机械构造 checked measured search gap（检查测量搜索间隙）。
```

这一步没有使用：

```text
tail_gap（尾部间隙）
root proof_length（根证明长度）
proof-length exactness（证明长度精确性）
literature Pudlak axiom（文献 Pudlak 公设）
```

对应 probe（探针）显示：

```text
proofLengthFreeLowerGapClosureTarget_to_checkedMeasuredSearchGap
depends on axioms: [propext, Classical.choice, Quot.sound]
```

因此，现在“打开黑盒”后的真实形状是：

```text
proof-code semantics + finite search + computable exclusion
  -> checked measured gap
```

这层已经是透明 adapter theorem（适配器定理），不是 `tail_gap` 的换名。

## 27. 最后一刀：root exactness 是唯一剩余接口

为了防止继续把 root proof_length（根证明长度）藏在别处，本轮新增：

```lean
ProofLengthFreeSourceRootExactness
```

它的意思是：

```text
对每个 n，
project root proof_length(PA, symbolSize, powerBoundRawCode n)
等于 proof-length-free source（无根证明长度源）里的 checked measured length
（检查测量长度）。
```

然后 Lean 证明：

```lean
proofLengthFreeSource_and_rootExactness_to_actualProofLengthGap
```

即：

```text
proof-length-free checked gap（检查间隙）
+ root exactness（根精确性）
=> actual proof-length gap（实际证明长度间隙）
```

同时 Lean 证明：

```lean
no_proofLengthFreeSourceRootExactness_currentRoot
```

含义是：

```text
在当前 root proof_length = formula-code size（根证明长度等于公式码大小）下，
任何 proof-length-free source（无根证明长度源）都不可能同时满足 root exactness
（根精确性）。
```

这就是本轮“釜底抽薪”的结果：剩余缺口不再散落在 tail_gap / rejection_search /
lengthCodeAt / exactness 这些名字里。它被压缩成一个不可绕开的数学任务：

```text
构造真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义），
证明 theorem-5 computable finite-search exclusion（第五定理可计算有限搜索排除），
并把 root proof_length（根证明长度）定义替换为该语义诱导的最小证明码长度。
```

如果不替换当前 root proof_length（根证明长度），Lean 已经证明这条线不可能闭合。

## 28. 本轮新增：根闭合 theorem-5 目标已经完全打开

为了避免再把下界义务藏在新的 bundle（打包对象）里，本轮在 Lean 中新增了一个最小
root-closed target（根闭合目标）：

```lean
RootClosedTheorem5LowerBoundWitness
RootClosedTheorem5LowerBoundTarget
```

其中 witness（见证）只有两项：

```text
source    : PAHilbertProofLengthFreeLowerGapSource
            （PA/Hilbert 无根证明长度下界源）

rootExact : ProofLengthFreeSourceRootExactness source
            （该下界源和项目 root proof_length 的逐点精确相等）
```

这说明旧工作的问题已经被压缩到一个不能再包装的形状：

```text
proof-code semantics（证明码语义）
+ small-code search（小码搜索）
+ computable finite-search exclusion（可计算有限搜索排除）
  -> checked measured gap（检查测量间隙）

checked measured gap（检查测量间隙）
+ root exactness（根精确性）
  -> actual proof-length gap（实际证明长度间隙）
```

Lean 已经证明：

```lean
rootClosedTheorem5LowerBoundTarget_to_actualProofLengthSearchGapTarget
rootClosedTheorem5LowerBoundTarget_to_actualProofLengthPointwiseSearchGapTarget
```

也就是说，一旦这个最小 root-closed target（根闭合目标）成立，实际
`proof_length(PA, symbolSize, powerBoundRawCode n)`（PA 符号大小证明长度）
的 search gap（搜索间隙）和 pointwise witness（逐点见证）都会机械推出。
这里没有再引入 `tail_gap`（尾部间隙）字段。

同时 Lean 也证明：

```lean
no_rootClosedTheorem5LowerBoundTarget_currentRoot
```

含义是：

```text
在当前 root proof_length = formula-code size（根证明长度等于公式码大小）的定义下，
即使把所有 adapter layer（适配层）都打开，最小 root-closed theorem-5 target
（根闭合第5定理目标）仍然不可能成立。
```

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

检查结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 本轮修正：强下界必须加入完备性，避免真空证明

复查后发现，单独的：

```lean
BAProofObjectStrongSizeLowerBound
```

还有一个审计风险。若某个 `target(n)` 根本没有任何 `BAProofObject`
（BA 证明对象），那么：

```text
所有证明对象都大于 U(n)
```

会因为“没有证明对象”而真空为真。这不是有效的 Pudlak 下界；真正需要的是：

```text
每个 target(n) 都有证明对象；
同时小证明对象被排除。
```

因此本轮新增非真空目标：

```lean
BAProofObjectCompleteness
BACompleteProofObjectStrongSizeLowerBound
```

其中：

```text
BAProofObjectCompleteness(Ax, target)
```

表示：

```text
对每个 n，都存在 proof : BAProofObject Ax，
使 proof.conclusion = target(n)。
```

而：

```text
BACompleteProofObjectStrongSizeLowerBound
```

同时包含：

```text
complete（完备性）
strong_lower（强下界）
```

Lean 已证明：

```lean
BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_option
BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_no_eventual
BACompleteProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
BACompleteProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
BACompleteProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
```

所以当前最干净的下界闭合目标应写成：

```text
BACompleteProofObjectStrongSizeLowerBound Ax target
```

而不是单独写：

```text
BAProofObjectStrongSizeLowerBound Ax target
```

本轮还证明了当前 toy finite-consistency 语义不能实例化这个非真空目标：

```lean
no_currentToyBACompleteProofObjectStrongSizeLowerBound_finiteConsistency
```

原因是当前 toy PA calculus（玩具 PA 演算）没有 `finiteConsistencyFormula n`
的证明对象，所以完备性字段已经失败。这防止了“无证明对象导致强下界真空成立”的漏洞。

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean > /tmp/pudlak_lower_complete_strong_probe24.log 2>&1
```

结果：

```text
无 error（错误）
无 warning（警告）
```

新增非真空目标及其下游接线公理剖面仍只含：

```text
[propext, Classical.choice, Quot.sound]
```

没有出现：

```text
proof_length
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

因此，现在可以把“旧工作有什么问题”说清楚：

```text
旧工作完成了很多 adapter theorem（适配定理）；
旧工作没有完成 theorem-5 lower bound（第5定理下界）本身；
旧工作中若要求 checked length = scale（检查长度等于尺度），会因 scale（尺度）
多项式有界而直接矛盾；
旧工作中若使用当前 root proof_length（根证明长度），会因 formula-code size
（公式码大小）多项式有界而直接矛盾；
旧工作中若使用 current toy CnBox semantics（当前玩具 CnBox 语义），长度恒为 0，
也不可能承载 EventualLowerBound（最终下界）。
```

所以“完全打开”后的真正剩余任务不是再展开一层接口，而是替换根部：

```text
用真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）
重新定义或校准 project root proof_length（项目根证明长度），
并在该真实语义上证明 theorem-5 computable finite-search exclusion
（第5定理可计算有限搜索排除）。
```

这一步才是下界盒子的核心数学证明；当前 Lean 文件已经证明，任何不做这一步的
路线都会被当前根定义反证。

## 29. 旧 final exact checker-core input 也已经开盒

继续检查旧 `ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput`
（具体 PA/Hilbert 幂界最终精确检查器核心输入）后，Lean 新增：

```lean
finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundWitness
finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundTarget
no_finalExactCheckerCoreInput_currentRoot
```

这一步的含义很关键。旧 final exact input（最终精确输入）表面上会生成：

```text
canonical calibrated exactness core（规范校准精确性核心）
computable finite-search no-small core（可计算有限搜索无小码核心）
actual proof-length gap（实际证明长度间隙）
```

但打开结构后，它自身已经携带两个关键字段：

```text
proof_length_gap
（实际 root proof_length 的搜索间隙）

proof_length_eq_lengthCodeAt
（root proof_length 与校准长度的逐点相等）
```

所以它不是 theorem-5 lower bound（第5定理下界）的从零证明；它是把核心下界已经作为
输入放进结构里。Lean 现在把这一点精确化为：

```text
ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
  -> RootClosedTheorem5LowerBoundWitness
```

也就是说，旧 final exact input（最终精确输入）一旦存在，就已经给出了最小
root-closed theorem-5 witness（根闭合第5定理见证）。反过来，在当前
root proof_length = formula-code size（根证明长度等于公式码大小）下，Lean 证明：

```text
Nonempty ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput -> False
```

因此，这条旧路不能被当作“已经闭合的证明”。它只是把最终要证明的 root-closed target
（根闭合目标）换了一个名字放入输入结构；在当前根定义下，该输入结构本身不可能存在。

本轮探针仍为：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 最新核准结论：computable_search_exclusion 还不是最短目标

上面的旧结论说真正需要完成的是 `computable_search_exclusion`（可计算有限搜索排除）。
本轮继续向根部复查后，Lean 已经把它再压缩到更短的目标：

```lean
ShortestCheckedMinProofCodeGrowthObligation
```

它定义上等于：

```lean
CheckedMinProofCodeStrongLowerBound
```

并且 Lean 已证明：

```lean
shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
```

也就是说，当前最短下界义务等价于：

```lean
InternalPudlakTheorem5NoSmallProofCodes
```

纸面上就是：

```text
在真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）中，
minProofCodeSize(powerBoundRawCode n)
最终超过任意 polynomial bound（多项式上界）。
```

这条 Lean-验证过的等价链不含：

```text
proof_length（根证明长度）
tail_gap（尾部间隙）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（加强部分一致性载荷）
```

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果为退出码 0；`rg "error:|warning:|sorryAx"` 无输出。关键公理剖面为：

```text
shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
depends on axioms: [propext, Classical.choice, Quot.sound]
```

因此当前的准确状态是：

```text
形式化突破：
  下界黑盒已经被打开并压缩到 checked minProofCodeSize 强增长。

尚未完成：
  真实 PA/Hilbert proof-code semantics 上的 NoSmallProofCodes 定理本身。
```

## 最新工作基准：checked minProofCodeSize 强增长

本轮复查以前围绕 `tail_gap`（尾部间隙）、`rejection_search`（拒绝搜索）、
`proof_length`（证明长度）和 proof-code semantics（证明码语义）做过的工作后，
Lean 中已经固定了一个最短 root-free（不依赖根证明长度）目标：

```lean
ShortestCheckedMinProofCodeGrowthObligation
```

它的定义只是：

```lean
CheckedMinProofCodeStrongLowerBound
```

所以它不是新的包装公设，而是给当前最终要证明的增长义务取了一个不会混淆的名字。

纸面含义如下。给定真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）
`sem`，要证明：

```text
对任意 polynomial bound（多项式上界）U，
对任意起点 N，
存在 n >= N，使得

sem.minProofCodeSize(powerBoundRawCode n) > U(n).
```

这正是 `tail_gap`（尾部间隙）背后的核心数学内容：不是给一个现成 gap certificate
（间隙证书），而是证明目标公式族的最小接受证明码尺寸本身最终超过任意多项式。

Lean 已证明：

```lean
checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes
shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
```

因此当前最短目标等价于 theorem-5（第5定理）的标准 no-small-proof-code
（无小证明码）形式：

```lean
InternalPudlakTheorem5NoSmallProofCodes
```

这一步的意义是：

```text
tail_gap
  -> NoAcceptedBelowCutoff（截断界以下无接受码）
  -> checked minProofCodeSize strong lower bound
  <-> InternalPudlakTheorem5NoSmallProofCodes
```

已经在 Lean 中打通。也就是说，下界侧现在不需要再把 `tail_gap`、`proof_length_gap`
（证明长度间隙）或 `proof_length` 当作输入来表达主缺口。

本轮探针：

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
proof_length
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

不过必须严格区分两件事：

```text
已经完成：
  Lean 形式化地确认了最短下界目标是什么，并证明它等价于 no-small-proof-code 标准形式。

尚未完成：
  在真实 PA/Hilbert proof-code semantics 上无条件证明这个 no-small-proof-code 定理。
```

所以当前可以说有“根本性形式化突破”：缺口已经被砍到根上，且旧黑盒已经不再是目标本身。
但还不能说下界定理已经完全无条件证明。下一步必须直接证明：

```text
real PA/Hilbert proof-code semantics（真实 PA/Hilbert 证明码语义）
+ verified checker（已验证检查器）
+ finite small-code enumeration（有限小码枚举）
+ Pudlak theorem-5 no-small-proof-code argument（Pudlak 第5定理无小证明码论证）
-> ShortestCheckedMinProofCodeGrowthObligation
```

## 本轮新增：正向 no-small proof-object 下界

上一轮已经把旧 `EventualLowerBound`（最终下界）打开成：

```text
¬ BAEventuallyPolynomialProofObjectFamily
（不存在最终多项式大小证明对象族）
```

本轮继续往根部压缩，把这个否定型命题改写成正向下界命题：

```lean
BAProofObjectStrongSizeLowerBound
```

展开为：

```text
对任意 polynomial upper bound U（多项式上界 U），
对任意起点 N，
存在 n >= N，
使得所有 proof : BAProofObject Ax（BA 证明对象）
只要 proof.conclusion = target n，
就有 U(n) < proof.size。
```

这比“没有最终多项式证明族”的表述更适合证明，因为它直接给出了 theorem-5 lower bound
（第5定理下界）应当构造的 witness（见证）：一个足够晚的 `n`，并证明这个 `n` 上没有
小证明对象。

Lean 已证明：

```lean
BAProofObjectStrongSizeLowerBound_iff_no_eventual_polynomial_proof_family
BAProofObjectStrongSizeLowerBound_iff_BAOptionMinProofSizeBeatsPolynomial
boundedEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
bussPudlakEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
```

并且已经接到下游：

```lean
BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
BAProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
```

所以当前最干净的 Pudlak 侧硬义务已经变成：

```text
证明 BAProofObjectStrongSizeLowerBound Ax target。
```

它一旦完成，会自动推出：

```text
不存在最终多项式证明对象族；
option-valued minimum proof size（可空最小证明大小）超过任意多项式；
checked minProofCodeSize strong lower bound（已检查最小证明码强下界）；
NoAcceptedBelowCutoff（截断界以下无接受码）。
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

新增定理公理剖面仍只含：

```text
[propext, Classical.choice, Quot.sound]
```

没有出现：

```text
proof_length
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

## 本轮新增：把下界盒子完全打开成“无最终多项式证明对象族”

本轮继续检查旧工作，发现旧路线真正的问题可以精确定位为：

```text
BussPudlakTheorem5PALowerBoundSource.lower_bound
```

这个字段不是 Lean 自动证明出来的 theorem（定理），而是一个已经很强的输入字段。它说：

```text
对任意 polynomial bound（多项式上界） f，
对任意起点 N，
存在 n >= N，
使 source.pa_length(n) > f(n).
```

如果不继续打开，这个字段就会把 Pudlak/Buss/Friedman 第5定理的核心下界内容藏起来。现在
Lean 中已经把它打开到证明对象层：

```lean
boundedEventualLowerBound_to_no_eventual_polynomial_proof_family
no_eventual_polynomial_proof_family_to_boundedEventualLowerBound
boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family

bussPudlakLowerSource_to_no_eventual_polynomial_proof_family
bussPudlakEventualLowerBound_iff_no_eventual_polynomial_proof_family
```

含义如下。设 `box.length`（盒子的长度函数）已经校准为：

```text
semanticBAMinProofSizeOption(Ax, target, n) = some k
=> box.length(n) = k.
```

并且每个目标公式都有实际的 `BAProofObject`（有界算术证明对象）。那么：

```text
EventualLowerBound(box)
```

等价于：

```text
¬ BAEventuallyPolynomialProofObjectFamily(Ax, target)
```

也就是：

```text
不存在一个 polynomial bound U（多项式上界 U）和阈值 N，
使得所有 n >= N 的 target(n) 都有 size <= U(n) 的 BAProofObject。
```

这一步把旧 `tail_gap`（尾部间隙）、`rejection_search`（拒绝搜索）和 `lower_bound`
（下界字段）背后的真实数学内容统一成一个清楚命题：

```text
真实下界 = 不存在最终多项式大小的证明对象族。
```

证明结构也很直接：

1. 若 `EventualLowerBound(box)` 成立，而存在多项式大小证明对象族，则取这个多项式 `U`；
   下界给出某个 `n` 使 `box.length(n) > U(n)`。
2. 但证明对象族给出一个 `proof`，其 `proof.size <= U(n)`。
3. `semanticBAMinProofSizeOption`（可空最小证明大小）给出最小值 `some k`，并且
   `k <= proof.size`。
4. 校准给出 `box.length(n) = k`。
5. 得到 `k > U(n)` 且 `k <= proof.size <= U(n)`，矛盾。

反方向使用此前已经证明的等价路线：

```text
¬ BAEventuallyPolynomialProofObjectFamily
=> BAOptionMinProofSizeBeatsPolynomial
=> EventualLowerBound(box).
```

这说明旧 `lower_bound` 字段没有被“换壳包装”，而是已经被解释成了一个准确的
proof-complexity lower-bound theorem（证明复杂度下界定理）。

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean > /tmp/pudlak_lower_source_no_poly_probe22.log 2>&1
```

结果：

```text
无 error（错误）
无 warning（警告）
```

新增等价定理的公理剖面：

```text
boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family
depends on axioms: [propext, Classical.choice, Quot.sound]

bussPudlakEventualLowerBound_iff_no_eventual_polynomial_proof_family
depends on axioms: [propext, Classical.choice, Quot.sound]
```

没有出现：

```text
proof_length
tail_gap
partial_consistency_payload
strengthened_partial_consistency_payload
```

同时复查旧 `PAHilbertCheckerExactnessCore`（PA/Hilbert 检查器精确性核心）发现：

```text
paHilbertCheckerExactnessCore_to_checkedMinProofCodeStrongLowerBound
```

的公理剖面仍带 `proof_length`。原因不是该桥接证明体重新调用了 `proof_length`，而是
`PAHilbertCheckerExactnessCore` 的结构字段中含有
`computable_finite_search_no_small_core`，其内部仍有 `proof_length_model`
（证明长度模型）路径。因此这条旧 core 路线不能作为当前最干净的下界入口。

剩余未闭合点因此不是包装层，而是唯一的硬数学命题：

```text
对真实 PA/Hilbert 目标族，证明
¬ BAEventuallyPolynomialProofObjectFamily。
```

换句话说，下一刀不是再展开接口，而是证明：

```text
不存在最终多项式大小的 PA/Hilbert 证明对象族。
```

## 31. 可空最小证明大小：把下界目标落到真实证明对象

复查旧工作后，最关键的问题不是某个 `tail_gap`（尾部间隙证书）字段没有下沉，
而是多个路线仍然可以在根部绕开真实 proof object（证明对象）：

```text
1. real-valued semantic proof length（实数值语义证明长度）
   用 infimum（下确界）表示最短证明长度；
   当证明集为空时，会落到 empty-infimum convention（空下确界约定）。

2. target-as-axiom（把目标公式直接作为公理）
   会给每个目标制造 1 步证明；
   这不是下界证明，而是直接破坏下界。

3. rejection_search（拒绝搜索）/ tail_gap（尾部间隙）
   如果没有接到真实最小证明对象大小，只是把证明义务换了名字。
```

本轮在 Lean 中新增根语义对象：

```lean
semanticBAMinProofSizeOption
```

它的含义是：

```text
none     表示没有 BAProofObject（有界算术证明对象）；
some k   表示最小证明对象大小为 k。
```

并补上反向语义定理：

```lean
semanticBAMinProofSizeOption_some_to_hasProofOfSize
semanticBAMinProofSizeOption_some_to_exists_proof
semanticBAMinProofSizeOption_some_iff_exists_proof
```

这一步很重要：以后任何下界见证点若写成 `some k`，Lean 都能反推出真的存在
`BAProofObject`（有界算术证明对象）。它不再允许“没有证明”被解释成“证明很长”。

随后在审计文件里定义了正确的下界目标：

```lean
BAOptionMinProofSizeBeatsPolynomial
```

数学含义是：

```text
对任何 polynomial upper bound U（多项式上界）和任何起点 N，
存在 n >= N 和真实最小证明大小 k，
使得 U(n) < k。
```

Lean 还证明了三个边界定理：

```lean
BAOptionMinProofSizeBeatsPolynomial_to_frequently_exists_proof
no_BAOptionMinProofSizeBeatsPolynomial_of_polynomial_upper_bound
no_BAOptionMinProofSizeBeatsPolynomial_of_target_axioms
```

含义分别是：

```text
1. 下界目标一旦成立，就能在任意起点以后给出真实证明对象；
2. 如果最小证明大小被任何 polynomial upper bound（多项式上界）压住，
   则该下界目标不可能成立；
3. 把目标公式直接加入公理会产生常数 1 长度证明，因此也不可能闭合下界目标。
```

对当前 toy PA（玩具 PA）语义，Lean 已证明：

```lean
currentToySemanticBAMinProofSizeOption_finiteConsistency_eq_none
no_currentToyBAOptionMinProofSizeBeatsPolynomial_finiteConsistency
```

这说明当前 toy PA（玩具 PA）根本没有 `finiteConsistencyFormula n`
（有限一致性公式）的证明对象，因此不能作为 Pudlak lower bound（Pudlak 下界）
的闭合语义。

本轮探针：

```text
lake env lean bounded_arithmetic_lab/BoundedArithmeticLab/SemanticProofLength.lean
lake build BoundedArithmeticLab.SemanticProofLength
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
新增定理 axiom profile（公理剖面）只有：
[propext, Classical.choice, Quot.sound]
```

特别地，新增根语义边界定理没有使用：

```text
proof_length（证明长度公设）
tail_gap（尾部间隙）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（强化部分一致性载荷）
```

所以，本轮不是把证明义务往后延，而是把旧路线中两个伪闭合口切掉：

```text
空证明集不能伪装成下界；
目标即公理不能伪装成下界。
```

剩余真正硬核义务现在变成：

```text
构造真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）；
证明目标公式族有真实证明对象；
证明这些真实最小证明对象大小不是 polynomially bounded（多项式有界）。
```

## 32. 正向接线：Option 最小证明大小已经接到 checked min proof-code 下界

上一节把正确的根目标固定为：

```lean
BAOptionMinProofSizeBeatsPolynomial
```

本轮进一步完成正向接线：这个目标现在已经能直接推出 root-free
`CheckedMinProofCodeStrongLowerBound`（检查最小证明码强下界），再推出
`ComputableNoAcceptedBelowCutoff`（截断以下无接受码）。

新增核心定理：

```lean
baProofObjectRootCodeSemantics_minProofCodeSize_eq_option
BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound
BAOptionMinProofSizeBeatsPolynomial_toNoAcceptedBelowCutoff
```

第一条定理的含义是：

```text
如果 semanticBAMinProofSizeOption(Ax, target, n) = some k，
那么对应 root ProofCodeSemantics（根证明码语义）上的
minProofCodeSize(powerBoundRawCode n) 正好等于 k。
```

这一步切掉了旧的 real-valued semanticBAProofLength（实数值语义证明长度）路径。
现在正向路线不再依赖 empty-infimum convention（空下确界约定），而是只在 `some k`
已经给出真实证明对象时才工作。

当前干净下界路线变成：

```text
BAOptionMinProofSizeBeatsPolynomial
  -> CheckedMinProofCodeStrongLowerBound
  -> ComputableNoAcceptedBelowCutoff
  -> checked measured search gap（检查测量搜索间隙）
```

这一段没有使用：

```text
tail_gap（尾部间隙）
root proof_length（根证明长度）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（强化部分一致性载荷）
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

关键 axiom profile（公理剖面）：

```text
baProofObjectRootCodeSemantics_minProofCodeSize_eq_option:
[propext, Classical.choice, Quot.sound]

BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound:
[propext, Classical.choice, Quot.sound]

BAOptionMinProofSizeBeatsPolynomial_toNoAcceptedBelowCutoff:
[propext, Classical.choice, Quot.sound]
```

因此，当前真正未闭合的点已经更窄：

```text
不是 tail_gap；
不是 rejection_search；
不是 root proof_length；
而是要证明真实 PA/Hilbert 或 BA proof-object semantics（证明对象语义）下：

BAOptionMinProofSizeBeatsPolynomial
```

换句话说，只要能在真实目标公式族上证明 option-valued minimum proof-object size
（可空最小证明对象大小）超过任意 polynomial bound（多项式界），Lean 现在已经能把它
接入下界管线。剩余工作不是接线，而是这个超多项式增长定理本身。

## 33. 最短硬义务：不存在最终多项式证明对象族

本轮把上一节的增长目标进一步改写成更直接的 proof family（证明族）命题。

新增定义：

```lean
BAEventuallyPolynomialProofObjectFamily
```

它表示：

```text
存在一个 polynomial bound U（多项式界）和一个 threshold N（阈值），
使得对所有 n >= N，
target(n) 都有一个 BAProofObject（有界算术证明对象），
并且该证明对象大小 <= U(n)。
```

这正是 Pudlak lower bound（Pudlak 下界）要排除的对象。Lean 已证明：

```lean
BAOptionMinProofSizeBeatsPolynomial_to_no_eventual_polynomial_proof_family
no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial
BAOptionMinProofSizeBeatsPolynomial_iff_no_eventual_polynomial_proof_family
```

第三条定理带一个 completeness（完备性）前提：

```text
每个 target(n) 都真的有 BAProofObject。
```

在这个前提下，下面两个命题等价：

```text
1. BAOptionMinProofSizeBeatsPolynomial
   （可空最小证明对象大小超过任意多项式）

2. ¬ BAEventuallyPolynomialProofObjectFamily
   （不存在最终多项式大小证明对象族）
```

本轮还补了最短正向入口：

```lean
no_eventual_polynomial_proof_family_to_checkedMinProofCodeStrongLowerBound
no_eventual_polynomial_proof_family_toNoAcceptedBelowCutoff
```

含义是：

```text
只要证明：

每个 target(n) 有真实证明对象；
不存在最终多项式大小证明对象族；
root code family（根公式码族）是 injective（单射），

就能推出：

CheckedMinProofCodeStrongLowerBound（检查最小证明码强下界）
ComputableNoAcceptedBelowCutoff（截断以下无接受码）。
```

本轮 Lean 探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
```

新增定理 axiom profile（公理剖面）仍然只有：

```text
[propext, Classical.choice, Quot.sound]
```

没有使用：

```text
proof_length（证明长度公设）
tail_gap（尾部间隙）
partial_consistency_payload（部分一致性载荷）
strengthened_partial_consistency_payload（强化部分一致性载荷）
```

因此，当前 Pudlak 侧缺口已经压缩为一个非常清楚的数学断言：

```text
对真实 Ax/target，证明不存在 eventually polynomial-size proof-object family
（最终多项式大小证明对象族）。
```

这不是 wrapper（包装器），也不是接口换名；它是下界定理本体。

## 44. 旧 powerBound checker 的根部 no-go

本轮又补了一个更直接的 Lean 探针：

```lean
no_currentToyBAProofObjectAcceptedNatCodeBridge_concretePowerBound
```

它证明：

```text
当前 concretePAHilbertPowerBoundChecker
（具体 PA/Hilbert 幂界检查器）
不能实例化
BAProofObjectAcceptedNatCodeBridge
（自然数证明码到 BA 证明对象桥）
```

证明逻辑很短：

```text
1. 旧 checker 接受数值码 n 作为 powerBoundRawCode(n) 的证明码；
2. 如果 BAProofObjectAcceptedNatCodeBridge 存在，
   就能从这个 accepted nat code（被接受自然数码）
   抽取一个 BAProofObject PAAxiom
   （PA 公理下的有界算术证明对象）；
3. 目标是 finiteConsistencyFormula(n)
   （有限一致性公式）；
4. 但当前 toy PA calculus（玩具 PA 演算）已经证明没有这种证明对象；
5. 矛盾。
```

所以原来工作的根本问题不是：

```text
缺少一个 adapter（适配器）。
```

而是：

```text
旧 concrete powerBound checker 本身太短；
它把 n 直接当作 powerBoundRawCode(n) 的接受证明码。
因此它不可能承载 Pudlak theorem-5 lower bound
（Pudlak 第5定理下界）。
```

新增探针通过：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
status = 0
```

新增定理公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

没有引入：

```text
proof_length（证明长度）
partial_consistency_payload（部分一致性载荷）
tail_gap（尾部间隙）
```

由此，下界路线现在必须改成下面二选一，不能再回到旧 checker：

```text
路线 A：
真实 PA/Hilbert proof-code semantics
（PA/Hilbert 证明码语义）
+ 真实 theorem-5 lower-bound formalization
（第5定理下界形式化）

路线 B：
真实 BAProofObject encoder/checker
（BA 证明对象编码/检查器）
+ BAProofObjectAcceptedNatCodeBridge
（自然数证明码到 BA 证明对象桥）
+ BussPudlakTheorem5PALowerBoundSource.lower_bound 的内部证明
（Buss-Pudlak 第5定理下界字段的内部证明）
```

当前已经打开到的准确缺口是：

```text
1. lower_bound 仍是 BussPudlakTheorem5PALowerBoundSource 的字段；
2. BAProofObjectAcceptedNatCodeBridge 仍未由真实编码器/检查器构造；
3. 当前 toy PA 语义不能证明 finiteConsistencyFormula(n)，
   所以它不能作为最终下界语义。
```

## 45. 公共证书层也被当前 toy 语义排除

本轮继续把 no-go（不可行结论）向公共 API 层推出。新增 Lean 定理：

```lean
no_projectPublicCollisionCertificateBundle_currentToySemantics
no_projectConcreteCertificateObligation_currentToySemantics
no_nonempty_projectPublicCollisionCertificateBundle_currentToySemantics
no_nonempty_projectConcreteCertificateObligation_currentToySemantics
no_projectPublicCollisionCompletionObligation_currentToySemantics
```

含义是：

```text
在当前 toy PA semantics（玩具 PA 语义）下，
ProjectPublicCollisionCertificateBundle
（项目公共碰撞证书包）
和 ProjectConcreteCertificateObligation
（项目具体证书义务）
都不能被实例化。
```

原因不是 Sondow 侧，而是 Pudlak 下界侧：

```text
公共证书包里有字段：

length_eq :
  lower_source.pa_length(n)
  = semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n)

但当前 toy PA calculus（玩具 PA 演算）已经证明：

semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n) = 0

而 lower_source.lower_bound（下界字段）要求该长度最终超过任意多项式，
特别要超过常数 0。

二者矛盾。
```

这一步的审计意义很大：

```text
不能再把 public certificate bundle（公共证书包）
或 completion obligation（完成义务）
当成已经闭合的下界证明。

它们在当前 toy 语义下反而被 Lean 证明不可存在。
```

新增探针结果：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
status = 0
```

新增公共层 no-go 的公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

没有使用：

```text
proof_length（证明长度）
partial_consistency_payload（部分一致性载荷）
literaturePudlakTheorem5ExternalRescaledLowerBound
（外部 Pudlak 第5定理重标定下界公设）
```

因此后续真正可行路线只剩：

```text
1. 替换 current toy PA semantics（当前玩具 PA 语义）；
2. 构造真实 PA/Hilbert proof-code semantics（证明码语义）；
3. 或构造真实 BAProofObject encoder/checker
   （BA 证明对象编码/检查器）；
4. 在该真实语义中证明 Buss/Pudlak theorem-5 lower_bound
   （Buss/Pudlak 第5定理下界），而不是把它作为字段传入。
```

## 46. 根语义修正：空证明集不能伪装成长度 0

本轮在根库中加入了一个更安全的语义：

```lean
BAHasProofOfSize
semanticBAMinProofSizeOption
semanticBAMinProofSizeOption_none_of_no_proof
semanticBAMinProofSizeOption_some_of_exists_proof
semanticBAMinProofSizeOption_min_le_of_proof
```

位置：

```text
bounded_arithmetic_lab/BoundedArithmeticLab/SemanticProofLength.lean
```

旧定义是：

```lean
semanticBAProofLength : Real
```

它用 real-valued `sInf`（实数下确界）定义证明长度。问题是：

```text
如果某个目标公式没有任何 BAProofObject（BA 证明对象），
证明大小集合是 empty set（空集），
Real.sInf_empty（实数空集下确界）会给出 0。
```

这在下界路线中很危险，因为：

```text
没有证明
```

会被旧实数长度语义看成：

```text
证明长度 = 0。
```

新增的安全语义是：

```lean
semanticBAMinProofSizeOption
```

它返回：

```text
some k  表示存在证明对象，并且 k 是最小大小；
none    表示没有证明对象。
```

审计文件新增：

```lean
currentToySemanticBAMinProofSizeOption_finiteConsistency_eq_none
```

含义是：

```text
当前 toy PA calculus（玩具 PA 演算）中，
finiteConsistencyFormula(n) 没有 BAProofObject（BA 证明对象），
所以新的 option-valued semantics（可空语义）返回 none。
```

这比旧结论更准确：

```lean
currentToySemanticBAProofLength_finiteConsistency_eq_zero
```

旧结论只是说明：

```text
因为空证明集被 sInf ∅ 映射为 0，
所以旧 Real 语义把无证明情形显示为长度 0。
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

新增审计定理公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

这给后续闭合路线增加了一个硬门槛：

```text
任何真正的 Pudlak 下界语义，
都必须先证明每个目标公式有 proof object（证明对象），
即不能只给出 Real-valued semanticBAProofLength。

必须先通过：

semanticBAMinProofSizeOption = some k

或等价的 proof-object completeness（证明对象完备性）。
```

## 42. 本轮复查：旧路线的问题与新的最小开盒目标

这轮复查的核心结论是：旧工作里有几条路线看起来在“消掉 `tail_gap`（尾部间隙）”，
但实际上只是把证明义务改名、下沉或换成更隐蔽的字段。

第一类问题是 `singleton gap`（单点间隙）路线。它把一个

```text
ComputableSearchGapCertificate
（可计算搜索间隙证书）
```

作为输入，然后从这个输入推出下游碰撞。这是正确的接口变换，但不是 Pudlak 下界本身的
证明。它没有从 PA/Hilbert checker（PA/Hilbert 检查器）、proof-code semantics
（证明码语义）、enumeration（枚举）和 rejection（拒绝）中构造出超多项式增长。

第二类问题是旧的 `concretePAHilbertPowerBoundChecker`（具体幂上界检查器）路线。Lean
已经检查出它不能承担真正下界：对目标公式 `powerBoundRawCode n`，它接受数值码 `n`。
因此如果又要求“所有小于某个大于 `n` 的 cutoff（截断值）的码都被拒绝”，就会直接把
这个已接受的码拒掉，产生矛盾。

本轮新增的 Lean 保险丝是：

```lean
paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor
PAHilbertAcceptedNatCodeExtractorNoSmallCore
PAHilbertAcceptedNatCodeExtractorNoSmallCore.to_checkedMinProofCodeStrongLowerBound
no_concretePAHilbertPowerBoundAcceptedNatCodeCheckerExtractor
no_concretePAHilbertPowerBoundRejectionExtractorInput
no_concretePAHilbertPowerBoundFourPiece
```

其中最重要的是：

```lean
paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor
```

它说明只有当 finite enumeration（有限枚举）固定为

```text
List.range cutoff
（所有小于 cutoff 的自然数码）
```

时，旧的 `rejectionExtractor`（拒绝抽取器）才能无损变成：

```text
PAHilbertAcceptedNatCodeRejectionExtractorData
（PA/Hilbert 接受数值码拒绝抽取数据）
```

也就是说，候选表不能偷偷筛掉小码。只拒绝一个被过滤后的候选表不够；真正要证明的是：

```text
∀ code < cutoff,
  code 不是 powerBoundRawCode(witness) 的 PA/Hilbert accepted proof code
（每个小于截断值的自然数码都不是该目标公式的已接受 PA/Hilbert 证明码）
```

这个对象一旦给出，Lean 已经验证它可以推出：

```text
CheckedMinProofCodeStrongLowerBound
（检查后最小证明码强下界）
```

并且新增桥的 axiom profile（公理画像）只出现 Lean 常规公理：

```text
propext, Classical.choice, Quot.sound
```

没有出现项目级 `proof_length`（证明长度）、`partial_consistency_payload`
（部分一致性载荷）或 `strengthened_partial_consistency_payload`
（强化部分一致性载荷）。

现在真正剩下的最小数学目标是：

```text
为真实 PA/Hilbert checker（检查器）构造
PAHilbertAcceptedNatCodeRejectionExtractorData。
```

这不是再包装，而是下界本体。它等价于要证明：对任意 polynomial upper bound（多项式上界）
`U` 和任意起点 `N`，可以找到 `witness >= N` 与 `cutoff > U(witness)`，并证明所有
`code < cutoff` 都不是 `powerBoundRawCode(witness)` 的已接受 PA/Hilbert 证明码。

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
status = 0
新增桥与反证定理均通过 Lean 检查
```

## 43. 本轮推进：BA proof-object 路线接到 accepted nat-code rejection

上一节把最小目标压到：

```text
PAHilbertAcceptedNatCodeRejectionExtractorData
（PA/Hilbert 接受数值码拒绝抽取数据）
```

本轮继续往上游打开，发现项目里已经有一条比旧 `powerBound checker`
（幂上界检查器）更真实的路线：

```lean
baProofObjectRootCodeSemantics
baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
```

这条路线使用：

```text
BAProofObject（有界算术证明对象）
semanticBAProofLength（语义 BA 证明长度）
```

Lean 已经证明：

```text
BAProofObject 语义里的 minProofCodeSize
= semanticBAProofLength
```

所以它不是旧式空壳 checker。它能够把 Buss-Pudlak lower source（Buss-Pudlak 下界源）和
语义长度校准转换成真正的 checked minimum lower bound（检查后最小证明码下界）。

本轮新增：

```lean
bussPudlakLowerSource_baProofObjectSemantics_toNoAcceptedBelowCutoff
bussPudlakLowerSource_baProofObjectSemantics_to_checkedMeasuredSearchGap
```

含义是：

```text
Buss-Pudlak lower source（Buss-Pudlak 下界源）
+ BAProofObject completeness（BA 证明对象完备性）
+ semantic length calibration（语义长度校准）
+ powerBoundRawCode injectivity（目标码族单射性）
=> ComputableNoAcceptedBelowCutoff（截断以下无接受证明）
=> checked measured search gap（检查后测量搜索间隙）
```

这一步已经把 BA 结构化证明对象路线接到了我们现在的干净开盒目标。

然后为了继续接到 PA/Hilbert numeric proof code（PA/Hilbert 自然数证明码），本轮新增了
精确的编码层义务：

```lean
BAProofObjectAcceptedNatCodeBridge
```

它要求：

```text
每个被 PA/Hilbert checker 接受的自然数码 code，
如果它证明 powerBoundRawCode n，
就能抽取一个 BAProofObject proof，
满足 proof.conclusion = target n 且 proof.size <= code。
```

在这个义务下，Lean 已证明：

```lean
baProofObjectNoAcceptedBelow_toPAHilbertAcceptedNatCodeRejectionData
bussPudlakLowerSource_baProofObjectBridge_toPAHilbertAcceptedNatCodeRejectionData
```

也就是说：

```text
BA 证明对象下界
+ accepted nat-code -> BAProofObject 的大小受控抽取
=> PAHilbertAcceptedNatCodeRejectionExtractorData
```

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
status = 0
新增 BA proof-object / accepted nat-code 桥通过 Lean 检查
新增桥的 axiom profile 只含 propext, Classical.choice, Quot.sound
```

因此现在缺口被进一步压缩为两个真正数学/形式化义务：

```text
1. BussPudlakTheorem5PALowerBoundSource.lower_bound
   （Buss-Pudlak 第5定理 PA 下界源）
   仍是源字段，不是项目内部从零证明。

2. BAProofObjectAcceptedNatCodeBridge
   （接受自然数码到 BA 证明对象的大小受控抽取桥）
   还没有由实际 PA/Hilbert checker/decoder 构造出来。
```

这比 `tail_gap`、`rejection_search` 或 `proof_length` 包装更接近根部：现在最后需要做的
不是再发明一个证书名，而是实现并证明真实 proof-code decoder/checker
（证明码解码器/检查器）的大小保持抽取定理，或者完整形式化 Buss-Pudlak theorem 5
（Buss-Pudlak 第5定理）。

## 38. 本轮复查后的最终开盒位置

这次复查以前围绕 `tail_gap`（尾部间隙）、`rejection_search`（拒绝搜索）、
`proof_length`（证明长度）、`computable_search_exclusion`（可计算搜索排除）做过的工作后，
结论要分三层说清楚。

第一层，旧工作真正的问题是把核心下界混在包装结构里。`PAHilbertCheckerExactnessCore`
（PA/Hilbert 检查器精确性核心）虽然能推出 checked minimum lower bound
（已检查最小证明码下界），但它仍经过 `proof_length_model.Calibration`
（证明长度模型校准），探针显示：

```text
paHilbertCheckerExactnessCore_to_checkedMinProofCodeStrongLowerBound
depends on axioms:
[proof_length, propext, Classical.choice, Quot.sound]
```

这条旧线不能作为最终投稿主线，因为它没有真正摆脱 root `proof_length`
（根证明长度）。

第二层，当前 native concrete checker（原生具体检查器）不是缺一个桥，而是逻辑上不能承载
Pudlak theorem-5 lower bound（第5定理下界）。Lean 已证明：

```lean
no_nativePowerBoundCheckedMinProofCodeStrongLowerBound
```

其含义是：在 `concretePAHilbertPowerBoundCheckerSemantics`
（具体 PA/Hilbert 幂界检查器语义）里，`powerBoundRawCode n` 有一个大小至多为 `n`
的 canonical accepted code（规范接受码）。因此最小接受证明码长度至多线性增长，
不可能在任意远处超过所有 polynomial bound（多项式上界）。探针剖面为：

```text
[propext, Classical.choice, Quot.sound]
```

所以这不是审计疑虑，而是 Lean 级别的 no-go theorem（不可能性定理）。

第三层，干净的下界盒子已经被打开到最直接的命题：

```lean
ProofLengthFreeNoAcceptedBelowClosureTarget
```

它只要求存在某个真实 proof-code semantics（证明码语义），并证明：

```text
对任意 polynomial bound f 和任意起点 N，
存在 n >= N 和 cutoff K > f(n)，
使得所有 size < K 的 proof code 都不能检查通过 powerBoundRawCode(n)。
```

这就是 `ComputableNoAcceptedBelowCutoff`（截断以下无接受码）。本轮新增并通过探针：

```lean
proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMeasuredSearchGap
proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMinProofCodeStrongLowerBound
```

剖面均为：

```text
[propext, Classical.choice, Quot.sound]
```

不含：

```text
tail_gap
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
```

因此，现在“完全打开”的准确含义是：

```text
tail_gap 黑盒已经消失；
candidate-rejection wrapper（候选拒绝包装）已经下沉；
剩下的唯一硬命题是 NoAcceptedBelowCutoff（截断以下无接受码）本身。
```

这个硬命题不能由当前 native checker 给出，因为 native checker 已被证明有短接受码。
真正下一步必须构造新的、与文献 Pudlak theorem-5 proof（第5定理证明）一致的
PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义），并在这个语义中证明
`NoAcceptedBelowCutoff`。

这不是继续包装，而是证明本体：

```text
真实 PA/Hilbert checker（检查器）
+ 真实 proof-code size（证明码尺寸）
+ theorem-5 no-small-proof argument（第5定理无小证明论证）
-> NoAcceptedBelowCutoff
-> CheckedMinProofCodeStrongLowerBound
-> checked measured gap
```

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
status=0
无 error（错误）
无 warning（警告）
```

## 39. 更底层复查：旧 PA/Hilbert checker interface 本身不可居住

继续向下检查 Month11 PA/Hilbert checker surface（第11月 PA/Hilbert 检查器表面）后，
发现一个比 root `proof_length`（根证明长度）更早出现的结构性问题。

当前旧接口：

```lean
PAHilbertCheckerDecoderExactness
```

包含字段：

```text
decodeProofCode_complete :
  对任意 PAHilbertProofObject proof，
  decoder.decode proof.code = some proof。
```

这个字段要求 decoder（解码器）能从一个 numeric code（数值码）恢复任意
proof object（证明对象）。但当前：

```lean
PAHilbertProofObject
```

允许两个不同对象带同一个 `code`。Lean 文件中已经有两个显式对象：

```lean
concretePAHilbertDecoderObstructionLeft
concretePAHilbertDecoderObstructionRight
```

它们 `code = 0`，但 `steps` 不同。因此 Lean 已证明：

```lean
no_full_decoder_exactness_for_unrestricted_proof_objects
```

本轮把这个 no-go（不可能性）继续投射到审计层：

```lean
no_paHilbertCheckerInterface_unrestrictedProofObjects
no_paHilbertCheckerExactnessCore_unrestrictedProofObjects
no_realPAHilbertRootReplacementTarget_unrestrictedProofObjects
```

其中最干净的接口级剖面为：

```text
no_paHilbertCheckerInterface_unrestrictedProofObjects
depends on axioms:
[propext]
```

含义是：

```text
旧 PAHilbertCheckerInterface（PA/Hilbert 检查器接口）
在当前 proof object 类型下不可居住；
这不是 proof_length 问题，而是 decoder exactness 规格本身过强。
```

所以旧目标：

```lean
RealPAHilbertRootReplacementTarget
```

不能再作为最终闭合目标。它不仅接回 current root proof_length（当前根证明长度）时失败；
即使不看 root proof_length，它也包含一个不可能的 full decoder exactness（完整解码器精确性）。

本轮新增了修正目标：

```lean
PAHilbertCanonicalDecoderExactness
```

它只要求 decoder 对 canonical decoded proof objects（规范解码证明对象）精确，而不是要求
同一个 numeric code 能恢复所有任意构造的 proof object。并且 Lean 已证明当前 seed decoder
（种子解码器）满足这个修正版接口：

```lean
concretePAHilbertSeedCanonicalDecoderExactness
concretePAHilbertSeedCanonicalDecoderExactness_nonempty
```

剖面：

```text
[propext]
```

这一步没有证明 Pudlak theorem 5（Pudlak 第五定理）下界；它完成的是根接口修复：

```text
旧路线：unrestricted proof object + full decoder exactness
        -> contradiction（矛盾）

新路线：canonical proof object predicate + canonical decoder exactness
        -> decoder 层不再自相矛盾
```

因此，真正可行的最终下界路线必须改成：

```text
PAHilbertCanonicalDecoderExactness（规范解码器精确性）
+ coherent accepts/rejects checker（相容的接受/拒绝检查器）
+ real proof-code semantics（真实证明码语义）
+ theorem-5 NoAcceptedBelowCutoff（第5定理截断以下无接受码）
-> CheckedMinProofCodeStrongLowerBound（已检查最小证明码强下界）
```

旧 `PAHilbertCheckerExactnessCore` 不能继续修补；它应被一个 canonical-decoder-based
core（基于规范解码器的新核心）替换。

## 40. 外部 Pudlak 文献输入仍是 axiom

复查 theorem-5 external surfaces（第五定理外部表面）后，结论同样明确。
文件：

```text
EulerLimit/PudlakTheorem5LowerBoundSourceSurface.lean
```

开头已经说明：

```text
it keeps the literature axioms as the only opaque mathematical input
（它把文献公设保留为唯一不透明数学输入）
```

具体 axiom（公设）在：

```text
EulerLimit/ExternalPudlakRawEncoding.lean
```

其中：

```lean
literaturePudlakTheorem5ExternalScaleData
literaturePudlakTheorem5ExternalRescaledLowerBound
```

仍是 `axiom`。而 bounded arithmetic sidecar（有界算术侧库）中的：

```lean
BussPudlakTheorem5PALowerBoundSource
```

也把真正的：

```text
EventualLowerBound（最终下界）
```

作为字段：

```lean
lower_bound
```

保存。该文件也明说：

```text
This file does not prove that theorem
（该文件没有证明那个定理）
```

所以当前可以引用文献输入做“条件化路线”，但不能说 Lean 内部已经完成 Pudlak theorem 5
下界证明。若要完成投稿级闭合，必须把这两个外部 axiom 替换成内部构造：

```text
真实 PA/Hilbert syntax（语法）
真实 proof checker（证明检查器）
真实 proof-code length（证明码长度）
Friedman/Pudlak no-small-proof argument（无小证明论证）
```

并最终产出：

```lean
ComputableNoAcceptedBelowCutoff
```

这是现在唯一没有被包装掩盖的核心证明缺口。

## 41. 本轮推进：accepted numeric-code rejection 是新的最小缺口

本轮把 canonical decoder（规范解码器）修复后的下界目标继续向下压缩。新的 Lean 桥为：

```lean
paHilbertAcceptedNatCodeRejectionData_toNoAcceptedBelowCutoff
```

它从：

```lean
PAHilbertAcceptedNatCodeRejectionExtractorData
```

直接推出：

```lean
ComputableNoAcceptedBelowCutoff
```

数学内容是：

```text
给定 polynomial bound（多项式上界）f 和起点 N，
构造 witness n 和 cutoff K；
证明每个 numeric proof code（数值证明码）c < K
都不是 powerBoundRawCode(n) 的 accepted PA/Hilbert proof code（被接受 PA/Hilbert 证明码）。
```

这比旧的 `computable_search_exclusion`（可计算搜索排除）更靠根部，因为它不再谈
候选列表，也不再依赖 root `proof_length`（根证明长度）或 calibration（校准）。

本轮新增 corrected core（修正核心）：

```lean
PAHilbertCanonicalAcceptedNatCodeNoSmallCore
```

它包含：

```text
checker（检查器）
semantics（语义）
canonical_interface（规范检查器接口）
completion（目标公式族有接受码）
rejection_data（接受数值码拒绝数据）
```

并且 Lean 已证明：

```lean
PAHilbertCanonicalAcceptedNatCodeNoSmallCore.toNoAcceptedBelowCutoff
PAHilbertCanonicalAcceptedNatCodeNoSmallCore.toProofLengthFreeNoAcceptedBelowClosureTarget
PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_checkedMinProofCodeStrongLowerBound
paHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget_to_checkedMinProofCodeStrongLowerBound
```

探针剖面均为：

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

同时，本轮证明旧 concrete power-bound checker（具体幂界检查器）不能提供这个新核心：

```lean
no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData
no_concretePAHilbertPowerBoundCanonicalAcceptedNatCodeNoSmallCore
```

原因很直接：旧 checker 已经接受 numeric code `n` 作为 `powerBoundRawCode n` 的证明码；
而 rejection data（拒绝数据）对 polynomial bound `f(n)=n` 会给出 cutoff `K>n`，
于是 code `n < K` 必须被拒绝，矛盾。

因此，当前最小真实缺口已经变成：

```text
在修正后的 canonical PA/Hilbert checker（规范 PA/Hilbert 检查器）上，
证明 PAHilbertAcceptedNatCodeRejectionExtractorData。
```

这就是 theorem-5 no-small-proof argument（第5定理无小证明论证）的精确 Lean 目标。
它不能由旧 concrete power-bound checker 给出，必须由新的真实 PA/Hilbert proof-code
semantics（证明码语义）给出。

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
status=0
无 error（错误）
无 warning（警告）
```

## 36. 本轮重新开盒：干净下界只停在 proof-code semantics

本轮重新检查以前围绕 lower bound（下界）、`tail_gap`（尾部间隙）、
`rejection_search`（拒绝搜索）、`proof_length`（证明长度）做过的路线后，结论如下。

旧路线的主要问题不是某个名字没有接好，而是把不同层次绑在一起：

```text
PAHilbertCheckerExactnessCore
```

虽然可以推出 checked minimum lower bound（已检查最小证明码下界），但它的结构中还绑着
`InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore`，而该 core（核心）含有
`proof_length_model.Calibration`（证明长度模型校准）。因此即使只是取
`computable_search_exclusion`（可计算搜索排除）字段，axiom profile（公理剖面）也会带上
`proof_length`。

Lean 探针显示：

```text
paHilbertCheckerExactnessCore_to_checkedMinProofCodeStrongLowerBound
depends on axioms:
[proof_length, propext, Classical.choice, Quot.sound]
```

这说明这条旧 core 路线还没有真正把下界从 root `proof_length`（根证明长度）中剥离。

本轮新增并验证了真正干净的下界入口：

```lean
proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound
proofLengthFreeLowerGapClosureTarget_to_checkedMinProofCodeStrongLowerBound
checkerComputableSearchProfile_to_checkedMinProofCodeStrongLowerBound
```

它们只从：

```text
PAHilbertProofLengthFreeLowerGapSource
```

出发。这个 source（来源）只包含：

```text
scale_data
proof_code_semantics
small_code_search
computable_search_exclusion
```

不包含：

```text
tail_gap
root proof_length
proof_length exactness
partial_consistency_payload
strengthened_partial_consistency_payload
```

Lean 探针显示：

```text
proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound
depends on axioms:
[propext, Classical.choice, Quot.sound]

proofLengthFreeLowerGapClosureTarget_to_checkedMinProofCodeStrongLowerBound
depends on axioms:
[propext, Classical.choice, Quot.sound]

checkerComputableSearchProfile_to_checkedMinProofCodeStrongLowerBound
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

所以现在下界开盒后的干净逻辑链是：

```text
computable finite-search exclusion（可计算有限搜索排除）
  -> no accepted code below cutoff（截断以下无接受码）
  -> minProofCodeSize beats every polynomial（最小证明码长度超过任意多项式）
  -> checked measured gap（已检查测量间隙）
```

这条链已经没有项目级 `tail_gap`、没有 root `proof_length`、没有两个 payload（载荷公设）。

同时，本轮也确认旧 MiniHilbert（小 Hilbert 系统）局部路线仍不能作为投稿主线。探针显示：

```text
MiniHilbert.FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_source_min_eq
depends on axioms:
[partial_consistency_payload, propext,
 strengthened_partial_consistency_payload, Classical.choice, Quot.sound]

MiniHilbert.FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_target_min_eq
depends on axioms:
[partial_consistency_payload, propext,
 strengthened_partial_consistency_payload, Classical.choice, Quot.sound]
```

因此，旧 Month6/MiniHilbert route（第6月/小 Hilbert 路线）仍然读到了两个 payload
predicate（载荷谓词），不能说是最终干净证明路线。

当前最短剩余硬义务已经不是 wrapper（包装器）问题，而是：

```text
构造真实 PA/Hilbert proof-code semantics（证明码语义）；
构造 small-code search（小证明码有限搜索）；
证明 computable_search_exclusion（可计算搜索排除）。
```

一旦这三个对象作为真实 checker/extractor（检查器/抽取器）构造出来，
Lean 已经能无 `proof_length`、无 `tail_gap`、无 payload 地推出：

```text
CheckedMinProofCodeStrongLowerBound
```

如果之后论文还要把这个 checked measured lower bound（已检查测量下界）读成项目级
`proof_length` 下界，则仍需要另外处理 root proof length exactness（根证明长度精确性）。
但这不应混进下界开盒步骤里；当前 root `proof_length = formula-code size`
（根证明长度等于公式码大小）已被 Lean 证明太小，不能承载 Pudlak 下界。

## 37. 合成超多项式 carrier 的闭合探针

本轮还把已有的模型 carrier（载体）

```lean
superPolynomialCanonicalLength n = (n + 1)^n
```

直接接到了 checked-minimum lower bound（已检查最小证明码下界）目标：

```lean
superPolynomialCanonicalLength_to_checkedMinProofCodeStrongLowerBound
```

其 Lean 结论是：

```text
如果 powerBoundRawCode 是 injective（单射），
则 calibrated checker semantics（校准检查器语义）中
minProofCodeSize(powerBoundRawCode n)
超过任意 polynomial bound（多项式上界）。
```

探针输出：

```text
superPolynomialCanonicalLength_to_checkedMinProofCodeStrongLowerBound
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

因此，adapter chain（适配链）已经完全闭合：

```text
显式超多项式长度 carrier
  -> finite singleton enumeration（有限单点枚举）
  -> no accepted code below cutoff（截断以下无接受码）
  -> checked measured gap（已检查测量间隙）
  -> CheckedMinProofCodeStrongLowerBound（已检查最小证明码强下界）
```

但这只是 proof probe（证明探针），不能在论文中直接说它就是真实 PA/Hilbert proof length
（PA/Hilbert 证明长度）。Lean 同时已有 no-go（不可能性）：

```lean
no_superPolynomialCanonicalLength_rootExactness_currentRoot
no_superPolynomialCalibratedCheckerExactness_currentRoot
```

含义是：当前 root `proof_length` 不能等同于这个合成超多项式 carrier。要让投稿路线无条件成立，
必须把这个 carrier 替换为真实 PA/Hilbert proof-code semantics 中自然产生的长度，并证明同样的
super-polynomial lower bound（超多项式下界）。

## 35. 把 pa_length/minProofCodeSize 校准打开到 BAProofObject 语义

本轮继续砍 `pa_length = minProofCodeSize`（PA 长度等于最小证明码尺寸）这个黑盒。
新的思路不是再包装一个 calibration（校准）字段，而是直接构造一个 proof-code semantics
（证明码语义）：

```text
Code := BAProofObject Ax
checks proof code :=
  proof 的结论等于 code 对应的目标公式
size proof := proof.size
```

Lean 新增：

```lean
baProofObjectRootCodeSemantics
baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
```

核心定理是：

```text
minProofCodeSize(rootCode n)
  =
semanticBAProofLength(Ax, target, n)
```

也就是说，只要真的有每个目标公式的 `BAProofObject`（BA 证明对象），并且 rootCode
（根公式码映射）是 injective（单射），那么 `semanticBAProofLength`（语义证明长度）
和主线检查器的 `minProofCodeSize`（最小证明码尺寸）已经被 Lean 证明为同一个对象。

这一步的意义很大：

```text
旧缺口：
  source.pa_length(n) = minProofCodeSize(powerBoundRawCode n)

现在打开成：
  source.pa_length(n) = semanticBAProofLength(Ax, target, n)
  每个 target n 有真实 BAProofObject
  powerBoundRawCode 单射
```

这不再是隐藏的 tail_gap（尾部间隙）或 proof_length（证明长度）黑盒，而是一个明确的
证明对象语义校准。

同时 Lean 也证明了当前 toy PA（玩具 PA）路线不能用：

```lean
no_currentToyFiniteConsistencyProofObjectCompleteness
no_currentToyBussPudlakLowerSource_semanticFiniteConsistency
```

含义是：

```text
当前 finiteConsistencyFormula（有限一致性公式）只是 toy BA 语言里的原子公式；
当前 PAAxiom / BADerivation 系统没有证明它的 BAProofObject；
因此 semanticBAProofLength(PAAxiom, finiteConsistencyFormula, n) = 0；
如果把 Buss-Pudlak lower_source.pa_length 校准到这个 0 长度对象，
会直接和 lower_source.lower_bound（下界字段）矛盾。
```

所以以前围绕 canonical CnBox / toy BAProofObject 的路线问题已经明确：

```text
不是缺一个命名校准；
而是当前 toy PA 语义不是 Pudlak 第5定理需要的真实 PA/Hilbert proof-code semantics。
```

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

新增定理的 axiom profile（公理剖面）：

```text
baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
  [propext, Classical.choice, Quot.sound]

bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
  [propext, Classical.choice, Quot.sound]

no_currentToyFiniteConsistencyProofObjectCompleteness
  [propext]

no_currentToyBussPudlakLowerSource_semanticFiniteConsistency
  [propext, Classical.choice, Quot.sound]
```

没有使用：

```text
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
```

现在下界侧剩余的真正数学义务被压成：

```text
1. 构造真实 PA/Hilbert proof-code semantics（证明码语义），不是 toy BA 原子公式语义；
2. 证明 Pudlak/Buss lower bound（下界）给出的 pa_length
   等于该真实语义的 semanticBAProofLength；
3. 证明每个目标公式有真实 proof object（证明对象）；
4. 证明 powerBoundRawCode（第5定理公式码映射）单射；
5. 在该真实语义上证明 checked minProofCodeSize strong lower bound
   （检查器最小证明码强下界）。
```

其中第 2--4 项现在已经有 Lean 桥可以直接消费；第 1 和第 5 项才是 Pudlak 下界的
真正数学主体。

## 34. bounded_arithmetic 下界源接入最短缺口

本轮把 bounded_arithmetic_lab（有界算术库）里的抽象下界接口接到本项目的最短缺口。

新增：

```lean
rootPolynomialBound_to_boundedArithmeticPolynomialBound
boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound
bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
```

第一条说明两个库里的 polynomial bound（多项式上界）定义形状一致，可以转换。

第二条说明：

```text
如果有 bounded_arithmetic 的 EventualLowerBound（最终下界）：

  box.length(n) > f(n)

并且有校准：

  box.length(n)
    = minProofCodeSize(powerBoundRawCode n)

那么可以推出：

  CheckedMinProofCodeStrongLowerBound
```

第三条是对 Buss-Pudlak source（Buss-Pudlak 下界源）的专门版本：

```text
BussPudlakTheorem5PALowerBoundSource
+ pa_length(n) = minProofCodeSize(powerBoundRawCode n)
-> CheckedMinProofCodeStrongLowerBound
```

也就是说，如果 bounded_arithmetic_lab 的 Buss-Pudlak 下界源真的已经提供：

```text
source.lower_bound
```

并且它的 `pa_length`（PA 长度）被校准为本项目 theorem-5 proof-code semantics（证明码语义）
上的最小证明码尺寸，那么最短缺口可以闭合到：

```text
InternalPudlakTheorem5NoSmallProofCodes
```

但是这也精确暴露了还缺的东西：

```text
1. source.lower_bound 目前仍是 BussPudlakTheorem5PALowerBoundSource 的字段；
2. pa_length = minProofCodeSize(powerBoundRawCode n) 的校准仍需证明；
3. 这两项必须来自真实 PA/Hilbert proof-code semantics（证明码语义），不能来自当前 toy/fallback root。
```

本轮 Lean 公理剖面：

```text
boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound
  [propext, Classical.choice, Quot.sound]

bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
  [propext, Classical.choice, Quot.sound]
```

没有 `proof_length`，也没有 `tail_gap`。

这说明桥接本身是干净的；剩余负债集中在真实下界源和真实长度校准。

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 33. 与 NoSmallProofCodes 的精确等价

本轮继续把剩余义务对齐到项目原有 theorem-5 internal surface（第5定理内部接口）中的标准形式：

```lean
InternalPudlakTheorem5NoSmallProofCodes
```

这个命题说：

```text
对任意 polynomial bound（多项式上界）f，
frequently atTop（在任意尾部之后经常存在）某个 n，
使得任意被接受的 proof code（证明码）c 都满足：

  f(n) < size(c)
```

它不说 `proof_length`（证明长度），只说 proof-code semantics（证明码语义）里的 accepted code
（被接受码）和 size（尺寸）。

Lean 现在证明了：

```lean
checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes
```

所以当前最短缺口可以等价写成：

```text
CheckedMinProofCodeStrongLowerBound
  <-> InternalPudlakTheorem5NoSmallProofCodes
  <-> ComputableNoAcceptedBelowCutoff
```

这三者都属于 root-free proof-code layer（不依赖根证明长度的证明码层）。

公理剖面：

```text
[propext, Classical.choice, Quot.sound]
```

没有：

```text
proof_length（证明长度）
tail_gap（尾部间隙）
proof_length_gap（证明长度间隙）
computable_search_exclusion（可计算搜索排除）字段
```

这说明现在不应再把目标称为“消掉 tail_gap”。它已经消掉了。真正剩下的是：

```text
证明 InternalPudlakTheorem5NoSmallProofCodes
（第5定理无小证明码）
```

也就是 Pudlak/Friedman proof-complexity lower bound（证明复杂性下界）本身。

### bounded_arithmetic_lab 的审计结果

复查 bounded_arithmetic_lab（有界算术库）后，Lean 新增：

```lean
bussPudlakTheorem5PALowerBoundSource_lower_bound_is_field
```

它直接说明：

```text
BussPudlakTheorem5PALowerBoundSource
```

里的 PA lower bound（PA 下界）目前是字段：

```lean
source.lower_bound
```

不是从库内部的 checker / proof predicate / proof-code semantics（检查器/证明谓词/证明码语义）
推导出来的 theorem。

这与源码注释一致：

```text
This file does not prove that theorem;
it fixes the exact PA/symbol-size lower-bound shape
that such a formalization must eventually provide.
```

所以 bounded_arithmetic_lab 当前能提供的是精确接口和传输路线，不是 theorem-5 lower bound
（第5定理下界）的内部闭合证明。

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 32. 再向根部打开：checked minProofCodeSize 下界

本轮把 `NoAcceptedBelowCutoff`（截断界以下无接受码）继续改写成一个更根本的
root-free（不依赖根证明长度）命题：

```lean
CheckedMinProofCodeStrongLowerBound
```

它的内容是：

```text
对任意 polynomial bound（多项式上界）f，
checked minProofCodeSize（检查器最小证明码尺寸）
会在任意尾部之后超过 f。
```

形式上：

```text
∀ f, is_polynomial_bound f ->
  frequently_atTop n,
    minProofCodeSize(powerBoundRawCode n) > f(n)
```

这一步非常关键，因为它完全不提：

```text
root proof_length（根证明长度）
tail_gap（尾部间隙）
proof_length_gap（证明长度间隙）
candidate rejection（候选拒绝）
```

它只谈 proof-code semantics（证明码语义）自己的最小接受证明码尺寸。

Lean 已证明两个方向中的核心方向：

```lean
ComputableNoAcceptedBelowCutoff.toCheckedMinProofCodeStrongLowerBound
checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
```

含义是：

```text
NoAcceptedBelowCutoff（截断界以下无接受码）
  -> checked minProofCodeSize strong lower bound

checked minProofCodeSize strong lower bound
  -> NoAcceptedBelowCutoff（截断界以下无接受码）
```

第二个方向的证明很直接：

```text
1. 从 strong lower bound（强下界）中选择一个 witness n；
2. 令 cutoff K = minProofCodeSize(powerBoundRawCode n)；
3. 下界给出 K > f(n)；
4. 若存在 accepted proof code c 且 size(c) < K，
   就违反 K 作为最小接受证明码尺寸的定义。
```

这就是下界盒子的最短数学形态。

本轮还证明：

```lean
strongProofLengthLowerBound_toNoAcceptedBelowCutoff
```

含义是：

```text
如果有 calibrated proof-length model（已校准证明长度模型），
并且 root proof_length（根证明长度）满足 StrongProofLengthLowerBound（强证明长度下界），
那么可以推出 NoAcceptedBelowCutoff（截断界以下无接受码）。
```

但是这个桥接分成两部分看：

```text
checked minProofCodeSize lower bound
  -> NoAcceptedBelowCutoff
```

这一段不含 `proof_length`。

```text
root proof_length lower bound + calibration
  -> checked minProofCodeSize lower bound
```

这一段才涉及 root proof_length（根证明长度）和 calibration（校准）。

Lean 公理剖面：

```text
checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
  [propext, Classical.choice, Quot.sound]

strongProofLengthLowerBound_toNoAcceptedBelowCutoff
  [propext, Classical.choice, Quot.sound]
```

注意：这里 `strongProofLengthLowerBound_toNoAcceptedBelowCutoff` 的定理本身不使用
`proof_length` 公设；它把 `StrongProofLengthLowerBound` 和 `calibration` 当作输入使用。
真正危险的是当前 root `proof_length` 的具体定义，因为它已经被证明是 polynomially bounded
（多项式有界）。

因此 Lean 同时证明：

```lean
no_proofLengthCalibratedStrongLowerBoundNoAcceptedCore_currentRoot
```

也就是：

```text
在当前 root proof_length = formula-code size（根证明长度等于公式码大小）下，
不存在同时包含 calibration（校准）和 strong proof-length lower bound（强证明长度下界）
的闭合包。
```

### 当前最精确的剩余义务

现在真正剩下的证明义务已经不是 `tail_gap`，也不是 `computable_search_exclusion`。

它被压缩为：

```text
在真实 PA/Hilbert proof-code semantics（证明码语义）中证明
CheckedMinProofCodeStrongLowerBound
（检查器最小证明码尺寸强下界）。
```

如果要接回项目级 `proof_length`，还需要：

```text
root proof_length exactness / calibration
（根证明长度精确性/校准）。
```

同时，复查外部 Pudlak 路线发现：

```lean
literaturePudlakTheorem5ExternalScaleData
literaturePudlakTheorem5ExternalRescaledLowerBound
```

仍是 `axiom`（公设）。所以它们可以作为文献假设路线，但不能算“完全闭合”的 Lean 内部证明。

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

## 31. 完全打开 computable_search_exclusion 的硬芯

本轮继续把 `computable_search_exclusion`（可计算搜索排除）向内打开。

复查旧工作后发现三个关键问题。

第一，旧的

```lean
InternalPudlakTheorem5SmallCodeSearch
```

只有 completeness（完备性）：

```text
如果某个证明码 c 被 checker 接受，并且 size(c) < K，
那么 c 一定出现在 candidates(n,K) 中。
```

它没有 size-filter / soundness（尺寸过滤/健全性）：

```text
如果 c 出现在 candidates(n,K) 中，
那么一定有 size(c) < K。
```

因此，候选列表层本身不能作为最终数学下界。真正的下界内容应当是：

```text
cutoff 以下没有任何 accepted proof code（被接受的证明码）。
```

第二，旧路线其实已经有一个比较靠近根部的形式：

```lean
PAHilbertAcceptedNatCodeRejectionExtractorData.rejects_lt_cutoff
```

它说的是：

```text
code < cutoff
  -> 不是 PAHilbertAcceptedProofCodeForFormulaCode
```

这已经比 `rejects_candidates`（拒绝候选）更干净。但它仍然是一个字段输入，不是从
Pudlak theorem-5 proof（第5定理证明）推出来的定理。

第三，当前 concrete power-bound checker（具体幂界检查器）有短接受码：

```lean
concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
```

Lean 已证明：

```lean
no_concretePAHilbertPowerBound_noSmallAccepted_at_succ
nativePowerBoundCheckedMeasured_le_index
no_nativePowerBoundCheckedMeasuredSearchGap
```

也就是说，在当前具体语义下，`powerBoundRawCode n` 有一个编号为 `n` 的 accepted proof code
（被接受证明码）。所以任何要求“所有小于 n+1 的证明码都不被接受”的下界断言都会立即矛盾。

因此，旧工作的问题不是少一个包装，而是：

```text
当前 concrete checker / root proof_length 不是可以承载 theorem-5 下界的真实语义。
```

### 31.1 新的直接对象

本轮新增：

```lean
ComputableNoAcceptedBelowCutoff
```

它的数学内容是：

```text
对任意 polynomial upper bound（多项式上界）f，
对任意起点 N，
构造 witness n >= N（见证指标）和 cutoff K（截断界），
满足 f(n) < K，
并证明：

  对任意 proof code c（证明码），
  如果 size(c) < K，
  那么 c 不会检查通过 powerBoundRawCode(n)。
```

这就是 `computable_search_exclusion`（可计算搜索排除）的硬芯。它不含：

```text
tail_gap（尾部间隙）
proof_length_gap（证明长度间隙）
候选列表拒绝黑盒
```

Lean 已证明：

```lean
ComputableNoAcceptedBelowCutoff.noSmallAtWitness
ComputableNoAcceptedBelowCutoff.minProofCodeSize_gt_at_witness
ComputableNoAcceptedBelowCutoff.toCheckedMeasuredSearchGap
```

含义是：

```text
只要有 NoAcceptedBelowCutoff（截断界以下无接受码），
Lean 就能推出：

1. 任意 accepted proof code 的 size 都超过 f(n)；
2. minProofCodeSize（最小证明码尺寸）超过 f(n)；
3. checked measured search gap（检查器测量间隙）成立。
```

这条线路不经过 root `proof_length`（根证明长度），所以其 axiom profile（公理剖面）为：

```text
[propext, Classical.choice, Quot.sound]
```

没有 `proof_length`。

### 31.2 旧证书怎样打开到新对象

Lean 已证明：

```lean
computableFiniteSearchExclusion_toNoAcceptedBelowCutoff
```

也就是说，旧的

```lean
InternalPudlakTheorem5ComputableFiniteSearchExclusion
```

可以打开成新的

```lean
ComputableNoAcceptedBelowCutoff
```

这个方向只用 `SmallCodeSearch.complete`（小码搜索完备性）。

反方向需要额外的 size-filter（尺寸过滤）：

```lean
SizeFilteredSmallCodeSearch
noAcceptedBelowCutoff_toComputableFiniteSearchExclusion
```

含义是：

```text
如果候选列表确实只枚举 size < K 的证明码，
那么 NoAcceptedBelowCutoff 可以重建旧的 rejects_candidates 字段。
```

这说明以前 `computable_search_exclusion` 里真正要证明的不是候选列表包装，而是：

```text
NoAcceptedBelowCutoff
```

候选列表只是可执行审计层。

### 31.3 新的 gap-free opened target

本轮新增：

```lean
OpenedGapFreeTheorem5ClosureCore
OpenedGapFreeTheorem5ClosureTarget
openedGapFreeTheorem5ClosureTarget_to_gapFreeTheorem5ClosureTarget
no_openedGapFreeTheorem5ClosureTarget_currentRoot
```

这个目标把第5定理闭合对象写成：

```text
proof_length_model（证明长度模型）
sizeFilteredSearch（尺寸过滤搜索）
noAcceptedBelow（截断界以下无接受码）
calibration（校准）
```

它不再把 `computable_search_exclusion` 作为黑盒字段。

Lean 已证明：

```text
OpenedGapFreeTheorem5ClosureTarget
  -> GapFreeTheorem5ClosureTarget
  -> RootClosedTheorem5LowerBoundTarget
```

并且当前 root proof_length（根证明长度）下：

```lean
OpenedGapFreeTheorem5ClosureTarget -> False
```

### 31.4 当前结论

现在下界缺口已经打开到最短形式：

```text
必须为真实 PA/Hilbert proof-code semantics（证明码语义）证明
ComputableNoAcceptedBelowCutoff（截断界以下无接受码）。
```

完成它以后，Lean 已经能推出 checked measured gap（检查器测量间隙）。

但要把它变成项目级 `proof_length`（证明长度）的下界，还必须另外完成：

```text
root proof_length exactness（根证明长度精确性）
```

当前 root `proof_length = formula-code size`（证明长度等于公式码大小）已经被 Lean 证明为多项式有界，
所以它不能承载 theorem-5 lower bound（第5定理下界）。这不是文档问题，也不是命名问题，而是语义必须更换或校准到真实 PA/Hilbert proof-code semantics。

本轮探针：

```text
lake env lean integration/SondowProjectPudlakLowerBoundInputAudit.lean
```

结果：

```text
无 error（错误）
无 warning（警告）
无 sorryAx（未完成证明公设）
```

因此，旧路线现在被进一步压缩：

```text
tail_gap（尾部间隙）不是终点；
rejection_search（拒绝搜索）不是终点；
FinalExactCheckerCoreInput（最终精确检查器核心输入）也不是终点。

真正终点仍然是：
真实 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）
+ theorem-5 finite-search exclusion（第5定理有限搜索排除）
+ root proof_length exactness（根证明长度精确性）。
```

## 30. 新增 gap-free theorem-5 入口

为了避免旧路线继续把 `proof_length_gap`（证明长度间隙）预先放入输入结构，本轮新增
一个更干净的目标：

```lean
GapFreeTheorem5ClosureTarget
```

它定义为：

```text
Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
```

这个 core（核心）不含 `proof_length_gap`（证明长度间隙）字段。它包含的是：

```text
proof_length_model
（证明长度模型，即 proof-code semantics + fallback）

small_code_search
（小码有限搜索）

computable_search_exclusion
（可计算有限搜索排除）

calibration
（root proof_length 与该模型最小证明码长度的校准）
```

Lean 新增：

```lean
computableFiniteSearchNoSmallCore_toRootClosedTheorem5LowerBoundWitness
gapFreeTheorem5ClosureTarget_to_rootClosedTheorem5LowerBoundTarget
no_gapFreeTheorem5ClosureTarget_currentRoot
```

含义是：

```text
如果能真正构造 InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore，
就能得到 RootClosedTheorem5LowerBoundTarget（根闭合第5定理目标）；
但在当前 root proof_length = formula-code size（根证明长度等于公式码大小）下，
这个 gap-free target（无 gap 字段目标）也不可能存在。
```

这一步比旧 `FinalExactCheckerCoreInput`（最终精确检查器核心输入）更接近真正证明，因为它
没有把 `proof_length_gap`（证明长度间隙）作为字段输入。现在真正需要完成的是其中的：

```text
computable_search_exclusion
（可计算有限搜索排除）
```

也就是对任意 polynomial bound（多项式上界）和任意起点 `N`，构造一个 witness
（见证）和 cutoff（截断），并证明所有枚举出来的小证明码都被拒绝。这个才是 theorem-5
lower-bound proof（第5定理下界证明）本身。

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
