# 最短证明增长下界：当前指导书

更新时间：2026-07-12。

## 主控方式

[定理依赖图 DOT](checked_minproof_theorem_dependency_graph_zh.dot) 是当前工作的唯一实时状态面板；
PNG/SVG/PDF 只视为历史快照，证明推进期间不再生成。本文件只保留图中节点所需的精确定义、
文献条件、关键不变量和成功判据，不再另建一套与图可能不同步的进度叙述。

图中绿色节点必须有已通过的 Lean theorem（Lean 定理）和 axiom profile（公理画像）证据；
黄色节点是唯一当前工作面；灰色虚线节点尚待前置条件；红色节点是审计后弃用的历史路线，
且不得有通向最终主定理的有向边。每次探针形成新内核证据后，先更新图再继续下一节点。

## 最终目标

在同一个 formula family（公式族）、PA checker（PA 检查器）和
paper-grade proof length（论文标准证明长度）上证明：

```text
Sondow：假设 gamma 有理 => 最短证明长度最终有多项式上界；
Buss-Pudlak：同一批公式的最短证明长度最终超过该上界；
两式在同一 n 冲突。
```

最终链路不得含 `tail_gap`、`upper_provider`、项目级 `proof_length` 公设或
toy PA（玩具 PA）闭合。

当前闭合路线示意图：[PNG](checked_minproof_lower_bound_route_zh.png)；
[Graphviz 源文件](checked_minproof_lower_bound_route_zh.dot)。

详细 theorem dependency graph（定理依赖图）以
[DOT 源文件](checked_minproof_theorem_dependency_graph_zh.dot) 为准。图中每个专业术语均附中文解释，
绿色为内核已检查，黄色为当前义务，灰色虚线为尚待闭合根定理。

## 文献定理校准

项目原接口实际指向 Buss 1994, Theorem 5，而不是一个可任意换公式族的抽象下界。
其精确结论是：对满足原文条件的算术理论 `T`，存在 `epsilon > 0` 和 `c`，使每个
time-constructible（时间可构造）函数 `f` 都满足（充分大 `n`）

```text
T 没有长度 <= f(n)^epsilon 的证明去证明 Con_T((f(n))^c).
```

原文要求：一致、可公理化且公理可多项式时间识别的强算术理论，短二进制数词、有效
元数学，以及 Hilbert-style symbol length（Hilbert 式符号长度）。Pudlak 1986
Theorem 3.1/条件 (0)-(3) 是其幂下界底层机制之一；Buss Theorem 5 还增加了
time-constructible rescaling（时间可构造重标定）。因此必须证明：

```text
同一公式族 = Con_T((f(n))^c)，
同一证明系统 = 文献 Hilbert 系统或已证多项式等价系统，
同一度量 = 完整证明字符串的 symbol length。
```

任何从该下界直接跳到 `sondowCertificateValidCode` 或 reflection-graft 的步骤都必须
给出公式恒等或双向多项式证明编译；仅有 `LowerBoundTransfer` 字段不算证明。

Pudlák 1986 Theorem 3.1 的四条条件应按原文理解为定量可导性条件，而不是四个抽象标签：

```text
(0) PA 内部证明 P 的 cutoff 单调性；
(1) 长度 n 的外部 PA 证明 phi，可用 p1(n) 长度证明 P(n, code(phi))；
(2) 可用 p2(|n|,|m|) 长度证明 P(n,m) -> P(q1(n), code(P(n,m)))；
(3) 可用 p3(|n|,|phi|,|psi|) 长度证明
    P(n,code(phi)) ∧ P(n,code(phi -> psi)) -> P(q2(n),code(psi))。
```

其中 `p1,p2,p3,q1,q2` 必须是显式固定多项式，`P` 必须就是同一个紧凑证明谓词。
公理集合 NP/polytime recognizability（NP/多项式时间可识别性）、短二进制数词和接受计算轨迹
是用来证明自然 arithmetization（算术化）满足 (0)–(3) 的前置条件，不能与 (0)–(3) 本身混写。

原文 Theorem 3.1（定理 3.1）的内部证明还必须拆成三段，而不能把 (0)–(3) 直接连到结论：

```text
quantitative diagonalization（定量对角化）：
  构造 D(x) <-> not P(x, code(D(x)))，并控制 D(m) 实例证明长度；
bounded proof assembly（有界证明拼接）：
  用固定命题重言式及 (0)–(3) 逐步得到 not P(q5(m), bottom) -> D(m)；
consistency/exponent extraction（一致性反证/指数提取）：
  短 D(m) 证明违反 A 的一致性，再由多项式 q5 提取 epsilon > 0。
```

其中每次 substitution（代入）、公式代码生成、modus ponens（肯定前件）和证明合并都要有显式
symbol-length（符号长度）界。DOT 已将这三段拆为独立灰色根节点；条件 (0)–(3) 通过不等于
Theorem 3.1 已形式化。

Foundation 已有 `Bootstrapping.FixedPoint.parameterized_diagonal₁`，可直接构造原文需要的单参数
`D(x)` 全称等价。其内部虽使用 semantic completeness（语义完备性），但对最终固定的 `P` 而言，所得
全称证明本身是一份固定有限对象，其长度可作为常数。故无需从零重证整个对角引理。真正的定量义务是：
构造 explicit universal-instantiation compiler（显式全称实例化编译器），把这份固定证明实例化到短二进制
数词 `m`，并证明 substitution/code generation（代入/代码生成）及推导转换开销为 `poly(|m|)`。
禁止的是对每个 `m` 分别调用完备性再任选一份证明，因为那不给统一长度界。
第 27、39 至 42 项现已关闭这一义务：公式输出码界、真实 proof object（证明对象）实例化、短二进制
数码项、完整结构证书及最终 `poly(Nat.size m)` 载荷长度界均已由 Lean 检查。后续只需把已关闭的通用编译器实例化到
具体紧凑证明谓词 `P`；不得把“具体 `P` 尚待算术化”误写成对角编译器仍是黑盒。

## 编码审计结论

[FoundationFiniteConsistencyEncodingAudit.lean](../integration/FoundationFiniteConsistencyEncodingAudit.lean)
已由 Lean 内核证明：

```text
e <= formulaTermDepth(Con_PA(e))
  < GoedelCode(Con_PA(e)).
```

[FoundationPAFiniteConsistencyLowerBoundTarget.lean](../integration/FoundationPAFiniteConsistencyLowerBoundTarget.lean)
又已证明：任何被 Foundation checker 接受、结论为 `F` 的原始证明码 `d` 都满足

```text
GoedelCode(F) < Nat.size(d).
```

因此当前坐标自动给出

```text
e < Nat.size(d).
```

这只来自两个编码事实：`e` 被写成 unary numeral（一元数词），且原始证明码把
结论单元素 sequent（序列）编码为 `2^GoedelCode(F)`。所以当前
`FiniteConsistencyProofPowerLowerBound` 取 `degree = 1` 即可形式闭合，但这是
encoding artifact（编码伪影），不是 Friedman-Pudlak/Buss（弗里德曼-普德拉克/
布斯）证明复杂度下界，禁止用它完成投稿主定理。

## 已可靠闭合

1. `d < 2^e` 与 `Nat.size d <= e` 的输入截断完全等价。
2. 真实 PA checker、有限一致性句的标准模型真值和逐项 PA 可证性已经接通。
3. 若有真实定量下界，外层 amplification（放大）和“指数超过任意多项式”的
   渐近算术已经闭合。
4. restricted-Godel（受限哥德尔）替代族的原始码强下界已闭合，但它同样不能
   在未完成长度校准和 Sondow 同对象编译器时替代主路线。
5. 上述审计定理的 axiom profile（公理画像）只有 `propext`、
   `Classical.choice`、`Quot.sound`，无 `sorryAx`。

## 新坐标进展

[FoundationSuccinctFiniteConsistencyTarget.lean](../integration/FoundationSuccinctFiniteConsistencyTarget.lean)
已经闭合：

1. `powTwoTerm m` 的标准值严格等于 `2^m`，项深度不超过 `m+2`，符号数精确为
   `4*m+1`。
2. 新句精确表达“无位长至多 `2^(A*n)` 的 PA 证明”，标准模型语义、
   `Sigma_1` 层级、逐项 PA 可证性和 checker 完备性均已通过。
3. 每个 accepted raw code（已接受原始码）都能提取为同一公式的真实
   `Derivation2`（推导树）。
4. 已在真实推导树上定义 `derivationSymbolLength`（结构符号长度）及
   `minStructuralProofLength`（最短结构证明长度），并证明其存在性和最小性。
5. 已定义 proof-field-free certificate tree（无证明字段证书树）；其有效性严格等于
   Foundation 的真实 PA checker 接受，不另设 `checker_soundness` 参数。
6. 已实现自然数、项、公式、序列和整棵证明的 prefix decoder（前缀解码器），并逐层
   证明任意合法序列化都解回同一个 Foundation 原始证明码与同一个结论码。
7. `packBinaryString` 将证明位串无损打包为自然数，且 Lean 已证明
   `Nat.size(packedCode) = binaryLength + 1`；旧哥德尔码大小不再参与长度。
8. 已定义具体标准模型谓词 `EfficientPAProofPredicate(x,y)`：存在 payload length
   （有效载荷长度）不超过 `x`、解码结论为 `y` 且被同一 PA checker 接受的二进制码。
   真实 `Derivation2` 到该谓词的长度保持编译和反向 checker soundness（检查器可靠性）
   均已闭合。
9. [FoundationEfficientPAProofPredicateArithmetic.lean](../integration/FoundationEfficientPAProofPredicateArithmetic.lean)
   已给同一证明树构造 postfix serialization（后缀序列化），并证明所有 PA 规则逐步执行后
   精确重建同一个 Foundation 原始证明码与同一个结论码。
10. [FoundationEfficientPAProofPredicateRE.lean](../integration/FoundationEfficientPAProofPredicateRE.lean)
    已证明完整 postfix checker（后缀检查器）及其真实二进制位长为 primitive recursive
    （原始递归），进而证明具体有界谓词为 `REPred`（递归可枚举谓词）。
11. 同一文件已生成真正二变量 `Sigma_1` 公式 `efficientPostfixPAProofFormula(x,y)`，并由
    Lean 证明其标准模型语义逐点精确等价于 `EfficientPostfixPAProofPredicate(x,y)`。
    三个关键审计定理的公理画像均只有 `propext`、`Classical.choice`、`Quot.sound`。
12. 后续复杂度审计发现：该 postfix checker 在执行中仍重建 Foundation 的嵌套
    `rawCode`；原始递归性不推出 NP/多项式时间性，故第 9 至 11 项只作表示层诊断，
    不作为 Theorem 3.1 的 suitable numeration（合适枚举）。
13. [FoundationPudlakQuantitativeConditions.lean](../integration/FoundationPudlakQuantitativeConditions.lean)
    已建立长度 `O(Nat.size n)` 的短二进制数词，并定义完全不含 `rawCode` 的逐规则
    `structurallyValid`；Lean 已证明其与同结论真实 `Derivation2` 双向对应。
14. [FoundationCompactPAProofVerifier.lean](../integration/FoundationCompactPAProofVerifier.lean)
    已直接把紧凑位串解析为类型化项、公式、序列和证明树，证明十种 PA 规则及整树的
    精确打包往返；新 `EfficientCompactPAProofPredicate` 的长度就是载荷位数，接受推出
    同公式真实 PA 推导，真实 PA 推导也产生等长接受码。
15. [FoundationCompactPAAxiomCertificate.lean](../integration/FoundationCompactPAAxiomCertificate.lean)
    已为有限 PA-minus/等词公理和归纳公理体构造显式证书；证书有效性与
    `structurallyValid` 精确等价，证书位串及自然数打包均已证明无损往返。
16. [FoundationCompactCertifiedPAProof.lean](../integration/FoundationCompactCertifiedPAProof.lean)
    已把证明树与局部证书合并为一个诚实证明位串，二者全部计入长度；解码接受与真实
    PA 推导双向对应，不再把无限制 auxiliary witness（辅助见证）藏在长度坐标之外。
    逐规则 `certificateValidBool` 和总验证器已可实际执行，手工规范编码的 `⊤` 引入
    正例返回 `true`，且 `verifier = true` 与数学接受关系已由 Lean 精确证明等价。

17. [FoundationComputableCompactPAProofEncoder.lean](../integration/FoundationComputableCompactPAProofEncoder.lean)
    已用公式二进制码顺序排序每个有限 sequent（序列），替换不可执行的
    `Finset.toList`。新编码器可实际运行，与旧诚实编码逐位等长，并已证明十种规则、整树、
    证书及自然数打包的精确往返。类型化 `⊤` 引入树经新编码后由独立验证器返回 `true`。
18. [FoundationCertifiedFiniteConsistencyTarget.lean](../integration/FoundationCertifiedFiniteConsistencyTarget.lean)
    已固定精确 Buss-style finite consistency（Buss 式有限一致性）标准模型语义：不存在
    完整载荷位长不超过 cutoff 且验证器接受为 `⊥` 的证明码。接受可恢复真实 PA 推导，
    因而普通及 `2^(A*n)` 放大语义均已无条件证明为真；旧 raw-code 位长完全退出该定义。
    这里的 `CertifiedFiniteConsistencyAt` 仍是 Lean `Prop`（元层命题），尚不是 PA 内部算术句；
    它闭合了标准模型目标，但不能代替 Buss Theorem 5 所需的公式族。
19. [FoundationCompactVerifierStructuralBound.lean](../integration/FoundationCompactVerifierStructuralBound.lean)
    已证明任意成功解码（包括非规范输入）都不会制造超出已消费位数的项、公式、序列或
    前三类证明节点；自然数前缀每次至少消费两位，定长向量的全部子项都计入总量。
20. [FoundationCompactProofDecoderStructuralBound.lean](../integration/FoundationCompactProofDecoderStructuralBound.lean)
    已逐条闭合十种真实 PA 相继式规则并统一归纳：若证明解析成功，则
    `tree.parseWeight + suffix.length <= input.length`。因此不能用短输入解析出隐藏的巨大
    证明树。当前路线固定为直接对该具体相继式系统重证 Pudlak 定量定理，不把尚未证明的
    Hilbert-system simulation（Hilbert 系统模拟）偷偷当作编译器。
21. [FoundationCompactCertificateDecoderStructuralBound.lean](../integration/FoundationCompactCertificateDecoderStructuralBound.lean)
    已对全部 PA 公理证书（含完整归纳公式体）、递归结构证书、证明与证书串联解析、自然数
    打包和最终公开验证器证明同类界。若 `verifier = true`，证明树、全部证书及目标公式的
    总结构量不超过两个诚实二进制输入载荷之和。三个关键定理的公理画像只有 `propext`、
    `Classical.choice`、`Quot.sound`，无 `sorryAx`。
22. [FoundationCompactSyntaxTransformationBounds.lean](../integration/FoundationCompactSyntaxTransformationBounds.lean)
    已证明 shift（移位）、free-variable embedding（自由变量嵌入）、negation（否定）和
    one-variable substitution（单变量代入）的显式符号数界；代入结果至多为原公式符号数
    与见证项符号数之积。这为局部验证步骤的多项式成本提供了已核验的数学界。
23. [FoundationCompactCanonicalDecodeLength.lean](../integration/FoundationCompactCanonicalDecodeLength.lean)、
    [FoundationCompactProofCanonicalDecodeLengthComplete.lean](../integration/FoundationCompactProofCanonicalDecodeLengthComplete.lean)
    和 [FoundationCompactCertificateCanonicalDecodeLength.lean](../integration/FoundationCompactCertificateCanonicalDecodeLength.lean)
    已把界加强为完整规范编码长度：任意成功解码的自然数、项、公式、序列、十种证明规则、
    23 种 PA 公理证书及递归结构证书，其规范重编码连同未消费后缀均不长于原输入。符号解码
    固定使用 `Encodable.decode₂`（规范可重编码解码），最终 `verifier = true` 的完整证明与
    证书规范码不长于诚实载荷。关键定理公理画像仍只有上述三个 Lean 标准公理。
24. [FoundationCompactVerifierBitCostPrimitives.lean](../integration/FoundationCompactVerifierBitCostPrimitives.lean)
    和 [FoundationCompactVerifierFormulaListChecks.lean](../integration/FoundationCompactVerifierFormulaListChecks.lean)
    已给逐位相等、成员、包含、集合等价及自然数二进制相等定义同步返回结果与步数的递归
    trace（轨迹），证明结果精确且有显式乘法界；公式列表检查还把生成全部规范公式码的位数
    计入成本，不再把有限集 `decide` 或重编码当成免费步骤。
25. [FoundationCompactListedCertifiedVerifier.lean](../integration/FoundationCompactListedCertifiedVerifier.lean)
    和 [FoundationCompactListedCertifiedEncoder.lean](../integration/FoundationCompactListedCertifiedEncoder.lean)
    已保留解码时的 list sequent（列表序列），用第 24 项替换原不透明有限集局部检查，并证明
    十种规则全部投影回原 Foundation checker。新验证器接受必恢复同公式真实 PA 推导；反向
    每棵真实 `Derivation2` 都产生含全部证书、被新验证器接受的规范码，故该检查器不是空的或
    人为缩窄的替代系统。soundness/completeness（可靠性/完备性）端点均无项目公设。
26. [FoundationCompactNatDecoderCost.lean](../integration/FoundationCompactNatDecoderCost.lean)、
    [FoundationCompactSyntaxDecoderCost.lean](../integration/FoundationCompactSyntaxDecoderCost.lean)、
    [FoundationCompactListedProofDecoderCost.lean](../integration/FoundationCompactListedProofDecoderCost.lean)、
    [FoundationCompactCertificateDecoderCost.lean](../integration/FoundationCompactCertificateDecoderCost.lean) 和
    [FoundationCompactListedCertifiedDecoderCost.lean](../integration/FoundationCompactListedCertifiedDecoderCost.lean)
    已把自然数、向量、项、公式、列表序列、十条证明规则、23 种 PA 公理证书、递归结构证书、
    自然数打包外壳以及公开验证器全部改写为同步返回结果和成本的 trace（轨迹）。Lean 已逐层证明
    每个轨迹的结果与原可执行定义完全相同；公开端点的公理画像仍只有 `propext`（命题外延）、
    `Classical.choice`（经典选择）和 `Quot.sound`（商类型可靠性），无 `sorryAx`。这一步只闭合
    result equivalence（结果等价）。随后
    [FoundationCompactDecoderCostPotential.lean](../integration/FoundationCompactDecoderCostPotential.lean)、
    [FoundationCompactSyntaxDecoderCostPotential.lean](../integration/FoundationCompactSyntaxDecoderCostPotential.lean)、
    [FoundationCompactListedProofDecoderCostPotential.lean](../integration/FoundationCompactListedProofDecoderCostPotential.lean)、
    [FoundationCompactCertificateDecoderCostPotential.lean](../integration/FoundationCompactCertificateDecoderCostPotential.lean) 和
    [FoundationCompactPackedDecoderCostPotential.lean](../integration/FoundationCompactPackedDecoderCostPotential.lean)
    已对成功与全部失败路径闭合 consumed-prefix potential（已消费前缀势能）四次界；两个公开打包
    解码器成本均不超过 `2 * decoderPotential(Nat.size code)`。这只证明 decoder（解码器）多项式，
    尚未自动证明递归局部证书检查或整个公开验证器多项式。
27. [FoundationCompactSyntaxTransformationCodeBounds.lean](../integration/FoundationCompactSyntaxTransformationCodeBounds.lean)
    已把第 22 项的符号数界提升到完整二进制码长：`shift`（移位）、`free`（自由化）和
    negation（否定）均至多线性膨胀；对一元公式 `phi` 与闭项 `t`，Lean 内核证明
    `|phi[t]| <= 3*(|phi|+1)*(|t|+1)*|phi|`。证明显式处理 `qpow`（量词下重写迭代），
    先证每层 `bShift`（束缚变量移位）只有加法开销，再用公式符号数作为统一深度预算，
    因而没有逐层倍增、隐藏深度参数或 `sorryAx`。关键端点公理画像仍只有三个 Lean 标准公理。
28. [FoundationCompactListedProofHonestWeight.lean](../integration/FoundationCompactListedProofHonestWeight.lean)
    已定义保留 list sequent（列表序列）重复项的
    `listedProofHonestBitWeight`（列表证明诚实位权），并对十条 PA 规则统一证明：
    任意成功解码都满足
    `weight(tree) + 8 * suffix.length <= 8 * input.length`。该界覆盖非规范但成功的输入，
    每个重复公式均单独计费，不通过 `toFinset`（转有限集）丢失数据量。
    统一端点无 `sorryAx`，公理画像仅有 `propext`、`Classical.choice`、`Quot.sound`。
29. [FoundationCompactListedCertifiedHonestWeight.lean](../integration/FoundationCompactListedCertifiedHonestWeight.lean)
    已把第 28 项的证明树位权与完整
    `StructuralValidityCertificate`（结构有效性证书）规范二进制码长合并，内核证明：
    任意成功打包解码都满足
    `jointWeight(tree, certificate) <= 8 * packedPayloadLength(code)`。因此 23 种 PA 公理标签、
    归纳公理体及一元/二元递归证书全部由实际输入位计费，无隐藏见证或长度参数。
    三个公开端点无 `sorryAx`，公理画像仍仅有三个 Lean 标准公理。
30. [FoundationCompactListedLocalCostPrimitives.lean](../integration/FoundationCompactListedLocalCostPrimitives.lean)
    已把 `formulaEqTrace`、`formulaMemTrace`、`formulaSubsetTrace` 和
    `formulaSetEqTrace`（公式相等/成员/包含/集合等价轨迹）的真实位成本统一压到
    `P(w) = 4 + 2*(w+3)^2 + w`，其中 `w` 是全部输入公式码位权，列表重复项仍逐个计入。
    四个端点及多项式单调性全部通过，无 `sorryAx`。
31. 同一文件已证明 proof-node count（证明节点数）不超过证明树诚实位权，并固定
    `G(w)=3*(w+1)^3+4*w+32` 和 `C(w)=8*P(G(w))+16` 两个显式多项式。
    `closed`、`verum`、`and`、`or`、`all`、`exs`、`wk`、`shift`、`cut` 九条规则的局部成本
    分支已全部通过；每条定理都将子证明递归成本与当前节点成本显式分开。
    只剩 `axm`（PA 公理规则）要接入带守卫的公理比较器后才能做十规则统一归纳。
32. 同一文件的
    `listedCertificateValidTrace_jointCost_le_polynomial_of_axm`（给定公理分支界的联合坐标证书检查总成本定理）
    已完成十规则证明树/证书同步归纳。令
    `b = proofWeight + certificateWeight`（证明树与证书联合诚实位权）；若具体 `axm` 局部成本不超过
    `C(局部联合位权)`，整树成本就不超过 `b*C(2*b)`。
    这是内部归纳骨架，不是最终无条件端点；它将全部剩余局部问题隔离为唯一命名义务 `haxm`。
    下一步必须用具体 guarded axiom comparator（带守卫公理比较器）的定理消掉 `haxm`；
    公开端点不得保留该参数。归纳骨架的公理画像仅有三个 Lean 标准公理。
33. [FoundationCompactListedPublicCostSkeleton.lean](../integration/FoundationCompactListedPublicCostSkeleton.lean)
    已把两个 packed decoder（打包解码器）、局部证书检查、结论集合比较和公式自然数码比较汇总到公开轨迹。
    令 `s = Nat.size(code) + Nat.size(formulaCode)`，Lean 已证明：若具体证书检查满足第 32 项的联合多项式界，
    公开验证器总轨迹成本就不超过
    `Q(s)=4*decoderPotential(s)+L(s)+1`，其中 `L(s)` 由已定义的联合成本、列表比较成本和线性码比较成本显式组成。
    该公开汇总骨架无 `sorryAx`，公理画像仅有三个 Lean 标准公理；它与第 32 项共享同一个必须消掉的具体 `haxm` 义务。
34. [FoundationCompactSyntaxNegationTrace.lean](../integration/FoundationCompactSyntaxNegationTrace.lean)
    已把 `Semiformula.neg`（公式否定）的真实递归执行单独显式化：轨迹结果精确等于 `∼formula`，每访问一个公式构造收费一步，
    原子式中的项向量按原定义直接复用而不虚构遍历。Lean 已证明该成本不超过 `formulaSymbolCount`（公式符号数），进而不超过
    输入 `binaryFormulaCode`（二进制公式码）的位长。该端点用于给 `closed`（闭合）和 `cut`（切）规则中生成 `∼formula`
    的执行补齐计费；单文件探针通过，公理画像仅有三个 Lean 标准公理，无 `sorryAx`。
35. [FoundationCompactListedAxiomJointWeight.lean](../integration/FoundationCompactListedAxiomJointWeight.lean)
    已把 `axm`（公理）节点的三个真实输入压到同一个 `listedLocalJointHonestBitWeight`（局部联合诚实位权）：
    上下文列表位权、候选句子二进制码长、公理证书二进制码长均分别不超过该联合位权，并得到
    `certificateBits + sentenceBits + 1 <= 2 * jointWeight + 1`。这使带守卫比较器的成本界可直接转到解码输入坐标，
    不再需要外部证书长度参数。四个定理通过，公理画像仅有 `propext` 和 `Quot.sound`，无 `sorryAx`。
36. [FoundationCompactListedMinProofLength.lean](../integration/FoundationCompactListedMinProofLength.lean)
    已直接在 `listedCompactCertifiedPAProofVerifier`（列表保持带证书验证器）上定义
    `minListedCertifiedPAProofPayloadLength(formula)`：最小化对象是完整证明树与完整结构证书共同形成的
    `packedPayloadLength`（打包有效载荷长度）。Lean 已证明真实同结论 `Derivation2`（推导树）保证接受集合非空、
    最小值由某个实际接受码实现、该值不超过任意接受码长度，并且任何接受码都恢复同公式真实 PA 推导。
    因此最终长度函数已有具体 checker-induced semantics（检查器诱导语义），不再需要项目级 `proof_length` 公设。
    五个端点公理画像仅有三个 Lean 标准公理，无 `sorryAx`。
37. [FoundationCompactListedFiniteConsistencyTarget.lean](../integration/FoundationCompactListedFiniteConsistencyTarget.lean)
    已在同一个 `ListedCertifiedPAProofOf`（列表保持带证书证明关系）和同一个完整
    `packedPayloadLength`（打包有效载荷长度）上定义 `ListedCertifiedFiniteConsistencyAt(k)`：
    不存在载荷长度不超过 `k` 且验证器接受为 `⊥` 的码。由接受码到真实同结论 `Derivation2`（推导树）的可靠性，
    Lean 无条件证明普通 cutoff 及 `2^(A*n)` 放大版本均为真。四个端点公理画像仅有三个 Lean 标准公理，无 `sorryAx`。
    该节点是后续 `Con_PA^compact(k)` 算术句必须逐点表示的精确元层语义，不等于算术化本身。
38. [FoundationCompactListedCanonicalNormalization.lean](../integration/FoundationCompactListedCanonicalNormalization.lean)
    已证明任意被列表保持验证器接受的 code（证明码）都可重编码为同公式的
    canonical code（规范码），且完整 proof + certificate payload（证明与证书载荷）长度不增加。
    进一步，`minListedCertifiedPAProofPayloadLength`（最短列表带证书证明载荷长度）必由一个真实
    规范码精确实现，并且“量化全部接受码”与“只量化规范接受码”的 finite consistency（有限一致性）
    在每个相同 cutoff（截断值）上逐点等价，没有常数损失。因此非规范、重复或畸形序列化不能把最短值人为压低；后续算术化可限制到规范关系，
    但仍必须证明该规范关系的 PA 内部短计算轨迹。同一文件还固定了纯自然数坐标
    `CanonicalListedCertifiedCodedPAProofOf(code, formulaCode)`；任意公开验证器接受输入都能无损归一化到
    同一个 `formulaCode` 的该关系，且其 falsum（矛盾式）有限一致性与原元层定义逐点同 cutoff 等价。
    同时已给出确定的 `canonicalListedCertifiedCodedPAProofVerifier`（规范数值证明布尔验证器），并证明
    `verifier = true` 当且仅当上述 `P_canon(code, formulaCode)` 成立。该节点当前是 normalization audit（规范化审计），
    不替换主路线的公开 guarded verifier（带守卫验证器）；最终 `CompactProof` 仍表示公开验证器，除非另行把
    `P_canon` 的总成本与 Pudlak 条件全部在同一坐标重证。八个端点公理画像仅有三个 Lean 标准公理，无 `sorryAx`。
39. [FoundationCompactDerivationSpecialization.lean](../integration/FoundationCompactDerivationSpecialization.lean)
    已在真实 PA `Derivation2`（具体推导树）中构造
    `cut(wk(base), exs(closed))` 的显式全称实例化证明对象，证明其 checker tree（检查器证明树）有效，
    给出精确二进制码长等式，并证明实例化证明长度不超过固定基证明长度加输入公式码长与闭项码长的显式三次多项式。
40. [FoundationCompactCertifiedDerivationSpecialization.lean](../integration/FoundationCompactCertifiedDerivationSpecialization.lean)
    已为第 39 项实例化证明构造显式结构证书
    `binary(unary(baseCertificate), unary(leaf))`，证明证书码长只增加固定常数；随后生成具体打包自然数码，
    并由公开 `listedCompactCertifiedPAProofVerifier` 证明接受。完整 `proof + certificate payload`（证明与证书载荷）
    仍满足三次界，不再只计证明树而漏掉证书。
41. [FoundationCompactBinaryNumeralTerm.lean](../integration/FoundationCompactBinaryNumeralTerm.lean)
    没有使用 Foundation 默认的一元数词，而是以 `2 * previous + bit` 构造短二进制数码项。
    Lean 已证明每一位只增加固定、无参数、可执行的 `binaryNumeralStepBudget`，故总项码长线性受
    `Nat.size n` 控制；同时该项在标准自然数模型中的值严格等于 `n`。
42. [FoundationCompactParameterizedDiagonalSpecialization.lean](../integration/FoundationCompactParameterizedDiagonalSpecialization.lean)
    已把 `parameterized_diagonal₁` 的固定全称证明一次性转换为同一 PA `Derivation2`，再用第 39 至 41 项
    对任意 `m` 构造真实对角实例证明及公开验证器接受的完整打包码。最终载荷端点给出
    `baseProofConstant + baseCertificateConstant + 192 + 2048 * (formulaConstant + stepConstant * Nat.size m + 1)^3`
    的显式界，并进一步证明同一公式实例的精确
    `minListedCertifiedPAProofPayloadLength`（最短列表带证书证明载荷长度）不超过该界。
    第 39 至 42 项全部探针通过，端点公理画像仅有 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。
43. [FoundationCompactCertifiedModusPonens.lean](../integration/FoundationCompactCertifiedModusPonens.lean)
    已在同一列表保持公开验证器和完整 `proof + certificate payload`（证明与证书载荷）上闭合
    bounded modus ponens compiler（有界肯定前件编译器）。对任意两个分别被接受为 `A -> B` 与 `A`
    的实际输入码，Lean 构造被同一验证器接受为 `B` 的规范输出码，并证明
    `outputPayload <= implicationPayload + antecedentPayload + 240 + 34*S(A,B)`。两份输入证书原样复用，
    没有隐藏 proof-existence（证明存在性）或长度参数。该结果关闭 condition (3) 的外部码合成部分；
    将这一合成及其界证明为 PA 内部短证明仍属于第 2 项根义务。全部端点公理画像仅有三个 Lean 标准公理。
44. [FoundationCompactCertifiedConjunction.lean](../integration/FoundationCompactCertifiedConjunction.lean)
    已用同一方法闭合 conjunction compiler（合取编译器）：任意被公开验证器接受为 `A` 与 `B`
    的两个完整码可组合为被接受为 `A and B` 的规范码，且
    `outputPayload <= leftPayload + rightPayload + 144 + 11*S(A,B)`。两棵输入证明树与两份完整证书
    均原样进入输出，无外部长度参数。它关闭 bounded proof assembly（有界证明拼接）的第二个外部原语；
    固定重言式实例化、PA 内部化及原文步骤 (i)-(v) 的整体链仍待完成。
45. [FoundationCompactListedGuardedAxiomCost.lean](../integration/FoundationCompactListedGuardedAxiomCost.lean)
    已以 candidate-length guard（候选句长度守卫）修复稀疏大自由变量编号导致的
    `univCl` 指数执行漏洞，闭合 23 个公理标签、十规则整树及公开打包验证器的固定多项式
    总位成本界。最终端点已无 `haxm`，结果逐点等于同一带守卫验证器。
46. 纯数值图已闭合 packed token stream（打包记号流）、项/公式/序列值解析、公式列表检查、
    六种直接公式构造以及否定、移位、自由化和单变量代入记号机。其中
    [FoundationCompactNumericFormulaSubstitution.lean](../integration/FoundationCompactNumericFormulaSubstitution.lean)
    证明了纯 `Nat`/`List Nat` 运行图的代入结果逐 token 等于
    `((Rew.subst ![w]).qpow d)`；规范端点保留同一 suffix，公理画像只有三个 Lean 标准公理。
47. [FoundationCompactNumericFixedPAAxiomSentence.lean](../integration/FoundationCompactNumericFixedPAAxiomSentence.lean)
    已将证书标签 `0..21` 的 22 个非归纳 PA 公理分支做成纯数值句 token 表。
    函数外延的四个合法 `(arity, symbolCode)` 和关系外延的两个合法对均显式分派；
    查表函数已证 `Primrec`（原始递归），每个规范固定证书逐 token 等于同一
    `certificate.sentence`。标签 `22` 的归纳句是当前唯一剩余公理构造分支。
48. [FoundationCompactNumericFormulaFixitr.lean](../integration/FoundationCompactNumericFormulaFixitr.lean)
    已将 `Rew.fixitr n m`（变量捕获转换）落实为只含 `Nat`/`List Nat` 的单遍 token 机器。
    任意量词深度下，bound variable（约束变量）保持不变，`i < m` 的 free variable（自由变量）
    精确转成 `#(n+d+i)`，其余转成 `&(i-m)`；项、项列表和公式任务均已证明逐 token 等于
    `((Rew.fixitr n m).qpow d)`。step（单步）、bounded run（有界运行）和公开变换均已证
    `Primrec`（原始递归）。定向探针退出码为 0，十个审计端点至多只依赖三个 Lean 标准公理。
49. [FoundationCompactNumericSuccIndSentence.lean](../integration/FoundationCompactNumericSuccIndSentence.lean)
    已把标签 `22` 的 `succInd(body)`（后继归纳公式）落实为纯数值组合函数。每个子变换必须完整消费
    输入公式 token，四条代入执行、三次否定、三个析取和两个全称量词在同一失败语义下组合；
    整体已证 `Primrec`（原始递归），并对任意规范 `body` 逐 token 精确等于原 `succInd body`。
    定向探针退出码为 0，关键端点只依赖三个 Lean 标准公理，无旧原始码或隐藏长度参数。
50. [FoundationCompactNumericFormulaFvSup.lean](../integration/FoundationCompactNumericFormulaFvSup.lean)
    已用同一纯数值语法任务栈闭合 `fvSup`（自由变量上确界）。机器只在真实 term（项）位置
    收集自由变量编号，结果逐点等于 `formula.fvarList`；`listFvSup` 的 `max(index+1)` 折叠也已独立
    证明为 `Primrec`（原始递归）。公开端点在任意规范公式上精确返回 `formula.fvSup` 与同一 suffix。
    定向探针退出码为 0，关键端点只依赖三个 Lean 标准公理。
51. [FoundationCompactNumericAllClosure.lean](../integration/FoundationCompactNumericAllClosure.lean)
    已将 `∀⁰* formula`（迭代全称闭包）落实为纯数值 token 迭代：每一步真实前置一个全称量词
    token，整体已证 `Primrec`（原始递归），并对任意 `arity = depth` 的规范公式逐 token 等于
    原依赖类型闭包。该节点不单独声称按二进制 `depth` 多项式时间；其执行现由第 53 项的
    `depth <= candidate bit length`（深度不超过候选句位长）纯数值守卫控制。
52. [FoundationCompactNumericTokenBitLength.lean](../integration/FoundationCompactNumericTokenBitLength.lean)
    已把每个 Nat token 用公开 `binaryNatCode`（二进制自然数码）重新编码，并证明任意 token 列表
    的总位长函数为 `Primrec`（原始递归）。项和公式的规范 token 流重新编码后逐位等于原公开
    `binaryTermCode` / `binaryFormulaCode`；因此候选公式的守卫使用真实 `formulaCode` 位长，
    不是 token 数量，也没有换长度坐标。定向探针退出码为 0，静态禁用项扫描为空。
53. [FoundationCompactNumericGuardedInductionSentence.lean](../integration/FoundationCompactNumericGuardedInductionSentence.lean)
    已闭合标签 `22` 的纯数值带守卫构造与比较。机器先构造 `succInd(body)`、计算精确 `fvSup`，
    仅在 `fvSup <= candidate formulaCode bit length` 时执行 `fixitr` 与 `allClosure`；对每个规范
    `body/candidate`，最终布尔值为真当且仅当真实 PA 归纳证书句等于候选句。守卫拒绝分支由既有
    `inductionSentenceGuardTrace_complete`（归纳句守卫完备性）排除漏接。全部构造器与比较器已证
    `Primrec`，关键端点公理画像仅为 `propext`、`Classical.choice`、`Quot.sound`。
54. [FoundationCompactNumericPAAxiomComparator.lean](../integration/FoundationCompactNumericPAAxiomComparator.lean)
    已把固定标签 `0..21` 与动态标签 `22` 合并为同一个纯数值 PA 公理比较器。最外层要求
    `compactPAAxiomCertificateTokenParser`（PA 公理证书记号解析器）精确返回空后缀，所以多余垃圾、
    非法函数/关系符号码和畸形归纳体均不能进入接受分支。对任意证书 token 和任意规范候选句，
    比较器为真当且仅当存在真实 `PAAxiomCertificate`，输入恰为其完整规范 token，且
    `certificate.sentence = candidate`。完整函数已证 `Primrec`，关键公理画像仍只有三个 Lean 标准公理。
55. [FoundationCompactNumericListedRuleChecks.lean](../integration/FoundationCompactNumericListedRuleChecks.lean)
    已闭合 `closed/axm/verum/and/or/all/exs/wk/shift/cut` 十条规则的全部纯数值局部合并器。
    输入只含已解析公式 token、序列 token 列表和子节点返回的布尔值；`free`、代入、否定和整序列移位
    均调用真实数值变换，`axm` 调用第 54 项同一 23 标签比较器。每条函数均已证 `Primrec`，并在
    规范字段上逐点等于 `listedCertificateValidTrace` 对应分支结果。子有效性是后续任务栈的递归返回值，
    不是外部 theorem/axiom（定理/公设）输入；关键公理画像仍只有三个 Lean 标准公理。
56. [FoundationCompactNumericListedNodeFields.lean](../integration/FoundationCompactNumericListedNodeFields.lean)
    已闭合 proof/certificate（证明/证书）两侧逐节点字段解析。证明标签 `0..9` 按公开编码顺序只消费
    父序列、主公式和见证项，并精确保留子证明流；结构证书的 `leaf/axiom/unary/binary` 四种形状
    同样只消费根标签，公理叶额外精确截取完整 PA 公理证书 token。两个 dispatcher（分派器）均已证
    `Primrec`，且对任意真实树/证书与任意 suffix 返回规范字段及同一后缀。关键公理画像仍只有三个
    Lean 标准公理，无类型化语法运行时输入。
57. [FoundationCompactNumericListedTaskMachine.lean](../integration/FoundationCompactNumericListedTaskMachine.lean) 与
    [FoundationCompactNumericListedPublicVerifier.lean](../integration/FoundationCompactNumericListedPublicVerifier.lean)
    已闭合完整公开局部检查纯数值图。有限任务栈同步消费证明/证书 token，核对递归形状，并把子结论与
    子布尔结果交给十条真实局部合并器；显式 fuel（燃料）覆盖完整规范树，其他路径统一拒绝。公开层对
    两个 sentinel-packed Nat（哨兵位打包自然数）做任意输入反演，并由
    `compactNumericListedPublicVerifier_pointwise` 证明新数值验证器与原公开验证器在每个
    `code/formulaCode` 上结果相等。两个模块的定向探针和目标构建均通过，禁用项扫描为空，端点公理画像
    只有 `propext`、`Classical.choice`、`Quot.sound`。
58. [FoundationCompactNumericListedProofPredicate.lean](../integration/FoundationCompactNumericListedProofPredicate.lean)
    已在同一完整载荷坐标上定义 `CompactListedPAProofPredicate(bound, formulaCode)`：存在载荷长度不超过
    `bound` 的 `code`，且第 57 项数值验证器返回 `true`。Lean 已证明其 witness relation（见证关系）
    原始递归、该谓词递归可枚举，并构造真实二变量 Σ₁ 算术公式。公式标准模型语义逐点等价于该谓词；
    以同一 `compactListedFalsumCode` 否定后，标准模型语义精确等价于
    `ListedCertifiedFiniteConsistencyAt(bound)`。表示层现固定一个 `Nat.ArithPart₁.Code`（算术部分递归程序码）
    并保留其 `Code.eval`（程序求值）证明，不再只暴露 `codeOfREPred` 的语义端点。短二进制数词实例符号数
    不超过固定公式常数乘 `6*Nat.size(bound)+6*Nat.size(formulaCode)+2`。目标构建通过，禁用项扫描为空，
    端点公理画像仅有三个 Lean 标准公理。另有明确命名的 qualitative（定性）端点证明接受实例在 PA 中
    可证且存在真实 `Derivation2`；它调用 Σ₁ 完备性且没有长度结论，不能替代下一步的定量 PA 接受轨迹。

    进一步源码审计确认：这条通用表示的实际构造链经过
    `REPred.projection -> Partrec.projection -> rfindOpt -> Nat.ArithPart₁.Code.rfind`。
    `Code.rfind` 的算术公式除成功阶段外，还要求所有更小搜索阶段失败。当前没有这个 bounded minimality
    （有界最小性）前缀的 PA 证明长度关于输入载荷位长的多项式界；搜索阶段还可能由数值很大的见证码控制。
    因此第 58 项保留为**定性语义审计**，不能作为 Theorem 3.1 的最终 suitable numeration（合适枚举）。
    这不是语义定理错误，而是定量路线不合格；依赖图已将它从黄色主链中分离。
59. [FoundationCompactNumericListedDirectTrace.lean](../integration/FoundationCompactNumericListedDirectTrace.lean)
    已建立不经最小化搜索的直接有限运行见证。对每个中央任务机状态，模块定义第 `i` 步真实状态及从
    `0` 到 `fuel` 的完整规范列表，证明列表长度精确为 `fuel+1`，且状态生成、索引与轨迹有效性均为
    `Primrec`/`PrimrecPred`。公开见证包同时记录两个 token 流、证明与证书解析结果、结论公式值和完整
    状态列表；最终端点对任意 `code/formulaCode` 证明：

    ```text
    compactNumericListedPublicVerifier(code, formulaCode) = true
      iff exists trace, CompactNumericListedDirectTraceValid(code, formulaCode, trace).
    ```

    单文件探针退出码为 0，六个审计端点公理画像只有三个 Lean 标准公理。该模块不调用
    `projection/rfind`。
60. 同一模块又把中央状态链加强为真正的 local tableau（局部计算表）。
    `CompactNumericVerifierLocalTraceValid` 要求列表长度精确为 `fuel+1`、第 0 行为同一公开初态，且每个
    `i<fuel` 的下一行严格等于 `compactNumericVerifierStep` 作用于当前行。Lean 已分别证明单步关系、长度、
    初态和总局部谓词原始递归；规范轨迹满足局部表，任意合法局部表又逐行等于规范轨迹。公开直接见证已
    正式改用该局部谓词，并保留第 59 项的双向接受等价。定向探针退出码为 0，公理画像仍只有三个标准项。

    当前边界缩小为组件内部：packed payload、binary-Nat token stream、proof/certificate/formula parser
    和局部语法变换仍以精确函数等式核对结果，尚未统一携带内部状态子轨迹；全部状态与子轨迹也尚未给出
    面向最终算术公式的显式自然数编码和多项式位长界。
61. [FoundationCompactPackedTokenStreamDirectTrace.lean](../integration/FoundationCompactPackedTokenStreamDirectTrace.lean)
    已关闭两个公开输入最外层的 packed/token 子轨迹。见证记录 sentinel（哨兵位）剥离后的真实 payload，
    并用 `BinaryNatStreamLocalTraceValid` 逐行检查精确行数、初态和每个 `binaryNatStreamStep`；规范流轨迹
    满足局部表，任意合法局部表恢复同一有界运行，最终状态输出严格等于目标 token 列表。Lean 已证明：

    ```text
    compactPackedTokenStream(code) = some tokens
      iff exists trace, CompactPackedTokenStreamDirectTraceValid(code,tokens,trace).
    ```

    proof code（证明码）和 formula code（公式码）的两份子轨迹均已接入第 59 项总见证，总见证不再直接
    以 `compactPackedTokenStream = some ...` 作为黑箱结果条件。新子模块目标构建及总见证探针均退出 0，
    公理画像仍只有三个 Lean 标准项。

62. [FoundationCompactParserDirectTrace.lean](../integration/FoundationCompactParserDirectTrace.lean)
    已打开 proof/certificate/formula parser（证明/证书/公式解析器）的三个外层有界迭代。三者共用同一
    local initial/step/final tableau（局部初态/单步/终态计算表）：轨迹长度精确为 `fuel+1`，第 0 行为
    真实初态，每个后继行由对应 `parserStep` 产生，末行输出为指定 suffix。规范轨迹满足局部表，任意合法
    局部表又恢复同一规范运行；Lean 对三个公开解析器分别证明“返回 `some suffix` 当且仅当存在合法局部
    轨迹”。三个有效性谓词均为 `PrimrecPred`。

    三份解析器轨迹已进一步接入第 59 项总公开见证；总见证的双向接受等价和原始递归性再次通过单文件
    探针。新模块目标构建、单模块探针和总见证探针均退出 0，全部审计端点公理画像仍只有
    `propext`、`Classical.choice`、`Quot.sound`。本检查点关闭的是三个 outer iterator（外层迭代器）；
    各 `parserStep/verifierStep` 内部调用的原子字段解析、`certified parts/formula value` 数值提取及局部
    语法变换仍是下一段黄色义务，尚未被误标为绿色。
63. [FoundationCompactNumericListedParseDecomposition.lean](../integration/FoundationCompactNumericListedParseDecomposition.lean)
    已把第 62 项之后仍存在的两个解析结果包装层精确拆开。对任意输入，Lean 证明
    `compactNumericCertifiedPartsParser = some parts` 当且仅当存在一个显式 root node（根节点），使同一
    proof parser 返回 `parts.2.1`、同一 certificate parser 完全消费该后缀、`parts.1` 严格等于输入减去
    证书后缀的 consumed prefix（已消费前缀）、根字段解析器返回该 root，且结论字段严格相等。另证明
    `compactNumericWholeFormulaValue = some value` 当且仅当同一 formula parser 返回空后缀并且
    `value = formulaTokens`。两个残余关系均已证 `PrimrecPred`。

    root node 已加入第 59 项的总公开见证；`DirectTraceValid` 中原来的两个整包装函数结果等式已完全删除，
    只保留显式前缀、根结果和 token 等式。总见证的原始递归性及
    `publicVerifier=true iff exists DirectTraceValid` 再次通过探针，公理画像仍只有三个 Lean 标准项。
    当前边界已精确落到 `compactListedProofNodeFieldsParser` 的十标签分派及其内部
    sequent/formula/term value parser（序列/公式/项值解析器），不再停留在包装函数。
64. [FoundationCompactNumericListedRootFieldsDecomposition.lean](../integration/FoundationCompactNumericListedRootFieldsDecomposition.lean)
    已继续删除 `compactListedProofNodeFieldsParser` 的十标签总分派黑箱。新关系直接匹配输入首 token：空流
    和标签不在 `0..9` 时严格为假；标签 `0..9` 分别选择公开定义中的 sequent-only、sequent+formula、
    sequent+two-formula、sequent+closed-formula 或 sequent+formula+term 分支，并同时要求 `root.1` 等于
    该标签、所选分支精确返回 `root.2`。Lean 已证明 whole root parser 返回 `some root` 当且仅当这条
    十分支关系成立，且该关系为 `PrimrecPred`。

    第 63 项的 certified-parts residual 已改用新十分支关系，因此总公开见证不再含 whole root parser
    结果等式。新模块目标构建、分解模块探针和总见证探针均通过；等价端点只需 `propext`，原始递归端点
    仍只有三个 Lean 标准依赖。当前边界继续下沉到所选标签分支内部的 sequent/formula/closed-formula/term
    value parser，下一步先打开 sequent value repeat（序列值重复迭代）及每个公式子运行。
65. [FoundationCompactSequentValueDirectTrace.lean](../integration/FoundationCompactSequentValueDirectTrace.lean)
    已打开 sequent value parser 的外层 counted repeat（按数目重复迭代）。输入首 token 严格作为公式数目，
    空输入拒绝；局部状态表长度精确为 `count+1`，第 0 行为 `some([], tokenTail)`，每个后继行严格等于
    `compactFormulaTokenValuesStep` 作用于前一行，末行严格为 `some(values,suffix)`。Lean 已证明规范表满足
    局部关系、任意合法表逐行等于同一规范运行，并得到公开 sequent value parser 返回目标结果当且仅当
    存在该局部表。状态表有效性及公开 trace relation（轨迹关系）均为 `PrimrecPred`。

    本项现已进一步增强：公开见证除 `count+1` 行 repeat 状态外，还携带恰好 `count` 份第 62 项公式
    parser 局部轨迹。第 `i` 份轨迹必须把第 `i` 行剩余 token 精确解析到第 `i+1` 行后缀，且下一行公式值
    严格等于上一行列表追加真实 consumed prefix。Lean 已证明增强单步推出原
    `compactFormulaTokenValuesStep`，最终成功又能逐行构造全部子轨迹；因此公开 sequent parser 成功当且仅当
    存在增强见证，整函数单步不再作为外部条件。单模块探针和目标构建通过，全部新增端点公理画像仍只有
    三个 Lean 标准项。剩余工作是把该增强见证按第 64 项 root 标签组合进节点字段分支。
66. [FoundationCompactParserDirectTrace.lean](../integration/FoundationCompactParserDirectTrace.lean)
    已补齐同一共享局部表框架的 term parser（项解析器）和 closed-formula parser（闭公式解析器）实例。
    term 端点使用真实 `compactSyntaxParserStep` 与 term 初态；闭公式端点使用
    `compactClosedSyntaxParserStep`，因此自由变量拒绝路径没有被普通公式 parser 偷换。两类有效性关系都核对
    精确燃料行数、初态、每个真实单步和最终 suffix，并分别证明公开 parser 返回 `some suffix` 当且仅当
    存在该局部轨迹。四个新端点均为 `PrimrecPred`/精确双向等价，探针和目标构建通过，公理画像只有三个
    Lean 标准项。至此 root 各分支需要的 sequent/formula/term/closed-formula 外层轨迹全部具备；下一义务是
    构造统一 branch trace（分支轨迹），并强制未使用的分支轨迹为空。
67. [FoundationCompactNumericListedRootFieldsDirectTrace.lean](../integration/FoundationCompactNumericListedRootFieldsDirectTrace.lean)
    已闭合 root-field branch trace（根字段分支轨迹）并接入公开总见证。一个统一见证容纳 sequent、两份
    formula、term 与 closed-formula 子轨迹；五种字段形状分别证明 parser 成功当且仅当存在直接轨迹，
    未使用分量必须为空，五类有效性关系均为 `PrimrecPred`。其上再按公开标签 `0..9` 精确分派；空流和
    未知标签无见证，whole root parser 成功当且仅当存在 tag-selected direct trace（标签选择直接轨迹）。
    [FoundationCompactNumericListedParseDecomposition.lean](../integration/FoundationCompactNumericListedParseDecomposition.lean)
    已用该关系替换旧 branch-result relation，并显式返回 `rootTrace`；
    [FoundationCompactNumericListedDirectTrace.lean](../integration/FoundationCompactNumericListedDirectTrace.lean)
    已把 `rootTrace` 加入总数据、总有效性和正反向总等价。定向探针与必要目标构建通过，关键端点公理画像
    只有三个 Lean 标准项。下一边界是显式 Nat 编码、`verifierStep` 内部原子算术图及统一多项式位长界。
68. [FoundationCompactAdditiveTokenCodec.lean](../integration/FoundationCompactAdditiveTokenCodec.lean)
    已建立加法型 typed token codec（类型化 token 编解码）。默认 `Encodable (List α)` 的
    `succ(pair(head,tailCode))` 递推虽为原始递归，但直接位长界可逐层翻倍，故已明确弃用。新 codec 对
    `Nat/Bool/Option/Product/List` 使用单 token、固定标签、直接拼接和“长度头 + 逐元素串联”；所有类型均
    证明 `decode(encode(x) ++ suffix)=some(x,suffix)`，编码、解码和计数迭代均为原始递归，列表总位长
    精确等于长度头加各元素位长之和。`binaryNatCode` 与 `packBinaryString` 也已补证原始递归，打包码位长
    精确为平坦 token 位长加一。

    [FoundationCompactNumericListedDirectTraceCode.lean](../integration/FoundationCompactNumericListedDirectTraceCode.lean)
    已把该 codec 分层实例化到完整 `CompactNumericListedDirectTrace`：总 token 往返、单一 Nat 打包码与
    解码器原始递归、`decode(code(trace))=some trace`、编码单射及精确 `Nat.size` 等式全部通过；关键端点
    公理画像仍只有三个 Lean 标准项。尚未闭合的是合法总轨迹位长关于两项公开输入位长的固定多项式界，
    以及 `verifierStep` 内部原子关系的直接算术图。
69. 同一两模块现已定义诚实结构位权
    `weight(tokens)=sum (Nat.size(token)+1)`，并证明打包码长精确为 `2*weight+1`。积类型位权严格相加；
    列表位权严格等于长度头成本加逐元素位权和，且“每项不超过 `B`”可推出总位权不超过
    `Nat.size(length)+1+length*B`。完整 `DirectTrace` 位权又被精确拆成十二个语义分量：两份 token、
    两份解包轨迹、三份 parser 轨迹、解析结果包、root、root-field 轨迹、公式值和中央状态表。
    全部探针无 `sorryAx`，公理画像仅三个 Lean 标准项。当前先证明最大分量中央状态表的逐行位权不变量。
70. [FoundationCompactNumericListedStateBounds.lean](../integration/FoundationCompactNumericListedStateBounds.lean)
    已闭合中央状态表的全部位权义务。节点 parser 成功时的 formula/term/Gamma 值均由
    原输入真实前缀或中缀控制；五种字段形状及十标签分派统一满足
    `fieldsWeight <= Nat.size(W)+1+W*W+4*W`。Lean 又逐分支证明 task/child 来源界被
    `nodeTransition`、`combineTransition`、`verifierStep` 及任意迭代保持；两栈数量不超过
    `1+2*fuel`。因此每行及 `fuel+1` 行整表均得到显式多项式位权界。所有总端点
    公理画像仅三个 Lean 标准项，无项目公设、无 `sorryAx`。十二分量中最大的第 12 项已闭合；
    下一步只对其余十一分量提取现有轨迹长度界并汇总总码长。
71. [FoundationCompactNumericListedDirectTraceBounds.lean](../integration/FoundationCompactNumericListedDirectTraceBounds.lean)
    前十一分量现已全部闭合。`certifiedTokens`、`formulaTokens`及与后者相等的
    `formulaValue` 均由公开码 `Nat.size` 显式控制；`parts/root` 由同一 proof prefix、
    certificate suffix、Gamma 及十标签分派控制。两份 packed-stream trace 又已通过
    “真实已解码 token 前缀 + 同一 bit suffix + 对应 status”全程不变量得到显式整表界。
    proof/certificate/formula 三类 parser trace 均逐分支证明流来源、任务字段、栈高、status、逐行重量
    和整表 fuel 界。root-field nested trace 又打开 sequent 的 `count+1` 外层状态、恰好 `count` 个逐公式
    子轨迹、term/closed-formula 真实执行机及五形状十标签分派；成功解析给出
    `count <= token weight`，排除了二进制 count 的指数表长风险。全部公开端点仅依赖三个 Lean 标准项，
    无项目公设、无 `sorryAx`。第 1..11 项与第 12 项中央状态表均已具备公开界；下一步按精确十二分量
    等式汇总完整 `traceWeight`，再用打包码长精确等式得到 `traceCode` 界。
72. 同一模块已完成上述汇总。中央状态表的实际 proof/certificate 流与线性 fuel 已提升到公开
    `Nat.size(code)` 预算；十二分量精确等式逐项实例化后得到完整 `traceWeight` 关于
    `Nat.size(code), Nat.size(formulaCode)` 的显式界，并由
    `Nat.size(traceCode)=2*traceWeight+1` 得到打包轨迹码长界。三个总端点公理画像仅三个 Lean 标准项。
73. [FoundationCompactNumericListedBoundedTraceCode.lean](../integration/FoundationCompactNumericListedBoundedTraceCode.lean)
    已把完整 typed trace（类型化轨迹）压成一个确定性 `traceCode : Nat` 证书。解码后直接调用已证明的
    `DirectTraceValid` 判定器，`CodeValid(code,formulaCode,traceCode)` 已证明为 primitive recursive
    （原始递归）；并精确证明 `publicVerifier=true` 当且仅当存在满足第 72 项显式 `Nat.size` 界的合法
    `traceCode`。同一模块又把全部分量界逐层组合，证明 `publicCodeSizeBound` 为二元原始递归函数，进而
    证明“`Nat.size(traceCode)` 不超过公开界且 `CodeValid`”这一完整 bounded witness（有界见证）为
    原始递归谓词。该链不使用搜索、`projection` 或 `rfind`，六个关键端点公理画像仅三个 Lean 标准项。
    当前入口已前移到 `verifierStep` 与各子关系的直接有界算术图和二变量 `Σ₁` 公式。
74. [FoundationCompactNumericListedDirectArithmeticPrimitives.lean](../integration/FoundationCompactNumericListedDirectArithmeticPrimitives.lean)
    已关闭第一项直接算术原语。Foundation 的 `lengthDef` 本身是无搜索的 `Σ₀/Δ₀` 二进制长度图；Lean
    又以 `Nat.binaryRec'` 分偶位、奇位证明标准自然数模型中的 `binaryLength n = Nat.size n`，从而得到
    `compactNatSizeDef(size,n) ↔ size = Nat.size n` 的逐点精确语义和层级证明。三个端点公理画像仅三个
    Lean 标准项。下一原子是复用 `lengthDef` 与 `bitDef`，为 packed `traceCode` 的终止哨兵、有效位前缀和
    token-stream 解码写直接有界图；不得退回通用程序表示。
75. 同一模块已关闭 packed payload sentinel（打包载荷终止哨兵）的直接图。任意 bit list 的
    `natOfBitsList` 严格小于 `2^length`，且真实 `packBinaryString(bits)` 精确等于
    `natOfBitsList(bits)+2^bits.length`。据此定义的 `compactPackedPayloadDef` 只使用 Foundation 的
    `expDef`、有界存在、加法和小于关系，层级严格为 `Σ₀/Δ₀`；其标准模型语义逐点等价于真实编码。
    全部新增端点仅依赖三个 Lean 标准项，无 `sorryAx`、`projection` 或 `rfind`。下一原子是按
    `binaryNatCode` 的 `1-bit pairs + 00 terminator` 对 payload 做自定界 token 分段图。
76. 同一模块已关闭单个 `binaryNatCode` token 段的直接图。Lean 先证明 Foundation 的
    `Bit(index,value)` 逐点等价于标准 `Nat.testBit value index`；随后
    `compactBinaryNatTokenSegmentDef(payload,offset,token,next)` 直接约束每个真实
    `(1,dataBit)` 二位组、末尾 `00` 终止符及
    `next = offset + 2*Nat.size(token)+2`。该公式标准模型语义逐点等价于真实段关系，层级严格为
    `Σ₀/Δ₀`；正式探针退出码 0，公理画像只有三个 Lean 标准项。下一义务是用有界
    `offsets/tokens` 序列把全部段拼成完整 token-stream tableau（记号流计算表），并证明首 offset 为 0、
    末 offset 等于 payload length。
77. 同一模块已关闭 fixed-width packed tableau（定宽打包计算表）原语。条目公式直接检查
    `Nat.size(value) <= width` 以及每个 `bit < width` 上
    `table[index*width+bit] = value[bit]`，标准模型语义逐点精确。规范 row-major（行优先）构造器
    又被证明能在每个合法索引恢复原列表值，并满足
    `Nat.size(tableCode) <= values.length*width`。因此 token/offset 序列表不会借 HFS 编码膨胀；正式探针
    退出码 0，公理画像仅三个 Lean 标准项。下一义务是用两份定宽表逐行拼接第 76 项的 token 段，并强制
    首 offset 为 0、末 offset 为 payload length。
78. [FoundationCompactNumericListedDirectTokenStreamTableau.lean](../integration/FoundationCompactNumericListedDirectTokenStreamTableau.lean)
    已关闭 token-stream tableau（记号流计算表）的规范正向构造。手写 `Σ₀/Δ₀` 公式用 token 表和累计
    offset 表逐行调用第 76 项关系，强制首 offset 为 0、末 offset 为完整 payload length。Lean 对任意真实
    token 列表逐位证明所有 marker/data/`00` 终止位，并构造两张规范表；其码长分别不超过
    `count*payloadLength` 与 `(count+1)*payloadLength`。五个正式端点探针退出码 0，公理画像仅三个标准项。
    公开 `decodeBinaryNat` 允许冗余高零位，所以任意原始 code 与规范段的逐码 `iff` 为假，禁止作为目标；
    该边界由第 79 项的规范反演和不增大规范化精确关闭。
79. [FoundationCompactNumericListedDirectTokenStreamInverse.lean](../integration/FoundationCompactNumericListedDirectTokenStreamInverse.lean)
    已关闭 token-stream tableau 的规范反向与非规范输入归一化。Lean 从任意合法定宽表唯一提取 token 和
    累计 offset，证明全部 offset 等于规范累计偏移、每个 payload bit 被某一 token 段覆盖，并由逐位外延
    得到 payload 精确等于提取 token 列表的规范重编码。因此 canonical tableau（规范计算表）与同一
    canonical packed code（规范打包码）双向等价，且可由当前公开 `compactPackedTokenStream` 解码回来。
    对公开解码器接受的冗余高零位 code，又构造同 token 的规范 code 并证明
    `Nat.size(canonicalCode) <= Nat.size(originalCode)`；故正确结论是“规范码逐点 `iff` + 保持 cutoff 的
    存在量词规范化”，而不是错误的原始码逐码 `iff`。十三个正式端点探针退出码 0，公理画像仅
    `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`、`projection`、`rfind` 或项目公设。
80. [FoundationCompactNumericListedDirectInputTableau.lean](../integration/FoundationCompactNumericListedDirectInputTableau.lean)
    已把 `proofCode` 与 `formulaCode` 两条公开输入流接入同一个直接算术关系。两份第 79 项规范表被合并为
    显式八变量 `Σ₀/Δ₀` 公式；任意接受的非规范 `proofCode` 可替换为同 token 的规范码，公开验证器结果
    逐点不变，`Nat.size` 与 `packedPayloadLength` 都不增加。接受条件本身又推出 `formulaCode` 等于其真实
    公式 token 流的规范打包码。最终得到原有“存在长度不超过 bound 的接受码”与“存在同 cutoff、携带
    两份规范算术表的接受码”的逐点 `iff`。九个正式端点探针退出码 0，仅依赖三个 Lean 标准公理或其
    子集；无 `sorryAx`、`projection`、`rfind` 或项目公设。
81. [FoundationCompactNumericListedDirectAdditiveCodecGraph.lean](../integration/FoundationCompactNumericListedDirectAdditiveCodecGraph.lean)
    已打开加法型 trace 编码的底层结构语法。`token cell`（单记号单元）在规范定宽表上随机读取一行并
    强制 `next=cursor+1`；list header（列表头）读取元素数并约束剩余 token；`List Nat` 切片精确占用
    一个头 token 加 `count` 个值 token。复合值统一使用严格递增 boundary table（边界表）保存每个分量
    的首尾游标，公式直接检查首尾行、所有中间行及相邻游标严格递增。任意给定的合法边界列表都能构造
    规范 row-major 表，且其码长不超过 `rows*tokenCount`。四类关系均为手写 `Σ₀/Δ₀` 公式；十三个
    正式端点探针退出码 0，仅依赖三个 Lean 标准公理或其子集，无项目公设或禁用表示路线。
82. [FoundationCompactNumericListedDirectTraceComponentTableau.lean](../integration/FoundationCompactNumericListedDirectTraceComponentTableau.lean)
    已关闭完整 trace 的顶层十二分量布局。模块按真实加法编码顺序显式列出 certified/formula 两流、三份
    parser trace、parts、root、root-branch trace、formula value 和 states，并证明完整 trace token 串精确
    等于这十二串依次 `flatten`。对 Nat、Bool、Option、Prod、List 递归建立的非空编码实例保证十二段均
    非空，故十三个累计边界严格递增、全部不超过 `tokenCount`，末边界精确等于完整串长度。规范边界表
    码长不超过 `13*tokenCount`；通用八变量 `Σ₀/Δ₀` 公式把规范 packed token 表和任意分量边界表合并，
    规范 typed trace（类型化轨迹）无条件产生 `partCount=12,start=0,finish=tokenCount` 的实例。十二个
    审计端点探针退出码 0，仅依赖标准三项或其子集。该项只关闭顶层分段，不把段内类型语法冒充已完成。
83. [FoundationCompactNumericListedDirectAdditiveTypeLayouts.lean](../integration/FoundationCompactNumericListedDirectAdditiveTypeLayouts.lean)
    已关闭加法编码四种通用类型构造子的直接布局。Bool 精确读取一个值为 `0/1` 的 token；Option 的
    `0` 标签强制空载荷，`1` 标签强制一个非空且有界的载荷区间；Prod 用严格中间游标分开两个非空分量；
    structured List 用 count header 和一张含 `count+1` 个游标的边界表分割所有非空元素。四个关系均为
    手写 `Σ₀/Δ₀` 公式，绑定变量下的内层公式调用通过有限坐标环境等式精确接线。十二个审计端点探针
    退出码 0，仅依赖标准三项或其子集。该项提供递归构造子，不提前宣称具体 trace 分量已经反演。
84. [FoundationCompactNumericListedDirectTraceNatListSlices.lean](../integration/FoundationCompactNumericListedDirectTraceNatListSlices.lean)
    已把三个真实 `List Nat` 分量接入其精确顶层边界。先证明该类型的加法编码严格等于
    `length :: values`，并建立任意分量的 `take/drop` 拼接分解、累计边界相邻差等于本段 token 长度，
    从而证明任何等于该编码的分量都在第 `i` 与 `i+1` 边界之间满足第 81 项直接 `Nat-list slice`。
    随后分别实例化 certifiedTokens（索引 0）、formulaTokens（索引 2）和 formulaValue（索引 10）。
    三段的 header、count 和 finish 均由真实规范 token 表随机读取，不允许任意切分。六个审计端点探针
    退出码 0，仅依赖标准三项，无项目公设或禁用表示路线。
85. [FoundationCompactNumericListedDirectTracePackedStreamSplits.lean](../integration/FoundationCompactNumericListedDirectTracePackedStreamSplits.lean)
    已关闭两份 packed-stream trace 的顶层积类型分割。通用定理证明任何等于
    `compactAdditiveEncode(left,right)` 的顶层分量都有精确中间游标
    `middle=start+|encode(left)|`，下一累计边界严格等于
    `middle+|encode(right)|`；两侧由非空 codec 定理保证严格非空，终点继续受完整 `tokenCount` 约束。
    随后实例化 certifiedStreamTrace（索引 1）与 formulaStreamTrace（索引 3），把各自的 payload 位列表
    和 BinaryNatStreamState 状态列表分离。两个审计端点探针退出码 0，仅依赖标准三项。
86. [FoundationCompactNumericListedDirectStructuredListCanonical.lean](../integration/FoundationCompactNumericListedDirectStructuredListCanonical.lean)
    已关闭任意 structured List 的规范直接计算表构造。模块证明列表编码精确等于 count token 后接全部
    element encodings（元素编码）的平坦拼接；元素编码非空保证 `count` 不超过列表体 token 长度。随后把
    元素累计边界整体平移到真实 `bodyStart`，证明首项、末项、逐项严格递增和完整 `tokenCount` 上界，
    并构造满足第 83 项公式的规范 elementBoundaryTable。表码长显式不超过
    `(count+1)*tokenCount`。八个审计端点探针退出码 0，仅依赖标准三项或其子集。该构造将统一复用于
    payload、stream states、parser states 和 verifier states，不再为每类列表重复引入编码接口。
87. [FoundationCompactNumericListedDirectTracePackedStreamListLayouts.lean](../integration/FoundationCompactNumericListedDirectTracePackedStreamListLayouts.lean)
    已把第 86 项实例化到两份 packed-stream trace 的四个真实字段。通用 pair-of-lists（列表对）定理先
    证明左列表终点与右列表起点严格等于第 85 项 product middle，且右列表终点等于对应顶层分量的下一
    累计边界；随后同时构造 proof/formula 两份 payload `List Bool` 和两份
    `List BinaryNatStreamState` 的四张元素边界表。每张表满足同一直接 structured-list 公式并保留
    `(count+1)*tokenCount` 码长界。两个审计端点探针退出码 0，仅依赖标准三项。
88. [FoundationCompactNumericListedDirectAdditiveTypeCanonical.lean](../integration/FoundationCompactNumericListedDirectAdditiveTypeCanonical.lean)
    已补齐 Bool、Option、Prod 三种布局从真实编码到直接见证的规范构造方向。任意前后缀中的 Bool 编码
    精确产生一个 `0/1` cell；Product 的中间游标严格由左编码长度决定，终点由右编码长度决定；Option
    的 `none` 精确产生 `0` 标签和空 payload，`some` 精确产生 `1` 标签和非空 payload。全部游标使用
    同一规范 tokenTable 和诚实 tokenCount，不能另选分割。三个审计端点探针退出码 0，仅依赖标准三项。
89. [FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout.lean)
    已完整打开 `BinaryNatStreamStatus = Option (Option (List Nat))`。外层 `none`、外层 `some` 加内层
    `none`、以及双层 `some` 加输出 token 列表三种分支均在同一规范 tokenTable 上共享同一 `finish`；
    每层 `0/1` 标签与 `payloadStart` 均由真实编码精确决定。双层 `some` 分支进一步构造输出 `List Nat`
    的 structured-list 边界表；第 102 项现又把输出列表的每个 Nat 原子行接到真实 token，并保留
    `(outputCount+1)*tokenCount` 码长界。status 与单状态回归探针退出码 0，仅依赖标准三项。
90. [FoundationCompactNumericListedDirectBinaryNatStreamStateLayout.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStateLayout.lean)
    已把一个完整 `BinaryNatStreamState = List Bool × List Nat × Option (Option (List Nat))`
    接到同一规范 tokenTable。两层 product split（积类型分割）由真实编码长度确定中间游标；bits 与
    decoded 两段分别获得 structured-list 边界表；末段严格复用第 89 项 status 三分支布局。全部游标
    对齐同一个状态区间，两张表分别保留 `(count+1)*tokenCount` 显式面积界。定向探针退出码 0，公理
    画像仅 `propext`、`Classical.choice`、`Quot.sound`，无项目公设或 `sorryAx`。
91. [FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout.lean)
    已把第 90 项逐行提升到任意真实状态列表。规范边界表第 `i`、`i+1` 行由同一 fixed-width table
    读取，并精确围住 `states.getI i` 的完整加法编码；该区间同时携带第 90 项完整状态布局。列表 header、
    `bodyStart`、`finish`、元素累计边界和真实 token 串逐点对齐，同一张表同时满足 structured-list 公式
    与逐行状态语义，且码长不超过 `(states.length+1)*tokenCount`。两个端点探针退出码 0，公理画像仅
    标准三项，无项目公设或 `sorryAx`。
92. [FoundationCompactNumericListedDirectTracePackedStreamStateLayouts.lean](../integration/FoundationCompactNumericListedDirectTracePackedStreamStateLayouts.lean)
    已把第 91 项安装到完整 direct trace（直接轨迹）的 proof-code 与 formula-code 两份 packed-stream
    分量。两个状态列表起点分别精确等于各自 payload 编码之后的游标，终点分别等于顶层第 2、4 个分量
    边界；每个真实状态行共享完整 trace 的同一 `tokenTable/width/tokenCount` 并携带第 90 项布局。两张
    边界表分别保留 `(stateCount+1)*tokenCount` 码长界。两个端点探针退出码 0，公理画像仅标准三项，
    无项目公设或 `sorryAx`。
93. [FoundationCompactNumericListedDirectAtomicListLayouts.lean](../integration/FoundationCompactNumericListedDirectAtomicListLayouts.lean)
    已给出可复用的 generic element-row construction（通用元素逐行构造）：同一 structured-list 边界表
    第 `i`、`i+1` 行精确围住真实 `values.getI i`，并在该区间安装指定的直接元素关系。该构造已实例化
    为 Bool 与 Nat：Bool 行直接读取真实 `0/1` tag，Nat 行直接读取真实自然数 token。第 90 项单状态
    布局已升级为 bits/decoded 两张内部表逐行携带这些强关系；第 91、92 项在升级后重新探针通过。六个
    新端点及三层回归公理画像均仅标准三项，无项目公设或 `sorryAx`。
94. [FoundationCompactNumericListedDirectBinaryNatStreamStepCases.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepCases.lean)
    已把真实 `binaryNatStreamStep` 精确拆成四个语义分支：status 已完成时保持原状态；运行中且 bits 为空
    时输出 `decoded.reverse`；非空 bits 解码失败时保持两列表并置 `some none`；解码成功时取得
    `token/suffix`，把 token 前插 decoded 并继续运行。四分支析取已逐点证明当且仅当真实下一状态，且
    明确保留 `decodeBinaryNat` 接受冗余高零位的非规范编码行为，未偷换成规范 `binaryNatCode` 长度。
    两个端点探针退出码 0，仅依赖 `propext`、`Quot.sound`。
95. [FoundationCompactNumericListedDirectFlexibleBinaryNatDecode.lean](../integration/FoundationCompactNumericListedDirectFlexibleBinaryNatDecode.lean)
    已从根上修正 canonical segment（规范解码段）不能覆盖冗余高零位的问题。首先证明真实成功解码精确
    分解成若干 `10/11` 数据对、终止 `00` 与 suffix，token 等于全部数据位的 `natOfBitsList`。随后定义
    独立 `digitCount` 的六变量 `CompactBinaryNatFlexibleDecodeSegment`，允许
    `digitCount ≥ Nat.size(token)`，并给出手写 `Δ₀` 公式及逐点语义规格。任何真实成功解码现已构造该段、
    显式消耗长度 `2*digitCount+2` 和精确 `suffix=bits.drop(consumed)`。反向证明从合法段奇数位重建全部
    数据位和 token，再以偶数/奇数位逐点外延证明输入前缀恰为这些数据对与终止 `00`，最终反推真实
    `decodeBinaryNat` 成功。现已得到“解码成功当且仅当存在 flexible segment（灵活解码段）及精确
    drop suffix（丢弃已消费前缀后的后缀）”的完整定理。全部端点探针退出码 0，公理画像仅标准三项
    或其子集，无项目公设、`sorryAx`、`projection` 或 `rfind`。
96. [FoundationCompactNumericListedDirectBoolListPackedValue.lean](../integration/FoundationCompactNumericListedDirectBoolListPackedValue.lean)
    已把状态 Bool（布尔值）原子逐行表汇总成唯一 packed payload（打包载荷）。六变量
    `CompactAdditiveBoolListPackedValue` 已写成直接 `Δ₀` 公式：每个位下标从同一边界表读取相邻游标，
    再从同一 token table（记号表）读取固定 `0/1` 单元；`Nat.size payload ≤ bitCount` 排除列表长度以外
    的垃圾高位。真实逐行语义直接构造 `payload = natOfBitsList values`，反向则利用边界表行值唯一性逐位
    恢复该等式。因此在同一 rows（逐行关系）下，公式成立当且仅当 payload 是真实 Bool 列表的精确
    打包值。五个端点探针退出码 0，仅依赖 `propext`、`Classical.choice`、`Quot.sound`，无项目公设、
    `sorryAx`、`projection` 或 `rfind`。
97. [FoundationCompactNumericListedDirectAtomicRowEquality.lean](../integration/FoundationCompactNumericListedDirectAtomicRowEquality.lean)
    已构造七变量 `CompactAdditiveAtomicRowEq`（原子行相等关系）及手写 `Δ₀` 公式。它要求两个原子行
    都是同一 token table（记号表）中的单 token 区间，并在固定宽度内逐位相等。两个携带同一值的
    token cell（记号单元）直接构造该关系；反向利用两侧 `Nat.size ≤ width` 排除宽度以外的差异，从而
    恢复真实 Nat（自然数）值相等，并进一步恢复 Bool 值相等。该公共原语同时服务后续 suffix、cons、
    reverse 三种列表更新。六个端点探针退出码 0，仅依赖标准三项或其子集，无项目公设或 `sorryAx`。
98. [FoundationCompactNumericListedDirectBoolListDropRows.lean](../integration/FoundationCompactNumericListedDirectBoolListDropRows.lean)
    已关闭成功解码分支的 Bool 位流转移。八变量 `CompactAdditiveBoolListDropRows` 是直接 `Δ₀` 公式：
    `consumed` 不越界，源长度等于消费长度加目标长度，且每个目标行等于源表中移位后的对应原子行；在
    真实逐行语义下，它成立当且仅当 `target = source.drop consumed`。十一变量
    `CompactAdditiveBoolListDecodeSuccessRows` 再把第 96 项的唯一 packed payload、第 95 项的 flexible
    segment 与该精确后缀公式合并，并逐项校准三个被引用公式的 `Fin` 参数向量。最终已证明该直接公式
    成立当且仅当真实 `decodeBinaryNat source = some (token, target)`。全部端点探针退出码 0，仅依赖
    标准三项，无项目公设、`sorryAx`、`projection` 或 `rfind`。
99. [FoundationCompactNumericListedDirectNatListConsRows.lean](../integration/FoundationCompactNumericListedDirectNatListConsRows.lean)
    已关闭成功分支的 decoded cons（已解码列表前插）。八变量 `CompactAdditiveNatListConsRows` 是手写
    `Δ₀` 公式：目标长度等于源长度加一，第 0 行精确承载新 head token（头部记号），其余目标行逐项
    等于前一源行。正向从真实 `head :: source` 构造全部边界与原子行；反向利用边界表唯一性和第 97 项
    恢复每个真实 Nat 值。最终公式成立当且仅当 `target = head :: source`。五个端点探针退出码 0，
    仅依赖标准三项或其子集，无项目公设或 `sorryAx`。
100. [FoundationCompactNumericListedDirectNatListReverseRows.lean](../integration/FoundationCompactNumericListedDirectNatListReverseRows.lean)
    已关闭空输入分支的 decoded reverse（已解码列表反转）。七变量 `CompactAdditiveNatListReverseRows`
    是手写 `Δ₀` 公式：源/目标长度相等，每个目标下标显式给出满足
    `sourceIndex + targetIndex + 1 = sourceCount` 的镜像源下标，再用第 97 项比较对应单 token 行。
    正反向均已逐元素恢复，最终公式成立当且仅当 `target = source.reverse`。五个端点探针退出码 0，
    仅依赖 `propext`、`Classical.choice`、`Quot.sound`，无项目公设、`sorryAx`、`projection` 或 `rfind`。
101. [FoundationCompactNumericListedDirectBinaryNatDecodeFailure.lean](../integration/FoundationCompactNumericListedDirectBinaryNatDecodeFailure.lean)
    已关闭真实 decoder（解码器）的失败分支，而且没有为 token 人为引入上界。三变量
    `CompactBinaryNatDecodeShape` 精确表示若干 marker（标记位）之后出现终止 `00`；两变量
    `CompactBinaryNatNoDecodeShape` 对每个候选位置构造四类局部阻断之一：消费长度越界、某个 marker
    为 `0`、终止首位为 `1`、终止次位为 `1`。两者均为手写 `Δ₀` 公式，并已证明“全部位置被阻断”
    当且仅当不存在成功形状。任意成功形状可反向构造真实 flexible segment 和成功解码，因此最终得到
    `decodeBinaryNat bits = none` 当且仅当这些有界局部失败证书成立。与第 96 项的 packed-value 公式合用
    时，公式束的两项同时成立当且仅当同一 Bool 行表真实解码失败；公式束不是输入假设，两个成员公式及
    其规格均已内核检查，最终 stream-step 公式只需在外层直接合取。全部端点探针退出码 0，仅依赖标准
    三项，无项目公设、`sorryAx`、`projection` 或 `rfind`。
102. [FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout.lean)
    已加强第 89 项的完成状态输出布局。`some (some outputTokens)` 分支不再只给 structured-list（结构化
    列表）边界，而是为每个输出元素给出同一边界表的相邻游标、精确单 token Nat 行及真实元素值，并
    保留输出边界表的显式面积界。这使第 100 项的 `decoded.reverse` 能直接连接到完成 status 内部输出，
    而不是停留在仅知道列表长度和边界的空壳。status 探针及下游单状态布局回归均退出码 0，公理画像
    仅 `propext`、`Classical.choice`、`Quot.sound`，无项目公设或 `sorryAx`。
103. [FoundationCompactNumericListedDirectBinaryNatStatusCases.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStatusCases.lean)
    已把嵌套 status 的三类标签分别写成直接 `Δ₀` 公式：running（运行中）是单标签 `0`，failed
    （失败完成）是 `1,0`，completed prefix（成功完成前缀）是 `1,1`。同一 tokenTable 和 cursor 上的
    cell 值唯一性排除了伪标签；在第 102 项完整 status 布局下，三个数值关系分别当且仅当真实 status 为
    `none`、`some none`、`some (some outputTokens)`，并证明完成输出起点精确为 status 起点加二。
    十个端点探针退出码 0，仅依赖标准三项，无项目公设、`sorryAx`、`projection` 或 `rfind`。
104. [FoundationCompactNumericListedDirectNatListSameRows.lean](../integration/FoundationCompactNumericListedDirectNatListSameRows.lean)
    已关闭 done/failure 分支 decoded 字段的直接同一性。七变量 `CompactAdditiveNatListSameRows` 是手写
    `Δ₀` 公式：源/目标长度相等，同下标的两张边界表行在固定宽度 tokenTable 中逐位相等。正向从真实
    列表相等构造全部行；反向由边界行唯一性和第 97 项恢复每个 Nat 值，最终公式成立当且仅当
    `target = source`。Bool 不变字段无需新公式，直接使用第 98 项的 `BoolListDropRows` 并令
    `consumed=0`，其已证 iff 立即化为 `target=source`。五个端点探针退出码 0，仅依赖标准三项或其
    子集，无项目公设、`sorryAx`、`projection` 或 `rfind`。
105. [FoundationCompactNumericListedDirectCompletedStatusReverseRows.lean](../integration/FoundationCompactNumericListedDirectCompletedStatusReverseRows.lean)
    已关闭完成 status（状态）输出与 decoded reverse（已解码列表反转）之间最后的边界歧义。配套的
    [FoundationCompactNumericListedDirectNatListBoundaryRigidity.lean](../integration/FoundationCompactNumericListedDirectNatListBoundaryRigidity.lean)
    证明：当每个 Nat 行恰占一个 token（编码单元）时，第 `i` 个边界必为 `outputStart+1+i`，列表终点
    必为 `outputStart+1+count`。因此公式给出的输出边界表不能指向另一组伪造 token 行。完成标签、输出
    structured-list（结构化列表）布局和 `NatListReverseRows` 组成的直接公式束，在真实 source/status
    行布局下成立，当且仅当 `status = some (some source.reverse)`。正反方向均已由实际行构造或恢复，
    未把反转结论作为输入。探针退出码 0，公理画像仅标准三项，无项目公设、`sorryAx`、`projection`
    或 `rfind`。
106. [FoundationCompactNumericListedDirectCompletedStatusSameRows.lean](../integration/FoundationCompactNumericListedDirectCompletedStatusSameRows.lean)
    已关闭 done（完成后保持不变）分支内部输出的同一性。两侧完成标签、同一 `outputCount` 的输出布局和
    `NatListSameRows` 直接行关系成立，当且仅当两个 status 都等于同一个 `some (some output)`。第 105 项
    的边界刚性排除伪输出表；本项及第 105 项又加入精确 `Nat.size` 字段，证明每张输出边界表位长不超过
    `(outputCount+1)*tokenCount`，因此后续 Σ₁ 见证不能携带任意高位垃圾。全部端点仅依赖标准三项。
107. [FoundationCompactNumericListedDirectBinaryNatStreamStepRows.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepRows.lean)
    已把状态布局展开成命名数值坐标，并证明该坐标视图与原布局双向等价。done、empty、decode-failure、
    decode-success 四个纯数值行关系分别当且仅当第 94 项对应语义分支；总析取当且仅当
    `next = binaryNatStreamStep current`。关系不输入 typed next-state equality（类型化下一状态等式），
    而是从 Bool/Nat 行、解码图和 status 标签恢复它。七个端点仅依赖标准三项。
108. [FoundationCompactNumericListedDirectBinaryNatStreamStepFormula.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepFormula.lean)
    与 [FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation.lean)
    已把第 107 项写成四个手写 31 自由变量 `Δ₀` 分支公式及一个总析取公式。显式 step witness（单步见证）
    记录分支标签、`payload/digitCount/token/consumed` 和带位长守卫的完成输出边界；所有子公式的 `Fin`
    环境向量均逐项证明。公式存在见证当且仅当真实 stream step。任意合法本地流轨迹的每对相邻状态行
    都产生该见证，并已安装到完整验证轨迹的 proof/formula 两张状态表。探针与定向构建均退出码 0，
    公理画像仅标准三项，无项目公设、`sorryAx`、`projection` 或 `rfind`。
109. [FoundationCompactNumericListedDirectAtomicListRowRealization.lean](../integration/FoundationCompactNumericListedDirectAtomicListRowRealization.lean)
    已从定宽边界表确定性定义 Bool/Nat 列表值。Bool 行有效性和单 token Nat 边界均写成手写 `Δ₀`
    公式；纯数值关系分别构造真实类型化 Bool/Nat 行，长度精确等于公开 `count`。端点仅依赖标准三项。
110. [FoundationCompactNumericListedDirectBinaryNatStreamStateFormula.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStateFormula.lean)
    已将一个 stream state 的两个 product split、bits/decoded 列表布局、原子行、计数、精确边界
    `Nat.size` 及面积界合为手写 13 自由变量 `Δ₀` 核心公式。数值核心确定性恢复两个真实列表，反向
    typed fixed layout 也产生同一核心图；该核心不再输入 typed state。
111. [FoundationCompactNumericListedDirectBinaryNatStreamStepRealization.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepRealization.lean)
    已从 `0 / 10 / 11` 数值片段直接构造 running/failed/completed status；完成输出由数值边界行恢复。
    因而两份纯数值状态核心加四分支 step witness 能构造真实 current/next，并证明
    `next = binaryNatStreamStep current`；反方向同样成立。不存在只满足数值图却不是实际执行的伪见证。
112. [FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula.lean)
    已把两份第 110 项状态核心与第 108 项单步图共享坐标，合为手写 35 自由变量 `Δ₀` 公式。全部
    `Fin` 环境逐项校准，规格定理逐点 iff 第 111 项已实现单步图；层级与规格端点仅依赖标准三项。
113. [FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable.lean)
    已把当前状态 10 列、下一状态 10 列和分支见证 12 列固定为同一 32 列 row-major（行优先）表。
    规范表码支持任意行列精确读取，表图逐行求值第 112 项公式，表码位长不超过
    `rowCount * 32 * tableWidth`；端点仅依赖标准三项。
114. [FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound.lean)
    已从状态核心图推出全部状态坐标的公开位长界，并按四分支把未使用见证字段规范化为零。保留字段全部
    落入 `tableWidth=(tokenCount+1)*tokenCount+8`，没有为任意见证另加隐藏上界输入。
115. [FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableInstallation.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableInstallation.lean)
    已把每个真实相邻状态步转换为满足第 114 项统一列宽的行，并构造 proof/formula 两张规范见证表；
    两表同时保留精确码长界并逐行满足 35 变量单步图。
116. [FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula.lean)
    已把 32 个定宽条目和 35 变量单步图写成真实 `Δ₀` 表公式。32 个有界见证按当前状态、下一状态、
    见证头、见证尾四级连续子公式引入，避免元层表关系冒充算术公式；公式规格和层级端点仅依赖标准三项。
117. [FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaBridge.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaBridge.lean)
    与 [FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaInstallation.lean](../integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaInstallation.lean)
    已证明每个条目值由表位唯一决定，`BoundedGraph(valueBound)` 当且仅当
    `valueBound=2^tableWidth` 且原 `TableGraph` 成立；任意公式见证均被强制回同一规范 32 列行。
    proof/formula 两张表现已直接满足手写公式。最终定向构建通过 1379 个任务，全部新增端点仅依赖
    `propext`、`Classical.choice`、`Quot.sound`，无项目公设或 `sorryAx`。
118. [FoundationCompactNumericListedDirectSyntaxTaskLayout.lean](../integration/FoundationCompactNumericListedDirectSyntaxTaskLayout.lean)
    已证明每个 `CompactSyntaxTask`（紧凑语法任务）的加法编码精确为连续三个 Nat token：任务种类、
    绑定元数和重复计数；三个单元在任意公共前后缀中均有规范直接布局，没有隐藏任务字段或游标参数。
119. [FoundationCompactNumericListedDirectParserStateLayout.lean](../integration/FoundationCompactNumericListedDirectParserStateLayout.lean)
    已把一个统一解析器状态精确拆成剩余 token 列表、语法任务栈和双层可选返回状态。两层 product split
    （积类型分割）、两个 structured-list（结构化列表）边界表、每个任务的三字段行及返回状态全部对齐
    同一状态区间；两张内部边界表均保留显式多项式面积界。
120. [FoundationCompactNumericListedDirectParserStateListLayout.lean](../integration/FoundationCompactNumericListedDirectParserStateListLayout.lean)
    已把第 119 项提升到任意有限解析器状态列表：一张规范边界表同时满足列表头、每行精确游标和每个
    真实 typed state（类型化状态）的完整布局，且表码长不超过 `(stateCount+1)*tokenCount`。
121. [FoundationCompactNumericListedDirectTraceParserStateLayouts.lean](../integration/FoundationCompactNumericListedDirectTraceParserStateLayouts.lean)
    已将第 120 项分别安装到完整直接轨迹的 proof、certificate、formula 三个 parser trace（解析器轨迹）
    分量。三段严格占据顶层边界 `4→5`、`5→6`、`6→7`，共享同一 tokenTable、width 和 tokenCount；
    定向构建通过 1354 个任务，全部端点仅依赖标准三项。这里仅关闭状态与边界语义，尚未把
    `initial/step/final`（初态／转移／终态）关系标为已算术化。
122. [FoundationCompactNumericListedDirectSyntaxTaskRowRealization.lean](../integration/FoundationCompactNumericListedDirectSyntaxTaskRowRealization.lean)
    已将任务栈每行“恰占三个 token”写成三变量手工 `Δ₀` 公式。真实任务行推出
    `right=left+3`；反方向仅从公共 token 表在 `left`、`left+1`、`left+2` 读取三值，确定性恢复
    `kind/binderArity/count`，不输入 typed task（类型化任务）见证。现又补齐八变量完整任务布局公式，
    将三个字段值分别绑定到三个连续 `CompactAdditiveTokenCell`（加法编码 token 单元）。
123. [FoundationCompactNumericListedDirectParserStateFormula.lean](../integration/FoundationCompactNumericListedDirectParserStateFormula.lean)
    已把两层 product split、剩余 Nat token 列表、三格任务列表、两张边界表的精确 `Nat.size` 与面积界
    合为手写 13 自由变量 `Δ₀` 核心公式。真实状态布局无条件产生该公式见证；反方向只凭表位恢复
    `tokens/tasks` 两个真实列表，再与后续给出的 status 布局组成完整解析器状态，核心不再输入 typed state。
    现已补充命名的固定坐标完整状态布局，并证明它与原直接布局双向等价，供相邻状态分支统一复用。
124. [FoundationCompactNumericListedDirectParserStateFormulaInstallation.lean](../integration/FoundationCompactNumericListedDirectParserStateFormulaInstallation.lean)
    已把第 123 项的实际 `Evalb`（公式求值）安装到 proof、certificate、formula 三条轨迹的每个状态行，
    同时保留真实 status 布局供下一步分支消元。最终定向构建通过 1359 个任务；全部新增端点只依赖
    标准三项，无项目公设、`sorryAx`、`projection` 或 `rfind`。下一义务是把两个相邻状态核心与
    status 标签、任务头和 token 操作合成三类 parser step 的纯数值公式。
125. [FoundationCompactNumericListedDirectParserStepCases.lean](../integration/FoundationCompactNumericListedDirectParserStepCases.lean)
    已证明三个 parser step 共有的精确外层正常形：status 已结束时状态保持不变；运行中且任务栈为空时
    以剩余 token 完成；运行中且任务栈非空时仅执行任务头。统一定理无损实例化到 syntax、proof、
    certificate 三个公开 step，四个端点只依赖 `propext`、`Quot.sound`。
126. [FoundationCompactNumericListedDirectSyntaxTaskListSameRows.lean](../integration/FoundationCompactNumericListedDirectSyntaxTaskListSameRows.lean)
    已把一个任务的三个 token 块分别接到三份 `AtomicRowEq`（原子行相等）公式，再逐任务提升为列表
    相等公式。在真实任务行布局下，该手写 `Δ₀` 关系当且仅当两个任务列表完全相等。
127. [FoundationCompactNumericListedDirectSyntaxTaskListDropRows.lean](../integration/FoundationCompactNumericListedDirectSyntaxTaskListDropRows.lean)
    已证明目标任务第 `i` 行等于源任务第 `consumed+i` 行的手写 `Δ₀` 关系，当且仅当
    `target=source.drop consumed`；取 `consumed=1` 即真实 parser step 的任务头弹出。
128. [FoundationCompactNumericListedDirectSyntaxTaskListConsRows.lean](../integration/FoundationCompactNumericListedDirectSyntaxTaskListConsRows.lean)
    已用第 122 项完整任务布局约束目标第零行，并把其余行逐项接到前一源行；所得手写 `Δ₀` 关系
    当且仅当 `target=head::source`。第 125 至 128 项联合定向构建通过 1362 个任务，全部新增端点无
    项目公设或 `sorryAx`。下一步将这些 same/drop/cons 组件与 status、Nat token 列表变换合成真实分支。
129. [FoundationCompactNumericListedDirectParserDoneRows.lean](../integration/FoundationCompactNumericListedDirectParserDoneRows.lean)
    已把 parser 的已结束分支拆成剩余 Nat token 列表相等、任务列表相等，以及两种 status 同一关系：
    两侧均 failed，或两侧 completed 且输出列表逐行相等。在两份固定状态布局下，该纯数值行关系
    当且仅当当前 status 已结束且 `next=current`。
130. [FoundationCompactNumericListedDirectParserDoneFormula.lean](../integration/FoundationCompactNumericListedDirectParserDoneFormula.lean)
    已将第 129 项写成 26 自由变量手工 `Δ₀` 公式：公共表 3 坐标、当前/下一状态各 8 坐标、completed
    输出 7 坐标。两张输出边界表均携带精确 `Nat.size` 与公开面积界；公式规格逐点 iff 行关系，且存在
    见证当且仅当真实 done case（已结束分支）成立。
131. [FoundationCompactNumericListedDirectParserDoneInstallation.lean](../integration/FoundationCompactNumericListedDirectParserDoneInstallation.lean)
    已把第 130 项分别接到 syntax、proof、certificate 三个公开 parser step。在当前 status 已结束时，
    公式存在见证当且仅当对应公开 step 产生给定 next。最终定向构建通过 1369 个任务，全部新增端点
    仅依赖标准三项；第二个完整外层分支由第 132 至 135 项继续闭合。
132. [FoundationCompactNumericListedDirectCompletedOutputSameRows.lean](../integration/FoundationCompactNumericListedDirectCompletedOutputSameRows.lean)
    已将 next 的 completed output（完成输出）直接绑定到当前剩余 Nat token 行。单位边界刚性排除指向
    另一片 token 表的伪输出；关系存在当且仅当 status 精确等于 `some (some source)`，并有带精确
    `Nat.size` 与 `(sourceCount+1)*tokenCount` 面积界的见证版本。
133. [FoundationCompactNumericListedDirectParserEmptyRows.lean](../integration/FoundationCompactNumericListedDirectParserEmptyRows.lean)
    已证明运行标签、两侧零任务计数、剩余 token 行保持及第 132 项完成输出关系，当且仅当真实
    empty case（空任务分支）为 `next=(current.tokens, [], some (some current.tokens))`。
134. [FoundationCompactNumericListedDirectParserEmptyFormula.lean](../integration/FoundationCompactNumericListedDirectParserEmptyFormula.lean)
    已把第 133 项写成 22 自由变量手工 `Δ₀` 公式：公共表 3 坐标、当前/下一状态各 8 坐标及完成输出
    3 坐标。全部 `Fin` 环境逐项校准；公式规格逐点 iff 纯数值行关系，存在见证 iff 真实 empty case。
135. [FoundationCompactNumericListedDirectParserEmptyInstallation.lean](../integration/FoundationCompactNumericListedDirectParserEmptyInstallation.lean)
    已把第 134 项分别安装到 syntax、proof、certificate 三个公开 parser step；在当前 status 运行且任务栈
    为空时，公式存在见证当且仅当实际 step 产生给定 next。最终定向构建通过 1369 个任务，所有新增端点
    仅依赖 `propext`、`Classical.choice`、`Quot.sound`。非空栈的公共拆头由第 136、137 项继续闭合。
136. [FoundationCompactNumericListedDirectSyntaxTaskListTailTable.lean](../integration/FoundationCompactNumericListedDirectSyntaxTaskListTailTable.lean)
    已把当前任务边界表第 `1,...,taskCount` 个游标重新打包为规范 tail boundary table（尾边界表）。新表
    逐行精确承载 `tasks.drop 1`，满足 `DropRows(..., consumed=1)`，且码长不超过
    `((tasks.drop 1).length+1)*tokenCount`；没有复制或修改任何任务 token。
137. [FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows.lean](../integration/FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows.lean)
    已将第 136 项与 `ConsRows` 合成 11 自由变量手工 `Δ₀` 拆头公式。存在带精确码长守卫的尾表见证，
    当且仅当真实任务栈为指定 `(kind,binderArity,repeatCount) :: tail`；因此任务头三个字段、pop 后尾栈及
    后续 push 的共同基准已经在同一算术坐标闭合。定向构建通过 1360 个任务，新增端点仅依赖标准三项。

这与 Pudlak 1986 原文一致：原文明确拒绝通常的一元数词，采用长度与
`log n` 成比例的短数词；公式和证明按二元串/符号数计长。

## 剩余根义务

1. 把完整 certified proof code（带证书证明码）的确定性验证器落实为多项式时间，
   再内部化为 suitable `P(x,y)`。解码结构及规范编码长度不膨胀已经由第 19 至 23 项闭合；
   第 24 至 26 项已打开公式比较、成员/包含、集合等价及全部 decoder（解码器）的结果路径和
   全路径摊还界，第 27 项已闭合所有局部语法变换的完整输出码长，第 28、29 项已闭合保留重复项的证明树
   及完整证书 honest decoded weight（解码对象诚实位权）。第 30 至 33 项的归纳骨架现已由第 45 项
   具体带守卫公理比较器闭合：`haxm` 已消失，十规则公开轨迹在所有成功/失败输入上都有同一固定
   多项式位成本界，稀疏 `fvSup` 漏洞和六次/八次界错位均已修复。

   第 46 项又将公开输入转成同一纯数值 token graph（记号图），并闭合否定、移位、自由化与代入；
   第 48 项进一步闭合 `fixitr`（变量捕获转换），第 49 项已经由这些原语闭合 `succInd(body)`，
   第 50 项又闭合其纯数值 `fvSup`（自由变量上确界），第 51 项闭合 `allClosure`（全称闭包）
   本体，第 52 项将守卫长度精确校准到候选公式公开二进制码，第 53 项闭合守卫、标签 `22`
   完整句及规范输入上的相等判定，第 54 项已合并全部 23 标签，并利用任意证书输入反演定理
   排除畸形 token 与垃圾尾部，第 55 项已闭合十条规则的全部纯数值局部合并器，第 56 项已闭合
   两侧根节点字段解析并精确保留子流，第 57 项现已闭合有限任务栈、显式燃料、全部拒绝路径和完整
   公开验证器逐点结果等式。第 58 项闭合的是同一有界谓词的**通用定性表示审计**；因其内含
   `rfind` 最小化前缀，不能直接承接定量短证明。

   第 59 至 137 项现已关闭非最小化外部轨迹语义、中央任务机局部计算表、两个公开 packed 输入子轨迹、
   proof/certificate/formula 三类解析器的外层局部计算表，以及 certified-parts/whole-formula 两个结果
   包装层、带逐公式子轨迹的 sequent repeat、term/closed-formula 外层轨迹、五类根字段分支、十标签
   直接分派、`rootTrace` 的公开总见证接入、整套见证的加法型 token/Nat 无损编码、精确结构位权、
   列表汇总界、十二分量分解、全部十二分量公开界、总轨迹码长界，以及确定性有界 `traceCode`
   证书关系；公开码长界函数、完整 size-guard witness（码长守卫见证）的原始递归性，以及 `Nat.size`
   的直接 `Δ₀` 算术图也已闭合；packed payload 的终止哨兵、单 token 段、定宽随机读取及完整 token 流
   的规范正反向均已成为直接 `Δ₀` 图，非规范公开码也已在不增加诚实位长下规范化；第 80 项进一步在
   有界接受谓词层证明两条输入规范表的同 cutoff 双向替换；第 81 项又关闭 token cell、列表头、
   `List Nat` 精确切片和复合值严格边界表；第 82 项进一步证明完整 trace 恰由十二个非空语义段组成并
   构造十三行规范边界表；第 83 项又关闭 Bool、Option、Prod 和 structured List 的通用直接布局。
   第 84 项已把第 1、3、11 个 `List Nat` 分量接到真实边界与直接列表公式，第 85 项又精确分开第 2、4
   个 packed-stream trace 的左右字段；第 86 项又给出所有 structured List 共用的规范移位边界表和
   多项式面积界，第 87 项又把它实例化为两份 stream trace 内的四张真实列表表。第 88 项使
   Bool/Option/Prod 的直接公式、标准语义和规范构造三方向齐全，第 89 项关闭最深的
   `Option(Option(List Nat))` 三分支布局，第 90 项进一步把 List Bool、List Nat 与该 status 合并为
   单个完整 `BinaryNatStreamState` 布局，第 91 项再证明任意状态列表的同一规范边界表逐行精确承载
   这些完整布局，第 92 项已把它安装到完整 trace 的 proof/formula 两个具体状态字段，并精确校准第
   2、4 个顶层分量边界，第 93 项进一步把状态内部 bits/decoded 列表的每个 Bool/Nat 原子全部打开，
   第 94 项固定了真实 stream step 的四分支精确正常形，第 95 项已构造允许冗余高零位的直接 decode
   segment，并证明真实解码成功与该段加精确 suffix 的完整双向等价；第 96 项又证明同一 Bool 行表中的
   packed payload 唯一且精确等于真实 `natOfBitsList`，第 97 项关闭单 token 原子行直接相等关系，第
   98 项据此证明成功分支的源/目标 Bool 行关系当且仅当真实解码与精确 suffix；第 99、100 项又分别
   关闭成功分支的 decoded cons 和空输入分支的 decoded reverse；第 101 项又以四类显式局部阻断关闭
   真实 decode failure；第 102 项进一步把完成 status 内部输出列表的每个 Nat 原子行全部打开，第
   103 项又把 `0 / 1,0 / 1,1` 标签精确对应到三种真实 status；第 104 项关闭 Nat 列表不变关系，Bool
   不变则由第 98 项取 `consumed=0` 直接得到；第 105 项再以单 token 边界刚性排除伪输出表，并证明完成
   status 的输出精确等于 `decoded.reverse`；第 106 项关闭两个完成 status 的同一输出及两张边界表的
   位长守卫；第 107 项把四分支逐项恢复为真实 `binaryNatStreamStep`；第 108 项写成 31 变量手写 `Δ₀`
   公式，并安装到 proof/formula 两张状态表的全部相邻行。第 109 至 112 项又从纯数值边界表确定性恢复
   typed 列表和三类 status，消去 typed state 输入，并把两状态核心与单步关系合成逐点精确的 35 变量
   `Δ₀` 公式。第 113 至 117 项进一步构造统一列宽的 32 列相邻步见证表、证明全部列的公开位长界、
   安装 proof/formula 两张规范表，并闭合真实手写 `Δ₀` 表公式及其与原表图的完整双向等价。
   第 118 至 137 项进一步给出三条 parser trace（解析器轨迹）的规范状态表、13 变量状态核心、共有三分支
   正常形、done/empty 两个完整分支，以及非空任务栈的规范有界拆头公式。当前黄色工作面已收窄到
   非空任务栈的 task-head dispatch（任务头标签分派）、parser initial/final（解析器初态／终态）及其余
   verifier（验证器）分量的直接算术图：

   ```text
   P_direct(bound,y) := exists proofCode,
     payloadLength(proofCode) <= bound and
     exists traceCode,
       Nat.size(traceCode) <= publicTraceCodeBound(proofCode,y) and
       DirectVerifierTraceCode(proofCode,y,traceCode).
   ```

   精确 `verifier=true iff exists bounded traceCode.Valid`、中央 `initial/step/final` 检查、packed token stream
   局部检查、全部 outer parser tableau、逐公式子运行、两个结果包装层、完整 root-field 子轨迹及无损
   自定界自然数编码、全部十二分量界和有界轨迹码双向等价均已闭合。下一步展开 `verifierStep` 内的
   原子字段解析和局部语法变换，直接构造该关系的二变量 Σ₁ 公式。
   只有这些步骤闭合后，才进入
   PA 内部 accepted-computation proof compiler（接受计算证明编译器）：合法轨迹产生真实 `Derivation2`，
   且完整证明载荷长度为输入位长的固定多项式。`Decidable`（可判定）、普通 `codeOfREPred` 或逐实例
   `sigma_one_completeness`（Σ₁ 完备性）均不能替代上述两个定量证明。

   第 38 项已证明限制到 canonical accepted codes（规范接受码）不改变精确最短长度，消除了畸形码风险。
   直接轨迹公式必须保持标准模型语义逐点精确等价于**同一个带守卫紧凑验证器**；再以短二进制数词定义
   `Con_PA^compact(k) := ¬∃p (payloadLength(p) <= k ∧ CompactProof(p, falsumCode))`。
   当前 `CertifiedFiniteConsistencyAt` 只是 Lean 元层 `Prop`，而旧
   `succinctFiniteConsistencySentence` 仍使用 Foundation raw-code checker，因此二者都不能直接充当该公式族。
   还必须为接受计算构造 PA 内部短证明，不能用第 58 项的定性表示定理代替。
2. 对该具体 `P` 和同一二进制长度逐项证明 Pudlak 1986 Theorem 3.1 的定量条件
   (0)-(3)，再完成 bounded proof assembly（有界证明拼接）与 exponent extraction（指数提取）。
   定量参数化对角实例化已由第 39 至 42 项关闭；第 43 项已关闭 condition (3) 所需的外部
   accepted-code MP composition（接受码肯定前件合成）及完整载荷界，但尚须把它内化为同一 PA 公式中的
   短证明。当前 Foundation 的 qualitative D1/D2/D3
   （定性可导条件）仍不足以自动给出其余证明长度多项式。
3. 形式化 Buss 1994 Theorem 5 的 time-constructible rescaling，选择显式超多项式
   `f`，得到 `Con_T((f(n))^c)` 的超多项式下界；同时闭合当前序列系统与原文
   Hilbert symbol-length 的多项式校准。
4. 构造 Sondow same-object compiler（同对象编译器），从已检查 Sondow 证书产生
   **同一 `Con_T((f(n))^c)` 公式**的真实证明对象和多项式长度上界。若做不到，碰撞
   路线即不成立，不能用 graft 接口代替。

第 1 至 3 项是当前下界根任务；旧 `Nat.size(rawProofCode)` 路线继续仅作反例审计，
不得回流投稿主定理。

## 成功标准

主定理必须同时通过：同一公式、同一参数、同一 checker、同一诚实长度坐标、
无项目公设，以及 dependency/axiom audit（依赖/公理审计）。开发阶段只跑目标
Lean probe（定向探针）；全部根义务闭合后再运行完整构建。

当前新增探针：

```bash
lake env lean integration/FoundationFiniteConsistencyEncodingAudit.lean
lake env lean integration/FoundationProofCodeSizeCalibration.lean
lake env lean integration/FoundationPAFiniteConsistencyLowerBoundTarget.lean
lake env lean integration/FoundationSuccinctFiniteConsistencyTarget.lean
lake env lean integration/FoundationEfficientPAProofPredicateArithmetic.lean
lake env lean integration/FoundationEfficientPAProofPredicateRepresentation.lean
lake env lean integration/FoundationEfficientPAProofPredicateRE.lean
lake env lean integration/FoundationPudlakQuantitativeConditions.lean
lake env lean integration/FoundationCompactPAProofVerifier.lean
lake env lean integration/FoundationCompactPAAxiomCertificate.lean
lake env lean integration/FoundationCompactCertifiedPAProof.lean
lake env lean integration/FoundationComputableCompactPAProofEncoder.lean
lake env lean integration/FoundationCertifiedFiniteConsistencyTarget.lean
lake env lean integration/FoundationCompactVerifierStructuralBound.lean
lake env lean integration/FoundationCompactProofDecoderStructuralBound.lean
lake env lean integration/FoundationCompactCertificateDecoderStructuralBound.lean
lake env lean integration/FoundationCompactSyntaxTransformationBounds.lean
lake env lean integration/FoundationCompactCanonicalDecodeLength.lean
lake env lean integration/FoundationCompactProofCanonicalDecodeLengthBase.lean
lake env lean integration/FoundationCompactProofCanonicalDecodeLength.lean
lake env lean integration/FoundationCompactProofCanonicalDecodeLengthComplete.lean
lake env lean integration/FoundationCompactPAAxiomCertificateCanonicalDecodeLength.lean
lake env lean integration/FoundationCompactCertificateCanonicalDecodeLength.lean
lake env lean integration/FoundationCompactVerifierBitCostPrimitives.lean
lake env lean integration/FoundationCompactVerifierFormulaListChecks.lean
lake env lean integration/FoundationCompactListedProofDecoder.lean
lake env lean integration/FoundationCompactListedCertificateVerifier.lean
lake env lean integration/FoundationCompactListedProofProjectionBase.lean
lake env lean integration/FoundationCompactListedProofProjection.lean
lake env lean integration/FoundationCompactListedProofProjectionComplete.lean
lake env lean integration/FoundationCompactListedCertifiedVerifier.lean
lake env lean integration/FoundationCompactListedProofEncoder.lean
lake env lean integration/FoundationCompactListedCertifiedEncoder.lean
lake env lean integration/FoundationCompactNatDecoderCost.lean
lake env lean integration/FoundationCompactSyntaxDecoderCost.lean
lake env lean integration/FoundationCompactListedProofDecoderCost.lean
lake env lean integration/FoundationCompactCertificateDecoderCost.lean
lake env lean integration/FoundationCompactListedCertifiedDecoderCost.lean
lake env lean integration/FoundationCompactDecoderCostPotential.lean
lake env lean integration/FoundationCompactSyntaxDecoderCostPotential.lean
lake env lean integration/FoundationCompactListedProofDecoderCostPotential.lean
lake env lean integration/FoundationCompactCertificateDecoderCostPotential.lean
lake env lean integration/FoundationCompactPackedDecoderCostPotential.lean
lake env lean integration/FoundationCompactSyntaxTransformationCodeBounds.lean
lake env lean integration/FoundationCompactSyntaxNegationTrace.lean
lake env lean integration/FoundationCompactListedAxiomJointWeight.lean
lake env lean integration/FoundationCompactListedMinProofLength.lean
lake env lean integration/FoundationCompactListedFiniteConsistencyTarget.lean
lake env lean integration/FoundationCompactListedCanonicalNormalization.lean
lake env lean integration/FoundationCompactDerivationSpecialization.lean
lake env lean integration/FoundationCompactCertifiedDerivationSpecialization.lean
lake env lean integration/FoundationCompactBinaryNumeralTerm.lean
lake env lean integration/FoundationCompactParameterizedDiagonalSpecialization.lean
lake env lean integration/FoundationCompactCertifiedModusPonens.lean
lake env lean integration/FoundationCompactCertifiedConjunction.lean
lake env lean integration/FoundationCompactListedGuardedAxiomCost.lean
lake env lean integration/FoundationCompactNumericFormulaNegation.lean
lake env lean integration/FoundationCompactNumericFormulaShift.lean
lake env lean integration/FoundationCompactNumericFormulaFree.lean
lake env lean integration/FoundationCompactNumericFormulaSubstitution.lean
lake env lean integration/FoundationCompactNumericFixedPAAxiomSentence.lean
lake env lean integration/FoundationCompactListedProofHonestWeight.lean
lake env lean integration/FoundationCompactListedCertifiedHonestWeight.lean
lake env lean integration/FoundationCompactListedLocalCostPrimitives.lean
lake env lean integration/FoundationCompactListedPublicCostSkeleton.lean
lake env lean integration/FoundationCompactNumericTokenBitLength.lean
lake env lean integration/FoundationCompactNumericGuardedInductionSentence.lean
lake env lean integration/FoundationCompactNumericPAAxiomComparator.lean
lake env lean integration/FoundationCompactNumericListedRuleChecks.lean
lake env lean integration/FoundationCompactNumericListedNodeFields.lean
lake env lean integration/FoundationCompactNumericListedTaskMachine.lean
lake env lean integration/FoundationCompactNumericListedPublicVerifier.lean
lake env lean integration/FoundationCompactNumericListedProofPredicate.lean
lake env lean integration/FoundationCompactPackedTokenStreamDirectTrace.lean
lake env lean integration/FoundationCompactParserDirectTrace.lean
lake env lean integration/FoundationCompactNumericListedParseDecomposition.lean
lake env lean integration/FoundationCompactNumericListedRootFieldsDecomposition.lean
lake env lean integration/FoundationCompactSequentValueDirectTrace.lean
lake env lean integration/FoundationCompactNumericListedRootFieldsDirectTrace.lean
lake env lean integration/FoundationCompactNumericListedDirectTrace.lean
lake env lean integration/FoundationCompactAdditiveTokenCodec.lean
lake env lean integration/FoundationCompactNumericListedDirectTraceCode.lean
lake env lean integration/FoundationCompactNumericListedStateBounds.lean
lake env lean integration/FoundationCompactNumericListedDirectTraceBounds.lean
lake env lean integration/FoundationCompactNumericListedBoundedTraceCode.lean
lake env lean integration/FoundationCompactNumericListedDirectArithmeticPrimitives.lean
lake env lean integration/FoundationCompactNumericListedDirectTokenStreamTableau.lean
lake env lean integration/FoundationCompactNumericListedDirectTokenStreamInverse.lean
lake env lean integration/FoundationCompactNumericListedDirectInputTableau.lean
lake env lean integration/FoundationCompactNumericListedDirectAdditiveCodecGraph.lean
lake env lean integration/FoundationCompactNumericListedDirectTraceComponentTableau.lean
lake env lean integration/FoundationCompactNumericListedDirectAdditiveTypeLayouts.lean
lake env lean integration/FoundationCompactNumericListedDirectTraceNatListSlices.lean
lake env lean integration/FoundationCompactNumericListedDirectTracePackedStreamSplits.lean
lake env lean integration/FoundationCompactNumericListedDirectStructuredListCanonical.lean
lake env lean integration/FoundationCompactNumericListedDirectTracePackedStreamListLayouts.lean
lake env lean integration/FoundationCompactNumericListedDirectAdditiveTypeCanonical.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStateLayout.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout.lean
lake env lean integration/FoundationCompactNumericListedDirectTracePackedStreamStateLayouts.lean
lake env lean integration/FoundationCompactNumericListedDirectAtomicListLayouts.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepCases.lean
lake env lean integration/FoundationCompactNumericListedDirectFlexibleBinaryNatDecode.lean
lake env lean integration/FoundationCompactNumericListedDirectNatListBoundaryRigidity.lean
lake env lean integration/FoundationCompactNumericListedDirectCompletedStatusReverseRows.lean
lake env lean integration/FoundationCompactNumericListedDirectCompletedStatusSameRows.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepRows.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation.lean
lake env lean integration/FoundationCompactNumericListedDirectAtomicListRowRealization.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStateFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepRealization.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableInstallation.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaBridge.lean
lake env lean integration/FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaInstallation.lean
lake env lean integration/FoundationCompactNumericListedDirectSyntaxTaskLayout.lean
lake env lean integration/FoundationCompactNumericListedDirectParserStateLayout.lean
lake env lean integration/FoundationCompactNumericListedDirectParserStateListLayout.lean
lake env lean integration/FoundationCompactNumericListedDirectTraceParserStateLayouts.lean
lake env lean integration/FoundationCompactNumericListedDirectSyntaxTaskRowRealization.lean
lake env lean integration/FoundationCompactNumericListedDirectParserStateFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectParserStateFormulaInstallation.lean
lake env lean integration/FoundationCompactNumericListedDirectParserStepCases.lean
lake env lean integration/FoundationCompactNumericListedDirectSyntaxTaskListSameRows.lean
lake env lean integration/FoundationCompactNumericListedDirectSyntaxTaskListDropRows.lean
lake env lean integration/FoundationCompactNumericListedDirectSyntaxTaskListConsRows.lean
lake env lean integration/FoundationCompactNumericListedDirectParserDoneRows.lean
lake env lean integration/FoundationCompactNumericListedDirectParserDoneFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectParserDoneInstallation.lean
lake env lean integration/FoundationCompactNumericListedDirectCompletedOutputSameRows.lean
lake env lean integration/FoundationCompactNumericListedDirectParserEmptyRows.lean
lake env lean integration/FoundationCompactNumericListedDirectParserEmptyFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectParserEmptyInstallation.lean
lake env lean integration/FoundationCompactNumericListedDirectSyntaxTaskListTailTable.lean
lake env lean integration/FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows.lean
```
