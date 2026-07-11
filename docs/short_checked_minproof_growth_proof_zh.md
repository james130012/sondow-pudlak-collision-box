# 最短证明增长下界：当前指导书

更新时间：2026-07-11。

## 主控方式

[定理依赖图 DOT](checked_minproof_theorem_dependency_graph_zh.dot) 是当前工作的唯一状态面板；
[SVG](checked_minproof_theorem_dependency_graph_zh.svg) 和
[PDF](checked_minproof_theorem_dependency_graph_zh.pdf) 是阅读版。本文件只保留图中节点所需的
精确定义、文献条件、关键不变量和成功判据，不再另建一套与图可能不同步的进度叙述。

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

详细 theorem dependency graph（定理依赖图）：
[可缩放 SVG](checked_minproof_theorem_dependency_graph_zh.svg)、
[PDF](checked_minproof_theorem_dependency_graph_zh.pdf)、
[PNG](checked_minproof_theorem_dependency_graph_zh.png)、
[DOT 源文件](checked_minproof_theorem_dependency_graph_zh.dot)。图中每个专业术语均附中文解释，
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

    单模块探针和目标构建均通过，六个审计端点公理画像只有三个 Lean 标准项。本检查点只关闭外层
    `count` 次迭代；每个 `compactFormulaTokenValuesStep` 内仍调用一次 formula value parser，尚未携带第 62 项
    的公式 parser 局部轨迹。因此该节点已标绿，但还没有冒充为完整 root 分支闭合；下一步为每行加入对应
    公式子轨迹，再组合进第 64 项的标签分支。

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

   第 59 至 65 项现已关闭非最小化外部轨迹语义、中央任务机局部计算表、两个公开 packed 输入子轨迹、
   proof/certificate/formula 三类解析器的外层局部计算表，以及 certified-parts/whole-formula 两个结果
   包装层、根节点十标签总分派和 sequent value 外层 counted repeat。当前黄色工作面是给 repeat 每一步加入
   公式 parser 子轨迹，再打开其余标签分支值解析器及验证器单步函数中的原子调用，并把整套见证显式编码成
   局部可核验算术公式：

   ```text
   P_direct(bound,y) := exists proofCode,
     payloadLength(proofCode) <= bound and
     exists trace, DirectVerifierTrace(proofCode,y,trace).
   ```

   精确 `verifier=true iff exists trace.Valid`、中央 `initial/step/final` 检查、packed token stream
   局部检查、三个 outer parser tableau 及两个结果包装层已闭合。下一步必须打开
   sequent repeat 中每个公式子运行以及 formula/closed-formula/term value parser，
   并继续展开 `parserStep/verifierStep` 内的原子字段解析和局部语法变换；随后给所有状态与子轨迹显式自然数编码，证明
   编码位长和局部核验具有统一多项式界，并直接构造
   该关系的二变量 Σ₁ 公式。只有这些步骤闭合后，才进入
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
lake env lean integration/FoundationCompactNumericListedDirectTrace.lean
```
