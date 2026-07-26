# 最短证明增长下界：证明主控书

更新时间：2026-07-26。

## 1. 目标与边界

固定同一个 formula family（公式族）、PA checker（PA 检查器）和
full-payload proof length（完整证明树加结构证书载荷长度）：

```text
F_b := not P_direct(b, falsumCode)
rho_d(n) := (n + 1)^(d*n)
G_n := F_{rho_d(n)}
```

下界目标是先证明：

```text
eventually (n + 1)^n < minProof(G_n),
```

再推出 `minProof(G_n)` 超过任意关于外层 `n` 的多项式。

最终对撞还需要一条独立的 Sondow bridge（Sondow 桥）：

```text
gamma 有理
  -> 同一 G_n 的真实 PA 证明具有最终多项式长度上界。
```

这条桥当前没有闭合。因此，即使下界完成，也不能据此宣称已经无条件证明
Euler 常数无理。

完成标准：

1. 同一 `n`、同一 `G_n`、同一公式码、同一检查器和同一载荷度量。
2. 无 `tail_gap`、`upper_provider`、项目级 `proof_length`、`sorryAx`
   或 toy PA（玩具 PA）。
3. 每个“存在短证明”结论都返回真实 `CertifiedPAProof`
   （带结构证书的 PA 证明），并由同一公开检查器验收。
4. Pudlak 下界必须在上述同一对象上完整形式化，不能用抽象
   super-polynomial gap（超多项式间隙）代替。

## 2. 数学路线

### 2.1 已固定公式族

Lean 端点：

```text
models_compactListedPADirectFiniteConsistencySentence_iff
```

源文件：

```text
integration/FoundationCompactNumericListedDirectFiniteConsistencyTarget.lean
```

它使用当前 `P_direct`、当前公开检查器、当前矛盾公式码和当前
`packedPayloadLength`（打包载荷长度）。

Pudlak 1986 Theorem 3.1（定理 3.1）给出固定正幂下界。选择足够大的固定
整数 `d` 后，在完美幂重标定

```text
rho_d(n) = (n + 1)^(d*n)
```

上可把该正幂放大到至少 `(n + 1)^n`。Lean 已证明纯增长闸门：

```text
eventually_lt_pudlakBussGrowthCarrier
PudlakBussPerfectPowerRescaledLowerBound.toStrongRescaledLowerBound
not_polynomial_bound_pudlakBussPerfectPowerScale
no_polynomialCofinalScale_pudlakBussPerfectPowerScale
```

源文件：

```text
integration/FoundationPudlakBussRescaledLowerBoundGate.lean
```

这些定理只依赖 `propext`、`Classical.choice`、`Quot.sound`。它们不证明
Pudlak 前提，也不能把结论转回未重标定的 `F_n`。

### 2.2 Pudlak 数学停工门

在对角化前，必须对当前 `P_direct` 关闭：

1. `PA` 一致且包含 Robinson `Q`；一致性由标准自然数模型的 PA
   soundness（可靠性）推出，不能作为项目公设。
2. 条件 `(0)`：证明界单调性。
3. 条件 `(1)`：真实 PA 证明可由 `P_direct` 在固定多项式开销内确认。
4. 条件 `(2)`：`P_direct` 的真接受实例在 PA 内有固定多项式短证明。
5. 条件 `(3)`：同一证明系统中的 MP（肯定前件）组合有固定多项式开销。
6. 对角化、代入、公式码和完整载荷长度使用同一编码，并有固定多项式界。

原文印刷条件 `(0)` 的方向仍须依据勘误或重证确认。文献 proof string
（证明串）到当前 full payload（完整载荷）的定量校准也尚未完成。

## 3. 已闭合基础

### 3.1 诚实证明坐标

- proof tree（证明树）和 structural certificate（结构证书）全部计入载荷。
- accepted code（接受码）可恢复同公式真实 `Derivation2 PA`（PA 推导树）。
- 规范化不增长载荷，畸形编码不能伪造更短证明。
- `minListedCertifiedPAProofPayloadLength` 由公开检查器诱导，无项目级
  `proof_length`。

### 3.2 定量 PA 编译基础

`A04.01--A04.17` 已闭合：

- PA 公理、全称实例化、MP、合取、析取和存在引入；
- 等式传递、加乘合同、短二进制数词加乘归一化；
- `expDef / lengthDef / bitDef` 的快速真实 PA 编译；
- 闭有界算术原子和有界公式的检查证书编译；
- 公开检查器验收和完整载荷显式界。

这些基础端点的公理画像只有：

```text
propext
Classical.choice
Quot.sound
```

### 3.3 `P_direct` 同对象等价

`M10 / A03.01--A03.08` 已闭合：

```text
compactListedPADirectProofFormula_iff_exists_publicVerifier

P_direct(bound, formulaCode)
  <->
  exists proofCode,
    packedPayloadLength(proofCode) <= bound
    and compactNumericListedPublicVerifier(proofCode, formulaCode) = true.
```

该等价锁定同一公式码、同一检查器、同一 proof + certificate
（证明加证书）编码和同一完整载荷度量。

## 4. 当前黄色节点：`M11 / A04.18`

目标：

```text
publicVerifier(proofCode, formulaCode) = true
  -> 构造同一 P_direct(bound, formulaCode) 的真实 PA 证明
  -> 公开检查器验收
  -> 完整 proof + certificate 载荷 <= 固定多项式。
```

已经闭合：

1. 接受码的规范 20 个外层见证及总二进制重量界。
2. 429 坐标接受轨迹表及逐行公开坐标界。
3. 输入表、公式表和输入分割的显式证书。
4. `P_direct` 的显式 20 层存在见证安装器。
5. 解析器六类步骤分支及开放索引相邻行的真实直接 PA 编译。
6. 相邻行有限全称及完整
   `CompactParserSyntaxAdjacentRowsBoundedGraph` 编译。
7. 解析器初态、终态和联合 36 坐标五叶证书。
8. 初末状态 23 个有界见证前缀的无黑盒直接编译。
9. `SequentFormulaStepRowBounded` 的原始 18 个有界见证直接编译。

### 4.1 最新闭合里程碑

初末状态五叶：

```text
parserInitialFinalFiveLeafBoundsOfGraph
compactUnifiedParserInitialFinalRowsClosedDirectBoundOfGraph
compactParserInitialFinalBoundedClosedDirectBoundOfBounded
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle.lean
integration/FoundationCompactNumericListedDirectParserInitialFinalRowsFullyFixedDirectBound.lean
integration/FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectStructuralCompiler.lean
```

旧 `endpointCertificate`（端点证书）和 graph-dependent payload
（依赖语义图的载荷）已从活跃 23 见证资源路线移除。

完整三叶解析器轨迹：

```text
compactParserSyntaxTraceBoundedDirectClosedFormula_alignment
compactParserSyntaxTraceBoundedClosedDirectBoundOfGraph
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectParserSyntaxTraceBoundedDirectCompiler.lean
```

该端点直接组合：

```text
stateCount = fuel + 1
  + parser initial/final（解析器初末状态）
  + adjacent rows universal（相邻行全称）
```

它返回同一原始 15 坐标闭公式的真实空上下文 PA 证明。受限单文件探针约
27 秒通过；公理画像只有标准三项；静态扫描无
`sorry/admit/axiom/sorryAx/tail_gap/upper_provider/proof_length`。

### 4.2 精确燃料项新增闭合

原复合燃料项现定义为：

```text
compactParserSyntaxExactFuelTerm inputCount
```

已完成并通过受限探针：

```text
shortBinaryNumeralTerm (16*(inputCount+1)^2+8)
  = compactParserSyntaxExactFuelTerm inputCount

iteratedSuccessorTerm fuel
  = compactParserSyntaxExactFuelTerm inputCount

adjacent rows universal at exact fuel term
exact-fuel complete adjacent-row graph
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.lean
integration/FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal.lean
integration/FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph.lean
```

等式由 valuation term compiler（赋值项编译器）和 PA 等式传递构造，
不是 Lean 数值 `cast`。精确相邻行图已返回原八坐标图实例的空上下文 PA
证明，并带完整载荷界。

对这条载荷界的固定资源重审现已推进到以下真实端点：

```text
任意赋值的 parser state row（解析器状态行）固定项码编译
  -> current / next / syntax-step 三叶相邻步
  -> current / next status（状态有效性）终端
  -> 原始 27 个有界见证直接安装
  -> &0 / &0+1 / &0+2 共用一个常数项码包
  -> 每个 rowIndex 共用同一分支资源
  -> 有限分支树
  -> 精确燃料项 bounded universal（有界全称）
  -> 原八参数 exact-fuel adjacent graph（精确燃料相邻图）。
```

关键新增端点：

```text
compactUnifiedParserStateAtRowsAtValuationIndexTermCodeFixedBoundAtValuation
compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedBoundOfGraph
compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound
compactParserSyntaxAdjacentRowsBoundedTermCodeFixedFullyDirectBranches
compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalContext
compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedContext
```

全部在 60 秒限制内通过；公开端点公理画像只有标准三项。该路线不再让
分支资源依赖开放索引项、27 个见证坐标或语义图证明。复合精确燃料闭项的
全称外壳、短数码指数等式叶和最终合取装配也已分别压入显式固定资源，并
接回原八参数相邻图。

新增固定资源端点：

```text
compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource_le_polynomial
compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext_payloadLength_le
compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext_payloadLength_le
```

初末状态方面也已完成：

```text
1. 精确 fuel 的 stateCount = fuel + 1 叶；
2. 精确 fuel 作为 final state-row index 的叶；
3. 与另外三叶组成的显式五合取 PA 证明；
4. 五叶逐层合取载荷账本；
5. 显式五合取与原 36 坐标母公式的分块对齐；
6. 原 36 坐标闭公式的空上下文 PA 证明；
7. 原 23 个有界见证的直接安装；
8. 只依赖公开参数、无见证坐标依赖的统一载荷上界。
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle.lean
integration/FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax.lean
integration/FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelAlignment.lean
integration/FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFullyFixedDirectBound.lean
integration/FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelUniformDirectBound.lean
integration/FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler.lean
```

全部新增已通过 60 秒内单文件探针；端点公理画像只有
`propext / Classical.choice / Quot.sound`。

### 4.3 原精确解析图语义闭合与固定资源重审

直接父节点：

```text
CompactParserSyntaxExactBoundedGraph
```

它在原公式中保留燃料项：

```text
16 * (inputCount + 1) * (inputCount + 1) + 8
```

数值与精确燃料项之间的 PA 等式、精确相邻行图和精确初末状态五叶均已
关闭。原 36 坐标母公式对齐和 23 个有界见证安装也已关闭；当前没有再把
数值相等冒充 PA 公式相等，也没有把见证坐标藏进公开载荷上界。

以下三项的真实 PA 证明和固定资源界均已关闭：

```text
1. 把精确 state-count、initial/final、adjacent 三部分装成 trace；
2. 对齐并返回原 compactParserSyntaxExactBoundedGraphDef 闭实例；
3. 给 trace 外层装配建立固定、无语义图依赖的最终显式多项式。
```

新增闭合定理：

```text
compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula_alignment
compactParserSyntaxExactBoundedDirectClosedFormula_alignment
compactParserSyntaxExactBoundedClosedDirectBoundOfGraph
compactParserSyntaxExactBoundedFullyFixedClosedDirectBoundOfGraph
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax.lean
integration/FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler.lean
integration/FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedDirectGraph.lean
integration/FoundationCompactNumericListedDirectParserSyntaxExactBoundedFullyFixedDirectCompiler.lean
```

新端点返回原 14 参数
`compactParserSyntaxExactBoundedGraphDef` 闭实例的空上下文真实 PA
证明。计数等式、初末状态、相邻行、两次合取的资源只依赖公开参数及统一
数值／位长界，不依赖端点见证或语义图证明。精确相邻图与完整精确解析器图
探针分别约 10 秒和 17 秒通过；公理画像均只有
`propext / Classical.choice / Quot.sound`。

36 坐标对齐曾拆成四个 16 坐标子公式桥，再汇总为母公式等式；汇总探针
约 11 秒通过。精确端点的 23 见证结构编译探针约 9 秒通过。

### 4.4 复合状态数坐标运输闭合

`SequentFormulaStep` 不使用数值状态数项，而直接使用：

```text
16 * (currentCount + 1) * (currentCount + 1) + 8 + 1
```

现已在 PA 内完成真实等式运输，未用 Lean `cast` 把数值相等冒充公式
替换：

```text
stateCount = exactFuelTerm(inputCount) + 1
  -> parserGraph(..., stateCount, ...)
  -> parserGraph(..., exactFuelTerm(inputCount) + 1, ...).
```

固定 15 变量母定理先由标准模型语义证明，再取得一个固定 PA 推导；随后
逐项特化 15 个公开项。母推导是固定常数，不接收随输入变化的
proof-existence（证明存在）或长度参数。特化、两次 MP 和完整结构证书均
有显式载荷账本。

闭合端点：

```text
specializeAllClosure
specializeAllClosure_payloadLength_le
compactParserSyntaxExactStateCountTransportPublicProof
compactParserSyntaxExactCompositeStateCountClosedDirectBoundOfGraph
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport.lean
```

受限单文件探针通过；端点公理画像只有
`propext / Classical.choice / Quot.sound`，无 `sorryAx` 或项目公设。

### 4.5 原始 `SequentFormulaStep` 直接编译闭合

原 26 坐标公式的 21 个右嵌套合取项现已全部产生空上下文真实 PA 证明：

```text
9 个数值界 + 6 个定宽表项 + 3 个列表见证
+ 1 个精确解析器图 + 1 个切片拼接 + 1 个末尾计数等式。
```

公开清单定理核验项目数恰为 21，并证明重组后的公式逐项等于原
`compactSequentFormulaStepDef` 闭实例。各叶资源已分别压到只依赖公开
数值坐标的有限包络；20 次合取装配由透明递归函数统一记账。最终
`payloadLength`（证明与证书总载荷长度）不再依赖 `hgraph`（语义图成立
证明）的内部形状。

闭合端点：

```text
compactSequentFormulaStepDirectPublicConjuncts_formula_alignment
compactSequentFormulaStepDirectStructuralBoundOfGraph
compactSequentFormulaStepDirectProofOfGraph_payloadLength_le_public
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectNatListWitnessRowsPublicBounds.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler.lean
```

最后一次受限探针约 22 秒通过；全部公开端点公理画像只有
`propext / Classical.choice / Quot.sound`，无项目公设和 `sorryAx`。

### 4.6 原始 18 个行见证编译闭合

现已从同一个
`CompactSequentFormulaStepRowBounded` 命题提取一份 checked data
（已检查数据），其中同一 `row` 同时满足：

```text
18 个 witness value <= valueBound
+ 原 CompactSequentFormulaStepGraph。
```

已逐层证明：

```text
原 9 坐标公式
= 18 层有界存在量 + 原 26 坐标终端；
18 个实际见证代入终端
= 已闭合的 SequentFormulaStep 直接公式；
终端、安装后终端和最终公式的自由变量均为空；
固定 18 元公共编译器返回原公式的空上下文 PA 证明。
```

闭合端点：

```text
compactSequentFormulaStepRowBoundedDef_eq_emptyRawBody
compactSequentFormulaStepRowBoundedDirectClosedFormula_alignment
compactSequentFormulaStepRowBoundedDirectRawTerminal_alignment
compactSequentFormulaStepRowBoundedDirectDataOfBounded
compactSequentFormulaStepRowBoundedExplicitWitnessDirectBoundOfData
compactSequentFormulaStepRowBoundedClosedDirectBoundOfBounded
```

固定元数 opaque wrapper（不透明包装器）有真实 Lean 实现，只用于阻止
下游重复展开已核验的 18 层递归；它不是 `axiom`（公设）。最终端点探针
约 9 秒通过，公理画像只有
`propext / Classical.choice / Quot.sound`。

### 4.7 原始行有限全称图编译闭合

有限全称不能复用闭合行公式，因为分支体必须保留开放索引 `&0`。现已完成
真正的开放索引路线：

```text
21 个原始合取项在 &0 下直接编译
  -> 同一 &0 下安装 18 个有界行见证
  -> 对每个 rowIndex < rowCount 生成真实分支证明
  -> 组装有限分支树
  -> 编译 bounded universal（有界全称）
  -> 合取 valueBound = 2^tableWidth 指数叶
  -> 对齐回原 SequentFormulaStepRowsBoundedGraph。
```

闭合端点：

```text
compactSequentFormulaStepRowBoundedAtValuationIndexProofOfData
compactSequentFormulaStepRowsBoundedFullyDirectBranches
compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext
compileCompactSequentFormulaStepRowsBoundedDirectClosedContext
compileCompactSequentFormulaStepRowsBoundedDirectClosedContext_payloadLength_le
```

关键实现文件：

```text
integration/FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessPublicProof.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTree.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversal.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraph.lean
```

指数叶、有限全称和最终原公式的定向探针均通过；公开端点公理画像只有
`propext / Classical.choice / Quot.sound`，无项目公设、`sorryAx`、
`tail_gap`、`upper_provider` 或 `proof_length`。

`SequentFormulaStepRowsBoundedGraph` 的“由真实图数据产生 PA 证明”已经闭合。

### 4.8 证明参数无关的统一资源界闭合

现已对 18 个有界行坐标的有限盒取 `Finset.sup`（有限上确界），再对
`rowIndex < rowCount` 取第二个有限上确界。这里取的是最大资源而不是把所有
候选相加，因此没有人为引入 `(valueBound + 1)^18` 的载荷因子。真实分支先
落入单行最大值，整棵分支树再由原有限全称装配器线性记账。

最终端点：

```text
compactSequentFormulaStepRowsBoundedDirectBranchResource_le_uniform
compactSequentFormulaStepRowsBoundedDirectBranchResource_le_familyUniform
compactSequentFormulaStepRowsBoundedFullyDirectBranches_structuralPayloadBound_le_uniform
compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext_payloadLength_le_uniform
compileCompactSequentFormulaStepRowsBoundedDirectClosedContext_payloadLength_le_uniform
```

最后一个资源函数只依赖原图公式的 10 个公开数值坐标，不再携带
`hgraph / hrows / checked data`（图证明、行证明或已检查数据）。全部受限
探针通过，公理画像仍只有
`propext / Classical.choice / Quot.sound`。

有限上确界不是最终多项式结论。当前第一义务是逐项证明候选资源只依赖公开
项的 `Nat.size`（二进制长度），从而把两个有限上确界压到一个显式多项式；
完成后再接入 `GuardedInductionSentenceRoute`（带保护归纳句生成路线）。

该显式化现已关闭终端全部 21 个叶子的固定资源界：

```text
9 个闭合数值不等式
6 个开放索引定宽表项
3 个自然数列表见证行
1 个精确解析器图
1 个列表切片拼接图
1 个后继计数等式
```

相应固定界只依赖统一数值界、位长界和固定索引项代码界；探针公理画像仍为
`propext / Classical.choice / Quot.sound`。列表切片拼接端点已经返回真实空
上下文 PA 证明及固定多项式载荷界；`rightCount` 和 `targetCount` 的公开界
显式来自外层已检查见证数据，不从局部拼接图中伪造。

三组自然数列表见证行共用一个已核验编译器。数值界显式取
`max width tokenCount`；位长界显式覆盖令牌表位长、该数值界位长和
`(tokenCount + 1) * tokenCount`。每组边界表位长由同一已检查行关系中的
精确 `Nat.size` 等式和边界面积界推出，无新增参数。外层
`CompactSequentFormulaStepGraph` 已同时接出 current / next / value
（当前／下一／值）三份真实空上下文 PA 证明。

新增端点：

```text
compactSequentFormulaStepNatListRowFullyFixedBound
compactSequentFormulaStepNatListRowsFullyFixedBoundsOfGraph
compactSequentFormulaStepNatListRowsFullyFixedBoundsOfCheckedData
```

对应文件：

```text
integration/FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowFullyFixedBound.lean
integration/FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedOfGraph.lean
```

公共界、单行证明和三叶接线探针分别在 60 秒限制内通过。精确解析器的
state-count/task transport（状态数／任务常量运输）、列表拼接和末尾计数
均已接入同一固定资源路线。第 16--21 项已按
`tail20 -> tail19 -> tail18 -> tail17 -> tail16` 分层关闭独立公式码界与证明
载荷界；最终端点
`compactSequentFormulaStepTail16FullyFixedEmptyBoundOfGraph` 的受限探针约
9 秒通过，公理画像只有标准三项。

六个开放索引定宽表项已经与第 16--21 项放入同一精确赋值上下文，并按
`tail15 -> tail14 -> tail13 -> tail12 -> tail11 -> tail10` 分层关闭。最终端点
`compactSequentFormulaStepDirectTail10AtValuationIndexFullyFixedResultOfData`
严格回接原 `DirectTail10AtValuationIndex` 公式；受限探针约 10 秒通过，公理
画像只有标准三项。

九个闭合数值不等式已经由同一 `data.graph` 提取，并向前接到第 10--21 项。
完整端点
`compactSequentFormulaStepDirectFormulaAtValuationIndexFullyFixedResultOfData`
严格回接原 21 项开放索引公式；受限探针约 12 秒通过。随后经原始终端代入
对齐和固定 18 元有界见证编译器，端点
`compactSequentFormulaStepRowBoundedAtValuationIndexFull21FullyFixedBoundOfData`
返回原单行公开公式的真实证明及显式载荷界；拆分后的两个探针均约 9 秒通过。
全部端点公理画像只有标准三项。

显式统一资源路线现已贯通整个有界行图：

```text
解析器指数资源单调界
  -> 相邻行 27 见证统一资源
  -> 初末状态 23 见证统一资源
  -> 原精确解析器图统一资源
  -> SequentFormulaStep 的 parser / list / append / count 叶
  -> 完整 21 项开放索引公式
  -> 原 18 元有界见证
  -> 每行共用同一显式资源的有限分支树
  -> bounded universal（有界全称）
  -> 原 SequentFormulaStepRowsBoundedGraph。
```

最终端点：

```text
compactSequentFormulaStepDirectFormulaAtValuationIndexUniformResultOfData
compactSequentFormulaStepRowBoundedAtValuationIndexFull21UniformBoundOfData
compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof_payloadLength_le
compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches_structuralPayloadBound_le
compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext_payloadLength_le
compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext_payloadLength_le
```

这里的统一 `bitBound`（位长界）是八个公开输入的 `Nat.size` 之和加一，
`numericBound`（行号数值界）直接取 `rowCount`。最终资源只依赖原图公式的
十个公开数值坐标；不依赖 `data.row`、18 个见证值、`hgraph / hrows`
（图证明／行证明），也不使用 `Finset.sup`（有限上确界）。公式码界和证明
载荷界始终分开记账。

上述新增端点均在 60 秒限制内通过，公理画像只有
`propext / Classical.choice / Quot.sound`；没有项目公设、`sorryAx`、
`tail_gap`、`upper_provider` 或 `proof_length`。因此
`SequentFormulaStepRowsBoundedGraph` 的显式统一资源节点已经关闭。
其直接父公式是 `CompactSequentFormulaTraceBoundedGraph`（序列公式解析轨迹
有界图），还需把计数等式、suffix/value 两张列表边界表良构证明和当前行图
合取起来。当前第一义务是为两张
`CompactAdditiveNatListListRowsWellFormed`（自然数列表边界表良构）公式建立
同样不依赖所选行见证的显式统一资源，再关闭该四项父公式。

后续链保持为：

```text
SequentFormulaStepRowsBoundedGraph 显式统一上界（已闭合）
  -> CompactSequentFormulaTraceBoundedGraph
  -> SequentFormulaEndpoint（序列公式解析端点）
  -> GuardedInductionSentenceRoute
  -> InductionPAAxiomRuleCheck（归纳 PA 公理规则检查）
  -> verifier StepGraph / BoundedGraph（验证器步骤图／有界图）
  -> complete direct matrix（完整直接矩阵）
  -> 20 层外部见证
  -> A04.18 闭合。
```

`A04.18` 仍为黄色；这项闭合的是完整 accepted-trace compiler
（接受轨迹编译器）中的一个真实父节点，不能表述为 Pudlak 下界已经完成。

## 5. 后续固定顺序

```text
M11 / A04.18  接受计算的 PA 短证明编译
  -> M12 / A05.03  Pudlak 条件 (0)--(3)
  -> M13--M14  Pudlak 定量对角化、证明拼接和指数提取
  -> M15  选择整数 d 并建立完美幂重标定
  -> M16  同一 G_n 的超多项式最短证明下界
  -> M17--M20  Sondow 独立桥、大 N 和最终对撞。
```

不得用 Buss 1994 Theorem 5 的外部输入、abstract gap（抽象间隙）或
`PolynomialCofinalScale` 把结论偷换回未重标定的 `F_n`。

## 6. 验证规则

开发阶段只跑受限单文件探针：

```bash
timeout --signal=TERM --kill-after=5s 60s \
  systemd-run --user --scope --quiet \
  -p CPUQuota=100% \
  -p MemoryHigh=1400M \
  -p MemoryMax=2300M \
  -p MemorySwapMax=128M \
  -p TasksMax=16 \
  lake env lean FILE -o OLEAN
```

每个局部里程碑还要执行：

```bash
rg -n "\\b(sorry|admit|axiom)\\b|sorryAx|tail_gap|upper_provider|proof_length" FILE
git diff --check
```

只有下游定向探针需要 import（导入）时才生成单模块 `.olean`
（Lean 编译对象）。`A04.18` 闭合前不运行全项目构建。

DOT/PDF 只在一个黄色节点整体转绿或路线发生根本变化时更新。
