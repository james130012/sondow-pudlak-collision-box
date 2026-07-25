# 最短证明增长下界：精简证明指导书

更新时间：2026-07-25。

## 1. 主控文件

- [主定理依赖图](checked_minproof_theorem_dependency_graph_zh.dot)：全局主路线。
- [附图 01：诚实证明坐标](checked_minproof_appendix_01_syntax_coordinate_zh.dot)。
- [附图 02：解析器与嵌套轨迹](checked_minproof_appendix_02_parser_traces_zh.dot)。
- [附图 03：验证器步骤与 P_direct](checked_minproof_appendix_03_verifier_predicate_zh.dot)。
- [附图 03 PDF](checked_minproof_appendix_03_verifier_predicate_zh.pdf)。
- [附图 04：PA 定量证明编译器](checked_minproof_appendix_04_pa_quantitative_compiler_zh.dot)。
- [附图 05：Pudlak 下界与对撞](checked_minproof_appendix_05_pudlak_collision_zh.dot)。

DOT 中绿色节点必须有 Lean 内核端点定理、源文件和公理画像
（axiom profile，定理依赖的公理集）。黄色只保留一个当前义务；灰色表示等待前置。

## 2. 最终目标

在同一 formula family（公式族）、PA checker（PA 检查器）和
full-payload proof length（完整证明树加证书载荷长度）上证明：

```text
F_b := not P_direct(b, falsumCode)
rho_d(n) := (n+1)^(d*n)
G_n := F_{rho_d(n)}

Sondow：假设 gamma 有理
  -> 构造同一 G_n 的规范 PA 证明
  -> minProof(G_n) <= U(n) eventually；

Pudlak：
  -> (n+1)^n < minProof(G_n) eventually
  -> minProof(G_n) 超过任意关于外层 n 的多项式；

取同一 N：U(N) < minProof(G_N) <= U(N)，矛盾。
```

成功标准：

1. 同一 `n`、同一 `F_n`、同一公式码、同一检查器和同一完整载荷度量。
2. 无 `tail_gap`、`upper_provider`、项目级 `proof_length`、`sorryAx` 或 toy PA（玩具 PA）。
3. 每个“存在短证明”结论都由真实 proof object（证明对象）和真实 checker 验收支撑。
4. Pudlak 下界必须对上述同一对象完整形式化，不用抽象超多项式间隙代替。

### 2.1 已固定的下界公式族与数学闸门

原始下界公式固定为

```text
F_b := not P_direct(b, falsumCode).
```

Lean 端点：

```text
models_compactListedPADirectFiniteConsistencySentence_iff
```

它逐字使用当前 `P_direct`、同一公开检查器、同一矛盾公式码和同一
`packedPayloadLength`。源文件：

```text
integration/FoundationCompactNumericListedDirectFiniteConsistencyTarget.lean
```

原文核验确认 Pudlak 1986 Theorem 3.1 允许任意满足其四个定量可导条件的
二变量证明谓词 `P(x,y)`；当前任务是证明这里的 `P_direct` 满足这些条件。
原定理给出某个固定正幂下界。取足够大的固定整数 `d` 后，在

```text
G_n := F_{rho_d(n)},  rho_d(n) = (n+1)^(d*n),
```

上该固定正幂已经至少为 `(n+1)^n`，因此直接得到关于外层 `n` 的超多项式
下界。对当前完美幂重标定，Buss 1994 Theorem 5 的任意
time-constructible function（时间可构造函数）推广不是必要前置；不再把它
列为主路线硬依赖。结论仍不能转回未重标定的 `F_n`。

Lean 已建立数学闸门：

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

它严格证明：

1. `(n+1)^n` 超过任意多项式；
2. 对 `G_n` 的最终 `(n+1)^n` 下界足以推出强下界；
3. `rho_d` 本身不是 polynomial scale（多项式尺度），所以旧
   `PolynomialCofinalScale` 转回 `F_n` 的路线不可使用。

这些端点的公理画像只有 `propext`、`Classical.choice`、`Quot.sound`。

必须与下界分开记录的最终闸门是：

```text
gamma 有理
  -> 构造同一 G_n = F_{rho_d(n)} 的多项式长度真实 PA 证明。
```

现有 Sondow checked certificate（已检查证书）只直接给出
`sondowCertificateValidCode(n)` 的短证明。旧 reflection-graft（反射嫁接）
把有限一致性载荷作为独立合取项，不能由 Sondow 证书自动补出，故不作为干净
投稿路线。这个闸门不影响下界形式化本身，但未关闭前不得宣称最终碰撞。

### 2.2 数学停工门

在继续对角化前，必须在当前对象上分别关闭 Pudlak Theorem 3.1 的全部前提：

1. `A = PA` 一致且包含 Robinson `Q`；一致性由标准自然数模型的 PA
   soundness（可靠性）给出，不作为项目公设。
2. 条件 `(0)`：证明界单调性。
3. 条件 `(1)`：任意真实 PA 证明可在固定多项式开销内被 `P_direct` 内部确认。
4. 条件 `(2)`：`P_direct` 的真接受实例可在 PA 内再次获得固定多项式短证明。
5. 条件 `(3)`：同一证明系统中的 MP（肯定前件）组合具有固定多项式开销。
6. 对角化、公式代入、公式码和完整载荷长度都使用当前同一编码，并给出
   固定多项式界。

任一项若只能通过参数、公设或不同长度坐标得到，就停止该分支，不能继续包装。
这道闸门通过后，下界路线才具有文献定理所需的数学对象一致性。

独立数学审计当前判决为 C：上述 Pudlak 条件及文献 proof string
（证明串）到当前 full payload（完整载荷）的定量校准尚未建立；
原文印刷条件 `(0)` 的方向也必须由勘误或对原证明的重证处理，不得
静默改向。该判决不否定 `A04.18` 的检查器算术化基础，但禁止把
`A04.18` 的闭合单独宣称为无条件最短证明下界。

最终 Sondow 桥是另一道独立闸门：

```text
gamma 有理 -> 同一 G_n 的多项式长度真实 PA 证明。
```

当前尚无这条桥的无条件证明。即使 Pudlak 下界全部完成，也不能据此宣称
Euler 常数无理；反过来，这不影响下界形式化本身成为独立、可审计的成果。

## 3. 已闭合主干

### 3.1 诚实证明坐标

- proof tree（证明树）与 structural certificate（结构证书）全部进入载荷。
- accepted code（接受码）可恢复同公式真实 `Derivation2 PA`（PA 推导树）。
- 规范化不增长载荷，畸形编码不能伪造更短证明。
- `minListedCertifiedPAProofPayloadLength` 由公开检查器诱导，无项目级 `proof_length`。

### 3.2 PA 定量证明编译器

`M05--M09 / A04.01--A04.17` 已闭合：

- PA 公理、全称实例化、MP（肯定前件）、合取和存在引入。
- 等式传递、加乘合同、短二进制数词加法与乘法归一化。
- 六类闭算术原子文字和有界公式证书编译。
- 所有输出都是真实 `CertifiedPAProof`（带证书 PA 证明），并有公开检查器接受和固定多项式完整载荷界。

定量编译联合端点：

```text
CheckedClosedBoundedFormulaCertificate.compile_checked_polynomial
  : checker(compile certificate) = true
    and payloadLength(compile certificate)
      <= fixedPolynomial(encodedSize certificate).
```

### 3.3 `P_direct` 与同一对象审计

`M10 / A03.01--A03.08` 已全部闭合。核心端点：

```text
compactListedPADirectProofFormula_iff_exists_publicVerifier

P_direct(bound, formulaCode)
  <-> exists proofCode,
        packedPayloadLength(proofCode) <= bound
        and compactNumericListedPublicVerifier(proofCode, formulaCode) = true.
```

这个等价同时锁定：

- 显式二变量 `Sigma-one`（存在算术）公式；
- 同一 `formulaCode`（公式码）；
- 同一 `compactNumericListedPublicVerifier`（公开检查器）；
- 同一 proof + certificate（证明加证书）编码；
- 同一 `packedPayloadLength`（完整载荷长度）。

接受的任意数值记号流现在都会反演为规范证明树、规范结构证书及同一唯一结论。
十类证明节点逐一反演，无 parser assumption（解析器假设）、无结论证书输入。
公理画像只有 `propext`、`Classical.choice`、`Quot.sound`。

## 4. 唯一当前义务：`M11 / A04.18`

目标是 accepted trace to short PA proof compiler（接受轨迹到 PA 短证明编译器）。

输入已经具备：

1. `P_direct(bound,y)` 的 20 个显式存在见证和同一有界矩阵。
2. 有界矩阵的真实性来自同一公开验证器接受执行。
3. `A04.17` 能把真的闭有界公式证书编译为真实 PA 证明。
4. `compileSigmaZeroTruth` 已从真实 `Sigma-zero`（有界算术）真值递归构造
   valuation certificate（赋值证书）和真实 PA 证明；定向探针通过，
   公理画像仅 `propext` / `Classical.choice` / `Quot.sound`。
5. 旧逻辑入口已经可构造同一闭合 `P_direct(bound,y)` 的真实
   `CertifiedPAProof`，且生成证明由同一数值公开检查器验收；但该入口的矩阵
   终端仍依赖 `ofSigmaZeroTruth`，因此不能作为 `A04.18` 的定量闭合端点。
6. 20 个存在见证已成为显式结构；规范轨迹的 `traceWidth`、`traceTable`
   也已改为同一确定执行产生的明确算术项，不再从不透明存在量中选择。

当前需要真正证明：

```text
publicVerifier(proofCode,y) = true
  -> 构造规范的 20 个数值见证
  -> 证明全部见证的总二进制重量 <= 固定多项式
  -> 对 expDef / bitDef / lengthDef 使用二进制递归或 PA 归纳的快速证明
  -> 其余小界 Sigma-zero 子式使用通用真值编译器
  -> 逐层存在引入得到 P_direct(bound,y) 的真实 PA 证明
  -> 完整 proof + certificate 载荷 <= 一个固定多项式。
```

定量审计已经排除一条错误捷径：通用 `compileSigmaZeroTruth` 会按有界全称
的数值界逐项生成分支；`traceValueBound = 2^traceWidth`，所以直接编译整个
矩阵不能推出输入载荷的固定多项式界。逻辑证明正确，但定量上不够。

轨迹表的 429 坐标二进制大小义务已经闭合：十种有效证明树构造的结构归纳覆盖全部树内步骤，
并与 finish（结束）和 halted（停机自环）合并为完整 fuel（燃料）轨迹。
新的 bounded row selector（有界行选择器）直接从有界存在定理取行，避免旧
任意 `Classical.choose` 丢失大小界；所得表逐行满足步骤公式、相邻行切片相等、
首行输入布局和末行接受布局，并有显式 `traceWidth / traceTable /
2^traceWidth` 二进制大小界。核心端点为：

```text
exists_compactNumericVerifierAcceptedTreeTaskCheckedStepRow_with_globalBound
exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalBound
compactNumericVerifierAcceptedBoundedTraceTable_complete
compactNumericVerifierAcceptedBoundedTraceTable_size_le
```

全部端点的公理画像仅为 `propext` / `Classical.choice` / `Quot.sound`，
无项目公设、无 `sorryAx`。

20 个外层见证的定量义务也已闭合。公开接受码现在直接产生 bounded direct
witness（有界直接见证）：17 个非轨迹坐标复用原规范坐标审计，3 个轨迹坐标
使用上述显式有界表；输入流预算在构造端固定为只依赖公开 `bound` 的
`compactNumericDecodedTokenListWeightBound bound`。核心端点为：

```text
directBoundedWitness_nonempty_of_public
directBoundedWitness_exists_with_bitWeight_le_of_public
directBoundedWitness_bitWeight_le
```

总二进制重量只依赖 `bound` 与 `Nat.size formulaCode`。此外，外层 20 个见证
以及每行 429 个局部坐标都已吸收到同一个公开位证明预算；正、负 `bitDef`
文字统一调用真实 PA 位递归编译器：

```text
proveBinaryBitLiteralAtShortNumerals_checked_directWitnessField
proveBinaryBitLiteralAtShortNumerals_checked_directRowCoordinate
```

这些新增端点的公理画像同样只有上述三项。

快速叶到任意赋值项的接线现已闭合：`expDef / lengthDef / bitDef` 的正负文字
都能沿真实 PA 项等式传送到原公式。Foundation 的指数、长度和位成员语义也已
从零证明分别等于 `2^n`、`Nat.size` 和 `Nat.testBit`，不是新增假设。自动
recognizer（识别器）先截获完整快速叶，其余 `Sigma-zero` 结构才递归展开；由
真值构造 hybrid certificate（混合证书）并编译真实 PA 证明的端点已经通过：

```text
FoundationCompactPANativeFastArithmeticSemantics.expInstance_value
FoundationCompactPANativeFastArithmeticSemantics.lengthInstance_value
FoundationCompactPANativeFastArithmeticSemantics.bitInstance_value
FoundationCompactPANativeFastArithmeticSemantics.notBitInstance_value
FoundationCompactPAHybridValuationBoundedFormulaBuilder.compileSigmaZeroTruth
```

普通赋值项的短数词归一化、加乘递归、上下文传送和最终项值等式也已有显式
payload resource（载荷资源）界。标准 `exp / length / bit / notBit` 实例的
recognizer completeness（识别器完备性）已由四个无条件定理关闭，排除了
意外回退到慢速结构展开。普通正负原子、指数、长度、移位界项及项界有界全称
编译器的显式资源界均已通过定向探针；这些端点的公理画像仅为
`propext` / `Classical.choice` / `Quot.sound`。

正负 `bitDef` 赋值资源界已经改接精确多项式位递归端点。
`compactFixedWidthEntryDef` 现已进一步给出完整 explicit hybrid certificate（显式
混合证书）：内部 `size := Nat.size value` 直接安装，每一个位分支由 `.nil/.snoc`
递归生成，等号/严格小于分支、真实 PA 上下文证明和结构资源上界均已通过探针：

```text
compactFixedWidthEntryExplicitHybridCertificate
compileCompactFixedWidthEntryExplicitHybridContext
compileCompactFixedWidthEntryExplicitHybridContext_payloadLength_le
```

公理画像仍只有上述三项；没有 `ofSigmaZeroTruth`、项目公设或 `sorryAx`。
闭实例之外，`indexTerm-at-valuation`（赋值下索引项）版本也已独立通过探针。
它允许四个坐标均为任意 `ValuationTerm`，并在 `extendValuation index` 下分别证明
`&0 = index` 与 `&0 + 1 = index + 1` 的求值坐标；因此 token-count 全称分支不再
需要把开放行号错误 `cast` 成闭数值。端点为：

```text
compactFixedWidthEntryAtValuationExplicitHybridCertificate
compileCompactFixedWidthEntryAtValuationExplicitHybridContext
compileCompactFixedWidthEntryAtValuationExplicitHybridContext_payloadLength_le
```

其公理画像同样只有标准三项，无真值回退或隐藏证明对象。

完整 22 坐标矩阵现已能从 proof-free hybrid certificate（无证明对象的混合
证书）编译到真实 PA 证明，并由同一公开检查器验收。这关闭了同对象逻辑接线，
但尚未给出组合后完整载荷的固定多项式界。混合编译器现已有互递归 proof-free
structural payload bound（无证明对象的结构载荷界）：叶资源、两次上下文弱化和
有界全称分支均被独立收费，最终端点的公理画像只有标准三项。

最新定量审计进一步发现：现有 `directMatrixHybridCertificate` 通过
`ofSigmaZeroTruth` 从真值选择矩阵内部存在见证。逻辑上这些见证正确，但部分只知
不超过 `2^traceWidth`；通用有界全称编译器又按见证给出的实际数值展开。因此这个
证书不能直接推出公开输入大小的固定多项式载荷界。继续给它套资源多项式会掩盖
指数成本，禁止采用。

通用 Sigma-one（存在算术）编译器会从真值重新选择见证，不能用于定量路线。
新的 explicit-witness builder（显式见证构造器）只接受调用者给出的见证并逐层
执行真实存在引入；其末端直接使用上述结构载荷界，不再接受生成后证明长度或
外部数值上界作为前提。该构造器及递归资源端点已经通过定向探针。

20 个外层见证的逻辑接线现已关闭。新的 vector closure builder（向量闭包构造器）
沿 `exsClosure` 的定义递归，把同一 20 坐标向量从最高坐标到最低坐标逐层安装；
末端是同一闭合 direct matrix（直接矩阵）的 hybrid certificate（混合证书），
不从语义真值选择见证。原来直接展开 20 层导致探针超时，改为该局部替换构造后
定向探针通过，公理画像仅为标准三项。端点为：

```text
buildExplicitWitnessHybridExsClosureFromVector
directExplicitWitnessPayload
compileDirectExplicitWitness
compileDirectExplicitWitness_publicVerifier_eq_true
compileDirectExplicitWitnessContext_payloadLength_le
```

后三个端点分别给出真实 context-free certified PA proof（无上下文带证书 PA
证明）、同一公开验证器验收和完整证明长度不超过显式结构资源；结构资源尚未被
误称为公开多项式。

规范公式 token table（记号表）已经闭合完全显式路线。每行的
`token / offset / next`（记号/偏移/下一偏移）都是确定的 `getI`
函数；三层存在见证、哨兵界、开放行号定宽表项、记号段以及
token-count 的 `.nil/.snoc` 有界全称分支均由显式证书构造。端点为：

```text
compactNumericListedDirectCanonicalFormulaTable_internalBounds
compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
compactBinaryNatTokenStreamTableauExplicitHybridCertificate
compileCompactBinaryNatTokenStreamTableauExplicitHybridContext
compileCompactBinaryNatTokenStreamTableauExplicitHybridContext_payloadLength_le
compactBinaryNatTokenStreamTableauCanonicalExplicitHybridCertificate
```

外层 payload / sentinel（载荷/哨兵）和上述显式令牌流也已合并成
新的规范公式表端点：

```text
compactCanonicalFormulaTableExplicitCertificate
compactCanonicalFormulaTableExplicitCertificateAtCode
compileCompactCanonicalFormulaTableExplicit
compileCompactCanonicalFormulaTableExplicit_publicVerifier_eq_true
compileCompactCanonicalFormulaTableExplicit_payloadLength_le_structure
```

新路线不调用 `ofSigmaZeroTruth`；保留的 `OuterWitness` 旧端点仍使用它，
不属于新端点的定义链。上述新端点的定向探针全部通过，公理画像仅
`propext` / `Classical.choice` / `Quot.sound`。当前只得称为“规范公式表的
显式逻辑证书及结构资源界已闭合”；尚未得到相对公开输入长度的固定
多项式资源界。

`AtCode` 端点只沿已证明的规范代码等式传送同一证书，供证明码输入表与公式表
共同复用。声明依赖闭包审计已从十七个公开显式端点递归检查 3729 个项目声明；若路径
重新到达 `ofSigmaZeroTruth`、对应真值选择定理或旧 `OuterWitness` 端点，探针
会直接失败。该审计已通过，位于
`FoundationCompactNumericListedDirectCanonicalFormulaTableDependencyAudit.lean`。

规范表现已接到真实 bounded direct witness（有界直接见证）的两组坐标：

```text
boundedWitnessInputTableauExplicitCertificate
boundedWitnessFormulaTableauExplicitCertificate
```

前者证明证明码输入流，后者证明结论公式流；两者只使用结构内已证明的规范坐标
等式。`AcceptedPayloadMatrix` 也已严格分解为“规范输入表、输入分割、接受轨迹表”
三个闭公式，分解端点的公理画像只有标准三项。规范输入表与 `InputSplit`
现均已显式闭合。输入分割的两个跨表切片分别以
`proofTokens.length` 与 `certificateTokens.length` 为明确见证，并保留
`proofStart + 1 / certificateStart + 1` 原算术项；证书、编译和结构载荷界
端点均通过标准三项公理画像。

`AcceptedTraceTable` 的最终接受行也已独立显式闭合：列 36、38 的索引保留
`rowIndex * 429 + 36/38` 原算术项，复用开放赋值定宽表项证书；编译、结构资源
和载荷界端点均通过标准三项公理画像。显式 `lastRow = fuel - 1` 尾部也已闭合，
其守卫和后继等式直接使用原 `fuelTerm`，没有把公式项替换为计算后的数值。
整张轨迹表仍因中间行图尚未全部闭合而保持未闭合状态。
轨迹表外层已严格分解为 `exp / fuel>0 / BoundedGraph / RowsAdjacent /
InitialRow / final tail` 六个分量；分解保留原 `fuelTerm`，端点已通过标准三项
公理画像与递归依赖审计。六分量的外层 hybrid certificate 组装也已闭合：
`exp`、`fuel>0` 与 final tail 直接构造，中间三项只接收已经检查过的证书，
不接收语义真值或存在包。

`InitialRow` 的解析见证供给已关闭关键选择缺口：任务坐标固定取第 0 行环境的
第 45--57 列，大小见证固定取第 58 列；新的 initial parse branch inversion
（初始解析分支反演）用初始状态排除 halted / finish / combine 三支，并从剩余
parse 支直接得到同一坐标上的 bounded head（有界任务头）及六个任务形状等式。
任务头、初始行公式证书和相邻行公式证书的正式模块现均已通过；其中初始行的
25 项直接安装向量、相邻行的 14 项直接安装向量以及全部边界证书均为显式构造，
公理画像仅为标准三项。`InitialRow` 的公式证书本体已经闭合；最终无参数入口仍须
由真实初始 `StepGraph` 调用上述分支反演，不能把显式解析参数留在总端点上。

`BoundedGraph` 的外层工程义务也已闭合：原始有界行被严格归一化为 429 个显式
有界见证；每个见证安装规范表值，429 个定宽表项由逐项证书合取，行数全称量词
由显式有限分支构造。当前端点只要求调用者为同一 429 坐标环境给出真实
`StepGraph` 证书，不接收语义真值或存在包。正式模块为：

```text
FoundationCompactPAExplicitHybridOfFnConjunction.lean
FoundationCompactNumericListedDirectVerifierStepWitnessTableBoundedGraphExplicitHybridCertificate.lean
```

其端点公理画像只有标准三项。combine（合并）环境的坐标数也已重新核对：三个
共享全局字段，加当前态 21 项、下一态 21 项、任务 14 项和规则见证 34 项，合计
恰为 93；不存在先前怀疑的 93/96 截断。

`StepGraph` 的顶层四路装配也已显式闭合：原公式逐字分解为 halted（停机）、
finish（完成）、parse（解析）、combine（合并）四支；四个构造器分别在 hybrid
certificate（混合证书）中直接选择对应分支，不从语义真值反推分支。正式模块为：

```text
FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate.lean
FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate.lean
```

公式对齐与四个选路端点均通过定向探针，公理画像只有标准三项。这里关闭的是
四路选择和装配外壳；halted / finish 两支还已严格拆成当前状态核心、下一状态
核心和分支行关系。各分支内部的状态核心、行关系及解析/合并子图仍须显式构造。

halted 行关系现也已显式闭合：同表 token 切片相等直接安装长度见证、两个终点
等式、两个终点界，并逐分支构造 offset / bitIndex 两层有界全称；状态标签等式和
429 坐标接线均不经过真值选择。状态核心中的任意长度 `NatListSlice` 也已从原先
仅支持零长度推广为公开显式构造。正式模块为：

```text
FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate.lean
FoundationCompactNumericListedDirectVerifierHaltedRowsExplicitHybridCertificate.lean
```

上述新端点均仅依赖标准三项。halted 整支尚未闭合，因为当前态和下一态的
`StateCoreGraph` 仍须按十二个直接分量构造。

`StateCoreGraph`（状态核心图）现已逐字拆成十二个分量，并完成当前态/下一态
24 坐标到 429 坐标步环境的精确接线。`TaskListRowsGraph`（任务列表行图）和
`ChildResultListRowsGraph`（子结果列表行图）的任意行有界见证、内部核心与终端
条件均已显式构造；十二分量总装配端点已通过标准三项公理画像。halted（停机）
与 finish（完成）行也已从各自原始语义图闭合，并与当前态、下一态证书合成为
两个完整终端分支。正式新增端点位于：

```text
FoundationCompactNumericListedDirectVerifierStateCoreGraphExplicitHybridCertificate.lean
FoundationCompactNumericListedDirectVerifierFinishRowsExplicitHybridCertificate.lean
FoundationCompactNumericListedDirectVerifierTerminalStepBranchGraphExplicitHybridCertificate.lean
```

为后续 proof-root / certificate-node 叶装配新增的共享原子中，
`NatListConsRows`（列表头插入行）与 `NatListAtRows`（列表索引取值行）现均已完成
原公式对齐和显式 hybrid certificate；单文件探针及禁用依赖扫描通过，公理画像
只有标准三项。这关闭的是高复用叶依赖，不代表 parse / combine 总分支已经闭合。
任意赋值项下的 `TokenSlicesEq`（定宽切片相等）以及直接复用它的
`NatListAppendSlices`（列表拼接切片）也已按原算术起点逐位闭合并通过同一审计；
`CertificateNodeSimpleEndpoint`（简单证书节点端点）现已成为首个按原 14 坐标
公式完全闭合的成功叶，`CertificateNodeOuterFailureEndpoint`（外层失败端点）的
空输入/非法标签两分支也已整体闭合。`NatListConsRows` 现另有保留任意表头
`ValuationTerm`（赋值项）语法的精确端点，修复一元数词 `1` 与短二进制数词 `1`
数值相同但公式项不同的接线风险；据此，`CertificateNodePAImmediateFailureEndpoint`
（PA 证书立即失败端点）的空尾表/非法大标签两分支也已按原 19 坐标公式整体闭合。
上述端点均通过单文件探针与禁用依赖扫描，公理画像只有标准三项；下一步按复用度
关闭其余成功/失败叶。`CertificateNodeSimpleEndpoint` 外面的六个 `<⁺ endpointBound`
（有界存在量）也已逐层显式安装，并与原九坐标 bounded graph（有界图）逐字对齐；
`CertificateNodeOuterFailureEndpoint` 外面的七个有界存在量也已按正确 de Bruijn
坐标 `#13 ... #7` 完成同样闭合。两个组合端点均只依赖标准三项，不把坐标界或
终端图包装成新假设；`CertificateNodePAImmediateFailureEndpoint` 外面的十四个
有界存在量现也已逐层安装，原六坐标 bounded graph、十九坐标终端图和全部坐标界
均通过证明探针、公理探针与禁用依赖扫描。公共量词移位规则另有已检查的复用支持端点。固定单记号
PA 公理叶也已按原 25 坐标完全闭合：四个列表行图、标签算术、两个列表头插入图
和列表拼接切片图均来自各自真实显式证书，不再缺少 `CompactFixedPAAxiomTag`
（固定 PA 公理标签）的证书构造；其外部十五个有界存在量也已与原十一坐标
bounded graph 逐层对齐并通过证明探针、公理探针与禁用依赖扫描。
`NatListAtRows`（列表索引取值行）现另有保留任意下标项语法的精确端点，消除了
普通数码 `0/1/2` 与短二进制数码数值相同但语法树不同的风险；据此，符号 PA
公理叶的原 27 坐标端点及外部十七个有界存在量均已通过证明、公理和禁用依赖
探针；公开入口只接收原 bounded graph，不暴露拆散的界参数。归纳 PA 公理叶仍待
闭合：其解析器状态核心的两次积切分、两个列表布局、单元/三格边界行、
两个精确 `Nat.size`（二进制长度）和两个面积界已从原 13 坐标图直接合成证书，
证明、公理及禁用依赖探针通过。该核心也已接入 `StateAtRows`（状态表指定行）：
行号严格界、左边界表项、保留原 `index + 1` 语法的右边界表项与状态核心已合并通过
同样探针。parser initial/final（解析器初态/终态）及其联合关系现也已显式闭合：
完成/运行状态、同表行、任务第 0 行、普通 `0/1` 公式语法、输出布局、`Nat.size`、
面积界和 `stateCount = fuel + 1` 均由原图直接构造证书；36 坐标联合公式逐项对齐，
公理画像仍只有标准三项。initial/final bounded（初终态有界）的 23 个真实见证、36
坐标代入、23 层共同上界移位、原始终端对齐和最终显式混合证书现已逐项通过单文件
证明探针；构造器不再把 `Prop`（命题）直接消去到数据类型，而是在命题内形成完整
见证后用 `Classical.choose`（经典选择）抽取，公理画像仍无 `sorryAx`。这些解析器
局部部件又闭合了 formula-transform state/row（公式变换状态/指定行）、parser Empty/Done
（解析器空分支/完成分支）、running/failed/completed（运行/失败/完成）及其完整 bounded status
validity（有界状态有效性），以及 `SyntaxTaskListSameRows`（语法任务列表同行关系）的
原公式显式证书；证明、公理和禁用依赖探针均通过，公理画像只有标准三项。这些解析器
局部证书只在相邻步骤完整结构证书的真实依赖要求下继续补齐，不作为独立旁路。
`SyntaxTaskListAtRows/ConsRows`（任务行读取／任务头插入）、保留调用方原生数词
`0/1/2` 的 `DropFixedNumeralRows`（固定行数删除）和
`SyntaxTaskListUnconsRowsWithSize`（拆出任务头及精确大小），以及 parser
Invalid/Repeat（解析器非法类型／重复任务分支）的原始 25 坐标公式，现均已逐字对齐并构造显式
hybrid certificate（混合证书）；单文件证明、公理和禁用依赖探针通过，公开端点只依赖
`propext` / `Classical.choice` / `Quot.sound`。这里修复了原生数词与短二进制数词
数值相同但公式树不同的风险。`UnconsRowsWithSize` 现进一步保留三个任务头项的原始
语法；TermContinue/TermFunction（项解析继续／函数分支）、函数码四对有限域的正反
证书以及完整 Term 原始 26 坐标公式也已由真实行关系闭合并通过同样探针。关系码
两对有限域的正反证书、FormulaBinary/FormulaQuantifier（二元公式／量词公式）和
完整 Formula 原始 26 坐标公式现也已闭合；所有语义分支均从同一行关系产生。这里仍
只关闭局部结构证书，不把 `A04.18` 或 Pudlak 下界标绿。六个 parser 分支现又已合并
为原始 26 坐标 `SyntaxStep`（语法步骤）证书；`StateAtRows`（状态表指定行）已扩展为
保留任意算术行号项的精确接口，据此原始 33 坐标 `SyntaxAdjacentStep`（相邻语法步骤）
保持原生 `index + 1` 并整体闭合。formula-transform state row（公式变换状态行）也已
通过同样的任意行号项接口探针。FormulaOutputRows / TermOutputRows（公式／项输出行）
现均已从原语义图逐分支构造显式证书；后者保留原生算术项、失败蕴含和 residual
（残余）有界存在见证，并给出结构性载荷界。四个 quiet parser branch（静止解析分支）、
同行输出和两类输出更新现又已装配为原始 38 坐标 FormulaTransformStepRows（公式变换
步骤行）证书，其公式对齐、图到证书和结构载荷界均通过探针。上述端点的公理画像均只有
标准三项。当前态、原生 `index + 1` 下一态和步骤行现又已装配为原始 47 坐标
FormulaTransformAdjacentStep（公式变换相邻步骤）证书，并通过同样探针。该证书所需
37 层有界见证中，最内层 9 个步骤见证现已连同两份 bounded status validity（有界状态
有效性）证书闭合；外层 14 个下一态见证也已按原量词次序接入并通过公式、证明、公理和
禁用依赖探针；最外层 14 个当前态见证现也已闭合。至此 37 个相邻行见证全部通过同样
探针，公理画像仍只有标准三项。下一义务是按 `rowCount`（行数）构造行全称量词证书，
其分支所需的 at-valuation index（赋值下索引）相邻行端点现已闭合：自由索引项不被
替换成数码，下一索引保留原生 `indexTerm + 1`，公理画像仍只有标准三项。尚需把
最内层 9 个有界步骤见证提升到同一自由索引项的端点也已通过探针，包含两份闭式状态
证书在任意赋值下的严格重建；外层 14 个下一态和 14 个当前态见证现也已逐层提升并
通过探针。至此全部 37 个见证在同一自由索引项下闭合。`rowCount` 范围的全称分支及
独立指数约束现也已接回原始 12 坐标公式并通过探针；分支数严格为 `rowCount`，不把
`valueBound = 2^tableWidth` 当作枚举次数。初末状态的七个真实合取、31 层有界见证、
PA 编译和结构资源端点也已通过同一探针；它们与相邻行证书现已装配成原始 19 坐标
`CompactFormulaTransformTraceBoundedGraph`（有界公式变换轨迹）证书。完整资源现又已精确
分解为状态计数、初末状态、相邻行三个真实子证书资源与六个固定外层连接器成本；分解
定向探针及公理探针通过，没有把行全称或见证前缀藏进新包络。六个外层成本现又严格
受五条实际公式编码之和给出的显式包络控制；该端点未把此包络冒充最终公共输入多项式。
状态计数叶已改由二进制加一证明器直接闭合，载荷受 `Nat.size fuel` 的固定多项式控制；
三个封闭分量现以空上下文直接组装，只需两次合取。总剩余资源因此精确缩为初末状态与
相邻行两个子资源以及显式公式编码包络。短二进制数词到迭代后继数词的转换资源现已有
关于公开数值界的固定多项式；相邻行全称编译器也已改用该闭合界并通过单文件探针，
不再依赖通用 shifted-bound resource（移位上界资源）。37 个相邻行见证现已按
`9 step + 14 next + 14 current` 直接复用内层 PA 证明，并已把每个行号的真实
`CertifiedPAContextProof` 直接汇总为有限全称分支；全称证明与显式资源端点探针通过，
公理画像仍只有标准三项。最内层 step 不再用“终端证明的实际载荷”给自己计界：
现已显式编译 row（行关系）、current/next status（当前／下一状态）三份真实
上下文证明，再仅加上四次 weakening（上下文弱化）与两次 conjunction（合取引入）
的完整组装成本。改写后的 `step -> next -> current -> rows` 已逐层重新通过探针，
新终端及上层端点的公理画像只有标准三项。内部 row 子证书的透明结构资源仍待用坐标
位宽界压成公开多项式。两份 bounded status 的四个存在见证已改用固定 4 元直接编译器，
不再把整个状态证明当作混合资源；该路线及 `step -> next -> current -> rows` 传递端点
已重新通过。四层见证前缀现又完成逐层 syntax resource（语法资源）多项式界、固定四层
精确展开式和四项单调合并；探针公理画像只有标准三项。任意元数依赖递归未进入正式路线。

37 层相邻行见证现进一步切换到 intrinsic uniform compiler（内生统一编译器）：
每层在构造证明的同时支付只依赖公共界和当前公式的统一成本，不再事后比较两棵依赖型
递归，也不把 9、14、14 元具体见证向量写入公开资源。公式码总和直接控制上下文基数，
故活跃路线也已删除 `card ≤ 4` 前提。`step -> next -> current -> rows` 全链重新通过定向
探针，公理画像仍只有 `propext`、`Classical.choice`、`Quot.sound`。这一步关闭见证层本身；
尚未关闭的仍是底部 row/status terminal（行关系／状态终端）资源的公共多项式界及其全行求和。

状态侧的 `fixed-width entry`（定宽条目）黑盒现已逐层打开：项归一化与传输、
四个真假位文字、所有 `bitIndex < width` 位叶的有限求和、分支递归、移位上界项、
bounded universal（有界全称）以及见证保护／二进制长度／大小保护／存在量词与合取
连接器，现均已接入同一透明、输入可计算的结构资源表达式。完整定宽条目证书的
单文件探针通过，公理画像只有标准三项；不再保留 caller-supplied leaf/resource
（调用者提供的叶／资源）参数。

开放行索引不再被误当作闭项：外层变量 `0` 经 `shift`（移位）后成为 `1`，内层位变量
占据 `0`；项编译器和位文字编译器现按自由变量并集基数不超过 4 工作。小上下文有限全称
的基步、递推步和线性汇总，以及非空外层上下文中的移位宽度等式均已公开化。原先按位求和
的 proof-dependent structural envelope（依赖证明对象的结构包络）已替换为每位公开多项式
的有限和；开放索引定宽入口及其上层布局、单位边界和完成状态端点探针通过，公理画像只有
标准三项。

定宽路线的位坐标压缩现已闭合。valuation context（赋值上下文）公式码、term
normalization（项归一化）递归、term transport（项传输）递归和二元函数同余均由同一个
自由变量数值界推出；左索引、左值、右索引、右值四个项等式编译器因此统一到与
`bitIndex` 无关的资源。端点
`fixedWidthBitLeafAggregatePayloadBound_le_uniform_of_openIndex` 已把逐位有限和严格压成
`width * uniformBound`（宽度乘统一上界），开放索引条目主资源也已切换到该坐标；各端点
公理画像只有标准三项。这个输入可计算表达式仍须与矩阵其余坐标一起证明受同一个全局固定
次数多项式控制，不能单独冒充 `A04.18`。running/failed/completed-prefix（运行／失败／完成前缀）现已分别接入
透明公开结构资源；failed/completed-prefix 的中间游标固定为由原图推出的 `start + 1`，
不再由 `Classical.choose` 选择。structured-list layout（结构化列表布局）与
unit-boundary rows（单位边界行）的分支、有限全称、语义图数据出口和透明结构资源现已
全部闭合；completed 分支的前缀、布局、单位边界、`Nat-size`（自然数位长）和面积不等式
五叶已在同一证书中组装。running/failed/completed 三分支随后已统一为同一状态终端，
四个有界输出见证和闭合状态公式也已通过显式公式等式接回。核心公开端点为
`compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent`；
单文件证明、公理和禁用依赖探针通过，公理画像只有标准三项。
直接有限全称分支的递归和全部连接器成本现也已受关于 `rowCount`、body code 和统一叶界
的显式固定多项式控制并通过探针。相邻行侧现在精确只剩证明具体终端载荷之和
`DirectLeafPayloadResourceSum` 受公开输入规模的固定多项式控制；初末状态侧仍需关闭其
其余非零终态输出及模块资源的公共界。已闭合的定宽统一坐标与其余坐标资源仍须统一
压成闭式固定多项式，
随后才能接回完整矩阵和 20 层见证前缀；`A04.18` 仍保持黄色。
其中 `FormulaOutputRows` 的七个真实分支，以及 `NatListAtRows` 精确索引值、追加一项、
追加两项和追加切片，现均由原语义图得到透明公开资源界。`TermOutputRows` 的十四个真实
分支也已改为显式 checked branch data（已检查分支数据）：失败分支、残余见证和子行图均
按实际证书收费；分支汇总与图端点通过探针，公理画像只有标准三项，且没有调用方资源参数。
`FormulaTransformStep` 的六个真实分支及 `AdjacentStep`（相邻步）的当前状态、下一状态、
步骤三段直接编译也已接入透明公开包络；九见证终端在单一行变量路线自动使用该包络，
不再把整张行证书的结构大小当作黑盒。下一步只汇总
`DirectLeafPayloadResourceSum`（直接叶载荷资源和）的固定多项式界。
2026-07-20 的独立
数学有效性审计确认：这些端点只是必要的定量检查器基础；即使 `A04.18` 闭合，也不自动
建立 Pudlák 条件 (0)--(3)、同载荷下界或 Sondow 到同一有限一致性公式族的缺失定理 U。

当前严格剩余三项，顺序不可交换：

1. 为完整 `compactNumericListedDirectPredicateMatrixDef` 建立 quantifier profile
   （量词画像）。外层、输入流、公式流和输入分割的全部动态全称界已经逐项核对：
   它们受 `bound` 与 `Nat.size formulaCode` 的固定二次多项式控制；
   `traceValueBound = 2^traceWidth` 只作存在见证和值域界，不进入指数次数枚举。
   十类证明节点已经沿证明树结构归纳到每个中间偏移，并与 finish / halted 合并为完整
   fuel 轨迹；实际选择器、受控表和主 `BoundedProofWitness` 对每一行都保留
   `stateWidth`、`stateTokenCount` 数值界与 429 坐标界。全行量词画像已经通过，公理画像
   只有标准三项。当前/下一状态的证明流、证书流、任务栈和值栈八个实际计数也已从同一
   `StepGraph` 反演并接入量词画像。parse（解析）分支的四个循环控制量
   已传到实际轨迹表、有界见证和量词画像，定向探针仅有标准三项公理。
   combine（合并）分支的四个任务计数、活动规则列表计数和二次长度变换
   轨迹已建立分支敏感公开界，并与同一 429 列公式见证绑定；未使用坐标
   不被误当作数值循环界。该界现已贯通已接受树行、终端行、轨迹选择器、
   实际 429 列轨迹表、`BoundedProofWitness`（有界证明见证）和量词画像；
   全部定向探针仅依赖标准逻辑公理。每个公式移位行内部的局部变换轨迹及其
   完整结构证书现已接入。原 29 个有界见证可重建为同一 40 坐标行环境，
   源/候选长度、内层状态数、最终及相邻状态的 parser/output（解析器/输出）
   列表计数均已有固定多项式控制；当前尚需证明新得到的具体结构资源受同一个
   固定多项式控制，随后汇总整张矩阵的总结构资源界。`NatListSameRows`
   （自然数列表同行关系）的四个行值见证现已由固定四元展开关闭：实际
   `sourceLeft/sourceRight/targetLeft/targetRight` 只通过各自
   `≤ tokenCount` 使用，不再进入见证前缀资源，也不再作
   `(tokenCount + 1)^4` 枚举。为避免依赖递归展开造成内存爆炸，任意元通用端点
   已替换为与规范完全一致的四层显式端点；两级探针均只依赖标准三项。
   四个 fixed-width entry（定宽表项）和一个 atomic row equality
   （原子行等式）的五叶终端合取也已压到固定多项式资源；随后又用
   `index < sourceCount ≤ numericBound` 消去行下标，得到不含行数据和行下标的
   uniform row resource（统一行资源），全部行的叶资源和严格界为
   `sourceCount × uniformRowResource`。外层公式的自由变量集合已严格证明为空；
   分支递归已进一步压成
   `(sourceCount + 1) × (行资源和 + 3 × 局部装配资源)`，并接回不含具体
   `rows` 数据的全称编译资源。五叶终端公式的代码长度现由 `bitBound`
   的显式多项式控制；四层有界存在主体又按 `04 → 03 → 02 → 01`
   分层编译并以 `rfl` 对齐原主体，最终 `bodyCode` 只依赖
   `numericBound/bitBound`。finite exhaustion（有限穷举）、weakening
   （弱化）、disjunction elimination（析取消去）和 cut（切规则）现已逐项收费；
   实际 shifted-bound equality compiler（移位边界等式编译器）及 closed short
   universal shell（封闭短全称外壳）也已接入。最外层计数等式与行全称证书最终由
   固定公式代码界合取，row-data（行数据）和 graph（语义图）公开端点均只依赖
   `numericBound/bitBound`，且公理画像只有标准三项。`NatListSameRows` 子义务至此
   闭合；当前局部义务转为把该端点接回 parser/output（解析器/输出）、
   verifier step（验证器步骤）及 complete direct matrix（完整直接矩阵）的总资源汇总。
   汇总链中的 `NatListAppendSourcePrefix`（自然数列表追加源前缀）现已整体闭合。
   单个 `TokenSlice`（令牌切片）的位原子、真假分支、`bitIndex` 和 `offset`
   双层有限全称、五个闭算术叶、五层合取及存在见证外壳均已由
   `numericBound/termCode/bitBound` 的显式固定多项式控制；复合起点
   `start + 1` 和 `targetStart + 1 + leftCount` 始终保留为同一闭项，没有按
   数值相等偷换成短数词。公开端点
   `compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed`
   只依赖标准三项公理。

   两个实际切片见证随后直接从同一个 `hgraph` 取出，并由
   `appendSourcePrefixTokenSlicesResource_le_fixed` 同时固定；三个算术叶由
   `appendSourcePrefixArithmeticLeavesResource_le_fixed` 固定。原 13 元
   `Σ₀` 公式通过一次闭短数词代入得到完整公式代码界和闭公式性，再由通用五叶
   合取定理支付四次真实装配成本。最终公开端点
   `compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_fullyFixed`
   直接约束原
   `compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope`，静态审计无
   `sorry/admit/axiom`、`tail_gap`、`upper_provider`、`proof_length` 或隐藏
   valuation 参数，公理画像只有 `propext`、`Classical.choice`、`Quot.sound`。
   `NatListAtRows` 的真实两游标路线现也已推进到固定子资源层：精确二元有界见证
   展开已通过；两个 fixed-width boundary entry（定宽边界条目）和一个 token
   cell（令牌单元）的实际证书均已取得固定资源界，并已送入同一个二元见证编译器。
   同一具体主体的 `bodyCode` 已由七坐标原公式的固定代入代码界关闭；终端公式闭合，
   故 valuation context（赋值上下文）代码和为零。进一步把真实 `left/right`
   安装进二元终端后的完整公式代码，也已由通用二元代入定理压到只依赖
   `bitBound` 的固定多项式；这些端点的公理画像仍只有标准三项，且没有
   finite-sum（有限求和）包装。
   两个 open-index entry scale（开放索引条目尺度）现已压到已有
   uniform ceiling（统一上限）；终端两层合取、精确二元有界见证、外层
   `index < count` 守卫和最终合取装配均已支付固定资源成本。公开端点
   `compactAdditiveNatListAtRowsAtShortIndexExplicitFormulaCertificate_structuralPayloadBound_le_fullyUniform`
   的上界只依赖 `index/numericBound/bitBound`，不含 `left/right`、
   finite-sum（有限求和）、`bodyCode`、赋值上下文参数或外部证明长度。
   该端点及全部新前置的公理画像只有
   `propext`、`Classical.choice`、`Quot.sound`。`NatListAtRows` 子义务至此闭合；
   它现已接入 `NatListAppendMappedSourcePrefix`（追加映射源前缀）的真实八叶
   checked certificate（已检查证书）。五个算术叶、两个由同一图见证提取的真实
   token slice（令牌切片）和一个真实 `NatListAtRows` 行查询叶，经通用八叶右结合
   合取定理支付全部装配成本。公开端点
   `compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed`
   不经过旧 graph envelope（图资源包络），上界只依赖
   `leftCount/numericBound/bitBound`，不含 `left/right`、有限求和、赋值上下文、
   外部证明长度或调用者资源参数；公理画像仍只有标准三项。当前局部义务转为在
   `FormulaTransformFormulaOutputRows`（公式变换输出行）中用该端点替换旧
   public-finite envelope（公开有限包络），再回接 parser/output（解析器/输出）
   和 verifier step（验证器步骤）总资源汇总。
   mapped branch（映射分支）的真实 `FromData` 证书现已完成这次替换，端点
   `compactFormulaTransformFormulaOutputRowsMappedBranchCertificate_structuralPayloadBound_le_rowsFullyFixed`
   中的 rows resource（行资源）只依赖
   `current.outputCount/numericBound/bitBound`。
   `NegationFormulaTag` 的七个真实原子叶现已统一压到只依赖 `bitBound` 的
   term-code / payload（项码／载荷）多项式；`8 <= tag` 大标签支的
   `8 = tag` / `8 < tag` 两个原子及真实析取装配也已闭合。相应端点均通过
   单文件探针，公理画像只有标准三项。偶数、奇数分支在见证代入后的三叶公式
   代码界、闭合性及两层真实合取也已分别通过；开放见证体、见证项、存在公式、
   两支存在量词和偶／奇／大标签三路外壳现亦全部闭合。最终 `OfGraph` 端点
   `compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed`
   只依赖 `bitBound`，不经过
   `compactNegationFormulaTagPublicFinitePayloadEnvelope` 或 graph payload
   envelope（图载荷包络），公理画像只有标准三项。该端点已回接 mapped branch；
   后者现在同时使用固定 tag/rows resource（标签／行资源）。原始 29 坐标
   `FormulaOutputRows` 闭公式现也已由显式短二进制数词向量重建；在同一
   29 坐标环境位界下，完整公式代码受
   `compactFormulaTransformFormulaOutputRowsFullFormulaCodePolynomial`
   控制且自由变量集合为空。两个端点的单文件探针通过，公理画像只有标准三项。
   count/positive（计数／正性）两个实际证书资源现已进一步固定：计数等式
   直接使用三个闭短数词和一个加法项；正性证书显式支付等号、小于号两个
   正关系编译器、两次弱化和一次析取引入。其固定界只依赖 `bitBound`，
   四个端点的单文件探针与公理画像均通过。`otherMode` 内五个模式否定等式
   也已完全固定。基础端点逐项支付两次项值等式、两次弱化、两次等式对称、
   反向关系传输、负闭原子源、源弱化及 modus tollens（反证式推理），得到
   只依赖 `numericBound/termCodeBound` 的
   `compileNegativeRelationFixedPayloadPolynomial`；没有把具体负关系资源留在
   结论中。上层再把模式 0/1/2/4/5 的五个真实否定证书和 tail 组成六叶
   右结合合取，由统一语法预算支付五层连接词成本。基础、原子和六叶端点
   均通过单文件探针，公理画像只有标准三项。mapped（映射）分支现也已完全
   固定：29 坐标完整公式预算统一支付 tag/rows tail（标签／输出行尾部）和
   最外层五级混合合取／析取成本，最终资源只依赖
   `current.outputCount/numericBound/bitBound`。该端点的单文件探针通过，
   源码无 `sorry/admit/axiom/sorryAx`，公理画像只有标准三项。
   rawMode（原样模式）四选一证书也已直接固定：模式 0/1/2/5 的闭等式叶
   分别经过一至三层真实析取选择，统一资源只依赖 `bitBound`；新路线不再
   展开旧的 proof-dependent（依赖证明数据的）`rawMode*PayloadEnvelope`。
   四条直接证书端点和叶／语法分层探针均通过，公理画像只有标准三项。
   现已进一步把四种模式分别与 AppendSourcePrefix（原样前缀追加）真实证书
   及完整外层公式装配，原 `FromData.rawZero/rawOne/rawTwo/rawFive` 四个分支
   均得到只依赖 `numericBound/bitBound` 的固定资源界。公共装配和四个原分支
   桥的探针通过，公理画像只有标准三项；这不是旁路证书。
   zero/sameFour 两个剩余分支也已分别用真实 SameRows（同行关系）证书闭合；
   七个 `CheckedBranchData` 构造子最终统一到
   `outputRowsAllBranchesFullyFixedPayloadPolynomial`。统一端点的探针通过，
   公理画像只有标准三项。因此 FormulaOutputRows（公式输出行）节点已完整
   闭合。当前局部义务转到 StepRows formula 分支的另一半：
   UnifiedParserSyntaxFormula（统一解析器公式证书）；其
   tag equality/disequality（标签等式／不等式）及四组二选一标签证书已经
   从真实原子证书得到只依赖统一 `bitBound` 的固定界，探针和公理画像均通过；
   `tokensCount ≤ 2` 与 `3 ≤ tokensCount` 两个顺序比较也已直接展开
   equality/strict-less（等号／严格小于）两条真实证书路径并得到固定界。
   上述原子层没有调用旧的 branch-data envelope（分支数据包络），全部探针
   只有标准三项。failure/continue（失败／继续）共享的
   SyntaxTaskListSameRows（语法任务栈同行）计数等式也已得到固定端点；当前须
   为原公式中的 `sourceLeft + 1/+2` 和 `targetLeft + 1/+2` 闭复合项扩展
   AtomicRowEquality（原子行相等）固定界，禁止把它们偷换成语法不同的短数词。
   这些复合项的闭性、精确求值和统一编码界，以及任务行八个分量均受同一
   `numericBound` 控制的语义引理，现已通过探针；下一义务精确缩小为推广
   atomic-row bit body/universal shell（原子行位体／全称壳）的闭项参数端点。
   现已完成任意受统一项编码界控制的 bit body 公式编码、外层全称公式闭性，
   以及在逐位分支界给定后全称壳自身的固定资源端点；界等式与全称装配均已
   内部支付。任意闭复合项的左右位索引和值项现已得到统一编码界、闭性、
   精确求值和位位置界；四种真假 bit literal（位文字）的真实编译资源也已
   固定。七个分支公式（四个文字、两个方向析取和最终合取）的统一公式编码界
   与自由变量 `{0}` 界均已通过探针，公理画像只有标准三项。剩余义务精确为
   汇总这七个公式的 valuation context（赋值上下文）、weakening（弱化）、
   disjunction（析取）与 conjunction（合取）装配成本，从而推广
   `atomicRowEqBranchesTransparentStructuralEnvelope`（原子行逐位真假分支包络）
   到同一闭复合项参数；随后即可无参数调用已闭合的全称壳。
   该步现已完成：逐位公开包络、有限求和、透明分支递归、有限穷尽上下文装配
   和全称壳已依次闭合，最终 universal（全称）端点不暴露 branch bound
   （分支界）参数。其上层 `CompactAdditiveAtomicRowEqAtValuation` 的四个
   算术关系叶与一个 universal 叶也已通过五叶闭合取通用装配器得到任意闭项
   固定界；该端点的探针和公理画像只有标准三项。三个实际 AtomicRow
   （原子行）公式的统一闭合性、总公式码界和三叶闭合取装配现也已完成，
   因而完整 `CompactAdditiveSyntaxTaskRowEq`（语法任务行相等）公开包络
   已得到无调用方资源参数的固定界，单文件探针通过，公理画像仍只有标准三项。
   当前义务上移到完整 `CompactAdditiveSyntaxTaskListSameRows`
   （语法任务列表同行）：把四个固定宽度条目、已闭合的 TaskRowEq 行证书、
   四重有界存在见证、有限行分支、上下文穷尽和最外层全称壳依次接到同一
   `numericBound/bitBound`（数值界／位宽界），最终给原始 Graph 证书一个
   无 row data（行数据）和无 branch bound（分支界）参数的固定公共端点。
   其中 witness compiler（见证编译器）实际使用的四变量 `BranchTerminal`
   （分支终端）现已与五变量 `Terminal` 严格区分：共享行索引保持为自由变量
   `&0`，四个条目值为 `#3..#0`。原始分支终端的五叶源公式已得到只依赖
   `bitBound` 的统一编码界，并以显式公式对齐定理接回原定义；探针和公理画像
   只有标准三项。四个 fixed-width entry（固定宽度条目）固定资源与
   TaskRowEq 行资源现已由五叶装配器合成完整 structural payload（结构载荷）；
   端点
   `compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed`
   的探针通过，公理画像只有标准三项。当前义务是把该固定终端接入原始
   `buildExplicitBoundedWitnessHybridCertificate`（显式有界见证编译器），
   关闭四重存在见证的 branch payload（分支载荷），不保留行数据或叶资源参数。
   该义务现已闭合：四重见证分支及全部 `sourceCount` 行的资源和都受同一
   `numericBound/bitBound` 固定界。五变量 source terminal（源终端）与释放行
   变量后的四变量 branch terminal（分支终端）也已严格分开；源终端码界、
   四层存在包装后的 universal body（全称体）码界、body 闭性和外层全称闭性
   均已通过探针，公理画像只有标准三项。为避免依赖类型归约爆炸，四层公式
   按 `05→04→03→02→01` 分层并证明两套 `closedShift` 完全对齐。
   有限行 branches（分支递归）现已进一步关闭：真实有限穷举、边界特化、
   下界矛盾、weakening（弱化）、disjunction elimination（析取消去）与
   cut（切规则）的完整上下文成本已压到同一固定多项式。随后实际
   shifted-bound equality compiler（移位边界等式编译器）和 closed short
   bounded universal shell（闭合短有界全称壳）也已接入。最外层
   `targetCount = sourceCount` 计数等式与行全称证书最终由固定公式码预算合取。
   公开 row-data（行数据）端点和原始 Graph（语义图）端点均只依赖
   `numericBound/bitBound`，不暴露 row data resource（行数据资源）、
   branch bound（分支界）或调用方公式码参数；全部定向探针的公理画像只有
   `propext`、`Classical.choice`、`Quot.sound`。因此完整
   `CompactAdditiveSyntaxTaskListSameRows` 子义务已经闭合。
   为此所需的开放索引五叶装配器也已单独闭合：
   `transparentHybridFiveConjunctionPayloadEnvelope_le_singletonGeneral`
   从总公式自由变量 `{0}` 界、`valuation 0 <= numericBound` 和统一公式码界，
   自动推出四层尾公式的上下文界并支付全部合取装配成本；它不暴露调用方
   context resource（上下文资源），探针和公理画像只有标准三项。
   当前局部义务转为把该 Graph 固定端点接入
   UnifiedParserSyntaxFormula（统一解析器语法公式）的 failure/continue
   （失败／继续）两个真实分支；随后关闭 binary/quantifier/selected
   （双目／量词／选中）其余分支，并汇总 parser/output（解析器／输出）与
   verifier step（验证器步骤）的总结构资源。
   failure 原 21 坐标证书现已闭合：failed-status（失败状态）、
   NatListSameRows 和 SyntaxTaskListSameRows 三张真实证书分别使用固定端点，
   再由原右结合三叶公式支付两次合取成本。失败语义图本身给出
   `innerStart = next.tasksFinish + 1` 与 `innerStart ≤ tokenCount`，故内部位置界
   由 `tokenCount ≤ numericBound` 推出，没有作为调用者参数。总公式码先与原
   21 坐标定义逐字对齐，再由 5／7／7 元三个闭叶码界合成；完整端点公理画像
   只有标准三项。continue 当前唯一未闭合叶是
   `NatListDropFixedNumeralRows`（固定数词自然数列表丢弃关系）；必须先把其
   真实行证书、有限分支、上下文穷举和全称壳压到统一固定界，禁止继续使用
   仍依赖具体坐标的旧 public-finite envelope（公开有限包络）。
   其中 continue 实际使用的 `consumed = 1` 已完成根部单行闭合：原生四个
   索引项 `1+i`、`1+i+1`、`i`、`i+1` 的自由变量和项码界已逐字证明；
   `sourceCount = 1 + targetCount` 与 `i < targetCount` 又在图内推出四个
   数值界和位长界，没有新增 caller index bound（调用者索引界）。任意开放
   索引项的 fixed-width entry（定宽条目）现有统一“资源界＋公式码界”端点；
   四个真实条目与 AtomicRowEq（原子行相等）第五叶已由 singleton
   five-conjunction（单自由变量五合取）组合器闭合。最终单行终端端点
   `compactAdditiveNatListDropOneRowsTerminalStructuralPayloadEnvelope_le_fullyFixed`
   的公理画像只有标准三项。该终端现已接入原始四重有界存在见证编译器；
   五变量 source terminal（源终端）代码界、四层 `05→04→03→02→01`
   witness body（见证体）代码界、body 闭性与外层全称公式闭性均已逐层证明。
   每个真实分支的固定载荷界又已对 `targetCount` 全部行求和，并接入透明有限
   分支递归；图内等式 `sourceCount = 1 + targetCount` 自行给出分支数界。
   上述新增端点的公理画像均只有标准三项。透明分支界现又已接入
   contextual finite exhaustion（带上下文有限穷举）：有限穷举、边界特化、
   下界矛盾、弱化、析取消去和 cut 的实际成本均由固定多项式支付。真实
   shifted-bound equality（移位边界等式）编译器和 closed short bounded
   universal shell（闭合短有界全称壳）随后也已闭合，公理画像仍只有标准
   三项。最外层两个闭算术叶 `1 ≤ sourceCount`、
   `sourceCount = 1 + targetCount` 的原始证书资源和公式码现也已由
   `bitBound` 固定；前者包含真实的等号／严格小于分支、弱化和析取成本，
   后者包含真实的加法项与等式编译成本。两次右结合合取随后按原公式
   `bound ∧ (equality ∧ universal)` 完成装配。闭公式代码、闭性、row-data
   载荷和原始 Graph 载荷四个总端点的公理画像均只有标准三项。因此
   `consumed = 1` 的完整 `NatListDropFixedNumeralRows` 子义务已经闭合。
   该 Graph 固定端点现已接入 parser continue（三叶继续分支）：真实
   running status（运行状态）、drop-one token list（丢弃一项的令牌列表）
   和 unchanged task list（不变任务列表）分别取得固定资源界，随后按原
   右结合三叶公式支付两次合取成本。总端点不再依赖旧的具体坐标
   public-finite envelope（公开有限包络），公理画像只有标准三项。
   Formula 的 logical-selected（逻辑标签选中）现也已闭合：标签
   `{2,3}` 的真实任选其一证书与上述 continue 证书共享同一
   `numericBound/bitBound`，标签公式和 continue 公式的代码界、闭性及
   合取装配成本均已显式支付；端点
   `syntaxFormulaLogicalSelectedCertificate_structuralPayloadBound_le_fullyFixed`
   的公理画像只有标准三项。invalid-selected（非法标签选中）也已闭合：
   八个真实标签不等式证书与真实 failure 证书组成原始右结合九叶公式；
   否定公式代码、全部闭性、九叶总码及八层合取装配均由固定多项式支付。
   端点
   `syntaxFormulaInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed`
   同样只有标准三项。quantifier（量词）分支现已整体闭合：
   `SyntaxTaskListConsRows`（语法任务列表头插入关系）的计数叶、头任务两层
   见证、尾部四层移位行、全部有限分支、上下文穷举、移位等式和 bounded
   universal shell（有界全称壳）均由固定资源端点给出；随后真实 running
   status（运行状态）、drop-one token list（丢弃一项的令牌列表）和
   quantifier task insertion（量词任务插入）按原右结合三叶公式完成装配。
   总端点
   `compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed`
   已通过单文件证明探针，公理画像只有 `propext`、`Classical.choice`、
   `Quot.sound`，没有调用者公式资源、旧 public-finite envelope（公开有限包络）
   或项目级公设；它与真实 `{6,7}` 标签的合取端点
   `syntaxFormulaQuantifierSelectedCertificate_structuralPayloadBound_le_fullyFixed`
   也已通过同一探针。当前精确义务只剩 Formula 的 relation / binary
   （关系／双目）分支，再把全部 tag path（标签路径）汇总到
   parser/output（解析器／输出）与 verifier step（验证器步骤）的总结构资源。
   binary 的三格任务布局现已关闭真实 native `1/0`、short-binary binder、
   三个 token-cell 和两层内部有界见证。该布局与两个真实 fixed-width
   boundary entries（定宽边界表项）组成的 task AtRows 三叶终端现也已闭合；
   对 parser 选中的下标 `0/1`，九项原公式代入、开放终端代码界和零自由变量
   上下文均已由真实公式结构推出。命名三叶终端、安装证书及通用二元见证安装
   核心现已拆分编译；两层 bounded witnesses（有界见证）已在真实 `left/right`
   游标上闭合。固定总界取下标 `0/1` 两个真实包络的最大值，而不是错误地把
   下标 `0` 的资源复用于下标 `1`。上述端点的单文件探针和公理探针均通过，
   只有标准三项。index guard（下标守卫）也已从真实 `index < count` 图事实
   闭合并通过标准三项公理探针。守卫与已安装见证现已按原 AtRows 公式完成
   合取：模块化证书先在命名公式上装配，再用已证明的公式对齐等式搬运到
   原项目公式；固定载荷界的公理画像只有标准三项。旧的一体化证书实现无须
   与新证书对象做昂贵的定义归约比较。两条下标 `0/1` 的完整 task AtRows
   因而已经闭合；当前义务上移到 binary parser 的 task DropTwo（任务栈丢弃
   两行）固定端点，随后装配 running、token DropOne、task DropTwo 与两条
   AtRows 五叶证书。DropTwo 的原始开放五叶终端现已建立模块化显式公式：
   固定偏移 `2 + index`、`(2 + index) + 1` 的代码成本为常数，四个定宽表项
   和任务行等式的总公式代码由 `bitBound` 固定；该公式与原终端逐字相等，
   自由变量严格包含于开放行下标 `{0}`。三个端点的公理画像均只有标准三项。
   五叶真实证书的结构载荷也已闭合：四个表项分别在真实坐标
   `2+index`、`3+index`、`index`、`index+1` 上调用定宽编译器，第五叶调用
   已闭合的三格任务行等式；singleton 五叶装配器显式支付开放下标上下文和
   四次合取成本。总端点不使用有限枚举包络或调用者资源参数，公理画像仍只有
   标准三项。四层有界见证现也已由真实四元值
   `[targetRight,targetLeft,sourceRight,sourceLeft]` 完成安装，且每个值的
   `≤ tokenCount` 事实直接来自 row data；终端代码、上下文与载荷均使用上述
   固定端点。全部 `targetCount` 个分支的资源和随后由
   `2 + targetCount ≤ numericBound` 压到
   `numericBound × 单分支资源`。两个新端点的公理画像仍只有标准三项。
   contextual branches（带上下文分支装配）现已显式支付有限穷举、弱化、
   析取消去与 cut（切规则）的结构成本；外层有限全称又把已闭合分支、
   shifted-bound equality（移位界等式）和 closed short universal shell
   （闭短数词全称外壳）汇合。代码长度、自由变量、分支、上下文分支和
   全称资源五层端点均通过单文件探针，公理画像只有标准三项。
   `2 ≤ sourceCount` 与 `sourceCount = 2 + targetCount` 两个闭计数叶
   现也已从真实等号／严格小于、加法和等式编译器闭合；它们与全称叶按原
   `bound ∧ (equality ∧ universal)` 公式完成右结合。闭公式代码、闭性、
   row-data 载荷和直接从真实图提取行数据的 Graph payload（图结构载荷）
   四个总端点均通过探针，公理画像只有标准三项。因此完整 Task DropTwo
   子义务已闭合。binary parser 的 running、token DropOne、task DropTwo
   与两条 AtRows 现已组成新的五叶模块证书；它通过原公式对齐等式证明同一
   22 坐标闭公式，而不要求新旧 AtRows 证明对象定义相等。五个子载荷、
   五叶闭性、总代码长度和四次合取成本均由共享
   `numericBound/bitBound` 固定，`tailCount` 界由真实 DropTwo 图等式
   推出；总端点通过探针且公理画像只有标准三项。真实 `{4,5}` 标签任选
   其一证书现又与该模块化 binary 证书完成 selected 合取；标签公式、
   binary 公式、闭性、代码和合取装配成本均已固定，端点公理画像仍只有
   标准三项。当前局部义务前移到 relation-short / relation-valid /
   relation-invalid（关系短输入／有效／非法）三子路；关闭后再汇总全部
   parser tag path（解析器标签路径）到 parser/output 与 verifier step
   总结构资源。三子路共享的 ArithmeticRelCode valid/invalid（算术关系码
   有效／非法）完整闭公式现已先取得固定语法端点：arity/code（元数／编码）
   只需统一 `bitBound`，四个代码长度／闭合性定理均通过受限单文件探针，
   公理画像只有标准三项。同一关系码的真实正／负证书资源现也已压到固定界：
   两个有效对 `(2,0)/(2,1)` 的正原子、合取与析取，以及两个非法对的负原子、
   析取与最终合取均逐层支付；两个原始 `OfGraph` 端点通过探针且仍只有标准
   三项，不经过旧 public envelope。relation-short（关系短输入）现已直接把
   真实短比较证书与真实 failure（失败）证书接入完整关系体，完整公式的未选
   长支只支付固定语法资源；命名证书、固定载荷界、禁用依赖扫描和单模块
   `.olean` 均通过，公理画像只有标准三项。relation-valid /
   relation-invalid（关系有效／非法）仍未闭合。其下一根义务是为原解析器实际
   使用的 `fixedNumeralTerm 1/2` 建立 `NatListAtRows` 固定证书资源；现有
   fully-uniform（全统一）定理使用定义不同的 `shortBinaryNumeralTerm`，不得
   靠替换证明对象绕过。该实际公式的完整代码界、终端代码界、终端闭性和安装
   两个行端点后的代码界现已逐字证明并通过探针。任意闭下标项的定宽表项
   编译器也已接入原 `fixedNumeralTerm` 终端：两个真实边界表项、真实
   token-cell（词元单元）及两层合取的统一载荷端点通过受限探针，公理画像
   只有标准三项，最终资源不含左右行见证值。该终端现已装入两个真实有界存在
   见证，并与外层 `index < count` 守卫合并；最终原始 `OfGraph` 端点为：

   ```text
   compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
   ```

   终端证书、见证证书、透明资源桥、二元固定包络及外层合取分别缓存为小模块，
   全部受限探针通过，公理画像只有 `propext`、`Classical.choice`、`Quot.sound`，
   静态扫描无 `sorry/axiom`、`tail_gap`、`upper_provider` 或 `proof_length`。
   本次同时修复一个真实坐标错误：二元见证包络要求代入前二变量 terminal
   formula（终端公式）的代码界，旧尝试误传了安装两个见证后的闭公式代码界；
   现已改接
   `compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_code_length_le_fixed`
   及 `natListAtRowsFixedIndexFormulaCodePolynomial`，不能再使用名称相近但对象不同的
   installed-terminal（已安装终端）代码界。`fixedNumeralTerm 1/2` 的
   `NatListAtRows` 精确资源至此闭合；下一义务是分别把它接入
   relation-valid / relation-invalid（关系有效／非法）的 function/failure
   （函数解析／失败）长支。这里的 failure 已有无图参数固定端点；function
   仍须关闭两个不同公式对象，不能把旧 public-finite envelope 当作结果：

   ```text
   CompactAdditiveNatListDropRows(..., dropCount = 3)
   CompactAdditiveSyntaxTaskListConsRows(...,
     taskKind = 2, binder = binderArity, arity = functionArity)
   ```

   现有完整固定路线只分别覆盖 `dropCount = 1` 和量词任务头
   `(taskKind,binder,arity) = (1,binderArity+1,0)`。下一顺序固定为：
   将 drop-one 的计数／行全称证明参数化到常数 3；将 quantifier-cons 的
   头布局与尾行证明参数化到函数任务三元组；组合
   `SyntaxTermFunctionFixedNumeral` 固定端点；最后分别装配
   relation-valid / relation-invalid。任一步若改变原生数词语法或仍保留
   graph-dependent payload envelope（依赖图的载荷包络），不得标为闭合。
   drop-three 路线现已完整关闭：原公式中的
   `3+i`、`(3+i)+1`、`i`、`i+1` 四个开放索引项均保留
   `fixedNumeralTerm 3`，其自由变量、求值和代码长度定理已通过；由真实
   `sourceCount = 3 + targetCount` 与 `i < targetCount` 又直接推出四项的
   `numericBound` 数值界和 `bitBound` 位长界。端点
   `dropThreeRowsIndexSemanticBounds_of_graph` 不接收额外 index ceiling
   （索引上限）。在此之上，四个 fixed-width entry（定宽表项）、atomic
   row equality（原子行相等）、四层有界见证、全部有限行分支、上下文化
   分支、有界全称壳、`3 ≤ sourceCount` 与
   `sourceCount = 3 + targetCount` 两个计数叶以及最终右结合三叶公式均已
   逐层压到固定资源。最终端点为：

   ```text
   compactAdditiveNatListDropThreeRowsGraphPayloadEnvelope_le_fullyFixed
   ```

   十一个新模块的受限单文件探针与 `.olean` 缓存均通过，公理画像只有
   `propext`、`Classical.choice`、`Quot.sound`；静态扫描无
   `sorry/axiom`、`tail_gap`、`upper_provider`、`proof_length`，常数审计
   也不再残留 consumed=1 的公式参数。函数任务头
   `(taskKind,binder,arity) = (2,binderArity,functionArity)` 的
   `SyntaxTaskListConsRows` 固定资源现也已关闭，并与 running-status、
   token DropThree 和公开闭公式对齐等式组合。最终公开端点为：

   ```text
   compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
   ```

   证明链拆为真实三叶证书到透明包络、透明包络到统一固定包络、短传递和
   公开 cast 四层；各层受限单文件探针均通过，公理画像仍只有标准三项。
   relation-valid / relation-invalid 也已关闭：共同公式树模块从完整关系体
   的闭性和代码界逐层提取十四个原生子公式事实；valid 路线组合固定
   `NatListAtRows(1/2)`、关系码正证书和 function 证书，invalid 路线组合
   同两个 AtRows、关系码负证书和 failure 证书。两条路线均按原右结合语法
   依次支付六层 connective assembly（联结词装配），`tailCount` 界分别从
   真实 function/failure 行关系推出，不作为输入包络。最终端点为：

   ```text
   syntaxFormulaRelationValidBodyCertificate_structuralPayloadBound_le_fullyFixed
   syntaxFormulaRelationInvalidBodyCertificate_structuralPayloadBound_le_fullyFixed
   ```

   两端点及公共公式树、选中联结词通用桥均通过受限探针，公理画像仍只有
   标准三项。relation-short/valid/invalid 三体现也已分别接入真实 `{0,1}`
   标签证书，得到三个固定资源端点：

   ```text
   syntaxFormulaRelationShortSelectedCertificate_structuralPayloadBound_le_fullyFixed
   syntaxFormulaRelationValidSelectedCertificate_structuralPayloadBound_le_fullyFixed
   syntaxFormulaRelationInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed
   ```

   单文件受限探针耗时约 11 秒、峰值约 252 MiB；三个端点均无 `sorryAx`，
   公理画像只有标准三项。完整五路 tag-branch 的右结合析取树装配现已
   独立关闭；relation 与 invalid-tag 两个叶子的 graph-free（不要求该分支
   执行关系成立）固定语法码界也已通过：

   ```text
   binaryFormulaCode_fiveRightDisjunction_length_le
   syntaxFormulaRelationSelectedFormula_code_length_le_fixed
   syntaxFormulaInvalidTagSelectedFormula_code_length_le_fixed
   ```

   invalid-tag 端点直接使用 failure 公式的 21 坐标代入语法界，不含
   `hfailure`。logical 的 continue 公式现也已由真实 22 坐标混合项向量
   直接计费；binary 与 quantifier 的完整公式则由各自 22 坐标短二进制
   数词代入模板直接计费。五叶汇总后的公开端点为：

   ```text
   compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
   compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
   ```

   两端点均不要求任何未选分支 graph，受限探针通过且公理画像只有标准
   三项。最外层 relation 析取装配也已关闭。通用端点先从完整五叶公式提取
   左右闭性与未选右尾代码界，再把真实 selected certificate（选中证书）装入
   左支；short/valid/invalid 三个具体端点分别为：

   ```text
   syntaxFormulaRelationShortTagBranchCertificate_structuralPayloadBound_le_fullyFixed
   syntaxFormulaRelationValidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
   syntaxFormulaRelationInvalidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
   ```

   short 的 `tailCount` 位长由显式数值界推出；valid/invalid 的 `tailCount`
   数值界分别由真实 function/failure graph 的任务栈关系推出，`bitBound`
   正性由 `3 <= current.tokensCount` 和状态坐标位长界推出，均未新增外部
   参数。单文件受限探针约 11 秒，三个端点及通用端点的公理画像都只有
   `propext`、`Classical.choice`、`Quot.sound`，静态扫描无项目公设、
   `sorry`、`tail_gap`、`upper_provider` 或 `proof_length`。通用五路右结合
   析取装配的四个右路径以及
   logical、binary、quantifier、invalid-tag 四个具体路径现均已关闭；后三
   路的 `tailCount` 分别由真实 DropRows / ConsRows / SameRows 关系推出，
   `bitBound` 正性由选中标签或 `tag ≠ 0` 推出。四个端点的受限探针和公理
   画像均通过。完整 tag 节点至此关闭。`empty ⋎ enough` 外层完整公式的
   graph-free 代码界与闭性现也已关闭；正式受限探针约 10 秒通过，静态扫描
   无项目公设或占位证明。empty 左证书、enough 右证书和全部八类 checked-data
   （已检查分支数据）现已汇总为公开干净入口
   `compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData`；
   其统一显式多项式界
   `compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData_structuralPayloadBound_le_fullyFixed`
   已通过受限探针。该入口在 binary（双子式）构造中直接选用已闭合的 modular
   certificate（模块化证书），不再把旧 monolithic certificate（单体证书）
   偷接到模块化资源界；其余七类仍使用原公开构造。最终公理画像只有
   `propext`、`Classical.choice`、`Quot.sound`，禁用项扫描为零。完整
   parser graph（解析器图关系）到 clean certificate（干净证书）的构造现已
   闭合；剩余的是该证书的统一固定资源界。其 `UnconsRowsWithSize` 六叶中，
   positivity / NatSize / tail-area 三个算术叶及 SyntaxTaskList DropOne
   （任务栈丢弃一行）的九层 graph payload（图负载）链已经通过受限探针。
   TripleBoundary（三级边界）的实际行终端、实际行资源和、原 hybrid 分支树、
   上下文有限穷尽、全称外壳及最终 graph envelope（图负载包络）现均已在同一
   证明对象上得到固定界，未再用 direct `CertifiedPAContextProof` 冒充旧
   hybrid certificate。ConsRows（头插入行）允许任意三个自然数任务字段，故
   未以 quantifier/function 特例代替通用图。三条真实
   `CompactAdditiveTokenCell` 布局关系现已推出全部字段位长和两个内部游标界；
   三个任意字段均以 short binary numeral（短二进制数词）编译。通用三单元
   terminal（终端）、两层内部游标安装、左右边界见证安装，以及 count /
   head / tail-universal 三叶原公式装配均已通过受限探针。头字段使用显式
   `numericBound + bitBound` 组合位长界，该界由布局关系内部推出，未增加调用者
   参数。最终 `taskConsGenericCertificate_structuralPayloadBound_le_fullyFixed`
   公理画像只有 `propext`、`Classical.choice`、`Quot.sound`。
   `UnconsRowsWithSize` 的六个真实叶子已沿原右结合公式树全部闭合：
   positivity、DropOne、TripleBoundary、ConsRows、NatSize 与 tail-area。
   `unconsRowsWithSizeCertificate_structuralPayloadBound_le_fullyFixed`
   已为原 graph certificate（图证书）给出统一固定多项式界，并精确支付五层
   conjunction（合取）标签成本；不含调用者资源参数。受限探针约 10 秒通过，
   静态扫描无 `sorry`、项目公设、`tail_gap`、`upper_provider` 或
   `proof_length`，两个最终端点的公理画像均只有 `propext`、
   `Classical.choice`、`Quot.sound`。此前性能故障已定位为缺少
   `FoundationCompactPABinaryNumeralAddition` 显式命名空间导致的展开器深度
   搜索，不是数学缺口。接回 clean tail 的首个受限探针进一步确认：该处实际
   使用 native `1/0`（原生数词）与 short-binary binder（短二进制绑定深度），
   而上述通用端点使用三个 short-binary 项；两者数值相同但 PA 语法码不同，
   禁止用重写冒充同一证书。现已证明 clean parser 的 `fixedNumeralTerm`
   与 binary-layout 的 `nativeNumeralTerm` 是定义相同的原生语法，并复用
   binary task layout 的真实三单元证书；两个边界表项、三叶 head terminal
   及两个显式边界见证的安装均已闭合。公开端点
   `taskConsParserHeadCertificate_structuralPayloadBound_le_fullyFixed`
   的受限探针通过，静态扫描无禁用项，公理画像只有标准三项。下一唯一局部
   义务中的 count 与 tail-universal 两叶现也已接入：
   `taskConsParserCertificate_structuralPayloadBound_le_fullyFixed`
   在同一原公式上装配真实 count、native parser head 和 tail-universal
   三条证书，受限探针、禁用项扫描及标准三项公理画像均通过。parser 专用
   六叶公式码坐标现已定义，并沿原右结合公式树依次闭合
   `Tail456`、`Tail3456`、`Tail23456` 和最外层 positivity（正性）。
   最终端点
   `parserSyntaxFormulaUnconsFullPartsCertificate_structuralPayloadBound_le_fullyFixed`
   给真实 native `1/0` parser 六叶证书统一固定多项式界。七个资源/紧公式码
   端点的受限探针通过；公理画像都只有 `propext`、`Classical.choice`、
   `Quot.sound`，禁用依赖扫描为空。实际 `UnconsRowsWithSize` graph（拆头带
   大小图）现已提取六个真实分量，并通过原公式 alignment（公式对齐）接到
   parts certificate（分量证书）。该端点又与 checked branch（已检查分支）
   和 running-status（运行状态）逐层装配；最终端点
   `compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed`
   已给完整 clean parser graph certificate 统一固定多项式结构载荷界。
   五个 clean-tail / clean-parts / final graph 端点的受限探针、公理画像和
   禁用依赖扫描全部通过。该 clean formula 证书现已真实接入六路原始
   `SyntaxStep`（语法步骤）公式，并继续接入保留原生 `index + 1` 项的原始
   33 坐标 `SyntaxAdjacentStep`（相邻语法步骤）公式。正式端点为：

   ```text
   compactUnifiedParserSyntaxStepCleanHybridCertificateOfGraph
   compactParserSyntaxAdjacentStepRowCleanHybridCertificateOfGraph
   ```

   两层受限单文件探针均通过，公理画像只有 `propext`、
   `Classical.choice`、`Quot.sound`。这证明 clean formula 不是脱离实际轨迹的
   旁路证书。当前唯一局部义务是把 `SyntaxStep` 其余五个分支的旧
   coordinate-dependent public-finite envelope（依赖具体坐标的公开有限包络）
   也压到同一 `numericBound/bitBound` 固定多项式，再给新的 clean
   `SyntaxStep / SyntaxAdjacentStep` 证书建立统一资源界。完成后才可提升到
   行全称证书并接入完整 verifier `StepGraph / BoundedGraph`
   （验证器步骤图／有界图）矩阵资源，最后与输入表、输入分割、相邻行和
   初末行汇总。Formula 选中路径现已先完成这项提升：

   ```text
   compactUnifiedParserSyntaxStepCleanHybridCertificateFromFormulaData_structuralPayloadBound_le_fixed
   ```

   它直接约束 clean `FromData.formula` 的真实证明对象，并支付从第五叶到
   六路原始 `SyntaxStep` 析取根部的五次连接器成本；上界使用刚闭合的
   `cleanParserSyntaxFormulaPartsPayloadPolynomial`，不回退到旧 formula
   public-finite envelope。受限探针通过，公理画像只有标准三项。其余五条
   选中路径仍须分别固定；当前先关闭 Invalid 原 25 坐标闭公式的统一代码界，
   再装配其已具备固定资源的六个真实叶。该项现已完成。新增原子桥直接复用
   已检查的 native disequality（原生不等式）固定端点，不重新展开昂贵的负
   关系编译器；完整 Invalid 端点保留 running / Uncons / 三个不等式 /
   failure 六个原证书，并由六叶通用装配器支付五次合取成本：

   ```text
   fixedNeCertificate_structuralPayloadBound_le_fullyFixed
   compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
   compactUnifiedParserSyntaxStepCleanHybridCertificateFromInvalidData_structuralPayloadBound_le_fixed
   ```

   25 坐标总公式代码界由每个真实证书的
   `formulaCodeLength <= structuralPayloadBound` 汇总得到，避免展开大代入式。
   三个端点受限探针通过，公理画像只有标准三项。Invalid 选中证书随后支付
   五次真实右析取并到达同一 `SyntaxStep` 根部。六条选中路径中现已固定
   Formula 与 Invalid。为 Done / Empty 两个九叶分支新增的
   `checkedHybridNineConjunctionPayloadBound_le_closedGeneral` 已通过受限探针，
   它从九个原证书、九个资源界和闭总公式代码界直接给出固定装配界，不引入
   新接口。Empty 的两个 `tasksCount = 0` 原子证书现已严格归约到同一个常数
   资源；输出面积证书也已由真实 `Nat.size` 等式和坐标界压到
   `completedAreaFixedPayloadPolynomial bitBound`。对应端点为：

   ```text
   closedEqZeroCertificate_structuralPayloadBound_le_fixed
   outputBoundaryAreaCertificate_structuralPayloadBound_le_fixed
   ```

   两者探针和公理画像均通过。继续约束 Empty 原 hybrid 证书会保留对所有
   `bodyStart` 的旧求和；该旁路现已被同一闭公式的 uniform direct compiler
   （统一直接编译器）替换。新增九叶直接合取编译器，把八个原 checked
   certificate（已检查证书）与一个 structured-layout direct proof
   （结构化布局直接证明）装配为原九叶公式；再由独立 alignment（对齐）层
   转回原 22 坐标 substitution formula（代入公式）：

   ```text
   compileDirectNineConjunction
   compileDirectNineConjunction_payloadLength_le_transparent
   compileCompactUnifiedParserEmptyUniformDirectContext
   compileCompactUnifiedParserEmptyUniformDirectOriginalContext
   ```

   九叶 transparent payload envelope（透明载荷包络）的八次合取成本现已由
   `compileDirectNineConjunction_payloadLength_le_closedGeneral` 用同一个闭公式
   代码界统一支付。八个旧叶分别使用自身固定界，structured-layout 叶直接
   使用 uniform direct fixed bound；最终端点为：

   ```text
   compileCompactUnifiedParserEmptyUniformDirectContext_payloadLength_le_fixed
   compileCompactUnifiedParserEmptyUniformDirectOriginalContext_payloadLength_le_fixed
   ```

   两者约束的正是新直接 proof term（证明项），不是旧求和包络。显式九叶
   定理约二十三秒，对齐后的原 22 坐标定理约七秒；独立公理探针确认全部新
   端点只依赖标准三项，禁用依赖扫描无命中。Empty 分支本体随后已支付一次
   left disjunction（左析取）和一次 right disjunction（右析取），直接接入
   六路 `SyntaxStep` 显式根公式：

   ```text
   compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext
   compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext_payloadLength_le_selected
   ```

   该选中路径约二十二秒通过，公理画像仍只有标准三项。六条选中路径中现已
   闭合 Formula、Invalid 与 Empty。Done 的 completed-same-rows（完成状态
   同排）九叶子图也已改为直接构造：两条完成前缀、两条结构化布局、同排关系、
   两个精确大小和两个面积界均由真实证书产生，两个布局不再使用旧见证求和：

   ```text
   compileCompactBinaryNatCompletedStatusSameRowsUniformDirect
   compileCompactBinaryNatCompletedStatusSameRowsUniformDirect_payloadLength_le_fixed
   ```

   后一定理约十四秒通过；静态禁用依赖扫描为零，公理画像只有标准三项。
   该子图现已与 failed-pair（双失败状态）二选一、tokens/tasks 同排两叶
   组合，并通过统一重写公式码界对齐原 26 坐标公式。26 个环境坐标只要求
   公共位长界，公式代码、闭性、全部连接器和完整载荷均已压到只依赖
   `numericBound / bitBound` 的固定多项式：

   ```text
   compactUnifiedParserDoneClosedFormula_environment_alignment
   compactUnifiedParserDoneClosedFormula_code_length_le_fixed
   compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_le_fixed
   compileCompactUnifiedParserSyntaxStepFromDoneDirectContext_payloadLength_le_selected
   ```

   最后一个端点把 Done 作为六路 `SyntaxStep` 第一支，只支付一次左析取。
   四个关键端点的受限探针、公理画像和禁用依赖扫描均通过，公理画像只有
   标准三项。六条选中路径现已闭合 Formula、Invalid、Empty、Done；剩余
   顺序为 Repeat、Term。

   Repeat 已关闭第一批真实组件：原 25 坐标公式的环境代入、闭性和统一公式
   码固定界；原生零等式与后继等式的固定完整载荷界；以及任务头类型为原生
   固定数词 `2` 的六叶 `UnconsRowsWithSize`（带大小解构）证书。最后一项没有
   偷换成语法不同的短二进制数词 `2`，而是从非空、DropOne、TripleBoundary、
   Function ConsRows、NatSize、面积六个真实叶子重新构造，并逐字对齐原公式：

   ```text
   compactUnifiedParserSyntaxRepeatClosedFormula_code_length_le_fixed
   nativeSuccessorEqCertificate_structuralPayloadBound_le_fixed
   parserSyntaxRepeatUnconsFullFormula_alignment
   parserSyntaxRepeatUnconsGraphCertificate_structuralPayloadBound_le_fullyFixed
   ```

   上述端点的单文件受限探针、禁用依赖扫描和公理探针均通过，公理画像只有
   标准三项。Repeat 的两个 `AtRows`（指定任务行）终端也已关闭：公共终端核心
   从真实图关系提取左右边界见证并组合两条定宽表项和真实三单元任务布局；
   固定索引 `0` 使用精确原生 `(0,binderArity,0)` 布局，固定索引 `1` 使用
   精确原生 `(2,binderArity,decrementedCount)` 布局。原生零并不与短二进制零
   语法相等，因此另行建立了原生零 terminal/installed（终端／见证安装）编译器，
   没有用同值改写偷换语法。现已继续完成统一开放 body（终端公式）的公式码界
   与闭性、真实左右游标的两层有界见证安装、固定索引 `0/1` 的
   `index < count` 守卫，以及最外层合取和原源公式对齐。两个完整 `AtRows`
   固定载荷端点及全部中间端点的公理探针均通过，公理画像只有标准三项；
   无 `sorry`、项目公设或外部载荷参数。两个 `AtRows` 子义务至此闭合。Repeat
   的零分支已由 `repeatCount = 0` 与真实 `SyntaxTaskListSameRows` 证书直接闭合；
   正分支已按原顺序组合后继等式、`DropTwo` 和两条 `AtRows` 完整证书。左右两条
   选中路径又分别接入原 25 坐标公式的统一语法界，定向探针均通过，公理画像只有
   `propext`、`Classical.choice`、`Quot.sound`。这里没有构造未选分支的假证书：
   已选分支由真实 graph data（图数据）生成，未选分支只作为原析取公式的语法子式
   计长。当前义务上移到把该分支选择器与 current/next status（当前／下一状态）、
   token SameRows（词元同行）和已闭合 Uncons（任务栈拆头）四个外层组件合并，
   随后支付六路 `SyntaxStep` 的第三条选中路径。现又已完成不依赖分支种类的
   五组件装配器：它按原公式顺序组合两份真实 RunningStatus（运行状态）证书、
   真实 token SameRows、精确原生任务类型 `2` 的 Uncons 证书和调用者给出的
   已检查分支证书；完整公式码直接复用原 25 坐标统一固定界。四个公共 graph
   证书也已接入该装配器并通过受限探针，公理画像仍只有标准三项。当前精确义务
   只剩把已闭合的零／正选择器分别对齐到原 branch formula（分支公式）后调用
   公共 graph 端点；完成两条调用即得到完整 Repeat 的两条固定端点。现已进一步
   完成这两条原分支公式对齐，且统一 `repeatFullGraphCertificate` 已把五组件
   逐字 cast（公式恒等转换）回原 25 坐标闭公式；分支对齐、完整公式转换和公共
   graph 资源端点的探针均通过，公理画像只有标准三项。当前只需形成零／正两条
   最外层命名组合定理（分别把分支资源界传入完整 graph 资源定理），随后即可把
   Repeat 作为六路 `SyntaxStep` 的第五条选中路径接入。现零／正两条最外层
   完整 Repeat 命名端点均已形成并通过探针；在实际六路公式顺序中 Repeat 是
   第三支，因此选中路径精确支付两次右析取和一次左析取。该“两右一左”选择器
   及其原 `SyntaxStep` 显式公式接口也已闭合，公理画像只有标准三项。当前只剩
   把零／正完整 Repeat 端点分别代入该接口，形成两条最终 SyntaxStep graph
   端点；不再存在 Repeat 内部数学叶子。该最终 graph 端点现已闭合：它从真实
   Repeat 行关系构造 `CompactSyntaxRepeatCheckedBranchData`（已检查分支数据），
   在 `Type` 层分情况生成零／正完整证书，并把两个固定预算统一压入 `max`；
   随后严格通过“两右一左”选择器进入原 SyntaxStep 显式公式。定向探针、公理
   探针和禁用依赖扫描均通过，公理画像只有标准三项。Repeat 路径至此完整关闭，
   Term（项任务）路径随后也已闭合：七种判定分支、完整 Term graph
   （项图）和六路 `SyntaxStep`（语法步骤）的第四条路径均得到固定资源界。
   六个 SyntaxStep 分支现分别产生同一原公式的真实直接 PA 证明对象，并由
   `syntaxStepAllBranchesClosedFixedResource` 的显式 `max`（最大值）统一：

   ```text
   compactUnifiedParserSyntaxStepFullyFixedBoundFromData
   compactUnifiedParserSyntaxStepFullyFixedBoundOfGraph
   ```

   两个汇总端点及六个分支端点均通过 60 秒受限单文件探针；独立公理探针
   全部仅含 `propext`、`Classical.choice`、`Quot.sound`，禁用依赖扫描为空。
   该统一界现已沿两条严格区分的索引路线接入
   `SyntaxAdjacentStep`（相邻语法步骤）原 33 坐标公式。闭索引端点
   `compactParserSyntaxAdjacentStepFullyFixedBoundOfGraph` 已通过；开放索引路线
   又新增任意 valuation（赋值）版 `StateAtRows`（状态指定行）编译器，并把
   `indexTerm` 与原生 `indexTerm + 1` 分别用于当前／下一行。三个坐标分量及聚合
   端点 `compactParserSyntaxAdjacentStepAtValuationIndexFullyFixedBoundOfGraph`
   均通过 60 秒受限探针，公理画像只有标准三项。

   两份 status-valid（状态有效）证书随后与开放索引相邻步骤合成为同一
   terminal body（终端主体）。其上的 `AdjacentRowBounded`（有界相邻行）
   27 个见证已按原量词顺序逐项提取、对齐并直接编译；原始终端的自由变量严格
   包含于 `{0}`，上下文码由公开 `numericBound` 统一支付。最终端点
   `compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedBound`
   直接从同一索引处的原 bounded proposition（有界命题）产生真实 PA 证明，
   不接收行证书、证明长度或隐藏上界参数。开放索引语法、见证代入、上下文界、
   27 元编译和最终原公式转换均通过受限探针，公理画像只有
   `propext`、`Classical.choice`、`Quot.sound`。

   `row universal`（行全称）外壳现也已闭合。原八参数
   `compactParserSyntaxAdjacentRowsBoundedGraphDef` 被严格对齐为
   `expDef valueBound tableWidth` 与
   `∀ rowIndex < rowCount, AdjacentRowBounded(rowIndex)` 的合取；每个全称
   分支都以 `extendValuation rowIndex zeroValuation` 调用上述开放索引端点，
   `rowIndex <= numericBound` 仅由
   `rowIndex < rowCount <= numericBound` 推出。27 见证的公开资源界与行号
   无关，因此全部分支共享同一叶资源；有限穷尽、短数词边界等式、全称引入
   和最终合取的完整成本进一步受显式
   `explicitDirectUniversalBranchesPayloadPolynomial` 控制。最终端点为：

   ```text
   compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext
   compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext_payloadLength_le
   ```

   语法对齐、单行分支、分支树、多项式包络、全称证明和原图公式端点均通过
   60 秒受限单文件探针；公理画像仍仅含标准三项，无 `sorryAx`、无项目公设、
   无证明长度或分支证书输入。当前局部义务已上移到：

   ```text
   verifier StepGraph / BoundedGraph（验证器步骤图／有界图）完整矩阵
   ```

   `A04.18` 尚未整体闭合，必须保持黄色。
2. 由规范接受执行构造同一闭矩阵的 quantitative hybrid certificate（定量混合
   证书），复用已闭合的输入表、公式表、输入分割、相邻行、初末行等端点；最终
   依赖闭包不得到达 `ofSigmaZeroTruth` 或
   `certificate_nonempty_of_sigmaZero_truth`，且其结构资源受同一固定多项式界。
3. 把矩阵资源界与已经闭合的 20 层显式存在见证前缀合并，得到同一
   `P_direct(bound, formulaCode)` 的真实 `CertifiedPAProof`、同一公开检查器验收和
   完整 proof + certificate 载荷固定多项式界。

第一项已排除输入/公式侧的指数枚举风险，但接受追踪侧和总资源定理尚未闭合；
第二项完成前，`A04.18` 必须保持黄色，旧 `directMatrixHybridCertificate` 不能作为
闭合证据。

精确 `expDef` 端点位于：

```text
integration/FoundationCompactPAExponentialShortNumeralTransportBounds.lean
```

精确 `lengthDef` 端点位于：

```text
integration/FoundationCompactPABinaryLengthRuleCompilerBounds.lean
```

精确 `bitDef` 端点位于：

```text
integration/FoundationCompactPABitMembershipRuleCompilerBounds.lean
```

定宽压力测试端点位于：

```text
integration/FoundationCompactPAFixedWidthEntryHybridCompiler.lean
```

已接受 PA 叶的原输入规则界、公共图界和完整 429 坐标端点位于：

```text
integration/FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight.lean
integration/FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionPublicBounds.lean
integration/FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds.lean
integration/FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedStepPublicBounds.lean
integration/FoundationCompactNumericListedPAAxiomLeafOccurrence.lean
integration/FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomTraceRow.lean
integration/FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound.lean
```

底层递归按指数高度只执行线性次数的倍增证明，不枚举 `2^height` 个数值；
`lengthDef` 同样只按输入二进制位递归；`bitDef` 按数值的二进制位和待查
位下标递归。三者随后都用真实 PA 等式证明把结果传到 `P_direct` 使用的
短二进制数词。已闭合端点的定向探针与所需单模块 `.olean` 生成均通过，
公理画像只有 `propext`、`Classical.choice`、`Quot.sound`。

不允许把“有短证明”、证明长度界、见证编译器或存在引入器作为参数。
成功端点必须返回真实 `CertifiedPAProof`，公开检查器验收通过，并给出固定多项式界。

## 5. 后续固定顺序

```text
M11 / A04.18  接受计算的 PA 短证明编译
  -> M12 / A05.03  Pudlak 定量条件 (0)--(3)
  -> M13--M14  Pudlak 1986 定量对角化、证明拼接与指数提取
  -> M15  从固定正幂下界选择整数 d，并建立完美幂重标定
  -> M16  同一 G_n = F_{rho_d(n)} 的超多项式最短证明下界
  -> M17--M20  Sondow 到同一 G_n 的独立桥、大 N 取法和最终对撞。
```

Pudlak 1986 Theorem 3.1（定理 3.1）必须在这个已固定的 `P_direct` 上给出
显式固定多项式 `p1,p2,p3,q1,q2`。不得用 Buss 1994 Theorem 5 的外部输入或
abstract super-polynomial gap（抽象超多项式间隙）代替这些义务。正确内部端点是
`PudlakBussPerfectPowerRescaledLowerBound`，随后只允许在同一 `G_n` 上转成
`StrongProofLengthLowerBound`；禁止使用 `PolynomialCofinalScale` 把结论转回
未重标定的 `F_n`。

## 6. 验证方式

开发阶段只运行当前目标的定向探针：

```bash
lake env lean integration/FoundationCompactNumericListedNodeFieldsTypedInversion.lean
lake env lean integration/FoundationCompactNumericListedCertificateNodeTypedInversion.lean
lake env lean integration/FoundationCompactNumericListedProofNodeTypedInversion.lean
lake env lean integration/FoundationCompactNumericListedTaskMachineSyntaxInversion.lean
lake env lean integration/FoundationCompactNumericListedDirectProofPredicateExactness.lean
lake env lean integration/FoundationCompactPABoundedFormulaCompiler.lean
lake env lean integration/FoundationCompactPABoundedFormulaCompilerBounds.lean
lake env lean integration/FoundationCompactPAValuationBoundedFormulaCompiler.lean
lake env lean integration/FoundationCompactPANativeFastArithmeticSemantics.lean
lake env lean integration/FoundationCompactPAHybridValuationBoundedFormulaBuilder.lean
lake env lean integration/FoundationCompactPAValuationTermCompilerBounds.lean
```

每个里程碑还必须执行：

```bash
rg -n "\\b(sorry|admit|axiom)\\b|sorryAx|tail_gap|upper_provider|proof_length" integration/FoundationCompactNumericListed*.lean
git diff --check
```

只有下游定向探针需要 import（导入）时才生成单模块 `.olean`（Lean 编译对象）；
当前黄色节点整体闭合前不运行全项目构建。
只在根义务全部闭合或需要发布时运行全项目构建。
图和指导书只在一个黄色节点整体转绿或路线发生根本变化时更新。
