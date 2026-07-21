# 最短证明增长下界：精简证明指导书

更新时间：2026-07-21。

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
   固定多项式控制，随后汇总整张矩阵的总结构资源界。
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
