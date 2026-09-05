# 当前直接证明谓词的外部确认与内部再确认

日期：2026-09-05。只作纸面研究；不新增 Lean，不把标准模型等价当作 PA 内定理。

本轮完成了同一矩阵的确认生成器的逐层成本推导，并定位尚须接齐的分支预算。
确认 (1) 与再确认 (2) 是两个不同任务：前者输出关于 a 的多项式大小证明；
后者要求关于输入位数的短蕴含证明，必须依靠一份统一的 PA 内正确性定理。
当前文档不将两项中的任一项宣布整体完成。

## 1. 必须输出的原公式

令 W 为输入被接受证明的完整 payload 长度，W<=a，f 为其结论的 compact 公式码。
输出目标必须是 `compactListedPADirectProofInstance a f`，即以下实际公式的短数词实例：

```text
EXISTS proofCode,inputTokenCount,inputTable,inputOffsetTable,inputWidth,
       sourceTable,sourceWidth,sourceTokenCount,
       proofStart,proofFinish,certificateStart,certificateFinish,split,
       traceWidth,traceTable,traceValueBound,
       formulaTokenCount,formulaTable,formulaOffsetTable,formulaWidth:
  inputWidth<=a
  AND AcceptedPayloadMatrix(上述实际坐标)
  AND CanonicalPackedTokenStreamAtWidth(f,上述公式表坐标)
  AND AcceptedConclusionRow(上述trace及公式表坐标)。
```

来源是 `FoundationCompactNumericListedDirectProofPredicate.lean` 的
`compactNumericListedDirectPredicateMatrixDef` 与 `compactListedPADirectProofFormula`。
其中 AcceptedPayloadMatrix 再展开为输入表、输入分割、完整接受轨迹三项；
其公共宏步燃料恰为 `4*(inputTokenCount+1)+8`，不接受任意外部燃料替换。

`FoundationCompactNumericListedAcceptedDirectPACompiler.lean` 已能从标准接受性输出
这一个原公式的真实 PA 证明，但它调用 `compileSigmaOneTruth`。
后者从真值选择存在见证，并对有界全称按界的自然数数值枚举；
该端点没有给出 poly(a) 的输出长度界。
因此“有真 Sigma-one 句的证明生成器”与条件 (1) 已闭合不是同一句话。

## 2. 宏步数小，不表示宏步内部免费

设 M 为 proof 与 certificate 的原 token 总数。每个 token 至少占 2 位，故 2M<=W。
于是外层宏步行数

```text
F=4*(M+1)+8 <= 2W+12。
```

每行不是一个原子检查，而是一份 429 列环境。原 `compactNumericVerifierStepGraphDef`
按 halted、finish、parse、combine 四个析取分支检查。
parse 中还含证明根解析、证书解析、PA 公理检查及量词/公式变换轨迹。
不能仅由 F=O(a) 就得出整个算术矩阵只有 O(a) 个原子。

内部三个解析器的实际燃料分别是：

```text
语法/公式解析：16*(L+1)^2+8；
证明树解析：  32*(L+1)^2+16；
结构证书解析：16*(L+1)^2+8。
```

这里 L 是实际输入 token 列表长度，不是 token 最大自然数值。
来源分别是 `FoundationCompactSyntaxTokenMachine.lean:503`、
`FoundationCompactProofTokenMachine.lean:260`、
`FoundationCompactCertificateTokenMachine.lean:361`。
因此对某个长度受 B 控制的规范解析输入，三个内部轨迹的行数均为 O((B+1)^2)。
还须计入每行任务列表和输出列表，而不能把其中存储的整份 parser 表当成一个单位。

### 2.1 已经具有的真实外层位宽界

`FoundationCompactNumericListedDirectBoundedProofWitness.lean` 给出的见证仍满足原矩阵。
其 trace 使用受控的规范行选择器，保留了小的实际表和数值控制字段。
令 C(a) 表示其
`compactNumericVerifierAcceptedCoordinateSizeBound(directBoundedWitnessStreamWeight a)`，
它由分支内的公开坐标预算合成。设 F_a 为公开燃料上界。现有见证给出

```text
traceWidth <= F_a*429*C(a)，
ell(traceTable) <= (F_a*429)^2*C(a)，
ell(traceValueBound) <= F_a*429*C(a)+1。
```

对应证明为 `FoundationCompactNumericListedDirectBoundedWitnessBounds.lean` 的
`directBoundedWitness_trace_sizeBounds`。
这里第一式控制 traceWidth 的自然数数值，后两式控制巨大表值和幂界的位数。
`traceValueBound=2^traceWidth` 本身可以指数大；它只是 429 个存在见证的上界，
不是外层程序应该从 0 枚举到的全称遍历范围。

该 bounded witness 同时保留以下实际数值界：

- 每个宏步的 stateWidth、stateTokenCount；
- current/next 状态中任务列表、子结果列表的实际 count；
- 活跃 parse 行的第 60、61、69、70 列，即 proofWidth、proofTokenCount、
  certificateWidth、certificateTokenCount；
- 活跃 combine 行的实际列表计数及末行状态计数。

这些比“每一列的 Nat.size 小”强，正是量词枚举需要的坐标。
但它们不能自动替代 parser/PA 公理辅助图内每一份存在子表的数值控制。

## 3. 实际原子和位原语可以短核验

对所有具体算术操作，使用现有闭原子编译器，成本按短数词总位宽计量。
加、乘、等式、反等式、正反序关系的成本都是固定多项式。
此处原子中只留下固定多个算术运算；长期计算必须展开为轨迹。

实际矩阵中的 `expDef`、`lengthDef`、`bitDef` 不能简单全部交给朴素数值枚举。
它们已有对应的短证明构造，且原式不需要改写为另一个未经证明等价的计算谓词：

- `FoundationCompactPAExponentialShortNumeralCompiler` 直接证明
  `expDef(nu(2^h),nu(h))`。完整载荷成本关于 h 多项式，而不关于 log h 多项式；
  这里所用 h 为表宽或位索引，必须另有 h<=poly(a) 的数值界。
- `FoundationCompactPABinaryLengthRuleCompiler` 针对原 `lengthDef`。
- `FoundationCompactPABitMembershipRuleCompiler` 针对原位成员关系及其否定，
  界同时依赖位索引的自然数数值和被测数的位宽。

位成员的商余解释不是额外公理。Foundation 的
`Arithmetic/Exponential/Bit.lean:188–195` 已在其算术模型中证明

```text
i 属于 v IFF EXISTS k>=0, 0<=r<2^i: v=k*2^(i+1)+2^i+r；
i 不属于 v IFF EXISTS k>=0, 0<=r<2^i: v=k*2^(i+1)+r。
```

原编译器用固定 PA 定理及短数词证明实现这些事实。
对于真实位索引 i<=B、ell(v)<=B，两式只涉及 O(B) 位的数字，
指数值本身有 i+1 位，因此可以获得 poly(B) 的完整载荷。
这里没有把标准模型 `Nat.testBit` 的运行结果直接提升成 PA 真命题。

例如原 `compactFixedWidthEntryDef(T,w,j,v)` 是

```text
EXISTS size<=v:
  lengthDef(size,v) AND size<=w
  AND FORALL i<w: (j*w+i 属于 T IFF i 属于 v)。
```

给定实际正确的一行，先证明 size=ell(v) 的原 lengthDef 实例，
再用实际位原语证明每个 i<w 的两边位值，最后合成为该原全称。
当 w、j*w 及各数位宽都由 B 控制，证明长度为 poly(B)。
存在量词上界 v 即使巨大，也不需要枚举 0,...,v。

## 4. 有界全称的完整 payload 如何相加

令 H(k,b)=`FORALL i<k: Q(i,b)`，其中 Q 是某个固定原矩阵子公式，b 为其他参数。
PA 的两份固定模板是

```text
H(0,b)，
H(k,b) AND Q(k,b) IMPLIES H(k+1,b)。
```

第二份证明只用自然数序的离散性和等式代换。
以短数词逐次实例化，再使用实际加性合取与 MP 构造，
已有 H(k,b) 的大证明在每次组合中只出现一次。
若各 Q(k,b) 的证明长度为 L_k，总输出界是

```text
sum(k<K) L_k + K*poly(共同公式和数词位宽)，
```

而不是把一个次数大于 1 的长度函数自我迭代 K 次。
将 `nu(k)+1` 转为 nu(k+1) 只用闭加法和固定等式代换模板。
所有成本包含结构证书；固定模板可用现有 certified specialization 界核算。

对一份固定算术矩阵作如下证明生成：选择实际正确的析取支和存在见证，
逐层处理原全称，在叶子调用第 3 节的原子或原位原语编译器，随后引回原量词。
如果沿这份具体证书的所有数值全称界不超过 B，
且所有存在见证、项值的位数及实际位索引数值也不超过 B，
则固定量词深度 d 至多产生 O((B+1)^d) 次局部调用。
因而总完整载荷不超过 K*(B+1)^e，K、e 仅依赖原矩阵和原语编译器。

这是一个明确的 proof-producing 递归算法及成本推导，不是把“矩阵为真”计作一条 PA 公理。
它也不声称每个任意 Sigma-one 公式都有按输入位数计量的短核验。

## 5. 本轮新增的控制事实：闭包深度按实际目标长度控制

PA 公理叶的某些现有公开坐标预算只写 `ell(depth)<=bound`。
该事实本身不足以支付下面原公式中的全称循环：

```text
compactAdditiveAllClosureSlicesDef:
  targetCount=depth+bodyCount
  AND FORALL index<depth: Entry(...,targetStart+1+index,6)
  AND 同一body片段的复制关系。
```

但这里可以直接补出真正的数值界。原定义第一项给出

```text
depth<=targetCount。
```

对选定的规范子表，targetCount 是实际目标 token 列表长度；
该列表在规范表中逐项写出，不是只写一个代表重复次数的大数。
因此 depth 不超过这个实际列表的长度。
若目标是原 PA 公理句，其长度不超过输入证明载荷；
若目标为一个检查用中间式，则按该规范中间列表的已核算 token 长度收费。
这允许按 depth 枚举原量词，而不支付 2^ell(depth) 的虚假上界。

反方向也说明为何不能任取一个语义正确但带无用高位的 witness：
必须使用已建立列表布局的规范目标，才能把 targetCount 与实际存储长度相联系。

## 6. 429 列到完整确认之间还应接齐什么

本轮沿 P_direct 的 Direct import 链检查了显式 `.mkSigma` 定义中的全称上界。
扫描涉及 405 个 Direct 文件，找到 45 个带显式全称的定义。
这是定位工具，不声称它已经穷尽所有宏展开后的公式节点。
它们的主要计费对象如下：

| 原图族 | 实际枚举上界 | 需要用数值界控制的来源 |
|---|---|---|
| 宏步和相邻行 | rowCount | 原公共燃料 F |
| 规范输入 token、二进制段 | tokenCount、size | token 列表长度、token 位宽 |
| Entry 和跨表复制 | width、sourceWidth+targetWidth、count | 规范表宽与片段长度 |
| proof/certificate/syntax parser | 内部 rowCount、任务 count | 各解析器实际燃料及栈列表长度 |
| 公式变换、sequent 扫描 | stateCount、formulaCount | 实际变换轨迹、公式列表长度 |
| 公式集合、子结果和任务列表 | sourceCount、targetCount、actualCount | 规范列表布局 |
| free-variable supremum | count | 索引列表长度；不是最大变量号的数值 |
| allClosure | depth | 第 5 节的 targetCount 界 |

列表/公式变换中的巨大边界表、valueBound、各个打包自然数通常处在存在见证位置。
不能据其数值巨大就断言短确认不可能；也不能据其位宽小就省略表内的实际控制量。

因此具体生成器应按以下顺序工作：

1. 解码输入接受证明，保留同一树、证书和结论；允许作不增大 payload 的规范重编码。
2. 执行原公共宏步日程，逐行选择实际成功分支。
   对 proof/certificate parser 使用其原燃料，写出每个内部状态和实际终态；
   对 PA 公理叶按证书携带的实际公理种类及实际源式构造检查列表。
3. 将这些实际数据按原 graph 的 canonical/controlled 构造填写为 429 列环境，
   并继续给出其内部存在子表和分支见证。所有表宽按实际最大位宽选择。
4. 对每个原矩阵子公式按第 3、4 节生成证明；随后构造 429 列有界存在量词、
   外层 F 行全称、相邻行、初末条件、结论等式，最后引入原 20 个存在量词。
5. 输出的结论仍是 `compactListedPADirectProofInstance a f`。

标准接受实例上，f 的公式编码出现在证明树根结论中，所以外部有 ell(f)<=a+1。
因此只要规范内部数据的所有上述控制量受一个已核实的 B(a) 固定多项式支配，
第 4 节就给出 p1(a)=K*(B(a)+1)^e。
最外层 429 与 20 都是固定数，不构成随 a 增长的循环次数。

当前尚未完成的具体工作是：把表中的每一族都与活跃 parse/PA 公理分支的
实际内部见证构造逐一连上，得到同一个 B(a)，包括默认/失败分支所选的短否定证据。
已有外层公开预算只约束暴露的环境坐标，不能不经这一步就替内部所有量词付款。
本轮完成了公共 parser 燃料、位原语、全称相加、闭包深度的明确推导；
尚未核实全部嵌套分支，所以不把整个条件 (1) 标为已证。

## 7. 即使完成 (1)，也不能自动宣布 (2)

条件 (1) 是外部的证明生成陈述：给定一个长度<=a 的真实接受证明，
构造 P_direct(a,f) 的长度<=p1(a) 的证明。
它可以运行多项式多个关于 a 的步骤。即使这个生成器已经完全构造，
实际执行它得到的证明长度也不能改记为 poly(log a,log f)。

条件 (2) 的结论是另一条、关于证明存在性的短 PA 蕴含：

```text
P_direct(a,f)
  IMPLIES P_direct(q1(a),code(P_direct(nu(a),nu(f))))。
```

要得到其 poly(ell(a),ell(f)) 的外部证明长度，合理路线是一份固定的统一 PA 定理，
再用短数词实例化。该统一定理至少必须完成以下实际推导：

1. 从任意给定的原 P_direct 见证，提取其原证明 payload 及真实接受的语法对象。
   在 PA 内证明 `ell(f)<=a+1`，因为 q1 的长度界只依赖 a。
2. 从小的原 payload 重建规范计算表。原见证表允许未使用高位，
   不能把任意给定的 19 个附加见证直接复制进一个 poly(a) 大小输出。
3. 对上述确认生成器在 PA 内作语法正确性证明：每个输出 PA 证明节点和结构证书
   确实符合当前原检查规则，输出结论恰为 P_direct(a,f)，完整 payload<=q1(a)。
4. 为这个输出 payload 在 PA 内构造同一 AcceptedPayloadMatrix、
   AcceptedConclusionRow 和规定燃料下的运行见证，再引回原 20 个存在量词。

第 3 项可以使用对编译树和循环前缀的 PA 归纳；第 4 项需要原 parser、模板实例化、
拼接及闭节点的内部验收论证。它们是句法构造事实，不是 PA 的语义反射；
但现有 Lean 标准模型 exactness 并没有自动提供这些 PA 内推导。

第 1 项可进一步缩减为一个具体的片段来源不变量，无需证明一般语义可靠性：
每个 value-stack Gamma 及每个 combine-task 的 fields.1 中的公式 token 串，
均是原 proofTokens 的连续片段。NodeFields 从 sequent parser 读取 Gamma；
formula parser 返回已消费 token 前缀，余流始终是原流后缀。
叶步压入该原 Gamma，内部节点将它存入 combine-task；
combine 的相关规则返回 task.fields.1，规则的布尔检查不改写该 Gamma。
finish 保留唯一结果。

最后的原 FormulaSetEqSingleton 只要求 actualCount>0 且每项等于 f，允许重复。
不能误写成 gammaCount=1。取其第 0 项，连续片段关系给 formulaWidth<=W，
于是 ell(f)<=W+1<=a+1。
这一内部长度接口随后已由更短的实际根标记论证闭合：
[MP 组装审计](paper_direct_mp_assembly_audit_20260905_zh.md) 跟踪首次根的栈底
combine；[公式来源稿](paper_direct_formula_provenance_20260905_zh.md) 用原
Sequent 的第 0 行 Append、两条 Cons 和原 offset 递推得到
formulaWidth+4≤inputWidth，从而给出所需 ell(f)≤a+1。
无需先证明每个中间字段都来源于原载荷。其余规范重建和生成器正确性仍未闭合。

公式码还有一个可单独解决的输出坐标。设 CodeP(a,f,c) 表示用当前短数词实例化
固定 P_direct 后得到 compact 码 c。该程序只处理 O(ell(a)+ell(f)+1) 位的输入，
可以按固定点文档的 compact 代入机方法对真实 c 构造短计算证明。
如果已经有固定 PA 定理

```text
FORALL a,f,c:
  CodeP(a,f,c) IMPLIES
    (P_direct(a,f) IMPLIES P_direct(q1(a),c))，
```

则固定次数短数词实例化、CodeP 计算和逻辑组合就给出条件 (2) 所需的
poly(ell(a),ell(f)) 证明。
上式目前是准确列出的尚待证明结论，不是作为新公理引入的解决方案。

## 8. 本轮范围

本稿没有用一个更容易核验的 Sigma-one 关系替代 P_direct。
新的工作集中在原矩阵：对 parser 的二次燃料、原位原语的数值索引成本、
有界全称的加性拼接，以及 allClosure 的 depth 数值界给出了具体论证。

条件 (1) 剩余的是完整活跃分支的统一内部量词账本和最后证明装配；
条件 (2) 还需要原 P_direct 的 PA 内规范化及生成器输出验收。
没有把任何一项改称为“只剩接口”，也没有将其当作已完成下界的无条件输入。
