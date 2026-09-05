# 直接运行矩阵的 PA 输运：已闭合的表格层与未闭合的续延层

日期：2026-09-05。只作纸面证明，不新增 Lean。

本稿得到四个关于当前实际算术公式的局部结果：429 列见证的唯一提取、
运行片段的重新编码与拼接、接受末态的吸收补行并保留结论关系，
以及单个 TaskCoreGraph 的 suffix 追加。
它们不使用标准自然数模型的 `spec`/`exactness` 作为 PA 内定理。
五节点 MP 的完整续延输运尚未闭合，准确缺项在第 6 节。

## 1. 源定义和实际坐标

记 G 为 `compactNumericVerifierStepGraphDef`，它是一个固定的 429 参数算术公式。
本稿写 `G(e)` 是把这 429 个参数替换为 e 的各个数值，不是调用满足性或真谓词。

`FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula.lean`
实际定义的一个外层步骤行是：429 个有界存在变量，逐个满足 `Entry`，
再将它们放入同一个 G。列号乘子是固定整数 429。

`FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula.lean`
只读取相邻两行的下列十个值：

```text
源行 i：   0,1,2,24,25；
目标 i+1：0,1,2,3,4。
```

前三个值分别是内部 stateTable、stateWidth、stateTokenCount。
源行的 24、25 是 next-state 的首尾游标，目标行的 3、4 是 current-state 的首尾游标。
这些值进入实际 `compactFixedWidthCrossTableSlicesEqDef`。

`FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula.lean`
的初始行读取列

```text
0,1,2,3,5,7,10,11,13,15,21。
```

其初始投影要求两个公共输入切片等于状态的两个流，任务栈头是 parse，任务数为 1，
值数为 0、statusTag 为 0。输入切分的另外一项纸面证明不在此重复。

`FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula.lean`
的接受末行只固定

```text
列 36=1，列 38=1。
```

另一个实际关系 `compactNumericVerifierAcceptedConclusionRowDef` 读取外层表格的
`0,1,2,34,35,44` 列；其中 34 固定为 1，表示 next-state 的值栈恰有一个结果。
其余内部见证确认这个结果的布尔值为 true，结论公式集合等于指定公式的单元素集合。

必须区分两层表格：外层 429 列的表格单元可以存放整个内部 stateTable 的自然数码。
改变外层行宽不是改变内部 stateWidth；把二者混为同一个宽度会改变原公式。

## 2. 429 个存在量的 PA 内唯一提取

用主稿第 5.3 节已经给出的商余定义，设

```text
Read(U,T,i,j)=(T div 2^((429*i+j)*U)) mod 2^U，j<429。
```

其中 U 是外层表的单元位宽。PA 可证明

```text
Entry(T,U,429*i+j,a) IFF a=Read(U,T,i,j)。          (2.1)
```

证明只用带余除法、有限位外延性及实际 `compactFixedWidthEntryDef`；
主稿已明确处理 U=0，不要求 T 没有额外高位。

将一行存在量依次消去，再用 (2.1) 把它们替换为对应 Read，得到固定 PA 等价：

```text
BoundedRow(U,T,2^U,i) IFF G(Read(U,T,i,0),...,Read(U,T,i,428))。
```

反方向用 429 个 Read 值作为见证。它们均严格小于 `2^U`，从而满足原来
`≤2^U` 的有界量词，并满足各自的原始 Entry 公式。
429 是固定常数，故这里是固定次数的存在量词与等式逻辑操作。
没有把 G 的真值转成 PA 证明，也没有引用 Lean 的 `Evalb` 语义定理。

对邻接的十个存在值作同样消去，精确得到

```text
Adj(U,T,2^U,i) IFF
CrossEq(e_i[0],e_i[1],e_i[2],e_i[24],e_i[25],
        e_(i+1)[0],e_(i+1)[1],e_(i+1)[2],e_(i+1)[3],e_(i+1)[4])。
```

这里 `e_i[j]=Read(U,T,i,j)`。初始行的 11 个存在值可同理消去。
末行的两个 Entry 则分别等价于 `e_i[36]=1`、`e_i[38]=1`。

因此，在明确代入 `valueBound=2^U` 后，当前外层 `AcceptedTraceTable` 与以下固定公式
的展开在 PA 内等价；若保留独立参数 valueBound，则须一并保留原首项
`expDef(valueBound,U)`，不能对任意 valueBound 省去它：

- F>0；
- 每个 i<F 上 G(e_i)；
- 每个 i+1<F 上上述原 CrossEq 邻接；
- e_0 满足实际初始投影；
- e_(F-1)[36]=e_(F-1)[38]=1。

这是当前矩阵的算术展开。它尚未断言 G(e_i) 与某个另外编码的机器函数图相等。

## 3. 重新编码与运行片段拼接

### 3.1 外层表格可以在 PA 内重新打包

给定 U、T、N，取 W≥U。按顺序读取 `429*N` 个旧单元，写入宽度 W 的新表。
令 a_j 是第 j 个旧单元值，定义逐项追加：

```text
B_0=0；
B_(j+1)=B_j+a_j*2^(W*j)。
```

PA 按 j 归纳维护：

```text
B_j<2^(W*j)；
对 h<j，ReadCell(W,B_j,h)=a_h。
```

因为 `a_j<2^U≤2^W`，新追加值不会改变前 j 个单元；商余唯一性给出新单元 a_j。
这同时构造实际表格见证，而非只声称有限序列能够编码。
如果要将中间 B_j 本身储存为归纳见证，使用宽度 `429*N*W+1` 的工作表就足够，
并按同一追加公式保存各阶段；所有幂由 PA 的指数全定义性提供。

新表的每个 e_i 与旧表逐坐标相等，故 G、邻接、初始投影、末行等式均用
固定公式的等式代换逐字保留。

AcceptedConclusionRow 的外层有界变量原来至多是 `2^U`，在 `W≥U` 后仍满足
新的界 `2^W`；其内部 `valueValueBound` 没有改变，原有内部见证全部保留。

**不能直接拿两个旧表格自然数相加来拼接。** 两表行宽可能不同，旧表还可能在
已声明行数以上有任意高位。必须先按声明单元重新编码，或先截断再按正确行宽拼接。

### 3.2 两段轨迹的拼接引理

给两段分别有 N、M 行的表格，它们各自的 G 行和内部邻接都成立。
若 N、M 都非零，另外要求第一段最后 next-state 切片与第二段首行 current-state
切片满足实际 CrossEq。

取外层行宽 `W=max(U1,U2)`，将第一段的全部单元和第二段的全部单元按第 3.1 节
依次写入新表。对任意新行 i 分 `i<N` 与 `N≤i<N+M`：

- G 行分别是原表对应行的同一 429 个值；
- 邻接分第一段内部、唯一接缝、第二段内部三种情况，分别使用旧邻接和明确的接缝前提。

因此新表严格满足原 `BoundedGraph` 和 `RowsAdjacent`。
首末投影分别继承第一段首行与第二段末行；空段单独使用恒等搬运。

该引理允许两个片段的内部 stateTable 完全不同，只要求实际 CrossEq 成立。
它不要求内部表格码相等，也不依靠“它们语义上代表同一状态”的未证判断。

## 4. 实际 G 的接受吸收行：完整局部构造

### 4.1 先从 G 提取 next-state core

`FoundationCompactNumericListedDirectVerifierStepFormula.lean:166` 的 G 为四个析取：
halted、Finish、parse、combine。

halted 与 Finish 分支显式合取两个 StateCoreGraph；parse 再分成功、失败，
两个子分支都显式合取两个 StateCoreGraph；combine 也显式合取两者。
因此对这个固定公式作有限次析取消去，PA 有固定证明

```text
G(e) IMPLIES NextCore(e)。                          (4.1)
```

NextCore 不是新状态接口，它就是
`compactNumericVerifierStateCoreGraphDef` 对参数
`e0,e1,e2,e24,e25,...,e44` 的实际替换。
当前与 next 的完整参数替换表见 `VerifierParseStateFormula.lean:271` 和 `:277`。

### 4.2 复制 21 个坐标构造吸收行

假设 G(e) 且 `e36=e38=1`。定义一个新的 429 项向量 h：

```text
h[j]=e[j]，       j=0,1,2；
h[j]=e[j+21]，    3≤j≤23；
h[j]=e[j]，       24≤j≤44；
h[j]=0，          45≤j≤428。
```

h 的 current core 和 next core 都逐字等于 e 的 next core，故由 (4.1) 得到两者。
h 的 currentStatusTag 是 `h15=e36=1`。
其 current/next 切片分别是同一内部表格的 `[e24,e25)`。

由 next core 的列表头、边界表和 option 子句，PA 可推出
`e24≤e25≤e2`：两个平列表均向右延伸；两个 structured list 的边界从其正文首游标
单调延伸至尾游标；最后 option 的终点在 tokenCount 以内。

在 `compactFixedWidthTokenSlicesEqDef` 中取

```text
count=e25-e24。
```

两个长度方程和端点界由上述序关系给出；每个 offset、bitIndex 的位等价是
同一算术原子与自身等价。因此 PA 得到同切片 SliceEq。

`FoundationCompactNumericListedDirectVerifierHaltedFormula.lean:27` 的原关系
恰为 `currentStatusTag=1 AND SliceEq(current,next)`。故 h 满足它。
与两个 core 合取，再引入 G 的第一个析取，得到

```text
G(e) AND e36=e38=1 IMPLIES G(h) AND h36=h38=1。      (4.2)
```

全部其余 384 个分支参数可以填 0，因为 G 的首个析取只使用前 45 个坐标。
这里不调用任何 parser、规则可靠性、标准模型 exact_step 或新的 Step 关系。
这是原 G 公式本身的一份固定 PA 推导。

### 4.3 邻接和结论坐标都保留

e 的 next-state 和 h 的 current-state 使用同一个内部表、同一宽度、同一首尾区间。
在实际 CrossEq 中取相同 count，所有位原子相同，得到 e 到 h 的接缝。
h 到 h 的接缝同理。

AcceptedConclusionRow 所读取的

```text
0,1,2,34,35,44
```

在 h 中与 e 完全相同。所以保留它的全部内部见证，只改外层行索引即可。
同一公式表格的单元素结论关系逐字保留。

于是若已有 t>0 行的实际接受矩阵，且 F≥t，则读取其最后 e，
在外层表中再追加 F-t 份 h；第 3 节的逐项追加归纳提供表格存在性及全部 Entry。
已有矩阵末行含 Entry(1)，所以原外层宽度 U≥1；h 的复制值和零都适合原宽度 U，
不必另行扩大行宽。

得到的恰 F 行表格满足原 AcceptedTraceTable，并保留同一 AcceptedConclusionRow。
这不是仅证明“机器停机后应当不再变化”，而是给出了原 429 列公式接受的补行证书。
它可与主稿的燃料计数合用，把已经构造出的接受前缀补到原规定燃料。

## 5. 续延变换必须修改哪些内容

直接拼接两条已经接受的输入轨迹不可行：第一条的 Finish 会把状态变成 halted，
以后只能进入吸收分支，不能继续处理另一输入子树。
需要取每条输入轨迹的“终结 Finish 之前”的运行前缀，并在新上下文中搬运它。

在实际 task machine 的列表层，候选变换必须形如

```text
P 变为 P++R；
C 变为 C++S；
K 变为 map(eta_R,K)++K0；
V 变为 V++V0。
```

其中 Parse 任务仍为 tag 10 和空 fields；combine 任务的 tag、Gamma、firstFormula、
secondFormula、witness 不变，但它保存的 fields.suffix 必须改成旧 suffix++R。
状态在搬运前后均为 running。必须排除原 Finish，以及原失败后已 halted 的部分。

这个 suffix 修改确有算术必要性。
`FoundationCompactNumericListedDirectVerifierTaskCrossTableBridgeGraph.lean:29`
要求 tag 相同以及五个字段切片分别 CrossEq；第五项明确比较
`witnessFinish` 到 task `finish` 的完整 suffix 列表，而不是只检查前四个字段。

例如在一个 wk 节点，原解析根的 suffix 是 childTokens。
追加非空 R 后，新根的 suffix 为 childTokens++R。
若仍复制原 combine 任务，第五切片的列表头分别为
`length(childTokens)+length(R)` 和 `length(childTokens)`。
原 CrossEq 要求对应行值相等，已经矛盾。
因此“只给当前两个流加 suffix、任务栈原样复制”的直觉变换不能满足实际矩阵。

在裸列表 Step 层，一旦成功 parser 的 append 性质已证，上述变换对 parse/成功 combine
分支应当可交换：解析时新产生的 combine 字段正是 eta_R；已有 combine 只读取前四类
字段及值栈头部，不读取保存的 suffix；旧成功 combine 已有足够的头部值，
在尾部追加 V0 不改变它所读的那些值。

但这段列表级说明还不是原 429 列 G 的输运证明。每个原字段切片、边界表、
解析终点图和分支内见证都必须在新表格中重新构造并满足其原来公式。

### 5.1 单个实际 TaskCoreGraph 的 suffix 追加可以独立闭合

这一局部构造不必等待 parser 的成功图。设原 `CompactNumericVerifierTaskCoreGraph`
在内部表 A、单元位宽 u、tokenCount N 上成立，任务区间为 `[s,f)`，
witnessFinish 为 w，suffixCount 为 k。由最后一个 NatListSlice，

```text
f=w+1+k，且 f≤N。
```

给定另一个有明确表格编码的原始 token 列表 R，其长度 r。取

```text
N'=3*N+2*r+2，D=N-s，s'=N。
```

原任务 tag 的 TokenCell 给 s<N，所以 D≥0。构造新的内部 token 表：

1. 前 N 个 token 保留 A 的原值。
2. 在位置 s'=N 处复制原区间 `[s,w)`，即直到原 suffix 列表头之前的全部 token。
3. 下一个 token 写入新的 suffix 长度头 k+r。
4. 接着复制原区间 `[w+1,f)` 的 k 个正文 token，再复制 R 的 r 个 token。
5. 在位置 `2*N+r+1` 另存一个完整的 `[r]++R` 列表，作为原 AppendSlices
   关系的独立右输入；其终点为 `2*N+2*r+2≤N'`。
6. 其余位置至 N' 用 0 填充。

新任务终点为 `f'=f+D+r`，因此 `f'≤2*N+r<N'`。
选择新 token 单元位宽不小于 u、R 的单元位宽以及 ell(k+r)，就能用第 3 节的
追加不变量在 PA 中构造这个表。这里的 N' 是一个足够大的合法表容量，
无要求表格所有 token 都必须被该单个任务使用。

tag、Gamma、firstFormula、secondFormula、witness 的全部区间端点统一加 D；
它们的正文数值和各自长度头不变。suffixCount 改成 k+r，finish 改成 f'。

还必须重建 Gamma 的边界表。其原单元位宽为 N，新的位宽必须为 N'。
对 j=0,...,gammaCount 读取旧边界 b_j，定义

```text
b'_j=b_j+D，
GammaBoundary'=Σ_{j≤gammaCount} b'_j*2^(j*N')。
```

由旧边界值 `b_j≤N` 得 `b'_j≤2*N<N'`，故各值适合宽度 N'。
逐项追加归纳给出全部新 Entry，并给

```text
ell(GammaBoundary')≤(gammaCount+1)*N'。
```

这正是原 TaskCoreGraph 要求的位长界，不是另加一个宽松新界。
取实际 ell(GammaBoundary') 作为 gammaBoundarySize 的见证。

以下逐项核验原公式：

- tag 的 TokenCell 由复制的一个 token 得到。
- Gamma 的 ListHeader 头值不变；正文首尾游标及所有边界均加 D，
  故 BoundaryTable 的初末 Entry、严格递增与 N' 内的界全部成立。
- 对原 NatListListRowsWellFormed 的每行，读取旧 left、right、innerCount；
  新见证取 left+D、right+D、同一 innerCount。原边界表的单调性与首末关系
  通过行索引归纳给出这些区间确在 Gamma 内，故其头和正文已经逐项复制。
  原 NatListSlice 的方程 `right=left+1+innerCount` 平移后保持；所有界都在 N' 内。
- first、second、witness 三个 NatListSlice 同样平移，其 count 保持。
- 最后的 suffix NatListSlice 使用新头 k+r 和
  `f'=(w+D)+1+(k+r)`。原 suffix 正文及 R 正文的两段拷贝，
  正好满足实际 `CompactAdditiveNatListAppendSlices` 的两个 SliceEq 条款：
  左输入为保留的 `[w,f)`，右输入为另存的 `[2*N+r+1,2*N+2*r+2)`，
  目标为 `[w+D,f')`。三段各自的 NatListSlice 也由其实际长度头验证。

因此在 PA 中得到一个真正满足原 TaskCoreGraph 的新任务，四个前置字段值不变，
suffix 等于旧 suffix++R。对 Parse 任务不应用此变换，仍保持规范空 fields。

这个构造还解释了另一个不能跳过的细节：若只改变内部 tokenCount 而保留旧
GammaBoundary 自然数码，原 Entry 的行宽已改变，读出的游标通常就不再相同。
必须同时按新 tokenCount 重编码边界表；只平移任务在大表中的起点也不够。

## 6. 具体输运义务与后续完成情况

以下 6.1、6.2 所列 parser 义务已由同日的两个后续纸面引理完成，链接见各节。
完整条件 (3) 仍缺 6.3 的外层运行构造；不能把 parser 的完成扩大为完整 MP 已证。

### 6.1 proof-root 成功图的 append 稳定性

当前状态：已在 [解析终点追加证明](paper_direct_parser_append_20260905_zh.md)
第 1–7 节闭合，包含普通/封闭语法、sequent、五类 proof-root 及 Bounded/Tagged 包装。

需要针对原关系

```text
CompactProofRootTaggedSuccessBoundedGraph
  table width count inputStart inputFinish rootStart rootFinish tag endpointBound
```

以及 `CompactNumericVerifierTaskCoreGraph` 的原字段坐标，在 PA 内证明：
若旧 input/root 图成立，给任意有明确有限列表编码的 R，存在新 table、width、count、
input/root 端点及全部内部界，使原关系再次成立，同时

- 新 input 是旧 input++R；
- tag、Gamma、firstFormula、secondFormula、witness 原字段逐行相等；
- 新 root suffix 是旧 suffix++R。

这里的 append 必须由现有 `compactAdditiveNatListAppendSlicesDef` 的长度方程与
两段正文拷贝表达，再加两侧的原 NatListSlice；跨表先按第 3 节同样的逐行方法搬到
共同内部 token 表，不能将一个外部列表等式冒充该算术关系。

原 proof-root 图实际分五类：SequentOnly、OneFormula、ClosedFormula、TwoFormula、
FormulaTerm（`ProofRootSuccessBoundedFormula.lean:29`）。每类都含自己的解析终点见证。
仅证明 parser 输出的 suffix 长度不增，或引用 Nat 上 parser_success_iff，
都不足以构造这五类新终点图。

### 6.2 certificate-node 成功图的对应输运

当前状态：已在 [证书节点追加证明](paper_direct_certificate_append_20260905_zh.md)
闭合。归纳公理分支使用上节普通语法终点的共同背景区版本。

同样必须对实际 `CompactCertificateNodeSuccessBoundedGraph` 证明在输入追加 S 后，
certificateTag 和 axiomTokens 保留、certificateSuffix 变成旧值++S。
叶、unary、binary 标签的直接消费关系较短；axiomCert 分支另含其具体 PA 公理
证书解析终点图，不能仅搬运最外层证书 tag。

以上两项正是实际
`CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph`
在更大上下文中继续成立所需的 parser 部分；它们已补齐，外层组合还需下节。

### 6.3 从 parser 输运到整段实际 G 输运

在已完成的 6.1、6.2 基础上，还要逐项重建：

- 两个状态 core 及任务/值列表边界表，证明 map(eta_R,K) 和尾部续延的坐标关系；
- one/two parse schedule 的原行关系；
- 完整 TaskCrossTableBridgeGraph，尤其第五个 suffix 切片；
- 各叶/合并规则已有见证中未变字段的精确搬运；
- 输入接受轨迹可在 PA 内截取其终结 Finish 前的成功前缀。

后续进展：上述任务栈的 eta_R/K0 续延、ReplaceHead/Drop、one/two schedule
与完整 TaskCrossTableBridge 已由
[任务栈调度稿](paper_direct_schedule_transport_20260905_zh.md) 完成；
[Finish 前缀稿](paper_direct_finish_prefix_20260905_zh.md) 通过状态切片的逐层游标刚性、
失败吸收及首个停机点的 PA 有界最小化，完成最后一项。
[值栈与非叶行稿](paper_direct_parse_state_transport_20260905_zh.md) 又完成
ChildResult 的 Core/RowsEq/HeadEq、Drop/PushDrop、两流与 CommonRows，
给出 one/two parse-success 的全部 429 列原 G 构造。
随后 [叶分支稿](paper_direct_leaf_state_transport_20260905_zh.md) 保留完整独立规则图，
重建三个叶的接口；[combine 稿](paper_direct_combine_state_transport_20260905_zh.md)
逐分支搬运全部公式变换、shift 表和规则双条件，补齐三个 combine-success。
[整段续延稿](paper_direct_segment_transport_20260905_zh.md) 再以 PA 行数归纳、
外层宽度扩张和真实 CrossEq 接齐每条源成功片段，并给基于源 fuel 的拼接预算。
仍须构造五个新节点、内部公式长度来源及最终同一输入/结论关系。

这时才可将五个新增节点和两条输入成功前缀按真实 CrossEq 接缝拼接，
最后用第 4 节补到规定 fuel。

当前 `VerifierCheckedStepRows.lean:24` 的规范行直接
`Classical.choose(exists_compactNumericVerifierCheckedStepRow state)`，
而后者在 `VerifierCheckedStepRow.lean:165` 使用现有外部布局/存在性定理。
它们证明了标准模型下相应行可以选择，不能作为上述统一 PA 输运定理的证明项。

## 7. 本轮准确结论

已经闭合的是原算术矩阵的外层提取、重编码、接缝拼接、accepted 吸收补行，
以及单个 TaskCoreGraph 的 suffix 追加；补行严格保留同一 AcceptedConclusionRow。

后续两稿已完成实际成功 parser 终点图的 suffix/上下文输运；
任务栈续延、调度及 Finish 前缀也已由后续稿完成；
值栈续延及 one/two 成功分支的完整 429 列合成随后闭合。
三个 leaf 和三个 combine-success 的完整局部 G 行也已有后续纸面构造。
源片段的全部接缝随后也已由整段续延稿补齐。
未闭合的是新 MP 节点、内部载荷长度账本及最后同一输入/结论的组装。
已明确排除一种错误捷径：更改输入流却不更改 combine task 的存储 suffix。
本稿没有把完整条件 (3) 或一般机器步骤双向对应标为完成。
