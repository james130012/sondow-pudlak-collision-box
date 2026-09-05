# 五节点 MP 的九个新 G 行、Finish 及实际存在矩阵

日期：2026-09-05。只作 PA 内纸面证明，不修改 Lean、主稿或 STATUS。

本稿把五个新增 proof 节点的五次 parse、四次 combine，以及末尾 Finish，接成实际固定的 429 参数 G 行；再与两份原接受矩阵的 Finish 前续延片段接合。所构造的是当前 P_direct 的原矩阵及其 20 个存在量，不是另一个等价计算谓词。全文不使用 Nat spec、typed verifier soundness、反射或“PR 可表示性”来产生关系见证。

本稿证明内部存在性。条件 (3) 另要求的短 PA 证明长度 p3，不由辅助整数存在性自动推出，留给独立的证明长度审计。

## 1. 语法参数及定理的范围

设 A、B 为当前 compact 编码下 binderArity=0 的 PA 公式，NA、NB 为其 NNF 否定，定义

```text
I  = [5] ++ NA ++ B，
NI = [4] ++ A ++ NB。
```

这里的公式符号同时指其 raw token 数组；列表连接不含额外长度头。[普通 syntax 基础稿](paper_direct_syntax_base_graph_20260905_zh.md) 第 2—4 节的有限后序语法证书明确了内部前提；[否定基础稿](paper_direct_negation_base_graph_20260905_zh.md) 第 7 节的编码对合和德摩根归纳给 neg(I)=NI。本文没有假设一个任意自然数自动是有效公式编码。

精确的内部版本采用 [短实例化稿](paper_direct_mp_short_instantiation_20260905_zh.md) 第 2 节定义的 SynImp(u,v,w)。其见证是 h=1+ell(u)+ell(v)+ell(w)、r≤h 个后序节点、8 字段 metadata，以及正负两张词表 Plus/Minus；字段记录 kind、tag、binder、param、symbol、left、right、len，子索引严格小于当前索引。原有界全称检查每个构造器的类别、binder、长度和逐 token 拼接；项的 Minus=Plus，公式的 Minus 按 NNF 配对标签和子 Minus 组成。两根是 binder=0 的公式，其 Plus 经原 canonical 图分别连接 u、v；w 经同图连接 `[5]++Minus(root_u)++Plus(root_v)`。

PA 对后序节点作加强归纳，给出 Plus/Minus 各自满足基础稿的合法语法分解；对公式节点同时维持二者互为 NNF 否定，项节点则两表相同。关系头的项子节点保持原值，二元和量词头取配对标签并使用子 Minus；再交换 Plus/Minus 作同一归纳，得到否定对合。因此取 A=Plus(root_u)、B=Plus(root_v)、NA=Minus(root_u)、NB=Minus(root_v)，就有本节所用全部语法前提和 `neg(I)=NI`。没有从一个非法的任意 u、v 推得解析成功。

本稿证明的**统一内部存在定理**为

```text
PA 证明：对所有 a,u,v,w，
SynImp(u,v,w) 且 P_direct(a,u) 且 P_direct(a,w)
推出 P_direct(29*a+128,v)。
```

这里仅引用短实例化稿的 SynImp 定义及上述节点检查，不引用该稿尚需本存在定理作为前提的证明长度结论，因此没有相互循环。对固定的实际 PA 公式实例，SynImp 证书由其构造给出，得到如下 PA 可证明的实例族：

```text
对每个 n，P_direct(n,code(I)) 且 P_direct(n,code(A))
推出 P_direct(29*n+128,code(B))。
```

证明从两份 P_direct 的 20 重存在式消去，取得实际输入矩阵。后文的 PA 数组归纳允许输入见证任意大；没有暗加输入矩阵的规范性或多项式位界。

调用的已成稿接口为：

- [Finish 前缀稿](paper_direct_finish_prefix_20260905_zh.md)：抽出 1≤k_X<F_X 的真正 running 前缀，末态两流、任务为空，值栈为一项 `(Gamma_X,1)`。
- [整段续延稿](paper_direct_segment_transport_20260905_zh.md) 第 2—4 节：保留所有实际 G 和 CrossEq，把此前缀嵌入指定 R、S、K0、V0。
- [组装审计稿](paper_direct_mp_assembly_audit_20260905_zh.md) 第 2—3 节与 [公式来源稿](paper_direct_formula_provenance_20260905_zh.md)：Gamma_X 可重复，但逐项正文等于公共 X；公共公式位宽不超过输入位宽。
- 普通 syntax、mode=3 基础稿：在预先指定的有限背景块之间，构造全部原始状态块；确定最终容量后重建真实 boundary 和所有实际步见证。

前两个输入分别记为 `(P_I,C_I)`、`(P_A,C_A)`，总 raw token 数为 M_I、M_A，F_X=4*M_X+12。公共输入位宽均≤n。

### 1.1 两份同 code 的 canonical 图必须先对齐正文

SynImp 的公共词表与任意输入 P_direct 矩阵中的 formulaTable 不必是同一个大整数。这里需要并可直接证明如下 PA 引理：两份原 CanonicalAtWidth 具有相同 code 时，其声明的 width、tokenCount 及全部 raw token 值相同。

两式各给 `code=2^W+p`、`p<2^W`，因而 `ell(code)=W+1`。长度唯一性先固定同一 W，再由加法消去固定同一 p。原 token 段在起点 o 的前 2*s 位具有 marker/data 交替结构，第 2*s 位为终止零，其中 s=ell(token)。若同一 o 的另一合法段长度为 t>s，则其第 2*s 位仍是 marker=1，与前段的终止零矛盾；t<s 对称。所以 s=t，每个 data 位相同，有限位外延性给两个 token 相同，nextOffset 都是 o+2*s+2。

对 j≤min(m_1,m_2) 作 PA 前缀归纳，维持两个第 j 个 offset 相同，以及之前各 token 相同。基例 offset=0；归纳步使用上面的段唯一性。若 m_1<m_2，则第一表终点已经是 W，第二表在同一位置之后还至少有一个宽度≥2 的段；第二表的 offset 严格递增，与其最终 offset 仍是 W 矛盾。反向同理，故 m_1=m_2。

这只识别声明范围内的读数，不断言任意表的未用高位也相同。应用此引理，把源 AcceptedConclusion 的公共 formula 表与 SynImp 中 u、w 的正词 canonical 表逐单元对齐，再使用原 singleton 全称，就取得后文所用 `Gamma_A` 每项为 A、`Gamma_I` 每项为 I 的完整 raw 内容结论。该对齐也让来源位宽界作用于本稿实际使用的 A、I。

## 2. 五个头部、五个 root 和准确的剩余流

记 `flat(X)=[|X|]++X`，`gam(F_0,...,F_(g-1))=[g]++flat(F_0)++...++flat(F_(g-1))`。gam 是内部 Gamma 存储块；proof 流里的 sequent 编码则是 `[g]++F_0++...++F_(g-1)`，二者不可混同。

取精确的公式列表

```text
Gamma_c  = [B]，             Gamma_wI = [I,B]，
Gamma_a  = [NI,B]，          Gamma_wA = [A,NI,B]，
Gamma_z  = [NB,NI,B]。
```

无论公式内容是否碰巧相等，计数头分别是 1、2、2、3、3，绝不去重。五个 proof 头部直接取

```text
H_c  = [9,1] ++ B ++ I；
H_wI = [7,2] ++ I ++ B；
H_a  = [3,2] ++ NI ++ B ++ A ++ NB；
H_wA = [7,3] ++ A ++ NI ++ B；
H_z  = [0,3] ++ NB ++ NI ++ B ++ B。

P_out = H_c ++ H_wI ++ P_I ++ H_a ++ H_wA ++ P_A ++ H_z；
C_out = [3,2] ++ C_I ++ [3,2] ++ C_A ++ [0]。
```

下表给每次新 parse 的完整输入 `H_r++Q_r`、`[certTag]++D_r` 以及输出的实际 root 字段。`Task(t,G,F,E,W,Q)` 表示存储块 `[t]++gam(G)++flat(F)++flat(E)++flat(W)++flat(Q)`。

| r | Q_r | D_r | root 的 `(tag,Gamma,first,second,witness,suffix)` | certTag |
| --- | --- | --- | --- | --- |
| c | H_wI++P_I++H_a++H_wA++P_A++H_z | [2]++C_I++[3,2]++C_A++[0] | 9,Gamma_c,I,[],[],Q_c | 3 |
| wI | P_I++H_a++H_wA++P_A++H_z | C_I++[3,2]++C_A++[0] | 7,Gamma_wI,[],[],[],Q_wI | 2 |
| a | H_wA++P_A++H_z | [2]++C_A++[0] | 3,Gamma_a,A,NB,[],Q_a | 3 |
| wA | P_A++H_z | C_A++[0] | 7,Gamma_wA,[],[],[],Q_wA | 2 |
| z | [] | [] | 0,Gamma_z,B,[],[],[] | 0 |

把前四个 root 同内容复制到后继任务栈，记为 C、WI、AN、WA。它们的 suffix 永远取上表创建时的 Q_r；执行 combine 时当前 proof 流通常已短于 Q_r，实际 CombineStateFrame 并不要求二者相等。后续不得把这些既有任务的 suffix 改成当时剩余 proof。

## 3. 从普通 syntax 基础图构造 sequent 的实际终点

这里给的是新图存在性，不以“旧成功图可以追加”作为新图的前提。设某个新根的 Gamma 为 `[F_0,...,F_(g-1)]`，解析 Gamma 后还要读额外字段 E，最后余流为 Q。令

```text
S_j = F_j++...++F_(g-1)++E++Q，0≤j≤g；
S_g = E++Q。
```

本次 g 只有 1、2、3。先规划 g+1 个**连续的**独立 raw 块 `flat(S_0),...,flat(S_g)`，令起止游标为 a_0,...,a_(g+1)。suffixBoundary 按最终 tokenCount=N 为条目宽度编码这些游标，suffixCount=g+1。连续性保证原 StepFormula 同时读取的 `current.finish=next.start=a_(j+1)` 真正成立，而不只是两个后缀内容等值。

另把 `gam(Gamma)` 直接放在 root 的 `[root.start+1,root.gammaFinish)`，Gamma 各项起止游标为 b_0,...,b_g。令 valueBoundary 编码这些 b_j，valueCount=g。每个值块恰为 flat(F_j)。对 j<g 使用普通基础稿的后缀版本：初始任务 `(1,0,0)`，输入 S_j，返回 S_(j+1)，fuel=16*(|S_j|+1)^2+8。其 input/expected WitnessRows 可以直接使用 a_j、a_(j+1)、a_(j+2) 所规定的两个块；所有内部状态另排在背景区中。

此时原 `SequentFormulaStepFormula` 的实际见证不是抽象 parser 结果，而是下面 18 个数：

```text
current=(a_j,a_(j+1),unitBoundary(S_j),|S_j|,ell(unitBoundary(S_j)))；
next=(a_(j+1),a_(j+2),unitBoundary(S_(j+1)),|S_(j+1)|,ell(...))；
value=(b_j,b_(j+1),unitBoundary(F_j),|F_j|,ell(...))；
parserStateBoundary，parserTableWidth，parserValueBound。
```

原有九个起点、终点、count 的≤N 界来自布局。suffixBoundary 的四个 Entry 和 valueBoundary 的两个 Entry 直接取上述游标；三条 NatListWitnessRows 由 flat 块的长度头及 unit boundary 给出。基础稿的 exact 图消去外层 input/expected WitnessRows 后，恰给 Step 所需的 SyntaxExactBoundedGraph，stateCount 是原式的 `16*(currentCount+1)^2+8+1`。

最后的原 AppendSlices 逐单元验证：`|S_j|=|F_j|+|S_(j+1)|`；正文前 |F_j| 个单元取 F_j，余下取 S_(j+1)。因此取得完整原 StepGraph。为 g 个实际行收集这些有限见证，选 traceWidth h_s 容纳它们，traceValueBound=2^h_s，依原有界存在顺序引入 `SequentFormulaStepRowsBoundedGraph`。两张 RowsWellFormed 表逐项使用以上 flat 块，和 suffixCount=valueCount+1 合取，得到原 SequentTraceBoundedGraph。

sequent 的输入独立写 `flat([g]++S_0)`，bodyStart/bodyFinish 取此块起止点。firstStart/Finish=a_0/a_1，finalStart/Finish=a_g/a_(g+1)。两条对应 WitnessRows 给 input、first、final；原 ConsRows 选头 g，并把 S_0 第 j 项映到输入第 j+1 项。valueStart/root.start+1、valueFinish/root.gammaFinish 的 StructuredList 和 boundarySize 界已由 gam 块给出。连同 suffixBoundary 第 0、1、g、g+1 项的 Entry，这正是 `SequentFormulaEndpointFormula` 的全部 27 参数实例。

所有语法轨迹的原始长度由 S_j 和事件表先确定；raw 状态中没有 boundary 大整数。因此先安排 root、后缀区、状态区和当前/下一 verifier 状态，再一次确定最终 N；之后构造 boundary、parser 控制界、sequent 控制界。这里没有先取得成品 parser 表再仅增加容量数字的步骤。

## 4. 五个 ProofRootEndpoint 和 simple 证书

每次 parse 将 input 存为 `flat(H_r++Q_r)`，root 存为第 2 节的 Task 块。TaskCore 的 14 个数由六字段的游标确定；GammaBoundary 用 root 内 g+1 个公式端点，size 取真实位长。平列表字段取长度头和单元边界。因而先得完整 TaskCore，不从外部 root 解码函数取得它。

外层原 ConsRows 将 proof 的第 0 项取为 proofTag，其余项与第 3 节 sequent 输入的正文逐项同值。随后分别引入实际三类 endpoint：

- **wI、wA：SequentOnly。** tag=7，firstCount=secondCount=witnessCount=0；E=[]，第 3 节 final 块是 flat(Q_r)。root 的 suffix 也是 flat(Q_r)，取整个带头块长度为 SameSlice 见证。即得 SequentOnly 的全部合取。
- **c、z：OneFormula。** tag=9/0 且 binderArity=0，secondCount=witnessCount=0；E=I/B。第 3 节 final 块是 flat(E++Q_r)。普通基础图给从此块到 root suffix 的 `(1,0,0)` exact endpoint；原 AppendSlices 用 root first 的 flat(E) 和 suffix 的 flat(Q_r)，分别比较前 |E| 项和余下正文。取得 OneFormula 的全部合取。
- **a：TwoFormula。** tag=3、witnessCount=0；E=A++NB。另设 middle 块 flat(NB++Q_a)。两份普通基础图分别给 final→middle 解析 A、middle→root.suffix 解析 NB，均初始 `(1,0,0)`、各用其真实输入 count 的规定 fuel。两条 AppendSlices 分别按 A 和 NB 的长度分段。取得 TwoFormula 的全部合取。

这些公式中的 root first/second 都是带头内部列表，proof 原流和 sequent 的 S_j 则是公式正文连接；上面的 AppendSlices 只比较各自正文，因此接口准确。

先选 branchBound 容纳该 endpoint 的全部坐标，再选 endpointBound 容纳 branchBound、bodyStart、bodyFinish。逐个引入相应 `ProofRoot*EndpointBoundedGraph` 的原存在量，再选 SuccessBoundedGraph 的相应析取。root.start 单元实际等于 proofTag，补原 TokenCell 得 TaggedSuccessBoundedGraph。外部暴露字段使用**同一份** TaskCore，因此 ExposedPayload 中的重复 root 描述没有独立选择造成的冲突。

证书从零更短：输入块为 `flat([q]++D_r)`，返回块为 flat(D_r)，q 分别为 3、2、3、2、0。两条 NatListWitnessRows 的 boundary 均取单位游标；ConsRows 在输入第 0 项取 q，第 j+1 项取 D_r[j]。q 属于 0、2、3，故得到完整 `CertificateNodeSimpleEndpointGraph` 的六个坐标。选证书 endpointBound 容纳这六数，选择 SimpleEndpointBounded/SuccessBounded 的第一析取。axiomStart/Finish、formulaStart/Finish 在该析取中不读取，均置 0。

原 TagMatch 对四类配对 `(9,3),(7,2),(3,3),(0,0)` 有对应有限析取。把 parser 输入与 current 两流的带头块逐单元 CrossEq，再合取新 proof/certificate 成功图、TagMatch、同一根 TaskCore，取得实际 40 参数 ExposedSeparatedTablesPayload。

## 5. 新 parse 行的状态、调度和全部 429 列

所有 verifier 原始状态使用

`flat(P)++flat(Cert)++[|K|]++各 Task 块++[|V|]++各 ChildResult 块++[0]`。

ChildResult(G,b) 的块为 `gam(G)++[b]`。按块长度作前缀游标归纳，给 TaskCore、ChildResultCore、栈的 StructuredList/RowsGraph、两个 StateCore。空列表的有读取 boundary 为唯一结束地址，不能一律写 0。统一取两个状态的 task 控制 `(H_t,2^H_t)`、value 控制 `(H_v,2^H_v)`，容纳全部实际栈元素、比较和调度见证；两个 running statusTag=0，未存储的 statusBool 坐标取 0。

规范 Parse 的实际块是 `[10,0,0,0,0,0]`。四个新非叶行把 `[Parse]++K` 改成 `[Parse,combine]++K` 或 `[Parse,Parse,combine]++K，值栈不变。以下直接构造原关系，不调用“已有行续延”的结论：

1. 当前首任务的两个栈 Entry、其 14 个 Core 数给 BoundedHead，tag=10、currentTag=0、taskCount≥1 给 ParseFrame。
2. ReplaceHeadRows 的 p=2/3；若旧任务数 s=1+|K|，新任务数 t=p+|K|，则 s+p=t+1。原全称 `1+i<s` 的 source[1+i] 与 target[p+i] 都是 K[i]；取四个真实端点并逐 token SameSlice。p 个新头的规范坐标给 Schedule 的 TaskAt、ParseShape；最后头为上节完整 root 的字段副本，给 TaskCrossTableBridge。实际 NonLeaf 对 Schedule 传入的 rootStart/rootFinish 是 combine 自己的 start/finish，所以其最后一条 SameSlice 取 combine 整块的自反等式；proof-root 到 combine 的五字段联系另由 TaskCrossTableBridge 给出。
3. 两个状态分别持有 `H_r++Q_r,[q]++D_r` 与 `Q_r,D_r`。payload 输入和 common 的两条 suffix CrossEq，均比较内容相同的带头列表。值栈 DropRows(0) 在每个索引直接取同一 ChildResult 的两份规范 Core，给全部 14 存在量和 Gamma SameRows。四个控制等式使用同一 H_t/H_v，nextTag=0。

这些正是 One/TwoNonLeafStateGraph 的 ExposedPayload、CommonRows、Schedule、TaskCrossBridge 四部分。逐固定析取引入 Parse success / NonLeaf，再选 G 的 Parse 分支。

四个新非叶 parse 的列赋值如下，范围均含两端；未列出的数没有自由悬空：

| 列 | 取值来源 |
| --- | --- |
| 0—2 | 本行共同 state/proof/certificate 表 T、宽 u、容量 N |
| 3—17 | current 的 start,finish,proofFinish,proofCount,certificateFinish,certificateCount,tasksFinish,taskCount,taskBoundary,valuesFinish,valueCount,valueBoundary,statusTag,statusPayloadStart,statusBool |
| 18—23 | current 的 taskBoundarySize,valueBoundarySize,H_t,2^H_t,H_v,2^H_v |
| 24—38、39—44 | next 的同顺序状态坐标和 size/control 数 |
| 45—58 | 当前规范 Parse 的 14 个 TaskCore/size 数 |
| 59—67 | T,u,N,proofInputStart,proofInputFinish,rootStart,rootFinish,proofTag,proofEndpointBound |
| 68—80 | T,u,N,certificateInputStart,certificateInputFinish,0,0,0,0,suffixStart,suffixFinish,certificateTag,certificateEndpointBound |
| 81—91 | 上节同一 root 的 gammaFinish,gammaCount,gammaBoundary,firstFinish,firstCount,secondFinish,secondCount,witnessFinish,witnessCount,suffixCount,gammaBoundarySize |
| 92—386 | 全 0 |
| 387—400 | next 第 0 个规范 Parse 的 14 个数 |
| 401—414 | two 时 next 第 1 个规范 Parse 的 14 个数；one 时全 0 |
| 415—428 | next 第 p-1 个 combine 的 14 个数，完整字段等于该次新 root |

14 个 Task 数的顺序是 `start,finish,tag,gammaFinish,gammaCount,gammaBoundary,firstFinish,firstCount,secondFinish,secondCount,witnessFinish,witnessCount,suffixCount,gammaBoundarySize`。一行之中重复引用同一数时不另选见证。

第五个 parse 是 Closed 叶。其 current `[Parse]++K` 改为 K，V 改为 `[(Gamma_z,1)]++V`。TaskDrop(1) 对尾索引 i 比较两份 K[i]；ValuePushDrop(0) 的计数式为 a+1=b，目标 HeadEq 取 Gamma_z、Boolean=1，其全称把 source[i] 与 target[i+1] 的完整子结果逐项连接。取新值栈头的同一七个 Core/size 数、两条目标 boundary Entry，以及它们≤nextValueValueBound 的界，另引入共同图实际要求的 ChildResultBoundedRowExposed；不是只提供 PushDrop 的 HeadEq。root Gamma 与新 target Gamma 的 CrossEq 使用 gam(Gamma_z)，targetBool=resultBool=1；两流 suffix CrossEq、四控制等式、nextTag=0 同上。这直接给 LeafParseSuccessTransportGraph 的全部共同条款。

Closed 的 0—91 列同上，92—98 为新值栈头的 `start,finish,gammaFinish,gammaCount,gammaBoundary,1,gammaBoundarySize`，99=1，100—127 由下一节完整构造，128—428 全 0。选择实际 ClosedLeafStateGraph、Parse success、G Parse 即得第五个新 parse 行。

## 6. Closed 的独立原规则图和 28 列

使用独立规则表 T_z,u_z,N_z，先规划以下块：gam(Gamma_z)、flat(B)、flat(NB)、flat([])，以及 [否定基础稿](paper_direct_negation_base_graph_20260905_zh.md) 第 2—6 节对 B 构造的全部 TransformState 原始块。随后一次确定 N_z，重建其全部 boundary、stateBoundary、状态/步见证，选 H_z 及 V_z=2^H_z。不能把普通 syntax 的绝对状态边界直接当作 TransformState 的边界。

基础稿给的恰是原 `FormulaTransformTotalExactBoundedGraph`：mode=3，binderArity=0，witness=[]，input=B，expectedOutput=NB，stateCount=16*(|B|+1)^2+8+1；其中同时有实际 initial、37 项步存在量、双 StatusValid、Done 填充、默认末输出的正确成功析取。以 flat(B)、flat(NB)、flat([]) 的地址/单位边界作为本行共享输入、输出和空见证。

GammaMember(B) 选 Gamma_z 的索引 2，GammaMember(NB) 选索引 0。各取 GammaBoundary 的 index/index+1 两个端点、完整带头列表的 SameSlice。两个成员式都成立，所以以 result=1 得原 `result≤1 AND (result=1 IFF member(B) AND member(NB))` 的两个方向。即使 B=NB 或列表中其它项相等，2<3、0<3 及两条列表等式仍真。

合取 mode=3 总轨迹，就得到实际 ClosedRuleCheck；再合取 proofTag=certificateTag=0 得 ClosedLeafRuleRows。Gamma 的 NatListListWitnessRows、B/NB/empty 的三条 NatListWitnessRows 由上述四块给出，完整组成原 29 参数 SelfContainedGraph。

第 100—127 列严格按该 SelfContainedGraph 的前 28 个参数排列：

```text
100..104 = T_z,u_z,N_z,0,0；
105..109 = gammaStart,gammaFinish,gammaBoundary,3,gammaBoundarySize；
110..114 = BStart,BFinish,BBoundary,|B|,BBoundarySize；
115..119 = NBStart,NBFinish,NBBoundary,|NB|,NBBoundarySize；
120..121 = transformStateBoundary,16*(|B|+1)^2+9；
122..125 = emptyStart,emptyFinish,emptyBoundary,emptyBoundarySize；
126..127 = H_z,V_z。
```

SelfContained 的第 29 个参数由全局 99=1 提供。root 的 Gamma/first 分别与规则表 gam(Gamma_z)/flat(B) 比较完整带头块，取实际两宽度跨表位等式，得 ClosedLeafCrossTableBridge 的两条 CrossEq。proofTag=ruleProofTag=0、certificateTag=ruleCertificateTag=0，故 ParsedRuleGraph 的标签等式也满足。

这里原规则文件没有额外的 free-variable-absent 或 ClosedSyntax guard。新增叶用 proof tag=0 的普通 OneFormulaEndpoint；不能误换成 PA 叶 tag=1 所用的 ClosedFormulaEndpoint。需要的 binder=0 语法有效性已经由普通基础图及本节 mode=3 图提供。

## 7. 两个 Wk 与 And 的新 SimpleCombine 行

四个 combine 均从头构造两条原 StateCore：current 是 `[task]++K`，next 是 K；两流完全不动；当前值栈弹掉规定 d 个结果后压入 `(task.Gamma,1)`。两份状态的值控制界取同一 H_v、V_v。

当前头的 14 个实际坐标给 BoundedHead。taskTag 属于 7、3、9，均不等于 10；currentTag=0。两流整个带头拼块逐单元 SameSlice，TaskDrop(1) 对 source[1+i]/target[i] 取相同 K[i] 的完整块。因此 `CombineStateFrameRows` 的全部七部分成立。nextTag=0 将在成功分支直接给出。

### 7.1 两次 Wk：完整 SubsetRows 与真实源栈连接

WI 行 right 是源第 0 项 `(Gamma_I,1)`；WA 行 right 是源第 0 项 `(Gamma_A,1)`。复制其实际有限 Gamma token 数组到本行状态，用前缀游标给原 RowsWellFormed 和 ChildResultCore。源 Γ 的第 j 项正文等于公共 I/A，来自原 AcceptedConclusion 的 singleton 全称经整段续延保持；其自身长度头同时强制为 |I|/|A|，所以**完整 flat 块**等于对应新 task Gamma 的第 0 项。

对每个 j<源 gammaCount，SubsetRows 的源两端点取该项规范端点；内部 Membership 的目标 index 固定为 0，目标两端点取新 task Gamma 第 0 项的端点。上述带头块等式给原 SameSlice。引入 j 的有界全称，得 `Subset(Gamma_I,Gamma_wI)` 或 `Subset(Gamma_A,Gamma_wA)`。原关系没有单射要求，所有重复项均可指向同一个目标 index=0。

rightBool=1，result=1，Subset 成立，故以双向蕴含引入实际 WkRuleCheck 的 IFF。PushDrop(1) 将源第 0 项弹掉，目标第 0 项是 task.Gamma；其 HeadEq 取这份 ChildResult 的七个数，Gamma SameRows 在每个新 Gamma 索引比较同一公式块，Boolean=1。尾部全称中 source[1+i] 与 target[i+1] 是相同尾结果，逐项给两边 14 个 Core/size 数。计数 d≤a、a+1=d+b、b≥1 都由显示的栈构造成立。

以上给 SimpleCombineRuleRows 的 tag=7 析取。还必须补 SimpleCombineTransitionRows：right RowsWellFormed 已给，source 第 0 项的 BoundedHeadEq 直接使用源头七数及其 Gamma SameRows。tag=3 的蕴含前提为假，left 三参数可置 0。加 nextTag=0 得 SimpleSuccess，连同 Frame 和两 StateCore 得原 CombineStateGraph。

### 7.2 And：构造器成员及两个准确 SetEqCons

AN 的 task Gamma=Gamma_a、first=A、second=NB。源栈第 0 项是 `(Gamma_z,1)`，第 1 项是 `(Gamma_wA,1)`；因此 right=Gamma_z，left=Gamma_wA，顺序不能互换。

在实际 BinaryFormulaConstructorMemberRows 中选 task Gamma 的 index=0，其存储块为 flat(NI)。第 1 节给 `NI=[4]++A++NB`，所以候选长度头=`|A|+|NB|+1`，正文首 token=4；left 正文与候选从 start+2 开始的 |A| 段 SameSlice，right 正文与其余 |NB| 段 SameSlice。原构造器图所需的全部长度和地址关系由该块逐单元成立。

两个实际 SetEqCons 的 actual 列表为

```text
Gamma_wA = A :: Gamma_a；
Gamma_z  = NB :: Gamma_a。
```

对每一条，actual 索引 0 选指定 head；索引 i>0 选 tail 索引 i-1。headMember 的索引选 0；tailSubset 的索引 j 选 actual 的 j+1。所有成员存在量取对应规范两端点，逐单元比较完整 flat 块。这给原 SetEqCons 的全部三部分，也覆盖任意相等/重复的公式项。

leftBool=rightBool=result=1，得到实际 AndRuleCheck 的完整 IFF。PushDrop(2) 把 right、left 弹掉，压入 `(Gamma_a,1)`，保留原尾 `(Gamma_wI,1)`；目标头和尾同样用七数/14 数的原 HeadEq/RowsEq 给出。再补两份 premise RowsWellFormed 和 source 索引 0/1 的 BoundedHeadEq，得到完整 SimpleTransition tag=3。以 nextTag=0、Frame、两 StateCore 引入新 And 的 G 行。

### 7.3 三条 Simple 行的 429 列

0—44 按第 5 节同顺序存两状态及其界，45—58 存当前 WI/WA/AN 的完整 Task 坐标。59—61 为 rightGammaCount,rightGammaBoundary,1；WI/WA 的 62—64 全 0，AN 的 62—64 为 leftGammaCount,leftGammaBoundary,1。65—91 全 0，92=1，93—428 全 0。

零值只放在当前 simple 析取未读取的字段。Wk 用 source/target count 分别为 1/1、2/2；And 为 3/2。原 SimpleTransition 引用的 sourceBoundary/targetBoundary、H_v/V_v 都取 0—44 中相同的状态参数，不另引入不相连的 premise 栈。

## 8. Cut 的新 ExsCut 行及完整参数

当前任务是 C，其 Gamma=Gamma_c、first=I；当前值栈第 0 项为 `(Gamma_a,1)`，第 1 项为 `(Gamma_wI,1)`，所以 right=Gamma_a、left=Gamma_wI。next 的任务空，值栈恰为 `(Gamma_c,1)`，两条流均空。

本行表同时预留两 verifier 状态、flat(NI)、flat([]) 和 I 的完整 mode=3 TransformState 区。输入 I 的 flat 块直接使用当前 task 的 `[gammaFinish,firstFinish)`，unit boundary 为 formulaBoundary；不是只提供相同编码却不连接 task 字段。否定基础稿给原 TotalExactBoundedGraph：mode=3、binder=0、空 witness、input=I、output=NI，fuel=16*(|I|+1)^2+8。

ExsCutCombineRuleRows 的三条**无条件** NatListWitnessRows 分别用 task.first、flat(NI)、flat([]) 给出。然后选 tag=9 析取：sourceCount=2；right/left RowsWellFormed 及 source 索引 0/1 的 BoundedHeadEq 均来自实际两项源值栈。

CutRuleCheck 的两个 SetEqCons 精确是

```text
left=Gamma_wI = I  :: Gamma_c；
right=Gamma_a = NI :: Gamma_c。
```

按第 7.2 节指定的 0、i-1、j+1 索引再次逐项给原存在见证。leftBool=rightBool=result=1，得到实际 CutRuleCheck 的 IFF；mode=3 总轨迹是它前面的无条件合取，不能省略。PushDrop(2) 的 a=2,b=1，其尾部蕴含 `2+i<2` 恒假；目标 HeadEq 直接给 Gamma_c、Boolean=1。于是全部 ExsCutRuleRows 成立。

与第 7 节 Frame、两 StateCore、nextTag=0 合取，选择 ExsCut success、Combine、G，得到第九条新 G。其列为：

```text
0..44 = 两状态及界；45..58 = 当前 C 的 14 数；
59..61 = 2,rightGammaBoundary,1；62..64 = 2,leftGammaBoundary,1；
65..66 = task.first 的 formulaBoundary,formulaBoundarySize；
67..71 = NIStart,NIFinish,NIBoundary,|NI|,NIBoundarySize；
72..73 = transformStateBoundary,16*(|I|+1)^2+9；
74..84 = 0；
85..88 = emptyStart,emptyFinish,emptyBoundary,emptyBoundarySize；
89 = 0；90..91 = transformTableWidth,transformValueBound；
92 = 1；93..428 = 0。
```

transformValueBound 是该实际 transform 表选取的 2 的幂；栈的 H_v/V_v 是另一组参数。可以按需要取相同的足够大幂界，但没有任何步骤把二者在未检查原式时直接混为一个任意数字。

## 9. 九条新行与两个旧片段的完整状态接缝

下表列出顺序与结束后的栈。值结果简记为下标 Gamma，布尔值均为 1；`oldI`、`oldA` 仍含源接受结果的原重复 Gamma。Parse 记为 P，仅在本表任务列使用。

| 片段 | 结束后的任务栈 | 结束后的值栈 | 结束后的 proof/certificate |
| --- | --- | --- | --- |
| 新 parse c | P,P,C | [] | Q_c,D_c |
| 新 parse wI | P,WI,P,C | [] | Q_wI,D_wI |
| I 的 k_I 行 | WI,P,C | oldI | H_a++H_wA++P_A++H_z，[3,2]++C_A++[0] |
| 新 combine WI | P,C | wI | 同上 |
| 新 parse a | P,P,AN,C | wI | Q_a,D_a |
| 新 parse wA | P,WA,P,AN,C | wI | Q_wA,D_wA |
| A 的 k_A 行 | WA,P,AN,C | oldA,wI | H_z，[0] |
| 新 combine WA | P,AN,C | wA,wI | H_z，[0] |
| 新 parse z | AN,C | z,wA,wI | []，[] |
| 新 combine AN | C | a,wI | []，[] |
| 新 combine C | [] | c | []，[] |

两旧片段分别使用

```text
R_I=H_a++H_wA++P_A++H_z，S_I=[3,2]++C_A++[0]，
K0_I=[WI,Parse,C]，V0_I=[]；
R_A=H_z，S_A=[0]，
K0_A=[WA,Parse,AN,C]，V0_A=[(Gamma_wI,1)]。
```

这些 K0 的完整任务均已在新 parse 行中构造；它们包含第 2 节原始 Q_r，不施加第二次 eta_R。整段续延引理的初末内容逐项正是本表的相邻行。源初始 Parse 为真实全空 Parse，故两个片段的首态也与前一新 parse 的末态整块一致。

每条接缝均使用两份内容相同的完整状态块，给出长度以及各 raw 单元值等式，再按两边真实位宽引入原 CrossTableSlicesEq。不同新行及旧片段可以使用不同内部表、地址和控制界；接缝只要求实际状态块内容相同。未存储的 running statusBool 均可取 0，也无需把源未使用数值强制相等。

PA 有限收集按已接行数归纳：维护当前外层位宽、429 列表、每行 G、已有全部接缝及指定首末内容。加入一行时先取其已证的 429 个见证，选择更大宽度，按 Entry 保值重包已有行，再附加新行和唯一新接缝。旧片段可逐行加入；该归纳正是整段续延稿第 3 节和矩阵输运稿的同一实际编码归纳。无需把“有限选择”或大证书存在性当作外部黑箱。

## 10. 新 Finish、规定 fuel 和末结论

令 E 为 `flat([])++flat([])++[0]++[1]++gam(Gamma_c)++[1]`，即空 proof、空 certificate、空任务、一项真值结果的完整 payload。新 Finish 的 current 块为 E++[0]，next 为 E++[1,1]。两 StateCore 用相同实际数据构造；currentTag=0,nextTag=1,nextBool=1。

原 FinishRows 的 payload SameSlice 比较 E 与 E，四个 count 等式分别是 0=0、0=0、0=0、1=1。成功析取要求的 ChildResultBoundedRowWithBool 在 currentValueBoundary 的索引 0 选唯一结果的七个 Core/size 数，Boolean=1。currentTaskCount=0 也真。于是得到完整 FinishRows 与 G 的 Finish 析取。0—44 取两状态坐标，45—428 全 0。

短接受表的行数为 t=k_I+k_A+10。令 H 为五个新 proof 头及五个证书标签的 raw token 总数，则 M_out=M_I+M_A+H，H≥5。由 k_X<F_X 和 F_X=4*M_X+12，PA 的加法不等式给

```text
t ≤ F_I+F_A+8 ≤ F_I+F_A+4*H-12 = 4*M_out+12 = F_out。
```

因此按 [矩阵输运稿](paper_direct_mp_transport_20260905_zh.md) 的实际接受吸收行，在新 Finish 后补 F_out-t 行。吸收行的 0—2 保留末行内部表，3—23 与 24—44 都取末 accepted next 的 21 数，45—428=0；其两端取同一已接受状态的坐标，原 Halted 分支成立。有限重复和外层重包给恰 F_out 行，并保留末 next 的唯一结果 Gamma_c=[B]。

最终 `AcceptedConclusionRow` 的 lastRow=F_out-1。取末行实际 0、1、2、35、44 列为 stateTable,stateWidth,stateTokenCount,valueBoundary,valueValueBound，34 列为 1。valueBoundary 的第 0、1 项取唯一结果起止点；它的 ChildResultCore 正是 Gamma_c、Boolean=1。

公共 formula 表采用 raw B 的 canonical 表。`CrossTableFormulaSetEqSingleton` 的 GammaCount=1；其唯一公式项长度头为 |B|，正文与公共 B 表逐单元一致。选该项 index=0 的起止端点和 bodyStart=start+1、单位边界，给实际 singleton 图。全称只含此一个合法 Gamma 索引。外层宽选择时容纳该行全部 429 数，内部 V_v 已容纳上述七 Core/size 数，因此 AcceptedConclusionRow 的两层实际有界存在量都能引入。

末行是新 Finish 或其吸收复制，两种情形同用这一末 next 结论。这里无需从整个 verifier 的语义正确性反推公共结论。

## 11. 同一初态、canonical 载荷和 20 个存在量

令 X=P_out++C_out，M=|X|，p=|P_out|，c=|C_out|。用 [输入分割稿](paper_direct_input_split_20260905_zh.md) 和主稿编码层的实际位权/前缀打包归纳构造 canonical 数据：

```text
W=Weight(X)，inputTable 按 W 位单元打包 X；
o_0=0，o_(j+1)=o_j+2*ell(X[j])+2，inputOffsetTable 按 W 位打包 o_0,...,o_M；
proofCode=2^W+payloadBits(X)。
```

这里 payloadBits(X) 是同一既定 token 编码的 W 个 payload 位所表示的整数，不是另外更改的 proof 编码。每个 token 与 offset<W 的位宽及末 offset=W<2^W，由 W>0 和前缀位权界给出；逐 token 编码位等式和最后 sentinel 给原 CanonicalPackedTokenStreamTableauAtWidth。

source 原始表直接存 `flat(P_out)++flat(C_out)`，sourceTokenCount=M+2，取任一容纳这些自然数单元的正 sourceWidth，按同一固定宽前缀打包得到 sourceTable。令

```text
proofStart=0，proofFinish=p+1，
certificateStart=p+1，certificateFinish=M+2，split=p。
```

InputSplit 第一条 CrossEq 比较 input raw 区间 [0,p) 与 source 区间 [1,p+1)，第二条比较 [p,M) 与 [p+2,M+2)。两者都逐项读取 P_out/C_out 的同一正文，split≤M 由长度等式给出。source 的两个带头列表则逐单元 CrossEq 到第一条新 parse c 的 current proof/certificate；该 current task 栈恰有一条全空 Parse，valueCount=0、statusTag=0。因此实际 InitialEnvironment 的两流 CrossEq、ParseTaskHead、三个 count/tag 等式全部成立。原 InitialRow 的有限读取见证由第一行 429 数给出。

对 B 再以同一编码归纳构造 `formulaTokenCount=|B|,formulaTable,formulaOffsetTable,formulaWidth=Weight(B)`，public code 取已指定 code(B)。输出载荷账本由现有 `wf≤n` 来源界及五个显示头的位权加法给 `W≤29*n+128`；本稿调用这一既有账本，不把大 auxiliary table 的位数计入公共 inputWidth，也不把 token 数当作位宽。

取第 9—10 节最终共同外层宽 U、矩阵 D 和 V=2^U。每个行数、坐标及 source 初态所需有限见证在打包前纳入宽度选择；原 BoundedRows、AdjacentRows、InitialRow、末 accepted 条款因而给精确 F_out 行的 AcceptedTraceTable。连同上面的 InputSplit、canonical proof tableau，得到原 AcceptedPayloadMatrix 的三个合取。再加 canonical B 和第 10 节末 conclusion，就是实际 PredicateMatrix 的四个合取。

现在按 `ProofPredicate.lean:284` 的原量词顺序，逐个存在引入以下 20 个数：

| 顺位 | 原参数 | 本稿取值 |
| --- | --- | --- |
| 1 | proofCode | X 的 sentinel canonical code |
| 2 | inputTokenCount | M |
| 3 | inputTable | W 位 raw X 表 |
| 4 | inputOffsetTable | 上述 o_j 的 W 位表 |
| 5 | inputWidth | W≤29*n+128 |
| 6 | sourceTable | flat(P_out)++flat(C_out) 表 |
| 7 | sourceWidth | 其选定单元位宽 |
| 8 | sourceTokenCount | M+2 |
| 9 | proofStart | 0 |
| 10 | proofFinish | p+1 |
| 11 | certificateStart | p+1 |
| 12 | certificateFinish | M+2 |
| 13 | split | p |
| 14 | traceWidth | U |
| 15 | traceTable | D |
| 16 | traceValueBound | 2^U |
| 17 | formulaTokenCount | |B| |
| 18 | formulaTable | B 的 canonical raw 表 |
| 19 | formulaOffsetTable | B 的 canonical offset 表 |
| 20 | formulaWidth | Weight(B) |

这与原固定 22 参数矩阵的调用顺序完全相同：前两个自由参数是 `bound=29*n+128`、`formulaCode=code(B)`；proofCode 是第一个存在量，之后另有 19 个辅助存在量。由原矩阵直接得到 P_direct，没有用其 Nat 语义等价定理替换任何中间证明。

## 12. 完成范围和独立成本义务

新 Sequent/Root/simple-certificate 图、新 Closed 独立规则图、两次 Wk、And、Cut、新 Finish，均已从指定原始数据和基础语法轨迹给出实际公式见证。九个 G 行的所有活动列有明确来源，其余列依所选析取置零；两段旧前缀、同一 initial、末 singleton conclusion、规定 fuel、原 20 个量词按上述顺序接齐。因此，在所引用纸面引理及既有 payload 位权账本下，MP 的**内部矩阵存在性部分**已闭合。

这不声称 p3 的短证明界已经完成。尤其语法证书实例化、公共公式代码计算及 29*n+128 算术预算的短数词证明，须给同一固定 PA 推导模板的完整载荷长度核算。本文允许内部辅助表和见证任意大，只证明它们在 PA 内通过明确有限归纳存在；此事实与“把这些大数写成数词所需的证明长度”是不同义务。
