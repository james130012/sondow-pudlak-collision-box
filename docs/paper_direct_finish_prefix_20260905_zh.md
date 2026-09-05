# 从实际接受矩阵提取成功 Finish 前的运行片段

日期：2026-09-05。仅作纸面证明，不新增 Lean。

本稿证明：从任意满足当前原 AcceptedTraceTable 的 429 列矩阵，PA 可以取出一个
成功 Finish 的位置 k；此前每一步都保持 running，之后每一步都是接受停机态的复制。
成功 Finish 前的状态已经耗尽两条输入流与任务栈，并含一个 Boolean 为 true 的子结果。
全过程只展开原固定算术公式，不使用 Nat 的 verifier exactness、sound 或 typed 状态存在定理。

## 1. 读取同一矩阵与状态坐标

设外层宽度 U、表 T、行数 F、值界 V 满足原 AcceptedTraceTable，故
`V=2^U`、F>0。按已证明的 Entry 唯一读取引理，定义

```text
e_i[j]=(T div 2^((429*i+j)*U)) mod 2^U，i<F，j<429。
```

每一行满足原 `compactNumericVerifierStepGraphDef`，记为 G(e_i)。
这是固定公式的 429 个变量替换，不是对任意 PA 公式定义满足性。

以下坐标来自 `VerifierParseStateFormula.lean:271–282` 的两个 StateCore 替换表。

| 字段 | current | next |
| --- | --- | --- |
| 内部表、宽度、容量 | 0、1、2 | 同一 0、1、2 |
| 状态 start、finish | 3、4 | 24、25 |
| proofFinish、proofCount | 5、6 | 26、27 |
| certificateFinish、certificateCount | 7、8 | 28、29 |
| tasksFinish、taskCount、taskBoundary | 9、10、11 | 30、31、32 |
| valuesFinish、valueCount、valueBoundary | 12、13、14 | 33、34、35 |
| statusTag、statusPayloadStart、statusBool | 15、16、17 | 36、37、38 |
| valueValueBound | 23 | 44 |

四个 G 析取都显式含 current 与 next 的原 StateCore，因此二者都可由有限次
析取消去取得。令 C_i、N_i 分别指这两个原状态 core。

原初始行给 `e_0[15]=0`、`e_0[10]=1`、`e_0[13]=0`。
原最终行给 `e_(F-1)[36]=1`、`e_(F-1)[38]=1`。
原邻接只给

```text
CrossEq(N_i 的整个状态切片，C_(i+1) 的整个状态切片)，i+1<F。
```

不能直接由这句话声称两行的 status 坐标相等。下面先从原 StateCore 建立所需刚性。

特别规定：running 是 `statusTag=0`；failed 是 `statusTag=1 AND statusBool=0`；
accepted 是 `statusTag=1 AND statusBool=1`。
原 StateCore 在 tag=0 时不约束 statusBool，故仅有 `statusBool=0` 绝不表示失败。

## 2. 原 StateCore 在完整切片相等下的刚性

### 2.1 CrossEq 给出相对位置上的 token 数值相等

设两个切片 `[s,t)`、`[s',t')` 满足原 CrossEq。
其存在 count 给出相同长度 L，且 t=s+L、t'=s'+L。
对 d<L，先用两个单元的 Read 值分别建立原 Entry，再展开 CrossEq 的零延伸位等价，
可在 PA 中推出

```text
ReadCell(u,A,s+d)=ReadCell(u',A',s'+d)。
```

两侧宽度可以不同。位索引达到某侧宽度以上时，该侧值的位为 0；
因此原 `bitIndex<u+u'` 足够推出完整数值相等，不需要宽度相等。
同表 SliceEq 给相同结论，是这项推导的同宽版本。

以下所有端点比较均指“端点减各自状态起点”的相对位置相等。
不比较不同表中的绝对地址，也不比较它们的 boundary 自然数码。

### 2.2 五个有限层级的游标引理

所有引理只使用当前文件中固定格式的算术公式。列表长可以是 PA 内任意自然数；
需要的循环由相应计数变量的 PA 归纳完成。

1. **NatListSlice。** 同相对起点的头单元相等，给出 count 相等。
   原 ListHeader 给 bodyStart=start+1，原 NatListSlice 给 finish=start+1+count。
   因而 finish 的相对位置相等，正文逐项数值相等。

2. **Gamma 这样的 NatList 列表。** 原 StructuredListLayout 给相同外层 count g
   及正文首游标；原 NatListListRowsWellFormed 在 j<g 给第 j 个 inner-list 的首尾
   与其真实 NatListSlice。BoundaryTable 的第 j、j+1 个 Entry 与这组见证用唯一性识别。
   对 j 从 0 到 g 归纳：第 j 项起点相对位置已相等时，应用上一条得到其 count 和
   终点相等，后者就是第 j+1 项起点。于是 Gamma 尾游标以及每个公式 token 列表相等。
   g=0 时，首、末边界为同一个 Entry，结论仍成立。

3. **TaskCore。** 原 TaskCore 依次检查一个 tag 单元、一个 Gamma、first、second、
   witness、suffix 四个 NatListSlice。先读相同 tag，再应用第 2 条及四次第 1 条，
   得到全部字段计数和相对终点相等。这里不要求 task tag 属于某个额外标签集合，
   也不要求 tag=10 时其余 fields 为空；这些条件并非原 TaskCore 的组成部分。

4. **ChildResultCore。** 原格式为 Gamma 后接一个 BoolSlice。
   用第 2 条对齐 gammaFinish；实际 BoolSlice 在此位置读一个 0 或 1 的单元，
   finish=gammaFinish+1。得到 Boolean 值、全部 Gamma 字段和终点相等。

5. **Task/ChildResult 的外层栈。** StructuredListLayout 首先给相同栈长度及首边界。
   原 TaskListRowsGraph 的每行存在量中含 TaskCore，原 ChildResultListRowsGraph
   的每行存在量中含 ChildResultCore。逐项消去这些原存在量，按栈索引归纳，
   分别用第 3、4 条对齐下一边界。最后得到整个栈的尾游标和每项字段相等。
   所有幂界与大小见证仅用于原存在量词；本推导没有假定两侧的界数值相同。

这些头部读取均落在原 CrossEq 的范围内：每个有效列表的头严格在其终点之前，
BoundaryTable 的递增性按索引归纳给所有内层区间夹在外层首尾之间；
外层字段又依次夹在状态 start 与 finish 之间。故不存在借用切片之外 token 的步骤。

### 2.3 状态标志一致

原 `StateCoreGraphDef` 依次检查 proof NatListSlice、certificate NatListSlice、
task 栈、value 栈，最后是 OptionLayout 和 Boolean 子句。
按第 2.2 节的 1、1、5、5 顺序对齐，得到 proof/certificate/task/value 四个 count
和 valuesFinish 的相对位置相等。OptionLayout 的 tag 单元恰在 valuesFinish，故 tag 相等。

若 tag=1，两侧 BoolSlice 都在 valuesFinish+1 开始，Boolean 单元数值相等。
若 tag=0，则状态在 valuesFinish+1 结束；未使用的 statusBool 坐标可以不同。

因此 PA 有以下关于两个原 StateCore 的固定推导：

```text
Core(C) AND Core(D) AND CrossEq(C.slice,D.slice)
IMPLIES C.statusTag=D.statusTag
    AND (C.statusTag=1 IMPLIES C.statusBool=D.statusBool)。       (2.1)
```

同时得到四个栈/流长度相等及对应 task、child-result 字段的逐项相等。
证明具有固定的嵌套层级；其中的列表索引归纳使用 PA 自身的归纳公理。
它没有以 typed decoder 的唯一性作未证明前提。

若只给 `start` 到 `valuesFinish` 的 payload SliceEq，按同一推导做到 value 栈末尾
就停止，也得到两条流、两栈及其内容一致。这一截短版本用于 Finish 的 payload 保持。

## 3. 每个实际 G 分支的 status 投影

所有下列事实由相应 `.mkSigma` 合取项和固定次析取消去直接推出。

| 实际分支 | current 必须满足 | next 必须满足 |
| --- | --- | --- |
| Halted | tag=1 | 整个状态与 current SliceEq，故 tag=1 且 Boolean 不变 |
| Finish | tag=0、taskCount=0 | tag=1，Boolean 由其两个末端析取给出 |
| Parse failure | tag=0、taskCount≥1、head task tag=10 | tag=1、Boolean=0 |
| Parse success 的三类 leaf | tag=0、taskCount≥1、head task tag=10 | tag=0 |
| Parse success 的 one/two nonleaf | 同上 | tag=0 |
| Combine 的三类 success | tag=0、taskCount≥1、head task tag≠10 | tag=0 |
| Combine failure | 同上 | tag=1、Boolean=0 |

精确源码依据如下。

- G 的四析取位于 `VerifierStepFormula.lean:166`。
- Parse 的 current 条件来自 `VerifierParseStateFrameRows.lean:44`；其 failure
  经 `VerifierParseFailureSeparatedTablesStateGraph` 和 `BranchRows` 到
  `VerifierParseFailureRows.lean:95`，明确给 nextTag=1、nextBool=0。
- Verum、Closed、PAAxiom 三个 leaf 共同含 `LeafParseSuccessTransportGraph`，
  经 `LeafParseSeparatedTablesTransportRows` 到 `VerifierLeafParseStackRows.lean:80`，
  明确给 nextStatusTag=0。这个条件不依赖 leaf 的 resultBool 是否为 1。
- One/Two nonleaf 的共同项 `VerifierParseSuccessNonLeafCommonRows.lean:88`
  明确给 nextStatusTag=0。
- Combine 的 current 条件来自 `VerifierCombineStateFrameRows.lean:65`。
  `VerifierCombineBranchRows.lean:171` 的前三个 success 析取分别经过
  `VerifierCombineSuccessRows.lean:60`、`:202`、`:395` 给 nextStatusTag=0；
  最后一个 failure 经 `VerifierCombineFailureRows.lean:139` 给 tag=1、Boolean=0。
- Halted 的原 SliceEq 位于 `VerifierHaltedFormula.lean:27`；其 status 保持使用 (2.1)，
  不能仅凭它保留了某个未解析切片就跳过第 2 节。
- Finish 的完整投影为 `VerifierFinishFormula.lean:59`。

由此，PA 有两个固定一步推论：

```text
G(e) AND currentTag=1
IMPLIES HaltedBranch(e) AND nextTag=1 AND nextBool=currentBool。 (3.1)

G(e) AND currentTag=0 AND nextTag=1 AND nextBool=1
IMPLIES FinishBranch(e)。                                   (3.2)
```

(3.1) 中其它分支的 currentTag=0 与前提矛盾；Halted 分支用第 2 节。
(3.2) 中 Halted 被 currentTag 排除，所有 success parse/combine 被 nextTag 排除，
所有 failure parse/combine 被 nextBool=1 排除，故只剩 Finish。

## 4. 有限矩阵内的失败吸收与首个停机点

把第 2 节应用于原邻接 CrossEq，可得对所有 i+1<F：

```text
e_i[36]=e_(i+1)[15]；
若 e_i[36]=1，则 e_i[38]=e_(i+1)[17]。             (4.1)
```

注意第二个等式有 tag=1 的前提。

由 (3.1)、(4.1)，若某行 next 已 failed，则其后一行 current failed，
该行只能 Halted 且 next 仍 failed。按后续行数作 PA 归纳，直到末行的 next 都 failed。
这与原末行的 nextTag=nextBool=1 矛盾。因此接受矩阵中没有任何 failed current/next。
这只使用算术 `0≠1` 和给定有限矩阵，没有假设 PA 的一致性或任何反射。

现在用 PA 的有界最小化，在 i<F 中取满足 `e_i[36]=1` 的最小 k。
其存在性由末行提供；最小化本身可用对搜索上界的普通 PA 归纳证明。
于是

```text
k<F；e_k[36]=1；对 j<k，e_j[36]≠1。
```

StateCore 的 OptionLayout 强制每个 statusTag 只能为 0 或 1，故 j<k 时 nextTag=0。
currentTag 的初值为 0，并由 (4.1) 在相邻行传递，故每个 j≤k 的 currentTag=0。

第 k 行的 next 不能 failed，所以其 BoolSlice 的 0/1 析取给 nextBool=1。
等价地也可由 (3.1)、(4.1) 把其 Boolean 向后传到原接受末态而得到 1。
将这些事实放入 (3.2)，第 k 行就是原 Finish 分支。

所有 j<k 的 current、next 都 running。G 中 Halted 要 currentTag=1，Finish 与
两类 failure 要 nextTag=1，因此这些行只可能处于原 parse-success 或 combine-success。
“success”在此严格指这些原分支；它不额外断言每个中间子结果的 resultBool=1。

第 k 行以后，(3.1) 和 (4.1) 强制所有后继行都是 Halted，status Boolean 均为 1。
因此 k 同时是首个停机点、首个接受点和唯一的 Finish 行。

原初始 taskCount=1，而 Finish 必须 currentTaskCount=0；所以 k≠0。
结合自然数序，得到 `1≤k<F`。这也说明本前缀并非依赖一个未处理的空轨迹例外。

## 5. 成功 Finish 前的精确终态

把 nextBool=1 代入原 Finish 的最后两个析取。
其第二析取含 nextBool=0，被 `0≠1` 排除。第一析取留下

```text
e_k[15]=0；
e_k[6]=0；e_k[8]=0；e_k[10]=0；e_k[13]=1；
CompactNumericChildResultBoundedRowWithBool
  e_k[0] e_k[1] e_k[2] e_k[14] e_k[23] 0 1。       (5.1)
```

即两条输入流的正文都为空，任务栈为空，值栈只有一个 Boolean 为 true 的结果。
正文为空不意味着整个带头列表切片长度为 0；它仍含真实的 `[0]` 长度头。

原 Finish 还包含

```text
SliceEq([e_k[3],e_k[12]),[e_k[24],e_k[33]))，
nextProofCount=currentProofCount，nextCertificateCount=currentCertificateCount，
nextTaskCount=currentTaskCount，nextValueCount=currentValueCount。
```

应用第 2 节的 payload 版本，唯一子结果的完整 Gamma 和 Boolean 都保持。
其后每条 Halted 的完整 SliceEq、各行之间的 CrossEq 可通过相对位置上的数值等式
传递；故该子结果与原最后接受状态的子结果逐项相同。
这里相同的是实际 token 列表及 Boolean，不要求 boundary 自然数码或内部行界相等。

若原输入还带 AcceptedConclusionRow，最后一行的 Gamma 与公共 formula 的
FormulaSetEqSingleton 已知。逐个 Gamma 项使用上述 token 等值，原跨表单公式比较
可传回成功 Finish 前的那个唯一子结果。这里的“唯一”指 value 栈长度为 1；
并不把 FormulaSetEqSingleton 错读成 Gamma 长度为 1，因为 Gamma 可以含重复项。

## 6. 把前 k 条原行真正取成外层表格

对每个 j<k，保留完整的原 429 个 Read 值。以原宽度 U，按顺序重新打包这 429*k 个
单元，或取旧表模 `2^(429*k*U)`；有限位/除余归纳给每个新 Entry 与旧值完全相同。
不直接沿用旧表的容量外高位，也不修改任意内部 stateTable 或 stateWidth。

因此 PA 内存在一个 k 行表 Tpre，满足：

- 原 `BoundedGraph(U,Tpre,k,2^U)`；
- 原 `RowsAdjacent(U,Tpre,k,2^U)`；
- 原输入的同一 InitialWitnessTableRow；
- 每一行的 currentTag=nextTag=0；
- 最后一行 next-state 的整个切片与第 k 行 current-state 满足原 CrossEq。

最后一项就是原第 k-1 与 k 行的接缝，虽然 Finish 行本身不放入 Tpre，
它的见证仍可在上述存在性推导中使用。
由第 2 节，Tpre 最后 next-state 的四个 count 与 (5.1) 相同。
该状态自己的 ChildResultListRowsGraph 给 row 0 的本地有界见证；
ChildResult 的刚性识别其 Boolean 为 1，因而这些本地见证满足其自己的原
ChildResultBoundedRowWithBool。没有把另一个内部表的大见证强塞进旧的小界。

Tpre 末态仍 running，所以本稿不把 Tpre 写成 AcceptedTraceTable。
它正是后续续延变换所需的运行片段：从原初态运行到单结果、空流、空任务的状态，
下一步的成功 Finish 被有意留在片段之外。

## 7. 得到的统一 PA 引理与剩余范围

第 1–6 节给出一个关于原固定公式的统一 PA 定理：
每个实际 AcceptedTraceTable 都存在 `1≤k<F`、成功 Finish 行及真实 k 行前缀，
满足上述所有原行、接缝、初态、running 与终端子结果条件。
若有 AcceptedConclusionRow，还保留该子结果的指定公式集合。

所用额外数学只是指数/除余/位算术、固定编码层的游标归纳、有限有界最小化与表格截取。
没有用原 verifier 的标准模型 exactness 代替任一步 PA 推导。

这闭合了 MP 搬运记录中的“Finish 前有效前缀”局部义务。
把前缀放进新的任务/值栈上下文、构造各具体规则与调度的 429 列见证、以及完成
五节点 MP 的全部拼装，仍是独立义务；本稿不将完整条件 (3) 标为完成。
