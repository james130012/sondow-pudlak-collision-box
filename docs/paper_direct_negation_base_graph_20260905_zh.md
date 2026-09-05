# 从原 Syntax 行构造 mode=3 的否定基础图

日期：2026-09-05。只作纸面数学推导，不新增 Lean。

本文处理《MP 整段组装审计》第 7 节第 2 项：对明确的合法算术公式编码，构造
原 TotalExactBoundedGraph，输出其否定正规形编码。Closed 的 B 和 Cut 的
I=NOT A OR B 都使用 mode=3、binderArity=0、空 witness。图的输出严格识别为
NOT B 和 A AND NOT B，并给出所需编码恒等式。

解析器本身复用《普通 Syntax 基础图》的原行构造和精确步数引理；这里逐条
补变换累积输出、真实 TransformState 布局、37 个受限见证及 Total 终点。
不调用 `...sound_selfContained`、Nat `...Def_spec` 或 PR 可表示性作为 PA 推导。

## 1. 原目标式及编码约定

以下源码名均省略 integration/ 下的共同前缀
`FoundationCompactNumericListedDirect`。

`ClosedRuleCheck.lean:38`、`CutRuleCheck.lean:38` 的无条件首项都是

```text
TotalExactBoundedGraph(T,w,N,stateB,stateCount,3,
  emptyStart,emptyFinish,0,
  inputB,inputCount,outputB,outputCount,emptyB,
  0,H,V)。                                         (1.1)
```

`FormulaTransformTotalExactFormula.lean:31` 把 fuel 固定为

```text
f=16*(inputCount+1)^2+8，stateCount=f+1。
```

这里 H 是该关系名为 tableWidth 的参数，V 是 valueBound；它们不等于原始
token 表的行宽 w。`FormulaTransformTotalTraceFormula.lean:47` 还要求
N*(N+1)≤H。下文构造直接满足这些原参数，绝不换成较短的替代关系。

`FoundationCompactSyntaxTokenMachine.lean:19–47` 的 raw 编码为：

| 构造 | raw 头 | 随后的编码 |
| --- | --- | --- |
| 绑定变量 | [0,index]，index<d | 无 |
| 自由变量 | [1,index] | 无 |
| 函数项 | [2,arity,symbolCode] | 按顺序连接全部项 |
| 正原子 / 负原子 | [0,arity,symbolCode] / [1,arity,symbolCode] | 全部项 |
| 真 / 假 | [2] / [3] | 无 |
| 合取 / 析取 | [4] / [5] | 左公式，再右公式 |
| 全称 / 存在 | [6] / [7] | binder d+1 下的公式体 |

用 E_d(A) 表示这种公式 raw 数列，E_d(t) 表示项数列。
N_d(A) 按同一语法构造定义：正负原子互换，真与假互换，合取与析取互换，
全称与存在互换；递归否定所有公式子项，所有项保持不变。它是当前系统的
否定正规形语法，不是额外添加一个一元 NOT 标签。

## 2. 复用的普通 Syntax 引理及输出加强式

引用 [普通 Syntax 基础图](paper_direct_syntax_base_graph_20260905_zh.md) 的如下精确接口。
任意合法语法片段、binder d、raw 后缀 R 和任务尾 K，从

```text
(E_d(t)++R, (0,d,0)::K, running)
(E_d(A)++R, (1,d,0)::K, running)
```

分别经 s_t、s_A 个原 SyntaxStep 行到 `(R,K,running)`。
Repeat(d,r) 对 r 个顺次项经 `1+sum_i(1+s_ti)` 行消耗它们。
每种 term/formula 的 s≤2L−1，L 是相应 raw 编码长度。
变量行消费 2 个 token，函数项和原子行消费 3 个，其他公式行消费 1 个；
Repeat、Empty、Done 不消费 token。

本节把事件加强为“parser 状态加累积输出 Z”。对同一条原 Syntax 路径，
添加如下输出变化：

```text
Term：Z 变成 Z++E_d(t)。
Formula：Z 变成 Z++E_d(N_d(A))。
Repeat：顺次追加各项的 E_d(t_i)。                  (2.1)
```

对语法构造和 Repeat 个数作同时归纳，证明 (2.1)：

- 变量一步复制原 [tag,index]；函数项先复制 [2,arity,code]，再依次复制参数项。
- 原子第一步只将头 0 改成 1，或 1 改成 0，arity/code 保持；Repeat 及项路径
  原样复制所有参数，故得到同一原子的相反极性编码。
- 常量一步将 2 与 3 互换。
- 二元式第一步将 4 与 5 互换；任务按原来的左、右顺序处理，归纳假设分别
  追加 N_d(left)、N_d(right)。这是需要的德摩根编码顺序。
- 量词第一步将 6 与 7 互换；原 Syntax 分支已经将 binder 更新为 d+1，
  子路径追加 E_(d+1)(N_(d+1)(body))。不改变任何绑定变量索引。
- Repeat 行本身不输出，随后项子路径依次追加，最后 Repeat(0) 也不输出。

这个归纳只说明应该构造哪些数列。其满足原变换公式的依据是下一节逐分支
给出的原有界算术式，不能仅用执行函数的外部运行结果替代。

PA 中使用的语法前提可写成有限构造树的节点记录、子区间和 binder 条件。
归纳量取节点数，参数保留 R、K、Z；各构造的 raw 连接等式就是上表。
新记录、数列和事件表通过逐行追加的算术编码归纳建立。此论证不需要额外
反射，也不从一个任意 Total 默认输出反推输入合法。

## 3. 每个输出更新满足原 StepRows

`FormulaTransformStepFormula.lean:61` 是三支析取：quiet 并 SameRows；
TermRows 并 TermOutputRows；FormulaRows 并 FormulaOutputRows。
沿第 2 节的每个事件，取同一 Syntax 原分支，填写以下额外参数与原输出子式。

### 3.1 Quiet 行

Repeat、Empty、Done 选 quiet 支的对应原 Syntax 子式，令 Z'=Z。
输出列表逐项相等，故原 NatListSameRows 的 count 式成立；对每个 index，取
两个规范边界的真实端点，AtomicRowEq 用相同的 Z[index] 逐位证明。
这里 consumedCount=mappedHead=0；quiet 支不读这两个数。

### 3.2 Term 行

令 c 为实际消费长度 2 或 3，P 为当前剩余 raw 流，则下一剩余流是 drop(c,P)，
取 Z'=Z++take(c,P)。`FormulaTransformTermOutputRows.lean:109` 的原第一项
是 current.parserTokensCount=c+next.parserTokensCount，直接由这个构造成立。

选 1≤c 的分支，并选最后
`mode≠0 ∧ mode≠1 ∧ mode≠2 ∧ mode≠4 ∧ mode≠5` 分支。
mode=3 的这五个不等式都是固定数词计算；witness 参数在此分支不被读取。
原输出关系恰是 AppendSourcePrefix，不会对变量作 free/shift/substitution。

设旧输出块的起点为 a、当前输入块起点为 s、新输出块起点为 b，均指其列表
长度头。`NatListAppendSourcePrefix.lean:25` 要求的两段相等是

```text
旧输出正文 [a+1,finishZ) = 新输出 [b+1,b+1+|Z|)，
当前输入 [s+1,s+1+c) = 新输出 [b+1+|Z|,finishZ')。
```

按 Z' 的定义，分别逐项复制 Z 和 take(c,P)。同时 c≤|P|、s+1+c≤finishP、
|Z'|=|Z|+c。这样给出该原输出图的全部条款。

### 3.3 Formula 行

令 c=3 对应原子，c=1 对应其他公式构造。若已消费的头为 tag，令 h 为下表
的 mappedHead，Z'=Z++[h]++drop(1,take(c,P))：

```text
tag：0 1 2 3 4 5 6 7
h：  1 0 3 2 5 4 7 6
pair：0 0 1 1 2 2 3 3。
```

`FormulaTransformOutputPrimitives.lean:110` 的原 NegationTagGraph 为
tag<8，且“tag=2*pair、h=tag+1”或“tag=2*pair+1、tag=h+1”，pair<4。
逐个取上表 pair 即得原图；不把外部 compactNegationFormulaTag 当作新原子。

`FormulaTransformFormulaOutputRows.lean:49` 选择 c≥1、mode 排除
0/1/2/4/5 的分支，然后给上述 TagGraph 和原 AppendMappedSourcePrefix。
后者的全部额外条件为：

```text
1≤c≤|P|，s+1+c≤finishP，finishZ'=b+1+|Z'|，|Z'|=|Z|+c；
旧 Z 正文复制到新 Z' 的前 |Z| 项；
新 Z' 的第 |Z| 项由 NatListAtRows 读取 h；
当前输入 [s+2,s+1+c) 复制到新输出 [b+2+|Z|,finishZ')。
```

取新输出规范边界第 |Z|、|Z|+1 项作 AtRows 的见证，即明确读取 h。
最后一个 slice 比较只复制原子头的 arity/code；c=1 时两边都是零长区间。
它不会误把第一个参数项的头当成公式标签再变换。至此，每个原 Formula 行的
所有实际输出子式均已构造。

## 4. 燃料、状态数组与无循环的共同布局

现在取 d=0、R=[]、K=[]、Z=[]，输入 X=E_0(A)，长 L≥1。
同一八构造归纳给输出 Y=E_0(N_0(A)) 的 token 个数也为 L。
第 2 节路径在 s_A≤2L−1 步后达到 parser 的 `(remaining=[],tasks=[],running)`，
输出已经是 Y=E_0(N_0(A))。再加一条原 Empty 行使 parser completed []，输出
仍为 Y。到这时总步数 q=s_A+1≤2L。

以原 Done_completed 分支重复补行，输出 SameRows，补到
f=16*(L+1)^2+8。故得到恰 f+1 个 TransformState，而非只给一个 fuel 以内
完成的抽象断言。所有状态都是 running 或 completed []，无失败分支。

TransformState 的实际编码是 ParserState 编码与输出 NatList 编码的乘积，
不是原 syntax-only 状态。对每个时刻 i，明确写 raw 块

```text
[remainingCount] ++ remaining ++
[taskCount] ++ concat(taskKind,binder,repeatCount) ++
statusTokens ++ [emittedCount] ++ emitted。
```

running 的 statusTokens=[0]，completed [] 的 statusTokens=[1,1,0]。
其中 completed [] 中的最后一个 0 是 parser 的空后缀列表头；其后还必须有
独立的 emittedCount，不能把这两个列表混为一段。

可同时给定任意有限背景区，内含实际规则要使用的输入 X、输出 Y 及 empty=[0]
的完整含头块；也可以把这些块补入背景。先按 raw 长度放置全部背景与 f+1 个
状态，得到总行数 N 和所有绝对端点。此时尚未写任何边界整数，因此没有
“先定 N、再加入依赖 N 的 raw 边界码”的循环。

对每个状态：

- parserTokensFinish 在 remaining 列表后；parserTasksFinish 在任务列表后；
  parserFinish 在 status 后；finish 在 emitted 列表后。
- token/output 边界依次记录各单元端点，任务边界依次每次增加 3；所有边界
  数字都使用宽度 N。外层 stateB 记录 f+2 个状态切点，也使用宽度 N。
- 任意空列表的边界有一个真实 finish 数字，不把必须读的空边界错误设为 0。

所有原 StructuredList、UnitBoundaryRows、TripleBoundaryRows、ProductSplit
由这些逐项端点等式成立；所有列表占至少一个头单元，故 ProductSplit 的
正长要求成立。于是逐状态满足原 FormulaTransformStateCoreGraph。

选 tau=1+max ell(raw token)，w=N+tau+3，令

```text
T=sum_(i<N) raw[i]*2^(w*i)，
H=N*(N+1)+w+1，V=2^H。
```

这里 raw 已完全确定，tau 不依赖边界整数。PA 的固定宽度逐行追加引理给所有
对应 TokenCell/Entry。端点≤N，所有 boundary 有至多 N+1 个 N 位数字，故
ell(boundary)≤N*(N+1)；所有原始 token<2^w，坐标、计数、长度见证及后面
Syntax 槽数都≤V。特别原面积界 N*(N+1)≤H 已满足。

不要求 T≤V；T 是此图公共 tokenTable 参数，37 个受限存在量中没有再量化 T。
若外层 G 还要约束整张 T，其共同上界应在后续组装时覆盖 T 本身。

## 5. 37 个行见证及状态有效性

在最终 N 和实际物理地址确定后，按《普通 Syntax 基础图》重新生成各事件的
七个 slot；不能直接复用一张旧 syntax-only 表上的绝对端点或 boundary 码。
关键槽的意义如下，未读取的槽填 0：

| 事件 | slot0,…,slot6 |
| --- | --- |
| Term / Formula | d, tailB, tailCount, ell(tailB), tag, argument 或 arity, symbolCode |
| Repeat | d, repeatCount, tailB, tailCount, ell(tailB), decrement 或 0, 0 |
| Empty | 新 statusStart+2, 新 status 内输出边界, 其 ell, 0,0,0,0 |
| Done_completed | 旧 statusStart+2, 旧 status 内输出边界, 其 ell, 新 statusStart+2, 新 status 内输出边界, 其 ell, 0 |

这里 Empty/Done 的“输出边界”指 parser status 保存的空后缀，不是 transform
累积输出 Y；两者必须分别布置。Done 最后槽为后缀长度 0。
这些槽属于原 Syntax 分支，由基础稿的逐行构造提供。

每行的原 37 个受限见证恰是：current 的 11 个坐标及 3 个 size，next 的
同样 14 项，七个 slot，consumedCount，mappedHead。前 28 项用第 4 节的
真实 TransformState 布局，最后两项用第 3 节值。第 4 节的 H/V 覆盖全部。

`FormulaTransformAdjacentStepBoundedFormula.lean:78` 除 StepRowGraph 外，
还要求 current/next 两个 status 的原 BinaryNatStatusValidBounded。
running 状态选择 RunningStatusSlice，四个不读的见证取 0；completed []
选择 CompletedStatusValidRows，取 outputStart=statusStart+2，outputCount=0，
边界是单数字 statusFinish，size=ell(statusFinish)。这些数≤V，而且 size≤N，
所以原受限有效性图也成立，不能只检查 StepRows 而漏掉它们。

stateB 的相邻两个 Entry 固定当前 start/finish 和下一 start/finish。
每个 i<f 都可从同一事件数组取出上述见证，得到原 AdjacentRows 的受限全称；
它不是一个另写的“执行到下一状态”替代关系。

## 6. 真正的 Total 终点与规定参数

原 `FormulaTransformInitialDefaultFinalFormula.lean:43` 的初态取第 0 状态：
输入 token 的 NatListSameRows 接背景 X，任务恰 [(1,0,0)]，status running，
transform.outputCount=0。其 InitialStateRows 所用 binderArity 是 0。

末态取第 f 状态。其 parser status 是完整 `[1,1,0]`，故构造原
EmptyFinalStateBounded 的三个见证：

```text
outputStart=parserTasksFinish+2，
outputBoundary=parserFinish（宽度 N 的单数字边界），
outputBoundarySize=ell(parserFinish)。
```

EmptyFinal 内 SameRows 的 sourceCount=0，其元素全称为空；上面真实输出
列表头仍须为 0，且其终点是 parserFinish。三见证≤V，size≤N。

`FormulaTransformFinalGetDOutputRows` 取其第一个析取：EmptyFinal 与
expectedOutput/Y 的 NatListSameRows。取背景 Y 与最终 emitted 的逐项相等
见证；两者长度均为 L。这样选的是成功输出分支，不是以默认 [] 蒙混过关。
终点中三个 reservedOutput 参数按原式取 0。

现在同时有 stateCount=f+1、面积界、原 InitialDefaultFinalBounded、原
AdjacentRowsBoundedGraph 及 V=2^H，故逐项合取并代入真实 fuel，得到 (1.1)。
若需要较强的 TotalExactEndpoint，还为背景 X/Y/empty 的规范逐单元边界补入
四个 NatListWitnessRows，witness 就用同一个 empty 块，witnessCount=0。

因此，原 TotalExactBoundedGraph 的存在已经由这份直接行构造闭合。共同
背景允许把输入、输出绑定到新增规则实际使用的 formula/negated 列表片段，
不需要把它们换成其它表中的未接回副本。

## 7. 两条编码恒等式及 MP 使用

第 1 节八种公式标签的置换是对合；项 raw 编码在两次变换中均保持。
对公式构造作归纳：原子和常量直接查八项表；二元构造保留左右顺序并用两个
归纳假设；量词构造两次恢复原标签，并在同一 d+1 下应用归纳假设。得到

```text
E_d(N_d(N_d(A)))=E_d(A)。                          (7.1)
```

令 X=E_0(A)、Y=E_0(B)，记 Neg(X)=E_0(N_0(A))。实际 implication 编码是
`[5]++Neg(X)++Y`。按原析取分支的第一步及两个递归路径，其否定输出为

```text
[4]++Neg(Neg(X))++Neg(Y)
 =[4]++X++Neg(Y)。                                (7.2)
```

这是同一 raw token 数列的等式，所以 binaryNat 展开和加 sentinel 后也是
同一 compactFormulaCode；不只是 PA 证明两个不同公式逻辑等价。
普通数列拼接结合律及 (7.1) 的构造归纳足以在 PA 中使用这个编码等式。

现在对 B 应用第 6 节，给 ClosedRuleCheck 要求的 B→NOT B 原图；对
I=NOT A OR B 再应用一次，给 CutRuleCheck 要求的 I→NOT I 原图。
(7.2) 使第二个图的 expectedOutput 确为 A AND NOT B，能直接接 And 的
constructor-member 图。

两个图的输出 token 个数都等于各自输入个数。binaryNat 的位长却不总相等：
只有原子标签 0↔1 的成本可能改变，其余三对标签等长；逐标签成本至多翻倍，
项不变，所以 Weight(Neg(X))≤2*Weight(X)。这正是主稿 5.1 使用的因子 2，
不能把“token 个数相等”误写成“载荷位数相等”。

## 8. 完成范围

本文复用普通 Syntax 的已展开原行构造，补全 mode=3 的全部额外输出、状态、
受限见证、规定燃料和成功 Total 终点，并给出双重否定与德摩根的实际编码
恒等式。共同背景的布局取法使两个图可接新增 Closed/Cut 使用的原片段。

这关闭的是新增节点的两条否定基础图义务。五个节点其余规则原子式、九条完整
外层 G 环境、最终存在量词及条件 (3) 的短 PA 证明长度由组装证明继续承担。
本稿未新增 Lean，也未把存在 PA 推导自动等同于已经获得要求的 p3 长度界。
