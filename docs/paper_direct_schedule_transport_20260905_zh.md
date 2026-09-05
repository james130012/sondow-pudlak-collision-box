# 实际任务栈续延与 one/two schedule 的 PA 输运

日期：2026-09-05。范围：外层 MP 矩阵尚缺的任务栈部分。

本记录在纸面上闭合实际 `TaskCore`、任务行等式、`TaskListRowsGraph`、`DropRows`、`ReplaceHeadRows`、`TaskCrossTableBridgeGraph` 及 one/two schedule 的续延构造。证明对象是下列源码里的固定算术公式；不经 Nat `spec`、typed layout 的 `sound` 或 `Classical.choose`。本记录不宣称整个 429 列外层步骤及条件 (3) 已经闭合，也没有新增 Lean。

## 1. 源关系和应当保留的前提

源码文件均位于 `integration/`，共同前缀为 `FoundationCompactNumericListedDirect`：

| 文件尾名 | 本文使用的实际关系 |
| --- | --- |
| `VerifierTaskFormula.lean` | 17 参数 `compactNumericVerifierTaskCoreGraphDef` |
| `VerifierTaskListRowsFormula.lean` | 每行 14 个存在见证及 `valueBound=2^tableWidth` |
| `VerifierTaskBoundedAtFormula.lean` | 指定索引的 14 个有界坐标、两个 boundary Entry、TaskCore |
| `VerifierTaskListDropRows.lean` | `TaskBoundedRowsEq`、`TaskListDropRows` |
| `VerifierTaskListReplaceHeadRows.lean` | 替换一个栈顶后的任务行等式 |
| `VerifierTaskCrossTableBridgeGraph.lean` | tag 相等及 Γ、first、second、witness、suffix 五段 CrossTableSlicesEq |
| `VerifierParseScheduleFormula.lean` | 原 39 参数 one、53 参数 two schedule 公式 |
| `VerifierOneParseSuccessNonLeafStateGraph.lean`、`VerifierTwoParseSuccessNonLeafStateGraph.lean` | schedule 和 proof-root/state-task 跨表桥在实际外层图中的接合 |

给定旧 source、target 任务栈，其计数分别为 `s,t`。前提包括两个实际 TaskListRowsGraph；在外层状态中，还包括各自任务栈的 StructuredListLayout。这些前提由 StateCore 提供，不能只拿裸 ReplaceHeadRows 推断其每个单元都是合法 TaskCore。

令 `R` 为任意 PA 编码的有限自然数 token 数组，长度 `r`。令 `K0` 为一段已有实际 TaskCore 见证的有限任务数组，长度 `c`，作为新的外层续延。所有有限数组均由读数公式和固定宽度表编码，不借用元语言的“标准有限性”。

定义逐任务变换 `eta_R`：

- tag=10 时保留整条任务，尤其已满足 ParseShape 的空字段保持为空；
- tag≠10 时保留 tag、Γ、first、second、witness，只把 suffix `Q` 改成 `Q++R`。

对一般合法 TaskCore，tag=10 并不自动给出空字段。这里采用“保留”而非强制清空，因此不需要偷偷添加这一全局不变量；schedule 中新产生的 Parse 由实际 ParseShape 明确给出全空字段。

待构造的两个新栈是 `map(eta_R,source)++K0` 与 `map(eta_R,target)++K0`。`K0` 在两边按原内容复制，不再对它应用一次 `eta_R`。

所有新块可以连同任意有限背景区共同安排。先确定原始 token 块长度和位置，再一次确定最终 `N'`，之后重建条目宽度为 `N'` 的所有 boundary。不能只把原 boundary 参数里的 `N` 换成 `N'`。

## 2. TaskCore 的字段分界刚性

这是本轮新增的关键局部归纳。只知道两个旧任务的完整切片等值，还不能直接假定其 suffix 头位于同一相对位置；必须从实际字段布局推出这一点。

写 `read(T,u,i)=(T div 2^(i*u)) mod 2^u`。使用先前纸面编码层的 PA 引理：实际 Entry 与此读数等式等价，实际切片逐位相等给出逐单元读数相等，跨宽度时也成立。

一个 TaskCore 从位置 `a` 开始，字段坐标为

`a, gammaFinish, firstFinish, secondFinish, witnessFinish, finish`。

Γ 的元素数记 `m`，其 boundary 的第 `j` 项记 `g_j`。展开 StructuredListLayout 和 NatListListRowsWellFormed 得：

1. `g_0=a+2`，`g_m=gammaFinish`；位置 `a+1` 的单元为 `m`。
2. 对 `j<m`，存在 `n_j`，位置 `g_j` 的单元为 `n_j`，且 `g_(j+1)=g_j+1+n_j`。
3. 其余四个列表头顺次给出
   `firstFinish=gammaFinish+1+firstCount`，
   `secondFinish=firstFinish+1+secondCount`，
   `witnessFinish=secondFinish+1+witnessCount`，
   `finish=witnessFinish+1+suffixCount`。

这些都是原 NatListSlice 的长度等式。边界 Entry 的唯一性把第 `j` 个元素的 finish 和第 `j+1` 个元素的 start 识别为同一位置。

现假设两条实际 TaskCore 的完整切片相等，起点为 `a,b`。首先读相对位置 0、1，得到 tag 相等及 `m` 相等。对 `j≤m` 作 PA 归纳，证明

`g_j-a=h_j-b`，且前 `j` 个 Γ 元素的长度头与正文逐单元相等。

初值来自 `g_0=a+2,h_0=b+2`。归纳步在相同相对位置读取 `n_j`，由整片等值得到两边相同的长度头，再用 `next=current+1+n_j` 得到下一边界相同。正文的相等直接取整片等值在这些相对位置的实例。

在 `j=m` 处得到 gammaFinish 的相对位置相同。随后依次读取 first、second、witness、suffix 四个头，用上述四个固定长度等式，得到四个 count 及四个 finish 的相对位置相同，正文也相同。

因此在 PA 内有如下固定关系推论：两个合法 TaskCore 的完整字节相等，推出 tag 相等、五个字段各自带头字节相等、各字段分界相对于起点的偏移相等。这里没有使用 Γ 元素是合法逻辑公式这一更强性质；其原始列表头已经足够。

空 Γ 的基例也有效：`g_0=g_m=a+2=gammaFinish`。只保证 declared boundary 单元的值相等就够了，毋须先证明两个 boundary 大整数相等。

## 3. 单任务的原公式见证重建

### 3.1 显式 token 块及 14 个坐标

设旧任务起点 `a`，全长 `L=finish-a`，suffix 头偏移 `d=witnessFinish-a`，suffixCount 为 `q`；因此 `L=d+1+q`。令 `epsilon=0` 当 tag=10，否则 `epsilon=1`。

在新起点 `p` 写一条长度 `L+epsilon*r` 的任务块：

- epsilon=0：复制原区间的所有 `L` 个 token。
- epsilon=1：偏移 `j<d` 复制原单元；偏移 `d` 写 `q+r`；其后复制原 suffix 的 `q` 个正文 token，再写 `R` 的 `r` 个 token。

新坐标逐一为：

- start 为 `p`，finish 为 `p+L+epsilon*r`，tag 不变；
- gammaFinish、firstFinish、secondFinish、witnessFinish 分别为 `p+(旧值-a)`；
- gammaCount、firstCount、secondCount、witnessCount 不变；
- suffixCount 为 `q+epsilon*r`；
- Γ boundary 第 `j` 项为 `p+(g_j-a)`，条目宽度为最终 `N'`；gammaBoundarySize 取这个新整数的真实二进制长度。

所有差都在已由 TaskCore 得到的有序位置之间作自然数差，不把可能为负的整体平移量塞进 PA 自然数项。

逐项验证原 17 参数 TaskCore：首 tag 单元保持；Γ 头及每个内层列表的头/正文复制，各个 NatListSlice 的等式在新相对位置成立；first、second、witness 三个 flat slice 保持；suffix 的新结束等式为 `p+d+1+q+epsilon*r=p+L+epsilon*r`。Γ boundary 的地址均≤N'，规范固定宽度打包给实际 `ell(Bγ)≤(m+1)*N'`。

这里 `m+1` 是 boundary 的项数，`N'` 是一项的位宽；没有用 boundary 大整数的数值代替位数。

### 3.2 Parse 的全部坐标

原 ParseShape 是 tag=10 且五个 count 都为 0。其任务块严格是六个 token：

`[10,0,0,0,0,0]`。

放在 `p` 时，gammaFinish=`p+2`，firstFinish=`p+3`，secondFinish=`p+4`，witnessFinish=`p+5`，finish=`p+6`。Γ boundary 只有一项 `p+2`，不能误用整数 0 表示这个非零起点。这个六单元块在追加 R 时不加任何 token，因此新 ParseShape 的所有零等式仍真。

### 3.3 等任务经 eta_R 后仍满足实际整片等式

给定两条旧合法 TaskCore 及其完整切片等式，用第 2 节得到相同 tag、相同 `d,q,L` 及原正文相等。

若 tag=10，两边均完整复制。否则新块长度均为 `L+r`：对新偏移 `j<L+r` 分成旧前缀、更新后的 suffix 头、旧 suffix 正文、追加 R 四段；四段分别取旧读数相等、`q+r=q+r`、旧读数相等、同一 R 的读数相等。

由此引入新 `SameTableSlicesEq`，或者在两张不同新表上引入 `CrossTableSlicesEq`。宽度变化时，先证明单元自然数相等，再对新宽度范围的位建立等式。不能直接扩大旧位量词上界。

## 4. 任务栈的 PA 前缀构造

旧 `TaskListRowsGraph` 的每个索引给出 14 个有界存在见证。以索引为变量在 PA 内收集有限个元组：归纳命题存放已选前 `j` 个元组；第 `j` 步用原有界全称的实例消去存在量词，将该元组追加到工作表。实际 Γ boundary 的逐项读数及任务 token 则由原 T 直接读取。

设要构造的新任务序列有 `n` 项，各任务块长度为 `l_i≥6`。栈块起点为 `z`，先写头 `n`；定义

`b_0=z+1`，`b_(i+1)=b_i+l_i`。

长度归纳的不变量是：前 `i` 个任务占满 `[z+1,b_i)`，每个第 `j<i` 项在 `[b_j,b_(j+1))` 满足其指定 TaskCore，且边界严格递增。之后写规范栈 boundary，第 `i` 项就是 `b_i`。

最终 token 表仍使用先前的 PA 打包归纳：第 `j` 单元写 `a_j<2^u'`，令 `T_(j+1)=T_j+a_j*2^(j*u')`，不变量 `T_j<2^(j*u')` 且此前单元读数全部正确。Γ boundary 与任务栈 boundary 也用这个归纳，以最终 `N'` 为条目宽度。

这些指定块的原始长度先决定 N'，boundary 整数随后才生成，没有循环依赖。可先放任意有限背景区、proof-root 块、source 栈块、target 栈块，再统一生成全部 boundary；也允许把不同表合并为一张表，因为原分离表公式没有“表必须不同”的要求。

把 `N',u'`、所有新 TaskCore 的 14 个坐标、栈 boundary 及端点、有关的少量参数一起取有限最大值 M。选择 `H` 使 `M≤2^H`，令 `V=2^H`；特别有 `N'≤V`。每个 TaskBoundedAt 的所有界逐项满足，TaskBoundedRow 用这 14 个数引入存在量词，再引入 `∀i<n`，就得到新的实际 `TaskListRowsGraph(...,H,V)`。新 Stack StructuredListLayout 的见证是 `bodyStart=z+1` 和上述严格递增 boundary。

若外层 StateCore 还要求任务 boundary 的真实长度界，也由 `n+1` 项、每项宽 N' 的规范打包得到。空栈仍包含头 `[0]` 和 boundary 的唯一项 `z+1`。

## 5. 原 TaskBoundedRowsEq 的见证输运

源码 `VerifierTaskListDropRows.lean:30` 的关系只有四个有界端点、两张 boundary 的四个 Entry 以及整个任务区间的 SameTableSlicesEq；它本身不验证 TaskCore。

在两边 TaskListRowsGraph 和正确索引范围下，由 Entry 唯一性把它的四个端点识别为这两条任务的实际边界。第 3.3 节将两条原整片相等搬运为两条新任务整片相等。

新关系的四个存在见证直接取新 source/target 栈 boundary 在相应索引及后一索引的规范读数。它们均≤N'≤V；四个 Entry 和新的 SameTableSlicesEq 逐项引入。因此这一步是原 `compactNumericVerifierTaskBoundedRowsEqDef` 的完整见证构造。

对于两边都落在新增 K0 区的索引，也用同一方式取四个端点；两条任务是同一原背景任务的字节复制，因此新的整片等式直接成立，不对 K0 的 suffix 再追加 R。

## 6. ReplaceHeadRows 的续延引理

设原 `ReplaceHeadRows(source,target,V,p)` 成立。其准确合取是

`1≤s`，`s+p=t+1`，以及对每个 `i<s`，若 `1+i<s`，则比较 source 的 `1+i` 行与 target 的 `p+i` 行。

新 source、target 计数分别为 `s+c,t+c`；prefixCount 保持 p。新首个界由 `1≤s` 给出；新长度方程为

`(s+c)+p=(t+c)+1`。

现固定新公式中的任意 `i<s+c`，假设 `1+i<s+c`。分两种情形。

1. `1+i<s`。这给出旧全称条件需要的 `i<s`，且由旧计数方程得到 `p+i<t`。实例化旧 ReplaceHeadRows，取得旧 source[1+i] 与 target[p+i] 的实际 TaskBoundedRowsEq，再用第 5 节构造新同索引行等式。
2. `s≤1+i`。取 `j=1+i-s`。新尾范围给 `j<c`；旧计数方程给 `p+i=t+j`。因此新 source 的 `1+i=s+j` 行和新 target 的 `p+i=t+j` 行都是 K0 的第 j 个任务。使用第 5 节的背景任务复制关系。

这两个分支覆盖新有界全称的全部有效实例，故得到原 ReplaceHeadRows 的新实际公式。特别没有遗漏旧栈尾与 K0 的接缝。

边界情形：`s=1` 时旧尾为空；有效新尾全部进入第二种情形。`p=0` 时 `t=s-1`，同一算式仍成立；`s=1,p=0,t=0` 时就是比较两份 K0。`c=0` 时第二种情形无实例。

本引理不需要 p 只取 2 或 3，因此也覆盖叶调度使用的空前缀。

## 7. DropRows 的续延引理

原 `TaskListDropRows` 的准确合取是

`d≤s`，`s=d+t`，以及 `∀i<t, TaskBoundedRowsEq(source[d+i],target[i])`。

对两个新栈仍使用同一 consumed=d。长度方程变成 `s+c=d+(t+c)`。固定 `i<t+c`：

- 若 `i<t`，用旧 DropRows 实例和第 5 节。
- 若 `t≤i`，令 `j=i-t<c`，则 `d+i=s+j`；两边都对应 K0[j]，引入背景任务的行等式。

这逐项给出新的实际 DropRows。`d=s,t=0` 时整个新 target 就是 K0，仍成立；`d=0` 时是完整栈等式的续延。

源码中 `tableWidth` 在 DropRows 的公式体里没有使用；幂关系来自外围 TaskListRowsGraph。这里统一选新的 H,V，并以外围图提供 `V=2^H`，不从 DropRows 本身推导不存在的指数合取。

## 8. 完整 TaskCrossTableBridgeGraph

假设旧 proof-root 任务与旧 state 中 combine 任务均满足 TaskCore，且实际 TaskCrossTableBridgeGraph 成立。它给出 tag 相等及五个字段的跨表带头切片等式。

两边同时作 eta_R。tag 相等保证两边选择相同 epsilon。Γ、first、second、witness 四段的原始 token 内容完整保留，只重建位置；每段使用同一长度作为新 CrossTableSlicesEq 的 count，并用旧等值所得的逐单元数值相等引入新位量词。

suffix 一段若 epsilon=0 也直接复制。若 epsilon=1，旧带头切片相等先给相同 q 及相同旧正文；新两段均为 `[q+r]++Q++R`。取 count=`1+q+r`，对 offset=0、旧正文范围、新 R 范围分支引入新 CrossTableSlicesEq。五段加上 tag 等式正是原 20 参数图的全部合取。

这里证明的是“两边都变换后仍桥接”。在 r>0、tag≠10 时，原任务与其 eta_R 一般不满足原完整桥：suffix 头 q 与 q+r 不等。实际 schedule 应桥接已经变换的 proof-root 与已经变换的 combine 任务，不能继续引用旧根的整片。

若两个源表采用不同宽度，新表也可以不同。逐单元值相等的证明会在 `bit<sourceWidth'+targetWidth'` 的真实上界下处理宽度之外的零位；同表版本是其特例。

## 9. OneParseSchedule 的逐项构造

原 39 参数 `.mkSigma` 公式在 `VerifierParseScheduleFormula.lean:23`。从实际联合图取得：两个栈的布局/TaskListRowsGraph、旧 one schedule、proof-root 的 TaskCore，以及 root/combine 的完整跨表桥。

需要强调一个源码细节：裸 schedule 的 `rootTag∈{4,5,6,7,8}` 本身不直接声明 `combine.tag=rootTag`。实际 `VerifierOneParseSuccessNonLeafStateGraph` 中，TaskCrossTableBridgeGraph 的首个合取提供这个等式。其 schedule 子式传入的 rootStart/rootFinish 还是 combine 自己的区间，末尾同表切片等式在这个实际安装中是反身实例；真正连接 proof-root 的是跨表桥。本文使用这组原合取，不由裸标签析取推出多余的语义事实。

旧 ReplaceHead 的 p=2 给 `t=s+1`，所以 target 的第 0、1 行确实存在。由旧 indexed TaskBoundedAt 和 ParseShape，第 0 行是 `[10,0,0,0,0,0]`。第 1 行的 combine 与 root tag 相同，因而不等于 10。

按第 4 节构造两个新栈；第 6 节给 p=2 的新 ReplaceHead。新 target 的前两项分别是原 Parse 和 eta_R(combine)，K0 不会插入这两个位置。

现在依原公式顺序引入：

1. 保留 rootTag 的五择一数值等式。
2. 引入刚构造的 p=2 ReplaceHead。
3. 取新 target 第 0 项的 14 个规范坐标，按第 4 节引入 TaskBoundedAt(index=0)；第 3.2 节给出全部 ParseShape 等式。
4. 取新 target 第 1 项的 14 个规范坐标，引入 TaskBoundedAt(index=1)。combine 的 suffixCount 已增加 r，其余字段 count 保持。
5. 对实际外层安装，把 schedule 的 rootStart/rootFinish 参数取新 combine 区间，末尾 SameTableSlicesEq 以该区间长度和逐位反身等式构造。若调用者另指定同表的新 root 副本，则用第 3.3 节的完整任务等式。
6. 对独立 proof-root 表中的新根与 state 表中的新 combine，使用第 8 节重建完整 TaskCrossTableBridgeGraph。

所有坐标采用同一个新的 V 绑定。这给出原 one schedule 及其与原 root 桥的联合结论，没有使用外部 one-step 的 Nat 正确性。

## 10. TwoParseSchedule 的逐项构造

原公式位于同一个 `VerifierParseScheduleFormula.lean`，参数数为 53。标签条件为 rootTag=3 或 9，ReplaceHead 的 p=3，目标前缀严格为 Parse、Parse、combine。

旧长度方程给 `t=s+2≥3`，因此前 0、1、2 项均有合法索引；前两项由各自的 TaskBoundedAt 和 ParseShape 都是六单元空字段 Parse。跨表桥给 combine.tag=rootTag≠10。

按第 4 节构造两个新栈；第 6 节给 p=3 的 ReplaceHead。分别在新 target 的 0、1、2 三个位置，以各自的规范 14 坐标引入 TaskBoundedAt；前两项按第 3.2 节引入 ParseShape，第三项按第 3.1 节改 suffix。标签析取保持。末尾 schedule 切片采用新 combine 的反身实例，或已构造的新 root 副本等值；独立 proof-root/state combine 的真实连接再由第 8 节给出。

与 one 情形一样，这些步骤只是在已经证明的栈归纳上引入固定数量的原合取，没有新的 parser 语法归纳。

## 11. 已闭合的范围与下一道接缝

本轮的 PA 局部结论是：在旧 actual stack core/row 前提下，可以构造 `map(eta_R,K)++K0` 的新规范存储，保持所有需要的任务行比较，搬运 DropRows 和 ReplaceHeadRows，并由新 parser-root 与 combine 同时变换来满足完整 TaskCrossTableBridgeGraph。由此 one/two schedule 及其真实跨表连接已纸面闭合。

真正需要的可变长度归纳已在本文展开：Γ 字段分界、有限行见证收集、任务栈前缀长度、固定宽度打包。ReplaceHead 和 Drop 的新增量词范围则由旧段/K0 段的两个明确索引分支证明。其余 schedule 条款为固定次数的存在见证引入与合取组合。

尚未由本文完成的是 `VerifierParseSuccessNonLeafCommonRows` 的值栈及两段剩余输入输运、各叶与 combine 规则的整个状态图，以及全运行组装。
从接受轨迹截取 Finish 前缀已由 [独立前缀稿](paper_direct_finish_prefix_20260905_zh.md) 补齐。
这些结果还需要接合后才能组成实际 429 列 G 的全运行矩阵；不能以本轮 schedule 局部结论替代完整条件 (3)。
