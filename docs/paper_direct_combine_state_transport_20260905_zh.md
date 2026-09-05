# 三个 combine-success 原状态图的 PA 续延输运

日期：2026-09-05。本文只作数学纸面推导，不新增 Lean。

结论：给定实际 429 列步骤中已经成立的 simple、allShift 或 exsCut 成功分支，可以在两条剩余输入分别追加 R、S，旧任务栈施加 eta_R 后追加 K0，旧值栈追加 V0，构造同一成功分支的新 429 列行。规则的结果 Boolean 原样保留，包括结果为 0 的成功步骤。本文不借助 Nat exactness、typed verifier 语义或反射来获得原算术图。

## 1. 原公式与准确接口

以下文件都在 `integration/`，文件共同前缀为 `FoundationCompactNumericListedDirect`。

| 文件尾名 | 本文使用的实际公式 |
| --- | --- |
| `VerifierCombineStateGraph.lean` | 93 参数 StateGraph：两个 StateCore、TaskBoundedHead、Frame、Branch |
| `VerifierCombineStateFrameRows.lean` | currentTag=0、taskCount≥1、headTag≠10、两值栈控制界相等、输入整片相等、TaskDrop(1) |
| `VerifierCombineBranchRows.lean`、`VerifierCombineSuccessRows.lean` | simple/allShift/exsCut 三个成功析取与 nextTag=0 |
| `SimpleCombineTransitionRows.lean` | 规则结果之外，实际 source 第 0 项以及 tag=3 时第 1 项的 HeadEq |
| `SimpleCombineRuleRows.lean` | tag=3、4、7；分别 PushDrop(2)、PushDrop(1)、PushDrop(1) |
| `AllShiftCombineRuleRows.lean` | tag=5、8，均 PushDrop(1) |
| `ExsCutCombineRuleRows.lean` | tag=6、9，分别 PushDrop(1)、PushDrop(2) |
| `FormulaTransformTotalExactFormula.lean` | 固定燃料的实际公式变换全轨迹 |
| `FormulaShiftExactListRows.lean`、`FormulaShiftListRow.lean` | 每个原始公式的全轨迹、候选结果、success 表和整表默认结果 |

前提是完整旧 CombineStateGraph 并选择一个成功析取；裸 RuleCheck 不提供状态布局或源值栈连接，不能替代该前提。所有有限数组写法均表示 PA 内通过读数公式编码的有限数组。

把两个旧 StateCore 的内容记为 `(P,C,K,V,running)` 与 `(P1,C1,K1,V1,running)`。给定有限 token 数组 R、S，以及带实际 TaskCore/ChildResultCore 见证的续延 K0、V0，构造目标内容

```text
current'=(P++R,C++S,map(eta_R,K)++K0,V++V0,running)，
next'=(P1++R,C1++S,map(eta_R,K1)++K0,V1++V0,running)。
```

eta_R 采用 [任务栈稿](paper_direct_schedule_transport_20260905_zh.md) 的定义：tag=10 时完整保留任务，tag≠10 时只将 suffix 追加 R。K0 不再变换第二次。

本文复用任务栈稿第 2—7 节的 TaskCore/DropRows 构造，以及 [值栈及 parse-state 稿](paper_direct_parse_state_transport_20260905_zh.md) 第 2—4 节的 ChildResultCore、RowsEq、HeadEq 与 PushDropRows 构造。下面补的是原 RuleCheck 和公式变换的完整连接。

## 2. 共同布局：旧表前缀保留，边界整数重新编码

令旧 token 表参数为 T、u、N。先取其前 N 个实际单元

`a_i=(T div 2^(i*u)) mod 2^u`，`i<N`。

新表的前 N 个单元完整保留这些自然数。其后排列两个新状态及需要的其它新背景块。旧公式变换轨迹、候选公式、空列表和其它辅助列表的原始 token 块都留在旧地址，既不重新运行也不改变其内部剩余输入。这一点与外层 verifier 的 P/C 追加不同。

两个新状态的原始长度由 P/C、R/S、eta_R(K/K1)、K0、V/V1、V0 决定，均不取决于 boundary 的整数值。先决定整个长度 N'，再选择 u' 容纳所有新旧单元，最后用前缀打包归纳构造 T'。因此 N'≥N，且旧地址处的自然数读数不变。整个构造也允许加入已经指定的有限背景区。

每个 boundary 按其实际被读取的有限地址序列重包。若旧 boundary B 的声明读数是 b_0,...,b_q，则新值为

`B'=sum_(i≤q) b_i*2^(i*N')`。

保留旧地址时 b_i 不变；指向新状态块时使用该块新的相对位置所确定的地址。随后取 B' 的真实位长作为 size 见证。旧的高位未声明内容不作为新数据保留；原有真实长度界以及各 Entry 保证声明范围内的原读数足够。

对同一公式参数的多次使用，使用同一个重编码后的地址数组；若不同旧见证给出同一存储块的不同 boundary 整数，先以 Entry 唯一性和列表长度头归纳对齐被声明的读数，再取同一新规范 boundary。这里只识别实际读数，不要求不同旧大整数先相等。

所有实际地址≤N'，故一个 q+1 项规范 boundary 满足 `ell(B')≤(q+1)*N'`。即使 q=0，也要编码唯一端点；只有原公式没有读取该端点时，才允许选任意值。不能把每个空列表的 boundary 一律取 0。

这里“实际地址”仅指被原布局或行公式定位的端点，不把任意未读取的 boundary 位段当成≤N 的地址。例如空 syntax tail 的 Drop/Cons/TripleBoundary 全称都可能无实例，此时可以将未约束的 boundary 规范化为 0；若同时还有 StructuredList 或一个明确端点 Entry，则必须保留它所要求的端点。非空 tail 的每个端点由原 Drop 的有界四端点见证给出≤N。各角色按其实际读取范围选择，不能从一条 size≤N 的约束单独反推原 boundary 整数≤N。

状态栈、内层公式列表、公式变换 stateBoundary、syntax task 的 tailBoundary 都使用这一操作。特别，`FormulaShiftExactListRows` 的 successTable 的单元宽度是 N，而非 1；其新值必须为 `sum_(i<g) success_i*2^(i*N')`。success_i 仍为原来的 0 或 1。

## 3. 基础读数与规则条件的双向等价

### 3.1 有界列表操作的显式输运

固定新旧两个对应的合法 flat list 或列表数组。对应是：count 相同，每个列表长度头和正文的自然数读数相同；位置和 boundary 的位宽允许不同。

对实际 NatListAtRows，使用相同 index，取新 boundary 在 index、index+1 的两个端点。原 `index<count` 保持；TokenCell 的长度为 1，新读数为相同值。这给正向。反向从任意新端点见证，用 Entry 唯一性把它们强制为规范新端点，再取对应旧端点，故也成立。

对 SameRows、DropRows、Cons/UnconsRows，保留所有列表 count 和消费数。原有界全称的 index 范围因此不变。每个行等式通过上述端点唯一性和逐单元相同转移；需要的四端点或六端点见证直接取相应规范 boundary 读数。SyntaxTask 的单项是固定三个自然数单元，逐项读取 kind、binderArity、repeatCount 即给同样的构造。

对 `NatListAppendSlices`，保留等式 `targetCount=leftCount+rightCount`，在目标正文按 offset<leftCount 与 leftCount≤offset 分两段。两段的实际 SameTableSlicesEq 分别读取左、右正文。`AppendSourcePrefix` 再保留 consumed≤sourceCount，只使用 source 的前 consumed 项；`AppendOneValue`、`AppendTwoValues` 在最后一项或两项使用同一指定自然数；`AppendMappedSourcePrefix` 将第一个新项固定为 mappedHead，其余项取旧 source 的相应读数。

所有位等式均先从旧式取得自然数单元相等，再对新位宽引入位等式，不能直接扩大旧位量词范围。所有被访问的正文位置由列表长度方程、消费数界或构造条件限制在其合法片段内；不会把旧表 N 之后未定义的单元当成应保持的数据。

### 3.2 Membership、Subset 和 SetEq

`FormulaMemberRows` 的见证先选择一个 `index<gammaCount`，然后由 Γ boundary 的两个 Entry 确定该带头公式片段。新旧 Γ 项数不变，故保留同一 index，重建两个端点及整片相等即可。反向时，新端点由 Entry 唯一性强制为该项实际端点；它对应旧 Γ 的同一项，因此新存在见证不能因为 N' 较大而凭空多出一个成员。

`FormulaSubsetRows` 对左 Γ 的每个 index 引入上述 Membership；SetEq 是两次 Subset。`FormulaSetEqConsRows` 的准确三部分为：actual 每项属于指定 head 或 tail、head 属于 actual、tail 是 actual 的子集。`FormulaSetEqTwoConsRows` 多一个指定 head，逐项采用相同推导。这些定义不要求无重复公式，本文也不引入去重假设。

### 3.3 构造公式的 Membership

`FormulaConstructorMembership` 的候选仍是同一 Γ 索引。Unary 图检查该项的长度头为 `bodyCount+1`、正文首项为指定 tag，余下正文等于 body。Binary 图检查长度头为 `leftCount+rightCount+1`、首项为指定 tag，并在固定偏移 `leftCount` 处接合两段正文。

这些长度头、tag 和每个正文单元都保持，故两个构造 Membership 双向等价。尤其在反向中，构造的长度头使所有正文访问都落在合法 Γ 项内，不会因新表有额外空间而制造旧表中不存在的构造匹配。

因此 And/Or/Wk/All/Shift/Exs/Cut 中规则 Boolean 右侧的所有集合条件，都在对应的相同原始 token 内容下双向等价。若旧检查写作 `b≤1 AND (b=1 IFF A)`，保持 b 并使用 `A IFF A'` 即得到新检查；此推导同时覆盖 b=0 和 b=1。

## 4. 公式变换全轨迹的实际重编码

本节的对象为原 `compactFormulaTransformTotalExactBoundedGraphDef`，不是替代的计算谓词。其依赖链为：

```text
TotalExactBoundedGraph
→ TotalTraceBoundedGraph
→ InitialDefaultFinalBounded + AdjacentRowsBoundedGraph
→ StateAtRows + StateCore + InitialRows + FinalGetDOutputRows
  + AdjacentStepRowGraph + StepRows + StatusValidBounded。
```

### 4.1 不变参数与有限见证收集

mode、binderArity、inputCount、expectedOutputCount、witnessCount 均保持；输入、输出和 witness 的正文保持。外层 verifier 的新 task.first 或 task.witness 位于新地址时，仅把本节对应的输入/witness 参数接到这些新片段；旧内部状态块仍保留在旧表前缀。

燃料仍是 `f=16*(inputCount+1)^2+8`，stateCount 仍是 f+1。无需增加 fuel，也无需向公式变换状态中追加 R/S。

从原 `∀rowIndex<f` 的有界存在式，在 PA 内以行数作归纳，收集每行两个 14 项 StateAt 描述及 9 个 step 见证。每一步仅实例化原全称并将见证元组加入有限工作表。各个 StateAt 的外层 Entry 使相邻行的共同状态片段有相同 start/finish；其内部各列表头又确定各 count 和字段分界。新 stateBoundary 用这些原端点按 N' 位重包。每个原始状态块复制在原地址，所以既有重叠或复用的原片段仍然相容。

### 4.2 StateCore 与七个 syntax witness 槽

`FormulaTransformStateCoreGraph` 明确为 parser 状态后接一个带头输出 flat list；parser 状态又是 tokens 列表、三单元 syntax task 列表、双 Option 状态的固定布局。它没有要求输入是一条合法逻辑公式。

复制原始块后，start/finish、parserFinish、tokensFinish、tasksFinish、各 count 都保持。三个 boundary 按第 2 节重包，三个 size 取真实新位长。ProductSplit 的旧有序地址仍≤N≤N'；各 StructuredList、UnitBoundaryRows、实际长度界逐项成立。这就是新 StateCore 的全部合取。

七个 syntax witness 槽不能全部原数复制，须按所选分支解释：

| syntax 分支 | 槽位的实际含义及重建 |
| --- | --- |
| Done | slots 0/3 为两个 status 输出起点，保持；1/4 为其输出 boundary，重包；2/5 为 size，重算；6 为输出 count，保持 |
| Empty | slot 0 为 next status 输出起点，保持；1 为其 boundary，重包；2 为 size，重算；其它未用槽可取 0 |
| Repeat | 0/1 为 binderArity、repeatCount，保持；2 为 tailBoundary，重包；3 为 tailCount，保持；4 为 size，重算；5 为 decrementedCount，保持 |
| Term | 0 为 binderArity，保持；1 为 tailBoundary，重包；2 为 tailCount，保持；3 为 size，重算；4/5/6 为 tag、argument、functionCode，保持 |
| Formula | 与 Term 相同的前四槽；4/5/6 为 tag、relationArity、relationCode，保持 |
| Invalid | 0 为 tailBoundary，重包；1 为 tailCount，保持；2 为 size，重算；3/4/5 为 kind、binderArity、repeatCount，保持 |

这些位置直接来自 `ParserSyntaxStepFormula.lean` 的 done/empty/repeat/term/formula/invalid 替换向量。

### 4.3 原 StepRows 的六类分支

`FormulaTransformStepFormula.lean:78` 的原析取分为四类 quiet parser 与 Term、Formula 两类。

- Done：failed 子式保留原 `[1,0]`；completed 子式保留 `[1,1]` 以及后面的带头剩余 token 列表，用重包后的输出 boundary 引入同一 CompletedStatusSameRows。输入、任务列表的 SameRows 按第 3.1 节保持。
- Empty：原 tasksCount=0 仍为 0；current running 状态 `[0]` 保持；next completed 的输出列表仍逐项等于 current tokens。取上表 Empty 三槽，重新引入原 CompletedOutputSameRowsWithSize。
- Repeat：binderArity、repeatCount、decrementedCount 的等式不变；Uncons、Drop(2)、两个 TaskAt 和 SameRows 按第 3.1 节保持。无论 repeatCount=0 还是正数，都沿原析取重建。
- Invalid：kind≠0、1、2 的数值条件保持；Uncons 与原 failed 状态保持。
- Term：原 `tokensCount≤1`、`2≤tokensCount`、`tokensCount≤2`、`3≤tokensCount` 的分段条件全部保持。tag、argument、functionCode 的读取及函数码检查也保持；消费 2、消费 3、失败和压入 repeat task 的各个原子式均由 At/Drop/Cons/状态片段重建。包括失败子分支，不能假定整条 transform 只经过成功 parser 分支。
- Formula：空输入、关系头、常量 tag=2/3、二元 tag=4/5、量词 tag=6/7、非法头的原分支均保留。相应的消费数为 0、3、1、1、1 或失败分支规定的 0；所有读取、算术 guard、TaskDrop/TaskAt/TaskCons 都按第 3.1 节重建。

因此 quiet 分支再接原 OutputSameRows；其余两类还要接以下真实输出图。

`FormulaTransformTermOutputRows` 首先要求 `currentTokensCount=consumedCount+nextTokensCount`。两个 count 保持，因此 consumedCount 保持。对本次实际使用的 modes：

| mode | Term 输出原子图 |
| --- | --- |
| 0（free） | 在 `consumed=2,tag=0,argument+1=binderArity` 时追加 1、0；否则若 consumed=2、tag=1，追加 1、argument+1；其余追加原 consumed 前缀 |
| 1（shift） | consumed=2、tag=1 时追加 1、argument+1；其余追加原前缀 |
| 2（substitute） | consumed=2、tag=0、argument+1=binderArity 时追加指定 witness 正文；其余追加原前缀 |
| 3（negation） | Term 使用原 consumed 前缀 |

每一行在 consumed=0 时先进入 OutputSameRows。表中的真假 guard 只含被保留的自然数。输出 append 图按第 3.1 节逐单元重建；mode=2 的 witness 即使移到新 task 的地址，正文不变，AppendSlices 的右正文比较仍真。

`FormulaTransformFormulaOutputRows` 对 modes 0、1、2 追加原 consumed 前缀；mode=3 保留 `CompactNegationFormulaTagGraph(tag,mappedHead)`，以相同 mappedHead 替换所消费前缀的首项。该 TagGraph 只有有限自然数析取，不含 token 地址。AppendMappedSourcePrefix 的首项和余下逐项均保持。consumed=0 仍使用 OutputSameRows。

由这些原分支和同一所选析取，逐行得到实际新 StepRows，再与两个新 StateAt 合取成 AdjacentStepRowGraph。没有用 Nat 上的运行等式推出这些公式。

### 4.4 初态、最终默认输出与 success 的反向

初态 `UnifiedParserInitialStateRows` 的参数准确为 `taskKind=1,binderArity,repeatCount=0`。保留原初始状态块；其 tokens 与重新定位后的输入逐单元相同，故原 SameRows 成立；初始 outputCount=0 保持。InitialDefaultFinal 中三个 reservedOutput 见证要求等于 0，仍取 0，不把它们重编码成地址。

StatusValidBounded 的三个状态类别是原始 token 片段 `[0]`、`[1,0]`、`[1,1,c]++A` 且 |A|=c。前两个直接保持。第三个的 outputStart、outputCount 和正文保持；boundary 重包，size 重算后引入原有界存在式。

FinalGetDOutputRows 的原析取也保持：completed 且剩余列表为空时，expectedOutput 与累计输出的 NatListSameRows 保持；running、failed、或 completed 剩余列表非空时，用同一 DefaultStatus 分支并保留 expectedOutputCount=0。这里剩余列表与累计变换输出是两个不同列表，不能把两者混同。

`TotalOutcomeRows` 额外要求 `success≤1` 且

`success=1 IFF UnifiedParserEmptyFinalStateBounded`。

扩大 valueBound 后，这个 IFF 不能只靠正向见证输运。实际空最终式的存在见证由 CompletedStatusPrefix 及长度头唯一确定：在 status 起点 a 处，原始片段必须恰为 `[1,1,0]`，outputStart=a+2，outputBoundary 只有一项 finish=a+3，outputBoundarySize=ell(finish)。反过来该片段就给这三个见证，且 NatListSameRows 的两个 count 都为 0。

原 TotalTrace 自带 `tableWidth≥(N+1)*N`，以及 `valueBound=2^tableWidth`。合法旧状态使 N≥1，三个旧规范见证均≤N，故均≤旧 valueBound。这证明旧 EmptyFinalBounded 已等价于上述真实三单元片段，而非可能被旧界截断的性质。新旧 status 原始片段相同，所以新 EmptyFinalBounded 反推旧式也成立；原 success=0 因而不会在扩界后变成 1。

### 4.5 控制界与原有界量词

收集所有新 endpoint、state 和 step 见证，包括完成态 status 输出的有界见证；取有限最大值 M。选 H 满足 `(N'+1)*N'≤H`，且 M≤2^H，令 V=2^H。每个先前已重建的无界见证现在实际满足对应原界，可以依固定次序引入原 37 项 step 存在块、初末态存在块及原 `∀rowIndex<f`。

这样逐项获得新 AdjacentRowsBoundedGraph、InitialDefaultFinalBounded、TotalTraceBoundedGraph，最后代入未变的燃料项得到原 TotalExactBoundedGraph。total outcome 的末态描述采用同一末态实际地址和重包 boundary，并用第 4.4 节的 IFF 保留 success。

新 H/V 可以统一容纳有限多个公式变换轨迹；边界整数只由已定 N' 与原地址决定，H/V 在它们之后选择，没有大小定义循环。本节只证明 PA 内存在性和输运，不从原大见证推断任何多项式位界。

## 5. 逐公式 shift 的原整表构造

实际 `FormulaShiftExactListRows` 对每个 `i<g` 给出 29 个有界见证。源 Γ 可以来自新 task，也可以来自新/旧对应的 premise Γ；它的公式项数 g 及每个公式正文保持。

对每个 i：

1. 从原源 Γ 的两个 Entry 与原 NatListWitnessRows 读出该公式的长度头和正文。在新源 Γ 取同一 i 的两个端点，重建 NatListWitnessRows 及其 unit boundary。
2. 候选公式原始块保留在旧表前缀；重包 candidateBoundary 的对应两个端点、其 inner boundary 及 size。原候选输出数值保持，包括默认空候选。
3. 使用第 4 节输运原 TotalOutcomeRows。这里参数严格为 mode=1、witnessCount=0、binderArity=0；输入是该项的 inner boundary，输出是其候选 inner boundary。
4. 保留 success_i，重新打包以 N' 为单元宽的 successTable，得到该行的实际 Entry。候选/源外层 Entry、两个 NatListWitnessRows、TotalOutcomeRows 合起来恰是原 40 参数 ShiftListRow。

在 PA 内以 i 收集这些有限见证，再选 shiftWitnessBound 容纳全部新 29 项坐标、各行 H/V 和末态坐标，便得到原有界全称。

原整表末尾是明确析取：若全部 success_i=1，则候选列表与 expected 列表逐项 SameRows；若存在 success_i=0，则 expectedCount=0。保留同一全称证明或同一失败索引，前者用第 3 节重建 SameRows，后者保留 expectedCount=0。expected 列表已有的 RowsWellFormed 也按同样列表重编码得到。

g=0 时，逐行全称无实例；“存在失败项”不能成立，所以旧式已经提供空候选与 expected 的 SameRows，从而 expectedCount=0。新图沿全成功分支成立；不能任意选择失败分支。源码未要求 candidate Γ 额外带一个外层 count 头，故本构造也不添加这种隐藏前提。

## 6. 七条规则的实际 Boolean 与源值栈连接

共同设置：task 的 Gamma、first、second、witness 原始内容保持；suffix 追加 R 不参与任何以下规则检查。right 子结果始终指旧值栈第 0 项；二元规则的 left 指第 1 项。追加 V0 不改变这些位置，因为原规则已给 sourceCount≥消费数。

选择的 ruleWitness Γ 可以保留其旧原始块并重包 boundary，不必把独立 witness Γ 与新值栈中的副本放在同一地址。原 HeadEq 经值栈稿第 3 节保持实际逐项同值和 Boolean 相等。这是 premise 与真实 source 值栈的连接，不能省略。

| taskTag | 必须保持的实际规则检查 | 栈更新 |
| --- | --- | --- |
| 3 And | 构造 tag=4 的 `first,second` 属于 task Γ；left 集合等于 first::Γ；right 集合等于 second::Γ；两个 child Bool=1 的合取与 resultBool 的 IFF | PushDrop(2) |
| 4 Or | 构造 tag=5 的 first、second 属于 Γ；right 集合等于 first::second::Γ；right Bool=1 与 resultBool 的 IFF | PushDrop(1) |
| 7 Wk | right Γ 为 task Γ 的子集；right Bool=1 与 resultBool 的 IFF | PushDrop(1) |
| 5 All | first 的全 free 轨迹；task Γ 的逐公式 shift；构造 tag=6 的 first 属于 task Γ；right 集合等于 freed::shiftedΓ；right Bool=1 与 resultBool 的 IFF | PushDrop(1) |
| 8 Shift | **right premise Γ** 的逐公式 shift；task Γ 与 shiftedΓ 集合相等；right Bool=1 与 resultBool 的 IFF | PushDrop(1) |
| 6 Exs | first 的全 substitute 轨迹，以 task.witness 为替换项；构造 tag=7 的 first 属于 Γ；right 集合等于 substituted::Γ；right Bool=1 与 resultBool 的 IFF | PushDrop(1) |
| 9 Cut | first 的全 negation 轨迹；left 集合等于 first::Γ；right 集合等于 negated::Γ；两个 child Bool=1 与 resultBool 的 IFF | PushDrop(2) |

All 与 Shift 的 shift 输入不同，表中已分别注明，不能统一误接到 task Γ。

三个单公式 transform 的实际参数为：All 的 mode=0、binderArity=1、空 witness；Exs 的 mode=2、binderArity=1、task.witness；Cut 的 mode=3、binderArity=0、空 witness。Exs 的 witnessStart 是 task.secondFinish，witnessFinish 是 task.witnessFinish；并不是 firstFinish。

All 的 formulaBoundary 对应 `[task.gammaFinish,task.firstFinish)`，其 count 为 task.firstCount；freed 的 NatListWitnessRows 无条件存在。ExsCut 的公式、transformed 输出、空列表三个 NatListWitnessRows 都在 tag 析取之外，全部按第 2—4 节重建，不能在 resultBool=0 时省去。

And/Or/Wk 由第 3 节的双向等价直接保留 resultBool。All/Shift 先用第 4—5 节得到无条件变换和 shift 图，再用第 3 节保持 IFF。Exs/Cut 同理先重建无条件全轨迹，再保持集合条件 IFF。

对每条规则，以相同的消费数 d 和相同 resultBool，应用值栈稿第 4.2 节的实际 PushDrop 输运到 source++V0、target++V0。expectedGamma 取新 task Γ；其内容与原 expectedGamma 相同。新 target 第 0 项因此确为指定 Γ 和 resultBool，之后的全部 tail RowsEq 包括 V0 接缝均已有真实见证。

SimpleTransition 还无条件要求 right Γ RowsWellFormed 与 source 第 0 项 HeadEq；tag=3 时要求 left 两项。AllShift 对 premise 的两个条件无条件保留。ExsCut 在各自 tag 分支里按上述索引重建右侧或左右两侧条件。所有新的 HeadEq、PushDrop 有界见证共用最终选定的值栈 V_v。

## 7. Frame、StateCore 与完整 429 列

原 Frame 的输入条件是整个 `[proofCount]++P++[certificateCount]++C` 切片相等。先读首头，得到两边 proofCount 相同；由其长度定位第二个头，再得到 certificateCount 和对应正文相同。所以 P=P1、C=C1 是该实际输入切片条件的算术后果。

两边分别写新的带头 P++R 与 C++S，逐单元比较相同的新 count 头、原正文、相同的追加段，得到新的输入整片相等。不能只取原 count 头保持不变。

两个任务栈依任务栈稿构造；原 TaskDrop(1) 在 eta_R 与 K0 续延下保持。当前 headTag≠10，故 eta_R 正好只增长其 suffix；新 TaskCore、BoundedHead 的全部 14 个坐标已由同一构造给出。各值栈由第 6 节和已有 ChildResultCore 构造给出。

当前和下一状态均以真实 `[0]` 作为最后的 running Option 片段，statusTag=0；外部 statusBool 坐标取 0，因为该分支不读取它。值栈项的 Boolean 及规则 resultBool 则保留实际原值。

选择公共值栈控制 `H_v,V_v=2^H_v`，同时容纳两边全部 ChildResultCore、HeadEq、PushDrop 见证；Frame 要求的 nextValueTableWidth=currentValueTableWidth、nextValueValueBound=currentValueValueBound 因而成立。任务栈控制可以同样统一选取。所有幂界在 token 布局和 boundary 完成后选择。

此时两个 StateCore、当前 TaskBoundedHead、原 Frame，以及第 6 节相应 SuccessRows 的全部合取都已成立。最后加入 nextStatusTag=0，选择原 Branch 的相同成功析取，得到原 93 参数 CombineStateGraph。

其安装到 G 的替换向量是 `VerifierStepFormula.lean` 的 `compactNumericVerifierStepCombineTerms`：严格使用 429 列的前 93 列，不作重排。准确赋值如下。

| 列 | 内容 |
| --- | --- |
| 0—2 | T'、u'、N' |
| 3—23 | 新 current 的 15 个 StateCore 坐标与 6 个 size/control 坐标 |
| 24—44 | 新 next 的对应 21 个坐标 |
| 45—58 | 新当前任务头的 14 个 TaskCore/size 坐标 |
| 59—61 | rightGammaCount、rightGammaBoundary、rightBool |
| 62—64 | leftGammaCount、leftGammaBoundary、leftBool；未使用时可取 0 |
| 65—66 | formulaBoundary、formulaBoundarySize |
| 67—73 | transformedStart、Finish、Boundary、Count、BoundarySize、transformStateBoundary、transformStateCount |
| 74—80 | freedStart、Finish、Boundary、Count、BoundarySize、freeStateBoundary、freeStateCount |
| 81—84 | shiftCandidateBoundary、重包后的 shiftSuccessTable、shiftedBoundary、shiftedCount |
| 85—88 | emptyStart、emptyFinish、emptyBoundary、emptyBoundarySize |
| 89—91 | shiftWitnessBound、freeTableWidth、freeValueBound；ExsCut 的 transform 控制也安装于 90—91 |
| 92 | 原样保留的 resultBool，未必为 1 |
| 93—428 | 全取 0；选定 combine 子式不读取这些列 |

不同成功分支未使用的辅助列也可取 0，但一个无条件合取读取的列不能如此省略。取所有实际子图共享参数的同一份新值，以固定次数合取、析取引入就得到原 `compactNumericVerifierStepGraphDef(e')`。若须写入矩阵，再选外层单元位宽覆盖这些 429 个数，逐项打包并引入实际 BoundedRow；这是已有外层矩阵编码引理。

## 8. 本轮结论边界

本稿闭合三个 combine-success 原状态图及其 429 列 G 安装。主要新构造为：规则条件的双向内容等价、保留旧 token 前缀的全 transform 轨迹重编码、success=false 在扩大见证界后的保持，以及逐公式 shift 表的实际 N' 位重包。所有迭代都明确落在 PA 的有限见证收集、列表索引或固定宽度打包归纳上。

本文没有给任意原见证附加多项式位界，也没有把单行存在性当作整个接受矩阵。完整条件 (3) 仍须将各局部步骤、相邻状态的 CrossEq、Finish 前缀以及新增 MP 节点统一接合。
