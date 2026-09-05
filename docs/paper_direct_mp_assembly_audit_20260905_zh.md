# 实际 MP 接受矩阵的整段合成审计

日期：2026-09-05。只作纸面数学审计，不修改 Lean、主稿或 STATUS。

结论：所有旧 parse/combine 成功行的续延成立以后，整段合成仍不能自动视为完成。重复 Gamma、源有效前缀的选择、跨行宽度和规定燃料均有直接处理办法；真正需要另外给出的主要证据是五个新增节点所用的原 parser、两条否定变换和完整 G 行。主稿 5.1 的公式位长界还要通过实际接受矩阵的结论来源来引入。本稿补出其中“首次根 Gamma 保持到最终结果”的 PA 标记归纳，并精确说明后续接口。

所有短文件名均省略 integration 路径和 `FoundationCompactNumericListedDirect` 前缀。G 指实际固定的 429 参数 StepGraphDef；G(e) 只是固定替换，不是 PA 的真谓词。本文不调用 Nat spec、树解码 sound、verifier exactness 或 PA 反射。

## 1. 可以从两份输入矩阵取得什么

记两个公共公式为 A、I=A IMPLIES B。输入矩阵给完整载荷位长 L_A,L_I≤n、原始 proof/certificate 流 P_A,C_A、P_I,C_I、总 token 数 M_A,M_I，以及恰 F_X=4*M_X+12 行的接受表。

这里 M_X=|P_X|+|C_X| 来自实际 InputSplit 的两层 CrossEq 与长度头。L_X 是输入 canonical tableau 的 inputWidth；公式 tableau 的 formulaWidth 没有在 P_direct 的矩阵体中被直接限定为≤n。不能把二者同名替换。

[Finish 前缀稿](paper_direct_finish_prefix_20260905_zh.md) 第 1—6 节已经给出：

- PA 内存在 1≤k_X<F_X，旧第 k_X 行为成功 Finish；
- 取前 k_X 行得到真实的运行表，每个 current/next 均为 running；
- 前缀末态两条输入流和任务栈均空，值栈恰有一个 `(Gamma_X,1)`；
- Gamma_X 非空，每一项正文都等于同一公共公式的 raw token 流，但 Gamma_X 可含重复项。

为什么前缀只含可以输运的分支：Halted 要求 currentTag=1；Finish 要求 nextTag=1；parse/combine failure 要求 nextTag=1 且 nextBool=0。它们全部与前缀的两个 running 标志矛盾，有限析取消去后只剩五种 parse-success 和三种 combine-success。它并不推出每个中间规则结果都是 true，也不需要这个额外结论。

首停机点的提取使用实际 StateCore 在完整 CrossEq 下的游标刚性，再证明失败吸收和有界最小化。若省去这些步骤，仅把标准机器运行的前缀拿来解释任意 G 表，就仍有内部证明缺口；现有 Finish 稿已明确补了它们。

## 2. 重复 Gamma 可以直接进入弱化，不先修改旧结果

记新节点精确采用以下公式列表，允许其中某些公式恰好相等；列表长度头仍按显示项数取值：

```text
Gamma_c  = [B]
Gamma_wI = [I,B]
Gamma_a  = [NOT I,B]
Gamma_wA = [A,NOT I,B]
Gamma_z  = [NOT B,NOT I,B]。
```

旧 Gamma_I、Gamma_A 继续作为完整列表和 Boolean=1 的子结果传入。实际 `WkRuleCheck.lean:30` 要求 result≤1，以及

`result=1 IFF FormulaSubsetRows(premiseGamma,newGamma) AND premiseBool=1`。

以 I 输入为例。对任意 j<旧 Gamma_ICount，从原 singleton 全称取得第 j 项的两个实际端点及其正文到公共 I 表的 CrossEq。按 ChildResultCore 的长度头刚性，该项的完整带头列表是 `[|I|]++I`。重编码后的该项仍与新 Gamma_wI 第 0 项同值。

在原 `FormulaSubsetRows` 中取该项端点；在其 `FormulaMemberRows` 子式中把 membership index 固定为 0，取新 Gamma_wI 的第 0、1 条规范 boundary Entry，再逐单元给完整 SameSlice。每一个旧重复项都采用同一目标索引 0，原公式没有单射或互不重复要求。逐 j 引入原有界全称，得到真实 SubsetRows。A 的弱化完全同样，目标 Gamma_wA 的第 0 项为 A。

取两个新 Wk 的 resultBool=1，旧 premiseBool=1 与上述子集式给完整双条件。成功 combine 的实际 PushDropRows(1) 把规定的 task Gamma 压为新头，因此输出分别严格具有列表 Gamma_wI、Gamma_wA。这里新结果的规范列表由新节点字段提供，旧 Gamma 没有被凭空去重。

后续 And/Cut 要求的 `FormulaSetEqConsRows` 都可以用显示列表的具体索引证明：

- And 左右结果恰为 A::Gamma_a、NOT B::Gamma_a；
- Cut 左右结果恰为 I::Gamma_c、NOT I::Gamma_c。

原 SetEqConsRows 的三部分是：actual 的每项属于 head 或 tail；head 属于 actual；tail 的每项属于 actual。第一部分在 index=0 时选 head SameSlice，在 index>0 时选 tail 的 index-1；第二部分选 actual index=0；第三部分把 tail index=j 映到 actual index=j+1。每个存在量用真实规范端点，逐 token 证明 SameSlice。即使 head 与某个 tail 项内容相等，这些指定索引仍然合法。

所以重复 Gamma 不是新的逻辑障碍，也不需要增加 contraction 或额外的弱化节点。若直接把旧 GammaCount 改成 1 而保留旧状态或 boundary，则是错误构造。

## 3. 新局部证明：首次根 Gamma 保持到前缀终点

### 3.1 只跟踪任务栈底的一个标记

取一份源前缀，记其边界状态为 s_0,...,s_k：s_0 为第一行 current，s_(j+1) 为第 j 行 next。相邻行的 current 与这些状态用原 CrossEq 对齐。StateCore 游标引理保证任务数及逐任务字段、值栈内容一致，不要求相邻行的绝对地址、内部表、boundary 码或未使用的 running statusBool 一致。

初态 taskCount=1，实际 InitialEnvironment 的 ParseTaskHead 给唯一任务 tag=10 且所有字段为空；valueCount=0。第一行只能选 parse-success。令其暴露根 Gamma 为 Gamma_root。根 Tagged/Exposed 两份局部描述由同一根片段的 TaskCore 刚性对齐。

如果第一行选 leaf，TaskDrop(1) 给 s_1 的任务数为 0。若 k>1，第 1 行 current 就是 running 且 taskCount=0，它只能 Finish，与所有前缀行 next 仍 running 矛盾。因此 k=1。叶共同图的 root-Gamma/target-Gamma CrossEq 直接给最终唯一结果 Gamma=Gamma_root。

现在设第一行选 one/two。实际 schedule 把唯一 Parse 换成 `[Parse,combine]` 或 `[Parse,Parse,combine]`。完整 NonLeafStateGraph 的 TaskCrossTableBridge 把这个 combine 的全部根字段与首次 root 连接，特别其 Gamma 是 Gamma_root、tag 是该根 proofTag。one/two 的实际有限标签均不等于 10。

把这条最后任务的位置作为标记。不是假设其数据与其它任务不同：标记是栈底的那个索引，其数据即使与别处相同也不影响证明。

### 3.2 实际 ReplaceHead/Drop 给标记归纳

第一行非叶时 s_1 的任务数为 2 或 3，而 s_k 的任务数为 0，所以 k≥2。
对 1≤j<k 作 PA 有限索引归纳。在标记尚未弹出的边界状态 s_j 上维持：

```text
taskCount=t≥1；
第 t-1 项满足与首次 combine 相同的完整 TaskCore 字段，尤其 Gamma_root、tag≠10；
它以下没有其它任务。
```

若本行当前任务数 t>1，标记索引 r=t-1≥1，位于严格尾部。

- leaf 或任意 combine 的实际 TaskListDropRows(1) 把 source[r] 搬到 target[r-1]。新任务数 t-1，所以它仍在栈底。
- one/two parse 的实际 ReplaceHeadRows 取 p=2/3，计数式为 t+p=t'+1。取其全称的 i=r-1，则 source[1+i]=source[r] 与 target[p+i] 整任务 SliceEq，而 p+i=t'-1。标记仍是新的最后一项。

这些尾部等式都来自原 Drop/Replace 的实际有界全称。整任务 SliceEq 加两端 TaskCore 的字段游标归纳，保持 tag 和逐项 Gamma；它不是仅保持结论集合。跨越下一行时，再用完整状态 CrossEq 的任务栈刚性传递此不变量。

若标记成为当前头，则 t=1，其 tag≠10 排除 Parse。前缀只能选 combine-success；原 CombineStateFrameRows 的 TaskDrop(1) 给下一任务数 0。若这发生在最后一行以前，下一行必为 Finish，与运行前缀矛盾。因此弹出标记的行只能是第 k-1 行。

反过来，s_k 的任务数已知为 0，标记不可能一直保留到 s_k。若第 k-1 行当前仍有 t>1，上一段的两种尾输运都会保留它，亦不可能得到空任务栈。故标记确在第 k-1 行作为唯一任务被弹出。

### 3.3 末结果的 Gamma

三个 combine-success 的实际 rule/transition 子式都含 ChildResultListPushDropRows，其 expectedGamma 是当前 task Gamma。其 HeadEq 使用 NatListListSameRows，给的是逐公式列表内容相同，而不是单纯集合相等。标记 Gamma 已为 Gamma_root，所以最后行的 target 第 0 项 Gamma 为 Gamma_root。

源前缀末态 valueCount=1，故这就是最终唯一结果。结合第 3.1 节的叶情形，PA 得到统一结论：

```text
首次 parse-root 的 Gamma 与成功 Finish 前唯一结果的 Gamma 逐项同值，计数相等。
```

布尔值 1 来自成功 Finish 前缀引理，不必另外证明所有中间规则都 true。把末态的原 FormulaSetEqSingleton 沿此逐项同值传回根，即得 rootGammaCount>0，且根每一项正文等于同一个公共公式流。

本标记证明不需要先在 PA 中恢复整棵 proof tree，也没有使用深度优先遍历的 Nat 语义定理。它只需要已展开的 TaskDrop、ReplaceHead、TaskCrossBridge、PushDrop、StateCore/CrossEq 刚性。

### 3.4 公式位长接缝必须显式接上

第 3.3 节允许取首次根 Gamma 的第 0 项。五个实际 ProofRootEndpoint 家族都有外层 Cons：proof input=rootTag::sequentInput。SequentEndpoint 又有 Cons：sequentInput=GammaCount::firstSuffix。因为 GammaCount>0，SequentTrace 的第 0 行存在；其 `SequentFormulaStepFormula.lean:83` 的真实 AppendSlices 给

`firstSuffix = firstGammaFormula ++ nextSuffix`。

因此公共公式正文与原 proof 流从偏移 2 开始的一个前缀段逐单元相同。这里正文不含状态存储额外引入的公式列表长度头。

对同一 raw token 流定义二进制成本 Weight(X)=对 token x 求和 `2*ell(x)+2`。主稿 5.3 的 canonical offset 前缀归纳识别 inputWidth=Weight(P++C)、formulaWidth=Weight(F)。由于权重非负且公共 F 是上述 proof 片段，得到

`formulaWidth≤Weight(P)≤inputWidth≤n`。

这后一截已由 [公式来源稿](paper_direct_formula_provenance_20260905_zh.md)
沿 SequentEndpoint/Step、两条 Cons、原 canonical offset 递推及 public code
的 sentinel 等式完成，并加强为 formulaWidth+4≤inputWidth。
本稿的根 Gamma 来源接口已逐源码独立复核，采用上述准确的归纳端点。

对两个输入分别应用，得 |A|≤n、|I|≤n；固定语法编码 I=NOT A OR B 的长度等式再给 |B|≤|I|≤n。这样才可把主稿 5.1 的带 a,b 位长账本收束为 29n+128。公式 table 的任意辅助整数码多大，与这条 formulaWidth 上界是不同问题。

## 4. 严格拼接顺序及四个上下文

令 H_c、H_wI、H_a、H_wA、H_z 是五个新增 proof 节点的头部 raw token 块，精确采用第 2 节的列表及主稿 5.1 的公式字段。它们不含子树 token。新输入直接拼原两条 proof 流：

```text
P_out = H_c ++ H_wI ++ P_I ++ H_a ++ H_wA ++ P_A ++ H_z
C_out = [3,2] ++ C_I ++ [3,2] ++ C_A ++ [0]。
```

无需先去重、规范化或解码重编码旧 proof tree。旧 canonical 位流确定原 token 值，输出仍按同一自然数 token 编码重新打包。

五个新节点与两段旧前缀严格按以下顺序执行；task/value 栈左边是栈顶：

| 片段 | 结束后的关键内容 |
| --- | --- |
| parse cut；parse wkI | task 为 Parse,wkI,Parse,cut；值栈空 |
| 输运 I 的 k_I 行 | task 为 wkI,Parse,cut；值栈为旧 `(Gamma_I,1)` |
| combine wkI | 值栈为 `(Gamma_wI,1)` |
| parse and；parse wkA | task 为 Parse,wkA,Parse,and,cut |
| 输运 A 的 k_A 行 | task 为 wkA,Parse,and,cut；值栈为旧 `(Gamma_A,1)`，随后 Gamma_wI |
| combine wkA；parse closed | 值栈依次为 Gamma_z、Gamma_wA、Gamma_wI，Boolean 全为 1 |
| combine and | 值栈为 Gamma_a、Gamma_wI，Boolean 全为 1 |
| combine cut | 两流空、任务空、值栈仅 `(Gamma_c,1)` |
| Finish | accepted，并保留该单结果 |

输运 I 的四个上下文准确为：

```text
R_I = H_a++H_wA++P_A++H_z；S_I=[3,2]++C_A++[0]；
K0_I=[wkI,Parse,cut]；V0_I=[]。
```

输运 A 的四个上下文为：

```text
R_A=H_z；S_A=[0]；
K0_A=[wkA,Parse,and,cut]；V0_A=[(Gamma_wI,1)]。
```

各 combine 的完整字段，尤其其 suffix，必须取对应新 parse 已产生的字段；不能只凭本表的任务标签生成任务。两段旧任务栈施加 eta_R，K0 中的新任务不再追加一次 R。两段旧初态的唯一 Parse 是实际全空 Parse，所以其续延初态与上表前一新节点的 next-state 可以完整 CrossEq 对接。

二元 combine 的实际 right 是值栈第 0 项，left 是第 1 项。所以 And 接 right=Gamma_z、left=Gamma_wA；Cut 接 right=Gamma_a、left=Gamma_wI。反置两者一般无法通过真实规则图。

## 5. 任意有限逐行见证可以形成同一外层表

旧前缀的每行局部输运给新 429 元向量，其两端内容是统一定义的续延变换。原相邻状态 CrossEq 经字段游标刚性，给两条旧流和两栈的内容一致；施加同一个 R,S,eta_R,K0,V0 后，两边新 raw 状态块也逐 token 相同。由真实长度及零扩展位等式引入新 CrossEq，获得相邻接缝。

每行可以使用不同的内部 stateTable、宽度和容量。外层 RowsAdjacent 本来就通过十个存在值读取两侧表并比较切片，没有要求整段采用一个共同内部表。因而不存在必须把所有叶的旧规则表强制迁入统一大表的义务。

但 PA 内有限收集仍须写出来：按已处理行数 i 归纳，维护一张 i 行外层表、外层宽 U_i、已证 G 行和相邻接缝。下一步实例化第 i 个局部输运定理，得到新 429 个数，取 U_(i+1) 大于 U_i 和这些数的全部位长。用已证外层重编码引理搬运前 i 行，再追加此行。旧行的 G 是固定公式的同值替换，旧邻接不变，唯一新接缝如上。

此归纳给共同有限外层宽和实际表，甚至不需要预先知道全部新见证的数值统一上界。PA 的全归纳足以证明这一有限收集；不能只以“有限多个存在见证必有编码”一句省去它。完成后 expDef(traceValueBound,traceWidth) 取真实 2 的幂。19 个辅助见证无需多项式位界，但都必须按这些归纳确实存在。

父线程另写整段 segment 稿给完整的前后投影、拼接与填充版本；本节只标明其严格归纳不变量，不用本地行存在性代替它。

## 6. 燃料可以直接由两张旧表的行数解决

新增节点共五次 parse、四次 combine，再加一次 Finish。因此短接受矩阵总行数

`t=k_I+k_A+10`。

令 H 为新增两流 raw token 的总数。由上述原始串拼接，M_out=M_I+M_A+H。五个 proof 标签已给 H≥5；实际还有五个结构证书标签，因此下界还有余量。

由 k_I<F_I、k_A<F_A，得到 t≤F_I+F_A+8。另一方面

```text
F_out = 4*M_out+12
      = F_I+F_A+4*H-12
      ≥ F_I+F_A+8 ≥ t。
```

这些是 PA 内的加法不等式，输入 split 已给 M_X 的正确意义。本路线不必另从 Nat 树步数 S≤2P 推出 k≤2P，也不必为实际 G 重新证明势函数；主稿 5.4 的更强机器停机界可保留，但不是本次拼接必须调用的接口。

用已有 429 列接受吸收行，在短接受表后补 F_out-t 行，即得恰规定燃料的 AcceptedTraceTable。它同时保持 AcceptedConclusionRow 的内部数据。这里 fuel 充分性与 inputWidth_out≤29n+128 的位长账本独立：前者不需要后者，后者也不能省略。

## 7. 五个新增节点仍需哪些实际新见证

局部续延的前提是“已有一个满足原 G 的行”。五个新节点本身没有这样的旧行可供重用，故不能再次引用续延定理来声称它们存在。

新 proof-root 家族分别为：cut 的 tag=9 OneFormula，两个 wk 的 tag=7 SequentOnly，and 的 tag=3 TwoFormula，closed 的 tag=0 OneFormula。它们全部使用普通语法 parser；新增 closed 叶不是 tag=1 的 ClosedFormula parser。结构证书是 simple 的 3、2、3、2、0，每个 simple 端点可按两个 WitnessRows 和 Cons 从原始块直接构造。

需要的两组真正初始证据为：

1. **普通公式 parser 基础图。** 对本次 A、B、I、NOT B、NOT I 的真实编码，构造输入为该公式、返回空后缀、初始 `(taskKind,taskBinderArity,taskRepeatCount)=(1,0,0)` 的原 SyntaxExactEndpointGraph，并满足其规定燃料和所有状态、步骤、boundary 条款。随后用已有 append 引理加各节点的真实剩余流；按固定项数组装 sequent 和 One/TwoFormula 外壳。已有 append 稿仅证明已有成功图的输运，并未单独提供这些从零开始的基础图。
2. **两条 mode=3 否定图。** ClosedRuleCheck 无条件要求 B 到 NOT B 的 TotalExactBoundedGraph；CutRuleCheck 无条件要求 I 到 NOT I 的同一真实变换图。需要空 witness、binderArity=0、实际输入/输出列表、规定燃料及全部状态行。还须将后者输出准确识别为编码 A AND NOT B，才能给 And 的 constructor-member 原子图。保留旧变换图的输运定理不产生这两条新图。

这两组从零证据随后已经分别由
[普通 Syntax 稿](paper_direct_syntax_base_graph_20260905_zh.md) 和
[mode=3 否定稿](paper_direct_negation_base_graph_20260905_zh.md) 构造。
它们对明确编码的公式/项分解作加强归纳，逐原 StepRows 给出分支及槽，
证明实际步数≤2L，Empty 完成后用 Done 补到规定 fuel；否定稿另补完整输出、
状态有效性和末输出识别。不存在以“否定是 PR 函数”代替这些图的步骤。

上述基础证据取得后，五个规则的 Boolean=1 部分较短：两个 Wk 用第 2 节的任意重复项子集构造；And 在 Gamma_a 中取 constructor-member index=0，并用两个显示的 SetEqCons；Closed 的两个 membership 分别取 Gamma_z 的 index=2、0；Cut 用两条 SetEqCons 和已经为 1 的左右 Boolean。将这些真合取与 resultBool=1 组合，逐字得到各规则的 IFF。

然后仍要给九个新增宏步的完整 G 环境：五个 parse 行采用已给列布局，但其 payload/parser 要用上述新基础证据；两个 Wk 和 And 的 combine 使用真实 SimpleTransition、HeadEq、PushDrop；Cut 使用真实 ExsCut 分支及新否定轨迹。输入、task、value 片段及共同界必须一次赋值，对应第 4 节每个接缝。只有把这些数填写并引入实际析取，才算新节点验收闭合。

最后的 Finish 不需要新语法归纳。把空流、空任务、单一 `(Gamma_c,1)` 的 running 块和相同 payload 后接 `[1,1]` 的 accepted 块放入新表，给两个 StateCore；payload SameSlice、四个 count 等式以及 row-0 WithBool(1) 逐项引入 `VerifierFinishFormula.lean:59`。G 的其它分支坐标取 0 即可。根 Gamma_c=[B]，取规范边界的第 0 项并比较其正文与 B 的 canonical formula 表，得到原 AcceptedConclusionRow。

## 8. 本次审计的完成边界

本稿已经补出或具体核清：重复 Gamma 经原 Wk 进入规范新结果；有效前缀只含成功分支的逻辑依据；首次根 Gamma 的栈底标记归纳；五节点准确执行顺序和两个续延上下文；无需源树步数界的 fuel 不等式；有限逐行见证收集的实际归纳；新 Finish 和末结论的固定条款。

同一 public formulaWidth 的根切片/位权引理已由独立来源稿与本稿接合。
普通语法基础图和两条精确否定图也已由后续稿构造。
尚不可合并为“条件 (3) 已完成”的部分：它们的九个完整 G 行、输出 canonical payload 位账本和最终 20 个存在量词仍需逐项安装。所有存在性完成以后，条件 (3) 的短 PA 证明界 p3 还要从统一模板、短数词实例化及公式代码计算分别核算；存在一个 PA 证明不自动给这个多项式证明长度。

未发现重复项、燃料常数或先行 Finish 所造成的数学反例。当前实质缺项集中于“新增语法对象如何取得实际固定图见证”及这些见证与量化成本的接合，不能由外部树构造正确性一笔替代。
