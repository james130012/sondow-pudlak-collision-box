# 值栈续延及 one/two parse-success 的实际 429 列输运

日期：2026-09-05。只作纸面证明，不新增 Lean。

本稿完成两类实际外层步骤的局部输运：已给一个 one-parse 或 two-parse 成功行，在 proof/certificate 剩余输入分别追加 R/S、旧任务栈施加 eta_R 并追加 K0、值栈追加 V0 后，可以给出新的全部 429 个数值，使原 `compactNumericVerifierStepGraphDef` 再次成立，并保持同一 one/two 成功分支。

本稿还独立证明原 `ChildResultListPushDropRows` 的值栈续延引理，供叶和 combine 后续使用。这里没有因此宣称这些其它分支或完整条件 (3) 已闭合。

## 1. 精确的前提和结论

下文每个图名均指 integration 目录中 `FoundationCompactNumericListedDirect` 同名前缀文件的实际固定 `.mkSigma` 公式，所有集合、数组写法都以先前纸面读数编码展开。使用 PA 的归纳及算术编码引理，不调用 Nat `Evalb` 的 spec、外部 verifier 正确性、反射或 typed decoder 的未证明唯一性。

假设旧 429 列向量 e 满足 ParseStateGraph 的 success 析取，并在最后的 NonLeaf 子式中满足 one 或 two 析取。这个前提明确包含两个 StateCore、当前任务的 BoundedHead、ParseStateFrame，以及实际 NonLeafStateGraph；单独一个裸 schedule 不够。

从原 StateCore 的切片读出当前 `(P,C,K,V)` 和下一状态 `(P1,C1,K1,V1)`。从 proof-root TaskCore 读出根字段 `(tag,Gamma,A,B,W,Q)`，从证书成功图读出证书后缀 D。原 CommonRows 将 Q、D 分别与 P1、C1 的实际带头切片识别，并给 V 与 V1 的逐项 ChildResultRowsEq。

给定任意有限 token 数组 R、S，以及带实际 TaskCore/ChildResultCore 见证的有限续延 K0、V0，结论为存在新向量 e' 满足同一个实际 G，且其状态内容是：

```text
current' = (P++R, C++S, map(eta_R,K)++K0, V++V0, running)
next'    = (P1++R,C1++S,map(eta_R,K1)++K0,V1++V0,running)。
```

eta_R 与 schedule 稿一致：tag=10 的任务完整保留；tag≠10 时只把字段 suffix 追加 R。K0 不再做第二次变换。V0 的每个子结果按原 Gamma 与 Boolean 保留。

根的 tag、Gamma、first、second、witness 保持，root suffix 变成 Q++R；certificateTag 保持，certificate suffix 变成 D++S。这里“保持 Gamma”指相同的带头 token 内容及逐项值，允许重新编码其 boundary 整数。

两个状态的实际 statusTag 都是 0。StateCore 在这个分支不约束 statusBool，因此可把新向量的这两个未使用坐标都取 0；不能把旧 statusBool 当作一个必须保留的状态字段。与此相反，每个 ChildResultCore 的 Boolean 是实际存储的 0/1 单元，必须保留。

## 2. ChildResultCore 的重编码

实际 `VerifierChildResultFormula.lean:46` 的合取为：Gamma 的 StructuredListLayout、NatListListRowsWellFormed、Gamma boundary 的真实位长及 `(gammaCount+1)*tokenCount` 界、最后一个 BoolSlice。

若子结果为 Gamma=`A_0,...,A_(g-1)`、Boolean=b，它的原始 token 块严格是

```text
[g] ++ [|A_0|] ++ A_0 ++ ... ++ [|A_(g-1)|] ++ A_(g-1) ++ [b]。
```

b 是由原 BoolSlice 得到的 0 或 1。取新起点 a，定义 Gamma 边界

`h_0=a+1`，`h_(j+1)=h_j+1+|A_j|`；gammaFinish=`h_g`，finish=`h_g+1`。

先按此写所有原始 token 块，确定最终同一 N'，再以 N' 为条目宽度打包 `h_j`。取新 boundary 的真实二进制长度。对 j≤g 的 PA 前缀归纳逐项给出原 Γ 布局；地址≤N' 给 `ell(Bγ)≤(g+1)*N'`；最后单元直接给原 BoolSlice。这样得到每条新结果的全部七个 core 坐标/长度见证。

g=0 时，块为 `[0,b]`，Gamma boundary 只有地址 `a+1` 一项，不能误设为 0。子结果的完整块总是至少两个 token。

整个值栈在其起点 z 写长度头 n，并把上述各块连续排列。以块长度和定义栈 boundary，第 i 项是第 i 个块起点，末项是整栈终点。归纳不变量为此前块恰好填满前缀、各块满足指定 ChildResultCore、边界严格递增。它同时给新 StructuredListLayout、每行原 `ChildResultBoundedRow`、整体 `ChildResultListRowsGraph`。

所有七坐标、boundary 整数和 N' 先构造，再取有限最大值，选同一 `H_v,V_v=2^H_v` 容纳当前与下一值栈的一切相关见证。原公共图的幂等式因此真实成立。valueBoundary 本身的长度界来自 n+1 项、每项宽 N' 的规范打包。

## 3. 原 RowsEq 与 HeadEq 的全部局部见证

`ChildResultRowEquality.lean:32` 的 RowEqGraph 包含两条 ChildResultCore、`NatListListSameRows` 和两个 Boolean 相等。`ChildResultBoundedRowsEquality.lean:28` 再绑定两边共 14 个数，并给两张值栈 boundary 的四个 Entry。

旧 `NatListListSameRows` 不是一个未展开的“Gamma 相等”断言。其实际内容为两个 GammaCount 相等，以及对每个 j，两个 Gamma boundary 第 j、j+1 项和对应带头公式列表的完整 SameTableSlicesEq。

因此把两边第 j 个公式列表复制到新表后，取四个新规范端点，引入原 SameTableSlicesEq：取其实际原始 token 长度，逐单元复制保持数值，再逐位引入新宽度的等式。对 j 的原有界全称逐项引入，得到新的 NatListListSameRows；两边 Bool 都保留原相等值。结合第 2 节的两条新 Core，得到原 RowEqGraph。

最后取两边七坐标为 14 个存在见证，四个栈 boundary Entry 指向这些新块。选择公共 V_v 包含这 14 个数，即得到原 BoundedRowsEq。旧等式中的局部 core 描述与其它栈行 core 描述可能使用不同 boundary 数字，但同一行 start/finish 由 Entry 唯一性固定；Gamma 头、逐个 inner-list 的长度头和终点归纳给同一实际子结果。此刚性也已在 Finish-prefix 稿第 2 节逐层证明。

`ChildResultBoundedHeadEquality.lean:35` 的 HeadEq 只有一边七坐标，并在其 Core 之外检查指定 expectedGamma 的 NatListListSameRows 和 `targetBool=expectedBool`。同时重新编码指定 expectedGamma 的实际列表，以上同一逐 j 构造给新的 SameRows；把原 expectedBool 保持，就给完整的新 HeadEq。

在实际规则调用中，指定 expectedGamma 的布局由根的 TaskCore 或规则图提供；本文不从无布局的裸 boundary 数字推断一个 Gamma。新增两份 V0 的同索引结果比较直接使用相同数据复制，仍按这 14 个实际见证引入 RowsEq。

## 4. DropRows 与 PushDropRows 的值栈续延

### 4.1 DropRows

实际 `ChildResultListDropRows.lean:26` 是 `d≤a`、`a=d+b`，以及对 i<b 比较 source[d+i]、target[i]。这里 source/target 旧计数为 a,b，续延 V0 的计数为 c。

新计数为 a+c、b+c，仍使用 d。新长度等式成立。对 i<b+c：若 i<b，用旧 RowsEq 经第 3 节搬运；否则取 j=i-b<c，由 `d+i=a+j` 可知两边均为 V0[j]。逐项引入原全称后得到实际新 DropRows。

特别 d=0 时给两份原等值栈同时追加 V0 后仍满足原 DropRows(0)。one/two CommonRows 正是使用这一例。

### 4.2 PushDropRows

实际 `ChildResultListPushDropRows.lean:27` 给出：

`d≤a`，`a+1=d+b`，`1≤b`，target 第 0 项满足规定 HeadEq；并且

`∀i<a, d+i<a → RowsEq(source[d+i],target[i+1])`。

同时在 source、target 的尾部追加 V0，保留 expectedGamma、expectedBool 与 d。新前三个计数合取为

`d≤a+c`，`a+c+1=d+(b+c)`，`1≤b+c`。

因为旧 b≥1，新 target 的第 0 项仍是旧 target 第 0 项，故第 3 节直接给新 HeadEq。对任意新 i<a+c 且 d+i<a+c：

- 若 d+i<a，则 i<a，实例化旧全称并搬运其 RowsEq；`i+1<b` 由旧计数等式推出。
- 否则令 j=d+i-a<c；由 `a+1=d+b` 得 `i+1=b+j`。两边分别在 source 的 a+j 与 target 的 b+j 位置，均是 V0[j]。

这给出原 13 参数 PushDropRows 的全部合取，包括新增长度范围。d=a、b=1 时也成立：旧 source 被全部弹掉，target 仍保留规定新头，其后是 V0。a=0,d=0 的纯 push 情形同样包含。

DropRows 和 PushDropRows 中的 tableWidth 参数本身未出现在公式体的实质约束里；`V_v=2^H_v` 来自外围 ChildResultListRowsGraph。本构造统一选择这个真实外围幂界，不给裸关系增加不存在的条件。

## 5. 两条输入流及原 NonLeafCommonRows

先从旧实际关系得到需要保持的四个列表等式：

- `ParsePayloadSuccessSeparatedTablesGraph` 的前两条 CrossEq，连同两端的实际 flat-list 布局，给 parser 输入分别与当前状态 P、C 相同。
- `ParseSuccessNonLeafCommonRows` 的前两条 CrossEq，连同 proof-root suffix、certificate suffix、next StateCore 的实际 flat-list 布局，给 Q=P1、D=C1。

这些结论均通过 CrossEq 的头单元得到 count 相等，再通过每个正文单元的读数相等获得；不把 parser 的 Nat 返回值作为前提。

新当前状态的 proof/certificate 列表写成 `[|P|+|R|]++P++R`、`[|C|+|S|]++C++S`；新下一状态相应写 Q++R、D++S 的带头列表。新的 proof/certificate parser 输入和返回后缀使用相同数据。

因此每条新 CrossEq 可取 count 为相应完整带头列表长度。offset=0 比较增长后的 count 头；旧正文范围用原数值等值；追加段两边读取同一 R 或 S。内层位量词使用最终新宽度，旧等值只用来推出自然数单元值相等。

`VerifierParseSuccessNonLeafCommonRows.lean:30` 除这两条后缀 CrossEq 外，还要求：值栈 DropRows(0)、四个控制数的保持等式及 nextStatusTag=0。第 4.1 节给新 DropRows(0)；选择

```text
currentTaskTableWidth = nextTaskTableWidth = H_t，
currentTaskValueBound = nextTaskValueBound = 2^H_t，
currentValueTableWidth = nextValueTableWidth = H_v，
currentValueValueBound = nextValueValueBound = 2^H_v。
```

H_t 同时容纳当前/下一任务栈、任务头和 schedule 任务坐标；H_v 按第 2—3 节同时容纳两份值栈及比较见证。最后取 nextStatusTag=0，即逐项完成原 29 参数 CommonRows。

这些内部界不必等于原行的旧界，也不必在两张相邻外层行之间保持同一数值；实际跨行邻接比较的是存储状态内容。若希望全段统一选界，也可在最后取有限最大值再重建这些存在见证。

## 6. 当前与下一 StateCore 的同表构造

两条新状态按以下原始 token 顺序存储：

```text
带头 proof 列表 ++ 带头 certificate 列表
++ 带头任务栈 ++ 带头值栈 ++ [0]。
```

任务栈块来自 schedule 稿第 3—4 节，值栈块来自本稿第 2 节。两个流块的 finish 均是 start+1+实际正文 count；任务、值栈各自的 finish 由其连续元素块长度和确定。

最后 `[0]` 的位置为 valuesFinish，statusPayloadStart=valuesFinish+1，state finish=statusPayloadStart。以这一单元直接引入 OptionLayout 的 tag=0 子式和 StateCore 的 running 合取，不附加不存在的 Boolean 单元。外部 statusBool 坐标任取 0。

先把两条状态、已计划的 parser 内部状态、proof-root、证书输入/后缀和其它必要背景块的原始 token 长度都确定，再形成一个共同有限布局。最终总长度为 N'，选择 u' 容纳所有实际 token，按前缀打包归纳构造共同表 T'。随后才以 N' 重建每个 boundary 及其真实位长，最后选择所有内部幂界和 endpointBound。

这里使用 parser-append 引理的“给定相容背景块、共同决定最终 N'”版本，不能先把 parser 的成品表定死，再把两条状态附在其后而仅更改 tokenCount。parser 的原始状态块长度取决于旧读取数据、R/S 和规定燃料，不依赖之后生成的 boundary 大整数，所以共同布局没有循环依赖。

原分离表公式没有要求三张表互不相同。本构造可以取 stateTable'=proofTable'=certificateTable'=T'、共同宽度 u'、容量 N'，用不同块地址区分用途；每个 CrossEq 仍作为原跨表公式逐项证明。如果保留不同的物理表，同样的单元复制证明也成立。

当前任务栈非空来自原 ParseStateFrame，追加 K0 后仍非空。当前第 0 项 tag=10，eta_R 完整保留它的所有字段。取它的新 14 个坐标给原 TaskBoundedHead：两个 Entry、完整 TaskCore、各数≤2^H_t 全部满足。

实际 `VerifierParseStateFrameRows.lean:44` 只要求 currentStatusTag=0、currentTaskCount≥1、head tag=10；虽然其签名还带若干字段 count，公式没有要求它们为零。因此当前任务头可能具有非空字段，不能把它一律替换成六单元规范 Parse。只有 schedule 新产生的 Parse 有实际 ParseShape 的全空保证。

这样两个 StateCore、当前 BoundedHead 和 Frame 均已构造，且同一坐标在所有调用中使用一次确定的值。

## 7. Parser payload、schedule 和跨表 root 桥的接合

proof-root 使用 `paper_direct_parser_append_20260905_zh.md` 第 6—7 节的实际成功图输运：输入 P++R，根字段 tag/Gamma/first/second/witness 保持，suffix=Q++R；给新的 TaggedSuccessBounded 及同一根的完整 TaskCore。

这份 TaskCore 同时用于原 40 参数 `ParsePayloadSuccessExposedSeparatedTablesGraph` 的最后一个合取。旧 exposed 坐标与旧 Tagged 图中隐藏的根坐标若不同，第 2 节字段分界刚性（schedule 稿）以共同 rootStart/rootFinish 和同一 token 块将它们对齐，因此可以用一份新根的实际坐标满足两处，不能任取不一致的暴露字段。

certificate 成功图可使用 `paper_direct_certificate_append_20260905_zh.md`。在本稿的 one/two 范围，还可更短地直接使用其 simple 析取：实际 TagMatch 在 one 标签 4—8 时强制 certificateTag=2，在 two 标签 3、9 时强制 certificateTag=3。其它三类 PA 证书析取要求 certificateTag=1，故不能在这里发生。

simple 证书的两个 WitnessRows 和 ConsRows 从 `C=certificateTag::D` 变成 `C++S=certificateTag::(D++S)`，逐单元复制即可引入新公式；axiomStart/Finish、formulaStart/Finish 在这个选定析取中未被读取，可以取 0，不声称它们指向合法空列表。

proofTag、certificateTag 保持，所以 `NodeTransitionTagMatchDef` 中旧的同一数值析取仍成立。第 5 节构造的前两条输入 CrossEq 再加上两个成功 parser 图及 TagMatch，正是原 SeparatedTablesGraph 的五个合取；加上新 root TaskCore 得 ExposedSeparatedTablesGraph。

任务栈部分直接用 `paper_direct_schedule_transport_20260905_zh.md` 第 6、8—10 节：两栈同时施加 eta_R 并追加 K0，原 ReplaceHeadRows 保持；前缀一个或两个新 Parse 不变，combine 变成 eta_R(旧 combine)。proof-root 与 combine 两边同时追加同一 R，五个字段的原 TaskCrossTableBridgeGraph 保持。

结合新 ExposedPayload、CommonRows、One/TwoSchedule 及 TaskCrossBridge，逐项引入原 88 参数 one 或 102 参数 two NonLeafStateGraph。每个子式共享的状态边界、root 边界、公共界都来自同一已确定坐标表。

## 8. 全部 429 列的实际赋值

以下范围按十进制列索引、两端包含。依据是 `VerifierParseStateFormula.lean` 的 CurrentStateTerms、NextStateTerms、HeadTerms、SuccessCommonTerms、NonLeafTerms，以及原 ParseStateGraphDef 的替换向量。

| 列 | 新赋值 |
| --- | --- |
| 0—2 | 新 stateTable T'、单元宽 u'、容量 N' |
| 3—17 | 新 current 的 15 坐标：start、finish、proofFinish、proofCount、certificateFinish、certificateCount、tasksFinish、taskCount、taskBoundary、valuesFinish、valueCount、valueBoundary、statusTag、statusPayloadStart、statusBool |
| 18—23 | current 的 taskBoundarySize、valueBoundarySize、H_t、2^H_t、H_v、2^H_v |
| 24—38 | 新 next 的同顺序 15 坐标 |
| 39—44 | next 的两个 boundary 长度、同一个 H_t、2^H_t、H_v、2^H_v |
| 45—58 | 当前栈顶的 14 个 TaskCore/size 坐标；tag=10，其余字段按旧实际头保留 |
| 59—67 | proofTable、proofWidth、proofTokenCount、proofInputStart/Finish、rootStart/Finish、proofTag、proofEndpointBound |
| 68—80 | certificateTable、certificateWidth、certificateTokenCount、certificateInputStart/Finish、axiomStart/Finish、formulaStart/Finish、suffixStart/Finish、certificateTag、certificateEndpointBound |
| 81—91 | 新根的 gammaFinish、gammaCount、gammaBoundary、firstFinish、firstCount、secondFinish、secondCount、witnessFinish、witnessCount、suffixCount、gammaBoundarySize |
| 92—386 | 全部取 0；这些是其它叶/规则分支的坐标，选定的 NonLeaf 子式没有引用它们 |
| 387—400 | firstParse 的 14 个规范坐标 |
| 401—414 | two 分支为 secondParse 的 14 个规范坐标；one 分支全部可取 0 |
| 415—428 | 新 combine 的 14 个坐标 |

14 个任务坐标的统一顺序为

```text
start,finish,tag,gammaFinish,gammaCount,gammaBoundary,
firstFinish,firstCount,secondFinish,secondCount,
witnessFinish,witnessCount,suffixCount,gammaBoundarySize。
```

在 one 情形置零 secondParse 合法的源码依据是 `ParseSuccessNonLeafStateGraphDef` 的 one 替换向量：它选取本地 0—73 及 88—101，跳过 74—87；安装到 429 列后正是跳过 401—414。two 子式使用全部 102 个本地参数。

运行态的 15、36 列为 0；16、37 是实际 `[0]` 后的 payload 起点；17、38 可取 0。后两列取 0 是合法存在见证选择，不是从旧 running 状态推得其 Boolean 必为 0。

上表每一个数都在前文构造。第 92—386 列的零值不必满足其它未选择析取的 leaf 或 rule 图；原 G 是析取，不能额外要求全部分支同时有效。

## 9. 从坐标表到原 G 的纸面 PA 推导

用第 6 节两个原 StateCore、BoundedHead、Frame，与第 7 节的 One/TwoNonLeafStateGraph，按 `VerifierParseStateFormula.lean:349` 的固定嵌套析取次序引入：先选 NonLeaf，再选 Parse success，再得到原 ParseStateGraph。

随后在 `VerifierStepFormula.lean:166` 的四个外层析取中选择 Parse。这就给出原固定 429 参数 `compactNumericVerifierStepGraphDef(e')`，不是仅给出 Nat 上“下一状态应当如此”的等式。

如果需要把这一行写进外层矩阵，取 U 大于这 429 个数的全部二进制长度，按

`A_0=0`，`A_(j+1)=A_j+e'[j]*2^(j*U)`

作 429 次前缀构造。每个单元严格小于 2^U，原 Entry 逐项成立，原 BoundedRow 的 429 个存在量即可由这些值引入。多行的共同 U 和前缀打包由先前矩阵重编码引理提供。

本行两端与旧两端的续延关系，已经由流的 CrossEq、任务字段与栈索引输运、值栈 RowsEq 逐项给出。后续把相邻源行一起搬运时，仍需用这些端点内容相同来建立原外层 CrossEq 接缝；不能把本地行存在性自动当成整个接受矩阵已存在。

## 10. 本轮完成范围

已纸面闭合：ChildResultCore/RowsEq/HeadEq 的实际重编码，值栈 DropRows 与 PushDropRows 的续延，原 NonLeafCommonRows，以及 one/two parse-success 的完整 429 列 G 行输运。除先前已证明的 parser、证书、schedule 引理外，本稿新增的归纳都已落在具体 Γ/值栈前缀、有限见证收集和逐单元打包上。

尚未由本稿闭合：三个 leaf 的规则图输运、三个 combine-success 的完整规则状态图输运，以及这些局部步骤、Finish 前缀和五个新增 MP 节点的整段矩阵合成。完整条件 (3) 仍须完成这些剩余接缝；本文不以“已经给出非叶行”代替它们。
