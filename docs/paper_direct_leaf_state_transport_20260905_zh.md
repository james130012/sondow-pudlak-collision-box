# 三类 leaf parse-success 的实际 429 列续延输运

日期：2026-09-05。仅作纸面证明，不新增 Lean。

本稿完成 Verum、Closed、PAAxiom 三个叶成功分支的局部 G 行输运。这里的“成功分支”表示解析及行构造成功，不预设规则结果 resultBool=1；resultBool=0 也被保留。Closed 的 28 列规则块、PAAxiom 的全部 259 列规则块可以逐数字原样复用，所需新证明只发生在其与新 parser 表之间的接口。

## 1. 原公式前提及结论

下文短文件名均省略 integration 路径及 `FoundationCompactNumericListedDirect` 前缀。图名指这些文件中实际固定 `.mkSigma` 公式，不调用 Nat 的 spec、sound、exactness 或 verifier 语义正确性。数组表示使用已有纸面 PA 商余读取及有限前缀编码；所有归纳均在 PA 中进行。

设旧 429 列 e 满足 `VerifierParseStateFormula.lean:349` 的 success 析取，并且最内层选定 Verum、Closed 或 PAAxiom。前提包括两个 StateCore、当前任务 BoundedHead、ParseStateFrame 和对应的完整 LeafStateGraph，不能只给一条裸规则检查。

从实际状态布局读取当前 `(P,C,K,V)`、下一状态 `(Q,D,L,W)`。给定有限 token 数组 R、S，以及带实际 TaskCore、ChildResultCore 见证的有限尾栈 K0、V0，构造新 e'，使同一个叶分支及原 429 参数 G 成立，且状态内容为：

```text
current' = (P++R,C++S,map(eta_R,K)++K0,V++V0,running)
next'    = (Q++R,D++S,map(eta_R,L)++K0,W++V0,running)。
```

eta_R 在 tag=10 时完整保留旧任务，在 tag≠10 时只把该任务的 suffix 字段追加 R；K0 不再施加一次 eta_R。根的 tag、Gamma、first、second、witness 不变，根 suffix 追加 R；certificateTag 不变，certificate suffix 追加 S。值栈的每个真实 Boolean 保持。

三个分支的标签及本次使用的实际 proof-root 图为：

| 叶分支 | proofTag / certificateTag | proof-root 成功图 |
| --- | --- | --- |
| Verum | 2 / 0 | SequentOnly |
| Closed | 0 / 0 | OneFormula，binderArity=0 |
| PAAxiom | 1 / 1 | ClosedFormula，binderArity=0 |

尤其 Closed 叶的名称不等于 ClosedFormula parser 家族的标签。外层 PA 公理叶需要封闭语法 parser 的追加引理；Closed 叶使用普通 one-formula 引理。

本稿使用已经逐原公式证明的局部结果：parser-append 稿第 2—7 节、certificate-append 稿第 2—6 节、schedule 稿第 2—7 节，以及 parse-state-transport 稿第 2—6 节。它们给重新编码、共同布局、任务 DropRows 与值栈 PushDropRows。下面补齐叶专有的接口及完整分支，而非假定这些接口成立。

## 2. 保留切片与一端重编码的原 CrossEq

原 `CrossTableSliceEquality.lean:41` 的 CrossEq 有长度见证 k，要求 k≤两端容量、两段 finish=start+k、finish≤各自容量，并在 offset<k、bit<两端宽度之和上比较零扩展后的单元位。

假设旧 X 与 Y 满足这个原公式，新 X' 按顺序复制 X 的全部 k 个单元且有合法新端点。保持 Y 的表、宽度、容量、端点全部不变。由旧位等式，在每个 offset 上按 bit 作有限二进制归纳，得到两边 ReadCell 的自然数值相等。复制构造又给 ReadCell(X',offset)=ReadCell(X,offset)，故新 X' 与旧 Y 的单元值相等。

取同一个 k。它等于新 X' 的合法切片长度，所以 k≤新容量；其它长度及旧 Y 容量界直接保持。对任意新范围内的 bit，若 bit 小于相应单元宽度，Entry 识别该位为共同读数的位；若超出宽度，共同读数小于该宽度对应的 2 的幂，故该位为 0。由此引入新完整位全称，得到 CrossEq(X',Y)。不能直接把旧的位量词上界扩大。

这是一端重编码、另一端完全固定的引理。它不要求新旧两个表数值不同，也不要求被复制的切片代表有效公式。后文的规则接口只需这个原始 token 层结论。

Gamma 的重编码还保留逐公式分界。若 Gamma 有 g 个列表，起点 a，列表正文长度为 n_j，则边界按

`b_0=a+1`，`b_(j+1)=b_j+1+n_j`

构造。PA 对 j 的归纳维持：已经复制的完整前缀长度、每个原列表长度头与正文相同、规范 boundary 的前 j+1 项为相应地址。原 Entry 唯一性把另一份同片段的 Gamma 见证与这些地址对齐。因此完整 Gamma CrossEq 加两端实际 Gamma 布局，足以得到 GammaCount 相等及逐列表内容相同；这里没有调用 typed decoder 的唯一性。

## 3. 实际共同 LeafParseTransport 的构造

`VerifierLeafParseSuccessTransportGraph.lean:36` 是两个合取：40 参数 ExposedSeparatedTablesPayload 与 43 参数 LeafParseSeparatedTablesTransportRows。后者在 `VerifierLeafParseSeparatedTablesTransportRows.lean:24` 的全部内容为：

1. proof-root suffix `[witnessFinish,rootFinish)` 与 next proof 切片 CrossEq；
2. certificate suffix 与 next certificate 切片 CrossEq；
3. target 值栈第 0 行满足显式七坐标的 ChildResultBoundedRowExposed；
4. proof-root Gamma `[rootStart+1,rootGammaFinish)` 与该结果 Gamma CrossEq；
5. targetBool=resultBool；
6. 原 LeafParseStackRows。

旧第 1、2 条及实际长度头给 proof suffix=Q、certificate suffix=D。新 parser 的这两个返回字段写成 Q++R、D++S，新 next 流按相同内容写入。取完整带头长度为 CrossEq 的 k，offset=0 读取新长度头，旧正文区使用旧等值，追加区读取同一 R/S，遂给新第 1、2 条。

旧第 3—5 条给 target 头是 `(Gamma,b)`，其中 Gamma 与根相同、b=resultBool。BoolSlice 推出 b=0 或 b=1。原值栈 StateCore 中对头部可能另有一份局部描述：两个栈 Entry 固定其 start/finish，再用 Gamma 长度头及逐公式游标归纳识别全部字段，故它确是旧 W 的第 0 项。

构造新 W++V0 时保留这项内容。若新头起点为 a、Gamma 终点为 z，给暴露七坐标

```text
targetStart=a，targetFinish=z+1，targetGammaFinish=z，
targetGammaCount=g，targetGammaBoundary=B，targetBool=b，
targetGammaBoundarySize=ell(B)。
```

B 以最终新容量 N' 为条目宽度打包 Gamma 的 g+1 个规范边界。由 ChildResultCore 的逐块构造，头块具有完整原 Core。target valueBoundary 的第 0、1 项分别是 a、z+1。取公共值栈界 V_v 包含这七个数，依序引入 `ChildResultBoundedRowExposedFormula.lean:46` 的七个 ≤V_v 合取、两个 Entry 及 ChildResultCore。这给实际第 3 条。根和头部 Gamma 均复制旧 Gamma，第 2 节给第 4 条；第 5 条以同一个 b 成立。

原 `VerifierLeafParseStackRows.lean:33` 恰好是四个控制数相等、nextStatusTag=0、TaskListDropRows(1)、ChildResultListPushDropRows(0,b)。下面分别引入，避免把“弹任务、压值”当作一个未经展开的操作。

设旧任务计数 s,t，旧值计数 a_v,b_v，续延计数 c_k,c_v。原关系给 s=1+t、a_v+1=b_v、b_v≥1。新计数为 s+c_k、t+c_k、a_v+c_v、b_v+c_v。

- Task Drop 的全称对 i<t+c_k：i<t 时搬运旧 source[1+i] 与 target[i] 的整任务等式；i≥t 时取 j=i-t<c_k，由 1+i=s+j，两边都是 K0[j]。旧任务同时施加 eta_R，所以原 TaskCore、BoundedRowsEq 由 schedule 稿第 3、5、7 节的同字段构造给出。
- Value PushDrop(0) 的头仍为原 W 的第 0 项，因为 b_v≥1。其 HeadEq 的 expected Gamma 正是新暴露头的 B,g；取同一头的七坐标，逐公式 SameRows 用规范端点作反身比较，expectedBool=b。对 i<a_v+c_v：i<a_v 时用旧 source[i] 与 target[i+1] 的 RowsEq；否则 j=i-a_v<c_v，且 i+1=b_v+j，两边都是 V0[j]。每项的 14 个局部坐标及四个栈 Entry 按 parse-state 稿第 3 节引入。

新计数等式分别为 s+c_k=1+(t+c_k)、a_v+c_v+1=b_v+c_v，并且 b_v+c_v≥1。这也覆盖旧值栈为空 a_v=0 以及两个续延为空的边界情形。

在构造当前与下一状态的全部任务、值栈坐标后，分别选共同 H_t,V_t=2^H_t 和 H_v,V_v=2^H_v 容纳两状态的一切局部数。两边使用同一组数，故四个保持等式成立；各外围栈 RowsGraph 的真实幂约束同时满足。把 nextStatusTag 取 0，便得到整个原 LeafParseStackRows，进而得到 43 参数 TransportRows。

## 4. 两个 StateCore、Frame 与 parser payload 同步安排

两状态的原始块都按以下顺序写入：proof 带头列表、certificate 带头列表、带头结构任务栈、带头结构值栈，最后单元 `[0]`。因此 statusPayloadStart=valuesFinish+1=stateFinish，statusTag=0；不写 Boolean 单元。StateCore 的运行分支不约束参数 statusBool，可把两个新坐标都取 0。

当前头由原 ParseStateFrame 得 tag=10、任务计数≥1。eta_R 保留整个头，故新头仍满足 Frame。此 Frame 不强制头的各字段为空；新 BoundedHead 使用保留内容后的实际 14 坐标，不能擅自换成全空的规范 Parse。

使用 parser-append 稿对应家族，重建 proof 输入 P++R、保持根的非 suffix 字段、把根 suffix 变为 Q++R。新根同一份 TaskCore 同时用于 TaggedSuccessBounded 与 ExposedPayload。使用 certificate-append 稿重建 C++S、D++S，并保持证书标签。

Verum/Closed 的 certificateTag=0，所以原成功证书的实际活动家族是 simple；axiom/formula 的四个公共地址在此家族未被读取，可取 0。PAAxiom 的 certificateTag=1，活动家族为 fixed、symbol 或 induction；追加引理保留 axiomTokens 的完整带头列表，并搬运其原成功公式。不能在 PA 分支把这些实际活动地址置零。

新当前流与 parser 输入是内容相同的带头列表，故两条输入 CrossEq 逐单元成立；proofTag、certificateTag 都保持，原 TagMatch 仍成立。这两条 CrossEq、两个成功 parser 图及 TagMatch 给原 SeparatedTablesPayload，连同新根 TaskCore 给 40 参数 ExposedPayload。与第 3 节合取，得到完整的 68 参数 LeafParseSuccessTransportGraph。

这里先计划两条状态、根、parser 内部全部状态、证书活动块以及辅助背景块的原始长度；最终新容量 N' 一次确定后，再编码所有新 boundary、其真实位长及控制界。可令三张新 state/proof/certificate 表共用 T',u',N'、采用不同块地址。parser 的“相容有限背景区”版本确保此安排成立，不允许先完成 parser 表后只修改其容量数字。

后两节保留的规则表并不纳入这些被修改的三张表。它们仍是旧独立数值参数；即使旧时两者偶然相等，也可在新赋值中保留旧规则表、另取新 parser 表。

## 5. Verum：实际成员公式的双向不变

`VerifierVerumLeafRuleRows.lean:25` 除标签 2/0 外，要求 `VerumRuleCheck.lean:148` 的实际公式：

`b≤1 ∧ (b=1 ↔ ConstantFormulaMemberRows(T,u,N,2,B_gamma,g))`。

MemberRows 的三个存在见证为 i<g、x≤N、y≤N；其五个末端合取是 Gamma boundary 的第 i、i+1 项为 x、y，y=x+2，表在 x 处为 1、x+1 处为 2。即只检查对应完整单项列表块 `[1,2]`。

由第 2 节的 Gamma 前缀归纳，旧第 i 项与新第 i 项具有相同长度头、正文长度和逐单元值。

正向：消去旧 MemberRows，保留 i；Entry 唯一性把旧 x、y 识别为第 i 项规范起止点。取新第 i 项端点 x'、y'，它们≤N'，并满足 y'=x'+2。新两单元仍为 1、2；两条新 boundary Entry 由构造成立，所以引入新 MemberRows。

反向：消去新 MemberRows，仍保留 i。新 Entry 唯一性确定它选的是新第 i 项；新长度 2 与 token 1、2 通过逐项复制还原到旧第 i 项。取旧该项的两个真实端点，它们≤旧 N，满足旧五个合取，因而引入旧 MemberRows。这里没有从“新成员属于某个列表”跳过对应索引和端点。

于是 PA 证明新旧 MemberRows 等价。g=0 时不存在 i<g，两边均假。保持同一个 b、旧 b≤1 和旧双条件，得到新双条件，既覆盖 b=1 也覆盖 b=0。标签保持后即为新完整 VerumLeafRuleRows；与第 4 节共同图合取得到原 VerumLeafStateGraph。

## 6. Closed：完整 28 列规则块原样保留

`VerifierClosedLeafParsedRuleGraph.lean:239` 的实际 69 参数公式正好有五部分：ExposedPayload；29 参数 SelfContainedGraph；proofTag=ruleProofTag；certificateTag=ruleCertificateTag；两条 CrossEq 的 ClosedLeafCrossTableBridgeGraph。

令新 28 个 rule 参数逐个等于旧参数，同时令新 resultBool 等于旧 resultBool。于是 SelfContainedGraph 的全部 29 个实参数都完全相同。它包含 Gamma WitnessRows、formula WitnessRows、negated WitnessRows、empty WitnessRows 和完整 ClosedLeafRuleRows；该规则图又包含实际 ClosedRuleCheck。其内部变换轨迹、boundary、stateCount、tableWidth、valueBound 和任何由公式绑定的见证都处在同一个未改变的公式实例中。

因此从旧前提通过合取消去取得该 29 参数子式，立即可将其作为新子式的同一公式使用。这是 PA 的同式重用，不是从旧图的 Nat 真值产生新证明，也没有改写内部自由参数而忽略约束。特别不修改旧规则表容量，不必给内部 negation/transform 轨迹另证重定位。

新 ExposedPayload 已由第 4 节给出。旧规则标签由原 RuleRows 为 0/0，新 proof/certificate 标签仍为 0/0，两个等式保持。跨表桥的两条关系分别比较：

```text
新 proof-root Gamma  <->  原规则表 Gamma；
新 proof-root first  <->  原规则表 formula。
```

proof-root 的这两段保持完整旧内容，右端全部参数固定；第 2 节一端重编码引理逐条给这两项。此处 first 切片准确为 `[rootGammaFinish,firstFinish)`，Gamma 切片为 `[rootStart+1,rootGammaFinish)`，均含各自长度头。

从而原 ParsedRuleGraph 的五部分全部成立。`VerifierClosedLeafStateGraph` 还要求共同 LeafParseSuccessTransportGraph，第 4 节已给。其重复出现的 ExposedPayload 使用同一新数值赋值，故完整 96 参数 ClosedLeafStateGraph 闭合。

## 7. PAAxiom：完整 259 列 JointLeafRows 原样保留

`VerifierPAAxiomLeafStateGraph.lean:100` 的实际 327 参数公式是：共同 68 参数图；独立的 259 参数 JointLeafRows；三条 CrossEq 的 PA 桥；三个标签/结果等式。

把整个旧 259 元向量 c 原样作为 c'。`VerifierPAAxiomJointLeafRowsCompleteness.lean:243` 的固定公式只读取这 259 个参数，其合取包括：三条 Gamma/candidate/axiom WitnessRows；内部 endpoint 表与 rule 表的 axiom CrossEq；proofTag=1；以及以下实际三选一：

- fixed endpoint 与 fixed rule check；
- symbol endpoint 与相应 fixed rule check；
- induction endpoint 与全部 184 参数 induction rule check。

所有这些公式的参数、内部两张表、endpoint 输入与 suffix、parser 轨迹、生成的各公式、depth、route、resultBool 均逐数字保持。故通过旧合取消去，直接得到新所需的同一个 JointLeafRows 公式实例，旧所选 fixed/symbol/induction 分支也保持。

这里旧内部 endpoint 的输入和 suffix 不追加 S：它是独立规则证书，外围公式没有把它的整个输入或 suffix 与当前 verifier 流识别。它只通过 axiomTokens 接入；错误地把内部 endpoint suffix 也改为追加 S，反而会增加不必要的数学义务。

新外部桥 `VerifierPAAxiomLeafCrossTableBridgeGraph.lean:51` 的三条 CrossEq 为：

```text
新 proof-root Gamma  <->  c 的原规则表 Gamma；
新 proof-root first  <->  c 的原规则表 candidate；
新 certificate axiomTokens  <->  c 的原规则表 ruleAxiom。
```

前两条左端由 proof-root append 保持内容；第三条由 certificate append 的 PA 分支保留 axiomTokens。所有右端参数保持，第 2 节逐条引入新 CrossEq。三个等式 proofTag=c.proofTag、certificateTag=c.certificateTag、resultBool=c.resultBool 仍使用原值，因而成立。结合第 4 节共同图，完整 PA 叶状态图闭合。

这不要求重新证明公理检验的可靠性、不要求 PA 反射，也不把归纳公理的 truth 当作内部推导。依赖的旧前提已经含完整规则图；本局部结论只输运其使用位置。

## 8. 全部 429 列赋值及原 G 的引入

以下为闭区间列索引。来源为 `VerifierParseStateFormula.lean` 的 CurrentStateTerms、NextStateTerms、HeadTerms、SuccessCommonTerms、LeafOutputTerms、ClosedExtraTerms、PATerms。前三节给所有新状态、子结果及界，第 4 节给 parser 坐标。

| 列 | 新赋值 |
| --- | --- |
| 0—2 | 新 stateTable T'、单元宽 u'、容量 N' |
| 3—17 | current 的 start、finish、proofFinish、proofCount、certificateFinish、certificateCount、tasksFinish、taskCount、taskBoundary、valuesFinish、valueCount、valueBoundary、statusTag、statusPayloadStart、statusBool |
| 18—23 | current 的 taskBoundarySize、valueBoundarySize、H_t、V_t、H_v、V_v |
| 24—38 | next 的同顺序 15 个状态坐标 |
| 39—44 | next 的两个 boundarySize 及同一个 H_t、V_t、H_v、V_v |
| 45—58 | 新 current 头的 14 个 TaskCore/size 坐标，完整保留原 tag=10 头的内容 |
| 59—67 | 新 proofTable、proofWidth、proofTokenCount、proofInputStart/Finish、rootStart/Finish、proofTag、proofEndpointBound |
| 68—80 | 新 certificateTable、certificateWidth、certificateTokenCount、certificateInputStart/Finish、axiomStart/Finish、formulaStart/Finish、suffixStart/Finish、certificateTag、certificateEndpointBound |
| 81—91 | 新根 gammaFinish、gammaCount、gammaBoundary、firstFinish、firstCount、secondFinish、secondCount、witnessFinish、witnessCount、suffixCount、gammaBoundarySize |
| 92—98 | 第 3 节新 target 头的 start、finish、gammaFinish、gammaCount、gammaBoundary、bool、gammaBoundarySize |
| 99 | 旧 e[99]，即同一个 resultBool |
| 100—127 | Closed 分支逐个取旧 e[i]；其它两个分支取 0 |
| 128—386 | PAAxiom 分支逐个取旧 e[i]；其它两个分支取 0 |
| 387—428 | 三个叶分支均取 0 |

14 个任务坐标的次序为 start、finish、tag、gammaFinish、gammaCount、gammaBoundary、firstFinish、firstCount、secondFinish、secondCount、witnessFinish、witnessCount、suffixCount、gammaBoundarySize。两条状态的 statusTag 位于 15、36 列，均为 0；17、38 的 statusBool 取 0；97 与 99 都取旧规则结果 b。

Closed 的 100—127 列依次为 ruleTable、ruleWidth、ruleTokenCount、ruleProofTag、ruleCertificateTag，随后 Gamma 五坐标、formula 五坐标、negated 五坐标、stateBoundary、stateCount、empty 四坐标、ruleTableWidth、ruleValueBound；每一个都保持，未漏掉旧规则表的容量或内部状态数。

PA 向量的若干接口位置可由实际替换向量直接核对：c.ruleTable/Width/TokenCount 对应 128—130；c.resultBool 对应 307；candidate 起止对应 310—311；proof/certificate 标签对应 323—324；Gamma 起止对应 325—326；ruleAxiom 起止对应 331—332。于是三个末端等式在 429 列中恰为

`e'[66]=e'[323]`，`e'[79]=e'[324]`，`e'[99]=e'[307]`。

它们通过两边保持原值成立。原 PA 桥的右端地址也恰引用上述保持的列，没有误接到新 proof 表的 boundary。

按第 4 节两个 StateCore、BoundedHead、Frame，及第 5、6 或 7 节对应叶图，在原 ParseStateGraphDef 的 success 位置引入所选析取。再在 `VerifierStepFormula.lean:166` 的 Halted/Finish/Parse/Combine 析取中选择 Parse，即得原固定 429 参数 `compactNumericVerifierStepGraphDef(e')`。未选分支的参数可以取 0，因为原公式不要求其它析取同时成立。

若要将此向量装入一条外层矩阵行，选 U 严格大于全部 429 个数的位长，包括保留的旧 Closed/PA 规则表及所有新界。以 A_0=0、A_(j+1)=A_j+e'[j]*2^(j*U) 作有限前缀构造，归纳保持每个已写 Entry 及 A_j<2^(j*U)。原 BoundedRow 的 429 个存在见证依序取上表值。旧规则块数值可能很大，但本存在性证明允许提高 U，不提出多项式大小结论。

## 9. 完成范围及仍不包含的义务

三类 leaf parse-success 的实际 429 列 G 行输运已经纸面闭合，包含 resultBool=0、空 Gamma、空旧值栈、空续延，以及旧表偶然别名等情形。Closed/PA 独立规则表无需额外内部搬运引理；PA 外层封闭 parser 和 induction 证书 parser 分别使用已经证明的 parser-append 引理，引用位置及活动数据已明确。

本稿证明对给定成功叶行的 PA 见证变换，没有把任意真规则图的证明生成、规则可靠性或整个接受矩阵隐含进结论。条件 (3) 的其余任务仍包括 combine-success 完整分支、跨行共同布局和相邻 CrossEq 接缝、五节点 MP 新片段与两段旧有效前缀的合成、最终 Finish 与规定燃料填充。不能仅凭本稿宣称整个条件 (3) 完成。
