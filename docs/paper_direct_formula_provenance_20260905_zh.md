# 当前 P_direct 的结论公式来源与原位宽界

日期：2026-09-05。仅纸面证明，不新增 Lean。

本文补充内部 MP 构造的一个具体计量环节：公开结论公式使用的那张公式表及
formulaWidth，确实受到当前输入见证的 inputWidth 控制。核心局部引理从实际
ProofRoot/Sequent 的 Cons、Append 子式推出，不调用解析器在标准自然数上的
sound/exactness 定理。

最终结果分清两个接口：本文独立证明“首次解析根的 Γ 第 0 项来自初始 proof
正文的 token 偏移 2”，再接《MP 整段组装审计》的“最终 Γ 等于首次根 Γ”
标记不变量。后一不变量不是本文重新假设所有 verifier 运行都语义正确。

## 1. 精确目标与所用源码

记当前 22 参数矩阵的 inputTable/inputWidth/inputTokenCount 为 A/W/M，
formulaTable/formulaWidth/formulaTokenCount 为 F/wf/L，formulaCode 为 f。
初态 proof 正文长 p，certificate 正文长 c。目标是原见证上的结论：

```text
2+L ≤ p ≤ M，
对每个 j<L：Row(F,wf,j)=Row(A,W,2+j)，               (1.1)
wf+4 ≤ W ≤ bound，ell(f)=wf+1 ≤ W+1 ≤ bound+1。    (1.2)
```

其中 Row(T,w,i)=(T div 2^(i*w)) mod 2^w，ell 是源码 lengthDef 所定义的
二进制位数，ell(0)=0。(1.2) 中保留较弱的 ell(f)≤W+1，足以用于载荷计量。
所有原表格数、位宽和原见证保持不变；不会改用某个更短的等价公式码。

主要源码均在 integration，以下省略共同前缀
`FoundationCompactNumericListedDirect`：

- `ProofPredicate.lean:48`：当前 22 参数矩阵。
- `VerifierAcceptedPayloadMatrix.lean:32`：输入实际采用 CanonicalAtWidth。
- `ProofRootSuccessBoundedFormula.lean:30`：五种成功 endpoint 的析取。
- 五个 `ProofRoot*Endpoint.lean`：共同的根 TaskCore、第一次 Cons、Sequent endpoint。
- `SequentFormulaEndpointInstallation.lean:51` 及对应 `SequentFormulaEndpointFormula.lean`：
  第二次 Cons、Γ 结构、初始 suffix 的两次 Entry。
- `SequentFormulaTraceFormula.lean:33`、`SequentFormulaStepFormula.lean:44`：
  对每个 Γ 元素的原受限行量词及 Append 子式。
- `NatListConsRows.lean:24`、`NatListAppendSlices.lean:25`：实际复制关系。
- `VerifierAcceptedConclusionRow.lean:42`、`CrossTableFormulaSetSingleton.lean:25`：
  接受结论的非空性和逐公式 CrossEq。
- `TokenStreamTableau.lean:27`、`ArithmeticPrimitives.lean:228`：原 offset 递推。
- `VerifierAcceptedTraceInputTableau.lean:26`：公开码的 sentinel 等式。

这里需要的是实际 `.mkSigma` 子式的 PA 推导。上述同名 `Compact...` 的展开仅作
阅读这些子式的记号，不通过 `...Def_spec` 把标准模型的真命题当作 PA 定理。

## 2. 两个无需语法语义的列表引理

沿用《公开载荷与两个内部列表》第 2 节的 PA 行读取引理：固定宽度 Entry 的值
唯一，TokenSlicesEq/CrossEq 给对应 Row 值相等。不同表宽和边界码的数值可以不同。

### 2.1 NatListWitnessRows 的位置刚性

若 `NatListWitnessRows(T,w,N,s,h,t,B,size)` 成立，StructuredList 的头和边界
首项给 B 的第 0 项为 s+1；UnitBoundaryRows 每项给后一边界等于前一边界加 1。
对 i≤h 作 PA 归纳，并用 Entry 唯一性连接相邻项，得到

```text
Entry(B,N,i,s+1+i)，t=s+1+h，Row(T,w,s)=h。
```

因此列表正文第 i 项就是 Row(T,w,s+1+i)，i<h。h=0 时从边界首、末 Entry
的唯一性得到 t=s+1，归纳不需要取得第 0 个元素。

把这个位置式代入实际 ConsRows：其计数式是 targetCount=sourceCount+1；
头 TokenCell 固定 target 正文第 0 项为 head；后续 AtomicRowEq 配对的是
source 第 i 项和 target 第 i+1 项。于是 PA 推出

```text
target[0]=head，target[i+1]=source[i]（i<sourceCount）。
```

这不是把 `eq_cons_of_rows` 的 Nat 列表结论移入 PA；它直接是原边界 Entry 和
有界位等价的消去。以下使用有限数组记号表示这些 Row 等式。

### 2.2 同一根块中的 Γ 边界对齐

成功 endpoint 的隐藏 TaskCore 与 parse 暴露的 TaskCore 使用相同的
rootStart/rootFinish；Sequent 的 Γ 结构从 rootStart+1 开始。
所有这些 Γ 的计数头位于同一单元 rootStart+1，所以其 gammaCount/valueCount
由 Entry 唯一性相等。Γ 外层边界第 0 项均为 rootStart+2。

设已对齐第 i 项的左边界 b。两侧 NatListListRowsWellFormed 在 b 读取该公式
列表长度 h；同一头单元使 h 相等，NatListSlice 使右边界都等于 b+1+h。
归纳给全部对应左右边界相等，最后给 gammaFinish 相等。无需先证明两边的
整个边界整数相等，也无需给旧见证添加规范上界。

后面只需第 0 项的这个结论：Sequent 第 0 个 value slice 恰是暴露根 Γ 的
第 0 个含长度头的公式列表。

## 3. 实际根 endpoint 给出的偏移 2 来源

任取五种 ProofRoot 成功分支，记其原输入列表正文为 P，长 p；
Sequent endpoint 的原输入正文为 Q，长 q；Sequent 的 first 列表正文为 U，长 u。
这些是原 parser 表中的有限 Row 数列，不要求它们在不同存储块中物理相邻。
五个分支都含如下原子式：

```text
NatListWitnessRows(原输入 P)，TaskCore(原根)，
ConsRows(Q.boundary,q,P.boundary,p,rootTag)，
SequentEndpoint(Q, valueStart=rootStart+1, valueFinish=gammaFinish, ...)。
```

SequentEndpoint 内又有

```text
NatListWitnessRows(Q)，NatListWitnessRows(U)，
ConsRows(U.boundary,u,Q.boundary,q,valueCount)。
```

两次应用第 2.1 节，得到同一 PA 分支内的等式

```text
p=q+1，q=u+1；P[0]=rootTag，P[1]=valueCount；
P[2+j]=U[j]，j<u。                               (3.1)
```

注意 P 不含其内部存储用的列表长度头。这里移去的是 raw proof 中本来就有的
rootTag 和 sequent 的公式个数；不是又移去两个存储长度头。

现在假设根 Γ 非空。第 2.2 节给 valueCount>0，所以可以实例化原
SequentFormulaStepRowsBoundedGraph 的 rowIndex=0。这个受限全称的 rowCount
实际就是 valueCount，不是另一个未核对的运行长度。

该行的 current.start/current.finish 与 SequentEndpoint 的 firstStart/
firstFinish 分别读取 suffixBoundary 的第 0、1 项，故相等。其列表长度也因
同一个头单元而相等：current.count=u。

该行的 value.start/value.finish 读取 valueBoundary 的第 0、1 项。
由第 2.2 节，这就是根 Γ0 的左右端点；设其正文长 h，正文为 V。
原 Append 子式逐字给出

```text
current.count=value.count+next.count，
TokenSlicesEq(value.start+1,value.finish,
              current.start+1,current.start+1+value.count)。
```

因此 h≤u，且 V[j]=U[j] 对所有 j<h 成立。与 (3.1) 合并得

```text
2+h≤p，Γ0 的正文 V[j]=P[2+j]（j<h）。             (3.2)
```

所有五个 ProofRoot 分支的差异都位于这个共同 Sequent endpoint 之后。
故对五个析取作固定次数消去、对其原有有界存在见证作消去，即得统一的 (3.2)。
并不需要证明其 Formula/Term parser 消耗了正确语法树；所需“value 是 current
的前缀”已由原 Append 明文给出。

## 4. 接到公开输入及公开结论的同一张表

首次操作是解析初始 proof 时，实际
`VerifierParsePayloadSuccessSeparatedTablesFormula.lean:35` 的前半 CrossEq
比较初态 proof 的完整含头 slice 与上节 parser 输入的完整含头 slice。
两边 NatList 的头及完整 slice 长度给相同 p，offset=1+i 的比较给正文第 i
项相等。该 offset 合法，因为整个 slice 长为 p+1。

《公开载荷与两个内部列表》第 3–4 节已直接沿原 InputSplit 和 Initial 的
两层 CrossEq 证明

```text
M=p+c，初始 proof[i]=Row(A,W,i)（i<p）。          (4.1)
```

为把 (3.2) 用于最后的公开结论，需要如下已单独展开的运行接口：

```text
接受矩阵的最终唯一 ChildResult 中 Γ，逐项等于首次 parse 暴露的根 Γ；
其计数和每个公式列表正文长度也对应相等。
```

该接口由 [MP 整段组装审计](paper_direct_mp_assembly_audit_20260905_zh.md)
第 3.1–3.3 节的根 combine 底标记归纳提供：叶根直接压入其 Γ；
非叶根的 combine 任务保留在栈底，栈顶 ReplaceHead/Drop 保留它；弹出它的
combine 给最终 Γ。Finish 前缀及其后的 halted 行、相邻行 CrossEq 的对齐也
属于该运行接口。本文不以“最终 Γ 非空”替代这个来源接口。

实际 AcceptedConclusionRow 从最后一行的 0/1/2/34/35/44 列取出结果表及
唯一值列表；它的 FormulaSetEqSingleton 只要求 gammaCount>0 和每个 Γ 项
都等于公开公式。它没有要求 gammaCount=1，允许 Γ 中重复公式。

在其有界全称中取 index=0：两个边界 Entry 把比较区间固定为最终 Γ0 的
正文 `[formulaStart+1,formulaFinish)`。CrossEq 把这段与 F 的 `[0,L)` 比较，
所以其正文长度等于 L，且正文第 j 项等于 Row(F,wf,j)。沿上述运行接口把该项
拉回首次根 Γ0，再用 (3.2)、(4.1)，恰得到 (1.1)。

这里的非空性只用于合法取第 0 项；没有为消除重复 Γ 添加任何集合到列表的
非法推断。尤其不能把整个 Γ 块等同于单元素列表 `[f]`。

## 5. 原 offset 递推直接给位宽，不需要重新编码

当前 AcceptedPayloadMatrix 对输入使用 CanonicalAtWidth；ProofPredicate
对公开公式也使用相同 CanonicalAtWidth。某些旧 InputTableau 文件允许冗余
binaryNat 位的说明不适用于这里实际调用的 16 参数 AcceptedPayloadMatrix。

在原输入 offsetTable 中，令 a_i 为第 i 个宽度 W 的行值，0≤i≤M；
公式 offsetTable 的相应值记 b_j，0≤j≤L。TokenStreamTableau 的两条边界
Entry 给

```text
a_0=0，a_M=W，b_0=0，b_L=wf。
```

对 i<M 实例化其原受限全称。token 表读取的见证由 Entry 唯一性等于
Row(A,W,i)，两次 offset Entry 同样固定为 a_i、a_(i+1)。实际 TokenSegment
含 `compactNatSizeDef size token` 和精确等式 `next=offset+2*size+2`，故

```text
a_(i+1)=a_i+2*ell(Row(A,W,i))+2。
b_(j+1)=b_j+2*ell(Row(F,wf,j))+2。               (5.1)
```

这些式子用的是同一个 lengthDef 的功能性；没有引入与原 token 编码无关的
“预期长度”。PA 对 i 作归纳可得 a_i 单调且 a_2≥4，2≤M 由 (1.1) 已得。

由 (1.1)，(5.1) 在 i=2+j 与公式的第 j 步增加完全相同的自然数。
对 j≤L 作 PA 归纳，基步 b_0=0，得到

```text
a_(2+j)=a_2+b_j。
```

取 j=L，并用 2+L≤M 和 a_i 单调，有

```text
4+wf ≤ a_2+b_L = a_(2+L) ≤ a_M=W。
```

这就证明原来的 wf+4≤W，不取新 tokenTable，也不把巨大内部表见证的位数
误当成公开 payload 的位数。若 L=0，公式 tableau 的两个端点均读取第 0 行，
从而 wf=0；同一个归纳及不等式仍然有效，无需空流例外。

最后，公式 CanonicalAtWidth 的原见证给

```text
f=payload+2^wf，0≤payload<2^wf。
```

故 2^wf≤f<2^(wf+1)，lengthDef 的通常 PA 刻画给 ell(f)=wf+1。
与矩阵已有 W≤bound 合并即为 (1.2)。当 f 恰是某公式的 compactFormulaCode，
这直接控制的是该同一公式码的位数，而不是另一个外延等价句子的码。

## 6. 消去矩阵见证及准确完成范围

上述论证只用固定次数的原子式消去及 PA 归纳：列表位置、Γ 游标对齐、
offset 单调性、匹配区间的 offset 差。所有数列都可写成 Row 的算术定义，
因此不要求在 PA 中凭空接受一个外部解码得到的 Lean 列表。

接入第 4 节的运行接口后，PA 对 22 参数原矩阵可证 (1.1)–(1.2)。
在 P_direct 的原有存在见证外依次作存在消去，得到

```text
PA 证明：对所有 bound、f，P_direct(bound,f) → ell(f)≤bound+1。
```

更具体地，对一个原矩阵见证，公开公式载荷 wf 本身≤W≤bound。MP 构造中
固定次数复制的公开公式字段，其 binaryNat 载荷因而有明确线性界；若字段另带
公式 token 数头，2L≤wf 给 L≤bound，新增长度头至多 2ell(bound)+2 位。
合成中其他任务/证书/规则 trace 的构造与计量仍由各自引理承担，本文不以此
宣布条件 (3) 的完整内部 MP 定理已经结束。

本局部长度推导不使用 Con(PA)、反射或 verifier 的标准模型 soundness。
尚需区分纸面与形式化状态：这里已给出沿实际矩阵的 PA 推导，未新增或声称
已有相应 Lean PA 导出定理；第 4 节明确依赖独立的运行标记引理。
