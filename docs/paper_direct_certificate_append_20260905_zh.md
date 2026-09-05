# 当前 certificate-node 成功公式的后缀追加

日期：2026-09-05。仅作纸面证明，不新增 Lean。

本稿直接处理 `compactCertificateNodeSuccessBoundedGraphDef`，不把 Nat 上的
`sound`、`spec`、`exists_bounded` 或 parser 函数等式当作 PA 内证明。
四类成功分支在纸面上均已闭合。前三类在下文独立证明；归纳公理分支
使用同轮已给出的普通 parser 追加引理，其准确接口与证书外壳列在第 6 节。

## 1. 实际四个析取与要保留的量

`FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula.lean:36`
的实际成功图有如下四个析取。

| 分支 | 结构证书 certificateTag | 内部关系 |
| --- | --- | --- |
| simple | 0、2、3 | 两个 NatListWitnessRows 与一个 ConsRows |
| fixed PA | 1 | 四个 NatListWitnessRows、两个 ConsRows、一个 AppendSlices，PA 标签小于 22 且不等于 3、4 |
| symbol PA | 1 | 四个 NatListWitnessRows、一个 ConsRows、一个 AppendSlices、三个 AtRows 及符号合法性公式 |
| induction PA | 1 | 三个外层 NatListWitnessRows、两个 ConsRows、一个 AppendSlices 及普通 SyntaxExactEndpointGraph |

simple 的标签 0、2、3 分别是普通叶、一元、二元结构证书节点。
它们在此处都只消费一个标签；子树证书仍在返回的 suffix 中。
不能把结构标签 3 与 symbol PA 分支内部的 PA 标签 3 混为同一个标签。

设旧公共 token 表为 A，单元位宽 u，总 token 容量 N。
记 I、Q、X、C、F 分别为其指定切片的 input、suffix、PA tail、
axiomTokens、formula-parser input。记相应正文长度为 p、q、x、c、f。
这些字母只是下述 Read 值序列的简写，不向 PA 语言添加列表类型。

追加数据由另一张原始表 B、位宽 v、声明长度 r 给定：

```text
R(j)=ReadCell(v,B,j)，j<r。
ReadCell(w,T,j)=(T div 2^(j*w)) mod 2^w。
```

目标是存在一组新的公共表、位宽、容量、活动切片端点及 endpointBound，
使原成功公式再次成立，并以原 NatListSlice、AppendSlices、CrossEq 表达：

```text
I' = I++R；Q' = Q++R；certificateTag' = certificateTag；
在 PA 分支中，C' 与 C 的完整列表切片 CrossEq。
```

这里的 `++` 全部在第 2 节展开为计数方程与逐项复制，不能单独用作 PA 前提。
新 endpointBound 允许增大。本稿证明 PA 内存在性，不声称任意旧见证已经有小界，
也不从本稿直接推出短证明生成器的多项式长度界。

simple 析取不读取 axiomStart、axiomFinish、formulaStart、formulaFinish；
fixed/symbol 析取也不读取 formulaStart、formulaFinish。
因此不能仅由该析取推出这些未使用坐标指向一个合法空列表。
本构造可把未使用坐标原样保留；额外调用方若要求合法空字段，应另给实际空列表切片。

## 2. PA 内的列表行工具：抽取、重编码、复制

### 2.1 NatListWitnessRows 强制单位边界

`FoundationCompactNumericListedDirectNatListWitnessRows.lean:27` 的原公式为：
StructuredListLayout、UnitBoundaryRows、边界码真实位长、以及
`boundarySize≤(count+1)*N`。

从 `NatListWitnessRows(A,u,N,s,k,t,D,d)` 出发，PA 可推出

```text
t=s+1+k≤N；s<N；
ReadCell(N,D,j)=s+1+j，对所有 j≤k。
```

证明：ListHeader 给出 bodyStart=s+1；BoundaryTable 的第 0 项给出该初值。
UnitBoundaryRows 在 j<k 给出第 j+1 项等于第 j 项加一。
两份 Entry 的数值由唯一读取引理识别，按 j 作 PA 归纳即得全部边界。
最后一个 Entry 给出 t=s+1+k。k=0 时，首项和末项是同一 Entry，结论仍成立。

于是第 j 个正文值恰为 `ReadCell(u,A,s+1+j)`。ConsRows 或 AtRows 内部另取的
left/right 见证必须等于这些游标；这由 Entry 唯一性给出，不需要调用列表 realize。

### 2.2 在同一新表中安排有限块

给定若干要写入的块，每块含一个长度头和明确数量的正文 token，先决定所有块的位置。
可取前 N 项保留旧 A 的前 N 个 Read 值，接着写一个完整的 `[r]++R` 列表，
再写所需的新 I、Q、X 等列表块。总容量 N* 是这些块的长度之和。
非活动空位如有需要填 0。所有块的位置与 N* 在计算边界码之前确定。

选

```text
u*=max(u,v,ell(N*))。
```

每个复制的旧值适合 u；每个 R 值适合 v；每个新增长度头不超过 N*。
故全部值适合 u*。按 token 索引逐项构造

```text
T_0=0；T_(j+1)=T_j+a_j*2^(j*u*)。
```

PA 归纳维持 `T_j<2^(j*u*)` 及每个已写单元的原 Entry。
商余总定义性、指数总定义性和归纳给出最终表 T*，也排除了进位污染。
任意旧表的声明容量外高位均不复制。

构造正文 I++R 时，逐项定义为

```text
Iplus(j)=旧 I(j)，j<p；
Iplus(p+j)=R(j)，j<r。
```

其它追加块同理。没有先假定存在一个外部列表，再把其存在性送进 PA。

### 2.3 为每个新列表重新建立原 WitnessRows

新列表起点 s*、正文长度 k*、终点 t*=s*+1+k* 满足 t*≤N*。
取边界码

```text
D*=Σ_{j≤k*}(s*+1+j)*2^(j*N*)；d*=ell(D*)。
```

每个边界值不超过 N*，故小于 2^N*；第 2.2 节的追加归纳构造所有 Entry。
相邻值差一，首末值正确，因而同时满足原 BoundaryTable 和 UnitBoundaryRows。
表格位长满足 `d*≤(k*+1)*N*`，恰好是原公式要求的界。
原 NatListSlice 也由真实头值与 `t*=s*+1+k*` 得到。

对保留在旧位置的 C 等列表，也使用此处的新边界码。
只因 token 正文不变就保留旧边界自然数码是错误的：原边界 Entry 的位宽参数
从 N 变成 N*，必须重新编码。

### 2.4 两个严格保持引理

其一，若旧 `ConsRows(Y,X,h)` 连同两侧 WitnessRows 成立，则新
`ConsRows(Y++R,X++R,h)` 成立。旧公式给出

```text
|X|=|Y|+1；X(0)=h；X(j+1)=Y(j)，j<|Y|。
```

这些是 Entry 唯一性与 AtomicRowEq 的位外延性推出的算术等式。
新头值由复制保留；对新 ConsRows 中任意 j<|Y|+r：

- j<|Y| 时使用旧等式及旧正文拷贝；
- j=|Y|+b、b<r 时，两边都是同一 R(b)，因为新 X 的索引 j+1 等于 |X|+b。

显式选择新边界读数 `sY+1+j`、`sY+2+j`、`sX+2+j`、`sX+3+j`。
它们的原有界量词由各列表终点≤N*保证；AtomicRowEq 的两个单位长度方程成立。
对应 token 数值相同，结合各自 Entry 给出所有 bitIndex<u* 的原位等价。

其二，若旧 `AppendSlices(C,Q,X)` 及三侧列表有效，则新
`AppendSlices(C,Q++R,X++R)` 成立，C 正文保持。
旧关系给 `x=c+q`；新关系的长度方程为 `x+r=c+(q+r)`。
左段第 j<c 项由旧左 SliceEq 保持。右段第 j<q+r 项分 j<q 与 j=q+b：
前者由旧右 SliceEq，后者两边都是 R(b)，因为 c+q+b=x+b。
显式取两个 SliceEq 的 count 分别为 c、q+r，端点方程和容量界逐项满足。
这也证明 I、Q 等追加块与保留的旧列表及独立 `[r]++R` 列表之间的原 AppendSlices。

在不同旧位宽与 u* 之间，先识别单元数值再从新 Entry 推出位等价。
不能只复制旧 width 范围的位等价而遗漏新加的高位；高位为零由数值适合各自位宽保证。

## 3. simple 的 0、2、3 三个分支已闭合

从原六个有界存在量依次取 input/suffix 边界、计数与边界位长。
保留 tag 的原析取，旧 ConsRows 给 p=q+1。

在第 2.2 节的旧前缀之后依次写 `[r]++R`、I++R、Q++R。
可精确取

```text
N*=N+(1+r)+(1+p+r)+(1+q+r)。
```

两个新 WitnessRows 由第 2.3 节构造；新 ConsRows 由第 2.4 节构造。
这样得到原 `compactCertificateNodeSimpleEndpointGraphDef` 的全部合取项。

把新的 inputBoundary、inputCount、inputBoundarySize、suffixBoundary、suffixCount、
suffixBoundarySize 的和加 1 作为 endpointBound*，逐个引入六个原有界存在量，
得到原 `compactCertificateNodeSimpleEndpointBoundedGraphDef`，再引入统一成功图的
第一个析取。这里不需要分开运行 leaf/unary/binary parser，也不需要有限燃料论证。

r=0、q=0 都包含在上述分情况中；零长度正文的位全称为空，但真实列表头仍被写入。

## 4. fixed PA 分支已闭合

原 `CertificateNodeFixedPAEndpoint.lean:60` 的矩阵给出四个 WitnessRows，
两个 ConsRows 分别为 `Cons(X,I,1)`、`Cons(Q,X,paTag)`，以及 `Append(C,Q,X)`。
故 PA 有

```text
p=x+1；x=q+1；x=c+q，因此 c=1。
```

保留 paTag，并保留 `paTag<22 AND paTag≠3 AND paTag≠4`。
新表写独立 R、I++R、X++R、Q++R；旧 C 列表保留在原位置。
容量取旧 N 加四个新块的精确长度即可。

用第 2.3 节重建这四个活动列表的 WitnessRows，包括 C 的边界码。
两个 ConsRows 分别应用第 2.4 节的 cons 引理，AppendSlices 应用其 append 引理。
certificateTag=1 和 paTag 的固定算术条件原样保留。

由此原 FixedPAEndpointGraph 的每一合取项都已构造。
新的十五个内部量为四个列表的边界/计数/位长、X 的首尾游标及 paTag；
取这些数的和加 1 为 endpointBound*，引入十五个原有界存在量即可。
C 的公共完整切片与旧 C 跨表相等，由保留头值和正文的全部 Entry 给出原 CrossEq。

## 5. symbol PA 分支已闭合

原 `CertificateNodeSymbolPAEndpoint.lean:66` 与上一分支的差别为：
只保留外层 `Cons(X,I,1)`；`c=3`；C 的第 0、1、2 项由原 AtRows 分别读出
paTag、arity、symbolCode；还有原函数或关系符号合法性析取。

仍构造 I++R、X++R、Q++R，保持 C；重建四个 WitnessRows。
外层 ConsRows 和 AppendSlices 分别使用第 2.4 节。
对 j=0、1、2，取 C 的新边界值 `sC+1+j` 和 `sC+2+j` 作为 AtRows 见证。
因 c=3，索引严格小于 c；原对应 token 值逐项保留，故三个原 AtRows 成立。

paTag、arity、symbolCode 数值均不变，所以原
`compactAdditiveArithmeticFuncCodeValidDef` 或
`compactAdditiveArithmeticRelCodeValidDef` 通过等式代换原样成立。
此处无需重新执行符号解码器，也不使用该 guard 的标准模型 spec。

十七个原有界见证取上述新值，endpointBound* 取它们的和加 1。
这给出原 SymbolPAEndpointBoundedGraph，而非仅一个更弱的“三个 token 未变”关系。

## 6. induction PA 的准确接口与全部外壳输运

### 6.1 唯一内嵌解析器

原 `CertificateNodeInductionPAEndpoint.lean:64` 的 parser 项逐字为

```text
CompactParserSyntaxExactEndpointGraph
  A u N formulaStart formulaFinish suffixStart suffixFinish 1 1 0 parserCoordinates。
```

三个参数的源码名分别是 taskKind、taskBinderArity、taskRepeatCount；
最后的 0 是 repeatCount，不是额外的 depth 参数。
这是普通 syntax parser，不是 ClosedSuccess 或 PA 反射公式。
formulaStart/formulaFinish 包围的是尚待解析的完整输入 F，包含返回的 Q；
它并非仅包围已经消费的公式 token。

所需普通解析器引理的准确内容为：从上述原 endpoint 公式，给任意明确 R，
在 PA 内构造同一个 endpoint 公式，其中输入是 F++R、expected 是 Q++R，
initial task triple 仍为 (1,1,0)。原十个 parser 坐标全部重新构造。
新精确 fuel 为

```text
16*(f+r+1)*(f+r+1)+8。
```

此外，构造新公共 token 表时须允许同时安排任意明确给定的有限背景块。
本应用的背景块是旧表前 N 项、独立 R、I++R 和 X++R。
必须先定最终 token 容量，再按该容量重建 parser 各层边界与界。
不能先得到一份 parser 表，再只改变 tokenCount 来塞入证书字段。

该引理由同轮文稿 [实际解析终点公式的后缀追加输运](paper_direct_parser_append_20260905_zh.md)
第 1 节的精确接口及第 2–4 节的构造提供，已核对上述背景块要求。
其证明从原相邻行提取状态，以 failed 吸收和最终 completed 排除全部失败行，
逐支搬运成功 Step，并用真实 Done-completed 行补到新精确 fuel。
第 4 节先统一背景区与所有状态块的原始长度，再确定 N* 及重建边界，
因此这里没有把一个独立 parser 表的 tokenCount 非法增大。

### 6.2 从该具体引理到原 induction 公式

旧矩阵给三个外层 WitnessRows、certificateTag=1、
`Cons(X,I,1)`、`Cons(F,X,22)`、上述 parser endpoint 与 `Append(C,Q,X)`。
在 PA 内消去旧有界见证，得到

```text
p=x+1；x=f+1；x=c+q。
```

在普通 parser 输运构造所允许的背景区保留旧 C，写 I++R、X++R 及独立 R。
parser 新输入与新 expected 的正文分别是同一 F++R、Q++R。
若各有重复列表副本，通过逐项相同的 Read 值建立 CrossEq，或直接共享指定切片；
最终所有证书合取项使用同一组公共端点和同一 token 表。

I++R、X++R、C 的原 WitnessRows 按第 2.3 节构造。
两个 ConsRows 按第 2.4 节分别搬运：

```text
Cons(X++R,I++R,1)；Cons(F++R,X++R,22)。
```

AppendSlices 按同一节得到 `Append(C,Q++R,X++R)`。
这保持了旧完整 axiomTokens C；没有把 R 误加进已消费的公理证书 payload。
certificateTag=1 原样保持。parser 项由第 6.1 节的同一个实际 endpoint 引理提供。

最后以原二十一项见证的新值构造 endpointBound*：三个外层列表各自的
boundary/count/boundarySize，X 的 start/finish，以及 parser 的十个坐标。
取这二十一数之和加 1，逐个引入原有界存在量，即得到原
`compactCertificateNodeInductionPAEndpointBoundedGraphDef`。

这里没有剩余的证书递归解析器：唯一递归部分就是第 6.1 节列出的普通公式解析器。
外壳输运不要求任何公式的真值或可证明性，不引入 Con(PA) 或反射。

## 7. 当前完成范围

simple 的三个结构标签、fixed PA 标签族、symbol PA 两族由本稿独立给出
当前实际算术公式的 PA 内追加构造。归纳公理分支由第 6.1 节已核对的普通
SyntaxExactEndpointGraph 共同引理，加第 6.2 节的全部外壳构造闭合。

对旧 SuccessBoundedGraph 的四个析取作固定次数的析取消去，分别使用第 3–6 节，
再引入原成功图相应析取，得到统一的 PA 内存在结论：任意旧成功见证和任意
编码 R 都产生新的原 SuccessBoundedGraph，I、Q 同时追加 R，certificateTag 保持，
所有 PA 分支的已消费 axiomTokens 完整保持。未使用公共坐标按第 1 节处理。

完整五节点 MP 仍另需任务/值栈续延、各规则字段搬运及整段 429 列运行的接缝组装；
本稿没有把标准自然数下的成功运行选取当作 PA 内输运，也不把完整条件 (3) 标为完成。
