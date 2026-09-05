# 实际解析终点公式的后缀追加输运

日期：2026-09-05。范围：MP 矩阵输运记录第 6.1 项中的 proof-root parser。

本文证明一个纸面 PA 引理：给定当前实际成功解析终点公式的见证，在输入和返回后缀同时追加同一有限 token 序列后，可以构造新的实际终点公式见证。普通语法解析、封闭语法解析、sequent 解析及五类 proof-root 成功图均在下面的构造范围内。本结论不包含整个 `P_direct` 的条件 (3)，也不是已经提交到 Lean 的 PA 证明。

这里的“PA 证明”是对源码中固定 `.mkSigma` 公式展开后作算术推导。名字如 `Entry`、`SameRows`、`Step` 均是这些固定公式的缩写。下面没有使用 `Evalb` 的 Nat `spec` 定理，没有由 typed parser 的 Nat `sound`/`completeness` 反推 PA，也没有调用反射、PA 一致性或通用“PR 可表示性”来替代公式核对。

## 1. 实际公式与结论的接口

普通终点的源码链为：

- `FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula.lean`：输入、expected 两个 `NatListWitnessRows`，以及 `ParserSyntaxExactBoundedGraph`。
- `FoundationCompactNumericListedDirectParserSyntaxExactFormula.lean`：固定燃料 `f(n) = 16*(n+1)*(n+1)+8`。
- `FoundationCompactNumericListedDirectParserSyntaxTraceFormula.lean`：`stateCount=fuel+1`、`InitialFinalBounded`、`AdjacentRowsBoundedGraph`。
- `FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula.lean`：每条相邻行绑定 27 个数值见证，并检查两边的 `BinaryNatStatusValidBounded`。
- `FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula.lean`：两次 `StateAtRows` 和一次固定 26 参数 `SyntaxStepRows`。
- `FoundationCompactNumericListedDirectParserSyntaxStepFormula.lean`：Done、Empty、Repeat、Term、Formula、Invalid 六个析取分支。

后面统一把 PA 内编码的有限数组写成 `X`，数组长度写成 `|X|`。这不是借用元语言的有限性：数组由固定宽度读数关系编码；所需长度归纳、前缀打包归纳和有限见证收集均在 PA 内完成。`[|X|] ++ X` 表示实际 additive flat-list 存储块。

普通终点输运引理的精确接口如下。

假设旧表 `T,u,N` 及十个坐标满足实际的

`compactParserSyntaxExactEndpointGraphDef(T,u,N, a,b, c,d, k,h,q, coordinates)`。

由两个实际列表见证读出输入数组 `X` 和 expected 数组 `Y`。任给编码有限数组 `R`，还可给定任意有限个背景存储块及其相容的布局要求。存在新表 `T',u',N'`、新输入与 expected 地址、新十坐标，使得：

1. 新输入块恰为 `[|X|+|R|] ++ X ++ R`；新 expected 块恰为 `[|Y|+|R|] ++ Y ++ R`。
2. 新实际 `compactParserSyntaxExactEndpointGraphDef` 成立，三个初始任务参数仍为 `taskKind=k`、`taskBinderArity=h`、`taskRepeatCount=q`。
3. 新状态数恰为 `f(|X|+|R|)+1`，不是任意一个足够大的数。
4. 给定的有限背景块可同时放在这个新表里；若新输入、expected 块已在一个相容的有限布局中指定，可使用这些块，内部状态放在后面的新空间。
5. 旧 `tokenCount`、旧地址和旧 boundary 整数不必保留。所有 boundary 都在最终的同一个 `N'` 确定后重建，不能先完成解析器表再只增加 `tokenCount`。

“相容的布局”仅要求要求重叠的 token 位置具有相同值；没有给予外部任意预填的冲突地址以实现保证。最常用情形是先列出互不相交的块，然后由前缀长度和分配地址。背景区也可以包括旧表的全部声明 token 单元，使旧有限内容仍可引用。

第 4 节给出这一引理的实际构造；特别包括证书 induction 分支需要的 `(k,h,q)=(1,1,0)`。

## 2. 基础行公式的算术读法与构造

### 2.1 表单元和刚性的列表边界

沿主稿编码层引理，在 PA 中定义

`read(A,w,i) = (A div 2^(i*w)) mod 2^w`。

实际 `compactFixedWidthEntryDef(A,w,i,v)` 与 `v=read(A,w,i)` 等价。其证明只用指数、除余和有界位归纳。因此同一表、宽度、索引上的两个 Entry 给出相等的值；若一个规范表的某单元值为 `v<2^w`，可以直接引入该实际 Entry 公式。

`NatListWitnessRows(T,u,N,s,n,e,B,ellB)` 展开后包含 StructuredListLayout、UnitBoundaryRows、真实二进制长度等式和 `ellB≤(n+1)*N`。对 UnitBoundary 的索引作 PA 归纳，得到：

`B[i]=s+1+i`，`0≤i≤n`，且 `e=s+1+n`。

这里和下文的 `B[i]` 均以实际 Entry 展开。列表头单元为 `n`，第 `i` 个数组值就是 `read(T,u,s+1+i)`。TripleBoundaryRows 的同一归纳给出任务数组的边界 `s+1+3*i`，每个任务严格是三个连续单元 `kind,binderArity,repeatCount`。

这些等式有一个关键用途：同一 `StateAtRows` 状态区间在两条相邻行中由不同存在见证描述时，它们仍读出同一 token 数组、同一任务数组和同一 status 区间。证明顺序为：state boundary 的两个 Entry 确定 start、finish；start 的 token 头确定 token 数；UnitBoundary 确定 tokensFinish；该位置的任务头确定任务数；TripleBoundary 确定 tasksFinish。无需先证明整个 boundary 整数相等。

### 2.2 逐单元关系的四个输运规则

下面四条都从实际公式的有界量词证明。新表中的单位边界取上一小节给出的规范值；每个有界存在地址就取该规范地址。

1. `AtRows(X,i,a)` 且 `i<|X|`，推出 `AtRows(X++R,i,a)`。在新表上该单元仍是旧值 `a`。
2. `SameRows(X,Y)` 推出 `SameRows(X++R,Y++R)`。对新量词 `i<|X|+|R|` 分 `i<|X|` 与 `|X|≤i`；前者用旧行等值，后者两边都读 `R[i-|X|]`。
3. 实际 `DropRows(X,Y,c)` 包含 `c≤|X|` 和 `|X|=c+|Y|`，并逐单元检查 `X[c+i]=Y[i]`。因此它推出 `DropRows(X++R,Y++R,c)`：新长度等式由加法结合律得到；在 `i<|Y|` 使用旧等值，在 `|Y|≤i<|Y|+|R|` 两边同读 `R[i-|Y|]`。这里实际公式没有“过量 drop 截断”的例外。
4. `AppendSlices(A,Y,X)` 连同三个实际 flat-list 布局，推出 `AppendSlices(A,Y++R,X++R)`，并保持 `A`。原第一段的 token 等式不变；第二段按 `i<|Y|` 和尾段 `R` 分开。三个列表头分别为 `|A|`、`|Y|+|R|`、`|X|+|R|`，其长度等式为 `|X|+|R|=|A|+(|Y|+|R|)`。

最后一条需要同时保留三个实际 flat-list 布局。`AppendSlices` 单独只给计数和 body 切片等式，并不验证三个列表头。

这些规则也覆盖新表宽度大于旧宽度的情形：先用旧宽度的有限位等式得到读数相等，再在新表用相等的数值建立新宽度的逐位等式。不能直接把旧 `∀bit<u` 当成新 `∀bit<u'`。

任务数组不作追加。它们的 Same、Drop、At、Cons、Uncons 关系只需要把旧三元组值复制到新位置。以 `UnconsRowsWithSize` 为例，取 `tailCount=tasksCount-1`，tail boundary 第 `i` 项为新首任务起点加 `3*(i+1)`；再依次引入 Drop(1)、TripleBoundary、Cons(head) 及新的 boundary 长度等式。空 tail 也有一个边界项，不能取整张 boundary 为零。

### 2.3 一次确定新表及所有长度见证

先按所需输出数据枚举背景块、输入/expected 块和全部状态块，确定每个块的原始 token 数。块地址是此前块长度的和，最终 `N'` 是总长度，必要时加一个零单元保证 `N'≥1`。这些长度不依赖稍后生成的 boundary 大整数。

取 `u'` 大于所有将写入的 token 值的二进制长度，至少为 1。对按地址排好的值 `a_j<2^u'`，作 PA 前缀归纳：

`T_0=0`，`T_(j+1)=T_j+a_j*2^(j*u')`。

归纳不变量为 `T_j<2^(j*u')` 且所有较早单元读数正确。boundary 表用完全相同的归纳，宽度一律为最终 `N'`，第 `i` 项写规定的地址。地址至多 `N'`，而 `N'<2^N'`，故具有 `l+1` 项的 boundary 表满足 `ell(B)≤(l+1)*N'`。

这一步解释了源码中反复出现的 boundary 长度界。它不是把大整数的数值当作位数；boundary 的数值可能指数大，而长度由实际条目数乘实际条目宽度控制。

旧 `∀i<fuel,∃27个有界数...` 的见证可先在 PA 内有限收集：以 `j` 为归纳变量，把已选择的前 `j` 个元组按固定宽度存入工作表；第 `j` 条用原公式的存在量词消去，然后附加这一个元组。原值界给出一个公共宽度。此归纳收集的是固定公式的见证，不是为 PA 公式定义全局真谓词。

新相邻行的全部坐标、slot、status 局部见证是有限组已构造的数。先对这些数取有限最大值，再选 `tableWidth` 使 `valueBound=2^tableWidth` 容纳它们。若上层 sequent 行还要把这个 `valueBound` 当作一个字段，则在上层重新选更大的界。按公式嵌套的固定层数逐层选界；从不要求某个界严格容纳它自身的幂。此处只证明存在，不声称辅助见证有多项式大小。

## 3. 成功轨迹的内部不变量

### 3.1 status 的互斥与失败吸收

`FoundationCompactNumericListedDirectBinaryNatStatusCases.lean` 的三个实际编码是：

- running：恰一个单元 `[0]`；
- failed：恰两个单元 `[1,0]`；
- completed：先 `[1,1]`，再一个带长度头的输出数组。

实际 `StatusValidBounded` 给 completed 输出的 UnitBoundaryRows。因此每种状态都可按第 2 节读成唯一的有限数组结构。三类互斥仅用 Entry 唯一性和 `0≠1`，不需要任何理论一致性假设。

检查六个 Step 分支可得 PA 内的一步事实：若 current 是 failed，则 next 仍是 failed。理由是 Empty、Repeat、Term、Formula、Invalid 全都要求 current running；Done 的两个子分支中，completed 子分支也被头值互斥排除，只剩 failed→failed。

对 `j≤fuel-i` 作 PA 归纳，得到：若第 `i` 个状态 failed，所有后续状态直到第 `fuel` 个都 failed。实际 FinalStateRows 要求第 `fuel` 个 completed。于是每个状态都非 failed。这是由同一给定有限矩阵的末行反推其先前行的性质，不是从语义接受推出公式可靠性。

每条 Term/Formula 中所有失败子分支、整个 Invalid 分支以及 Done 的 failed 子分支因而都可消去。

### 3.2 六类实际分支核对

以下记 `L` 为当前 token 数组、`K` 为当前任务数组、`Ktail` 为弹出头任务后的数组。所有改动均对实际 .mkSigma 合取、析取逐项验证。

| 分支及源码 | 原成功行的必要事实 | 新行的构造 |
| --- | --- | --- |
| Done，`ParserDoneFormula.lean:51` | token Same、task Same、completed 输出 Same | 两边 token 同加 `R`，两边输出同加 `R`，task 三元组不变；七 slot 改为新输出地址、boundary、长度、输出 count |
| Empty，`ParserEmptyFormula.lean:39` | current running，两个 taskCount 都为 0；next 输出与 current tokens 相同 | 两边 token 同加 `R`；next 输出也同加 `R`；三个输出见证重建，其余四个 slot 可取 0 |
| Repeat，`ParserSyntaxRepeatFormula.lean:35` | current/next running，头任务 `(2,h,q)`；`q=0` 弹出，或 `q=d+1` 推入 `(0,h,0),(2,h,d)` | token Same 用规则 2；任务值及 `h,q,d` 不变，重建 tail boundary、tail size；两个任务 At 和 Drop(2) 按三元组逐项成立 |
| Term，`ParserSyntaxTermFormula.lean:272` | 头任务 `(0,h,0)`；非失败强制 `2≤|L|` | 见下表；token Drop 用规则 3，原头部 At 用规则 1；任务数值分支不变 |
| Formula，`ParserSyntaxFormulaTaskFormula.lean:240` | 头任务 `(1,h,0)`；非失败强制 `1≤|L|` | 见下表；保留旧前 1 或 3 个 token 值及 binder；重建实际 task Cons/Drop/At |
| Invalid，`ParserSyntaxInvalidFormula.lean:33` | next 必须 failed | 已被 3.1 排除，无须输运其失败行为 |

Term 的剩余子分支恰为：

- `tag=0` 且 `argument<h`：消耗 2 个 token，next task 为 `Ktail`。
- `tag=1`：消耗 2 个 token，next task 为 `Ktail`。
- `tag=2`、`3≤|L|`、合法算术函数码：消耗 3 个 token，next task 为 `(2,h,argument)::Ktail`。

合法算术函数码的固定公式只涉及旧 `argument,functionCode`，即 `(0,0),(0,1),(2,0),(2,1)` 四组，完全不依赖追加内容。

Formula 的剩余子分支恰为：

- `tag=0` 或 `1`：原公式强制 `3≤|L|`，读取 `relationArity,relationCode`，合法性只允许 `(2,0),(2,1)`；消耗 3，并推入 `(2,h,relationArity)`。
- `tag=2` 或 `3`：消耗 1，next task 为 `Ktail`。
- `tag=4` 或 `5`：消耗 1，推入两个 `(1,h,0)`。
- `tag=6` 或 `7`：消耗 1，推入 `(1,h+1,0)`。

所有成功子分支读取的位置都小于旧 `|L|`。`|L|` 改成 `|L|+|R|` 后，原下界仍真，读取数值不变。那些“长度不足”“非法 tag”“非法码”等失败子分支不需要保持，也不能不加区分地声称保持。

slot 的含义随分支不同，不能整体平移七个 slot。例如 Term/Formula 的 slot0、slot4、slot5、slot6 是 binder 和实际 token 数值，保持原值；slot1、slot3 分别是 tail boundary 整数及其长度，需要重算，slot2 的 tailCount 保持。Repeat 的 slot0、slot1、slot5 保持，slot2 和 slot4 重算。Done 的 slot6 则是输出 count，必须增加 `|R|`。

### 3.3 所用不变量的精确内容

从每个旧状态实际读取 `L_i,K_i,status_i`。新状态要求：

`L'_i=L_i++R`，`K'_i=K_i`。

若旧 status 为 running，新 status 为 running；若旧 status 为 completed 输出 `O_i`，新 status 为 completed 输出 `O_i++R`。旧 failed 情形已由 3.1 排除。

对 `i<fuel`，3.2 逐分支构造七 slot 及两边状态的全部布局见证，证明新的实际 `SyntaxStepRows`。邻接中每个 `StateAtRows` 使用同一新状态 boundary 第 `i,i+1` 项，所以不会出现分别重建两次状态而在接缝上不一致的问题。

这是一条关于原成功矩阵的行输运不变量。无需额外先证明 parser 的全部语法可靠性，也不需要证明原 token 数组确实编码某个外部 typed formula。

## 4. 固定燃料的实际终点引理

令 `n=|X|`、`r=|R|`、`F=f(n)`、`F'=f(n+r)`。PA 的有序半环计算给 `F≤F'`。

前 `F+1` 个新状态由 3.3 指定。其后所有状态都复制第 `F` 个新状态的数组数据和 completed 输出，但使用各自的新存储地址。这些行由 Done 的 completed 子分支逐项引入：token Same、task Same、两份 completed 输出 Same；七个见证按新位置重建。

因此整个新序列严格具有 `F'+1` 个状态和 `F'` 条相邻行。增加输入长度后不能只更改 `inputCount`，也不能沿用旧 `stateCount`。

若第 `i` 个旧状态 token 数为 `n_i`、任务数为 `k_i`，其规范新存储为：

- running：`[n_i+r] ++ L_i ++ R ++ [k_i] ++ flatten(K_i) ++ [0]`；原始 token 数为 `n_i+r+3*k_i+3`。
- completed 输出数为 `e_i`：`[n_i+r] ++ L_i ++ R ++ [k_i] ++ flatten(K_i) ++ [1,1,e_i+r] ++ O_i ++ R`；原始 token 数为 `n_i+r+3*k_i+e_i+r+5`。

这里 `flatten` 只是把每个任务的三个原自然数单元顺序写入，并非另一个尚未表示的语法运算。它的第 `3*j,3*j+1,3*j+2` 项分别指定为原任务三个读数。

先把这些原始长度连同第 1 节的背景区和端点块长度加起来，再使用第 2.3 节一次生成 `T',u',N'` 及 state boundary。每个状态 token boundary 为 `start+1+j`；task boundary 为 `tokensFinish+1+3*j`；completed output boundary 为 `tasksFinish+3+j`。这些地址直接验证 ProductSplit、StructuredListLayout、Unit/TripleBoundaryRows、StatusValid 的实际公式。

初行的 `InitialStateRows` 所需 token Same 由 `X→X++R` 的规则 2 给出；taskCount 仍为 1，头任务仍为 `(k,h,q)`，status 为 running。末行的 `FinalStateRows` 所需 output Same 由 `Y→Y++R` 的规则 2 给出，两个 1 的 completed 头按实际单元构造。再以第 2.3 节选择的公共幂界，引入 `InitialFinalBounded` 和每个 `AdjacentRowBounded` 的存在量词，最后引入实际 `ExactBoundedGraph`。

两端的 `NatListWitnessRows` 同样按新 `[count]++array` 块引入。这完成第 1 节声明的整个实际普通终点引理，含背景存储块的版本。

空追加 `r=0` 时可使用同一证明；它仍可能重新分配地址。若原任务参数没有成功轨迹，前提即不成立；本引理没有暗中假设任意 `(k,h,q)` 都能成功解析。

## 5. 封闭公式的额外 guard

`ParserClosedEndpointFormula.lean:24` 使用 `ParserClosedSuccessTraceBoundedGraph`。其相邻行除普通 SyntaxStep 以外，额外合取 `ParserClosedSuccessStepFormula.lean:120` 的实际蕴涵：

`TermRows(current,next,same seven slots) → (currentTokensCount≤1 or slot4≠1)`。

不能只说自由变量“未改变”，因为输入长度增加会使 `count≤1` 从真变假。

严格处理如下。若旧行选择 Term 分支，3.1 排除失败强制旧 `count≥2`；旧 guard 因而给出 `slot4≠1`。新 Term 保留 slot4，故新 guard 成立。

若旧行选择其他成功分支，新 Term 前件不成立：Done 的 current 是 completed；Empty 的 taskCount 为 0；Repeat 的首 taskKind 为 2；Formula 的首 taskKind 为 1。这分别与 Term 的 running、非空头任务 kind=0 矛盾，矛盾均由 status 头、任务头 Entry 的唯一性得到。新补齐的 Done 行也属于此情形。

因此第 4 节的同一构造给出实际 `compactParserClosedEndpointGraphDef` 的 append 输运。不会把原来合法的 closed formula 加上任意 `R` 后误认为整个 `formula++R` 都是闭公式：被解析的前缀保持，返回后缀也从 `Y` 改成 `Y++R`。

## 6. SequentFormulaEndpoint 的逐层输运

`SequentFormulaEndpointFormula.lean` 的实际 27 参数图要求三组 NatListWitnessRows、一个 `SequentFormulaTraceBoundedGraph`、首尾 Entry、输入 Cons 以及输出 Γ 的 StructuredListLayout 和 boundary 长度界。

其中 `SequentFormulaTraceFormula.lean:33` 的精确内容是：

`suffixCount=valueCount+1`，suffix 与 value 两个 NatListListRowsWellFormed，以及 `valueCount` 条 `SequentFormulaStepRowsBoundedGraph`。

实际 `SequentFormulaStepFormula.lean:47` 第 `j` 行选择相邻 suffix `S_j,S_(j+1)` 和 value `A_j`，检查：

- 三者带头列表和 boundary 的原公式；
- 普通 SyntaxExact，初始任务 `(1,0,0)`，输入 `S_j`，expected `S_(j+1)`；其状态数明确为 `f(|S_j|)+1`；
- `AppendSlices(A_j,S_(j+1),S_j)`。

PA 内从旧逐行存在量词收集这些见证。令 `m=valueCount`，保留所有 `A_j`，改为 `S'_j=S_j++R`，`0≤j≤m`。第 4 节给每个内层 parser 的新见证；第 2.2 节规则 4 给每个新的 AppendSlices。没有从 `compactFormulaTokenValueParser` 的 Nat 执行结果取得这里的行。

新 suffix 列表块必须连续存放。若其起点为 `b_0`，按递推

`b_(j+1)=b_j+1+|S_j|+r`

指定第 `j` 个带头 suffix 块。suffix boundary 第 `j` 项写 `b_j`。于是同一个 Entry 同时作为第 `j` 行的 currentFinish 和 nextStart：这正是实际 StepGraph 的 `index+1` 双重使用。不能把各个 suffix 随意孤立放置后用一张 boundary 假装连续。

value 块依次写 `[|A_j|]++A_j`，保留整体 Γ 的头 `m`，在根节点需要的位置布局。其 value boundary 同样用前缀长度递推。逐 `j<m` 取相邻边界和值数组实际头，建立两个 NatListListRowsWellFormed。

再令 sequent 输入 `B'=B++R`、首 suffix 为 `S_0++R`、最终 suffix 为 `S_m++R`。旧 Cons 给 `B=m::S_0`，由 At/Same 的逐单元输运，实际 Cons 仍给 `B'=m::(S_0++R)`。Γ 的 `m` 个值数组不变。

所有背景、value、suffix、内层 parser 状态块先一起确定总 `N'`，再重建所有 boundary，按由内向外顺序选择幂界。最终逐项引入 SequentFormulaEndpoint 的实际合取。

这证明完整 sequent 终点输运。`m=0` 时内层全称条件为空，但 suffixCount=1：仍构造一个 `S_0++R` 块及其两个端点；Γ 为头 `[0]`，所有公式照常成立。

## 7. 五类 proof-root 成功图

以下保持旧根的 `tag,Gamma,first,second,witness`，只把根字段 `suffix=Q` 改为 `Q++R`。根记录各字段都是实际带头列表，根首 tag 为一个单元。TaskCore 的构造可用 `paper_direct_mp_transport_20260905_zh.md` 第 5.1 节已经闭合的字段追加引理，或直接按这些块重新布局；Γ boundary 的条目宽度同样必须变成最终 `N'`。

旧节点输入 `I=tag::B` 改成 `I++R=tag::(B++R)`。第 6 节保持解析出的 Γ，增加所有 sequent suffix。根和各 parser 块连同所有内部状态共同安排在一个表里。

### 7.1 SequentOnly：已逐合取闭合

源码 `ProofRootSequentOnlyEndpoint.lean:67`，tag 为 2、7、8，first/second/witness 三个 count 都为 0。

1. 新输入是 `I++R`，建立其 NatListWitnessRows。
2. 新根的 TaskCore 来自上一段；tag 和三个零 count 保持。
3. 原 `NatListConsRows` 变成 `I++R=tag::(B++R)`，逐单元引入新实际 Cons。
4. 用第 6 节的新 sequent 终点；输出 Γ 指向新根的 Γ 字段，终 suffix 指向单独的规范 `S_m++R` 块。
5. 原最后一个 SameTableSliceEq 比较的两个带头列表相等；它给 `S_m=Q`。新两个块均为 `[|Q|+r]++Q++R`，对整个块逐单元引入实际 SameTableSliceEq。

root.start/root.finish 的两个等式使用新根块地址；全部局部坐标以这些地址及规范 boundary 给出。这逐项给出实际 46 参数图，不只是一条外部 parser 语义等式。

### 7.2 OneFormula：已逐合取闭合

源码 `ProofRootOneFormulaEndpoint.lean:58`，tag 0、9 对 binderArity 0，tag 5 对 binderArity 1；secondCount=witnessCount=0。

前四项构造和 7.1 相同。令原 sequent 的 final suffix 为 `H`，原根 first 为 `A`，根最终 suffix 为 `Q`。原普通语法终点是 `(H,Q,1,binderArity,0)`，原 AppendSlices 给 `H=A++Q`。

第 4 节给新实际终点 `(H++R,Q++R,1,binderArity,0)`。它的 input 块就是新 sequent final 块；expected 块就是新根 suffix 字段，二者可直接在共同布局中指定。第 2.2 节规则 4 给 `AppendSlices(A,Q++R,H++R)`。tag/binder 的有限析取、两个零 count、root 地址等式和 TaskCore 同时保留。

这样原图的每个合取都有新公式见证。特别是最后的 formula.inputCount 必须改为 `|H|+r`，root.suffixCount 改为 `|Q|+r`；firstCount 保持 `|A|`。

### 7.3 另外三类：固定次数的同一构造

- ClosedFormula，`ProofRootClosedFormulaEndpoint.lean:45`：tag=1、binderArity=0；外壳与 OneFormula 相同，唯一差别是内层用第 5 节已证明的 ClosedEndpoint 输运。second/witness 的零 count 保持。
- TwoFormula，`ProofRootTwoFormulaEndpoint.lean:57`：tag=3 或 4，witnessCount=0。把 final、middle、root suffix 三个数组分别改成 `H++R,M++R,Q++R`。两个普通终点都取初始任务 `(1,0,0)`；分别应用第 4 节。两次 AppendSlices 分别保持 first 和 second 字段，用规则 4。
- FormulaTerm，`ProofRootFormulaTermEndpoint.lean:57`：tag=6，secondCount=0。第一个普通终点固定 `(1,1,0)`，第二个固定 `(0,0,0)`；把 final、middle、root suffix 同时追加 `R`，两次用第 4 节。两个 AppendSlices 分别保持 first 与 witness 字段，不能误把第二个左源写成 second 字段。

这里没有额外可变次的语法归纳：每一类仅在已证明的 sequent 终点外再合成零、一或两个固定 parser 终点。共享 middle 块按一次布局、一次赋值处理，两条 parser 关系引用同一块。

### 7.4 从未绑定图到原 Bounded/Tagged 图

`ProofRootSuccessBoundedFormula.lean` 对五类作固定析取，且每支存在 bodyStart、bodyFinish、branchBound；每个家族的 Bounded 公式再逐个绑定其固定数目的局部坐标。

旧公式的外层存在量词先消去，选择其实际成立的家族。新家族见证已由 7.1—7.3 构造；对新全部局部数取有限最大值，选择 branchBound，再取更大的 endpointBound，以其顺序重新引入原量词。所有规定为幂的内部 trace valueBound 已在构造时满足真实 expDef；普通 endpointBound 只需满足源码要求的大小关系。

`ProofRootTaggedSuccessBoundedFormula.lean:34` 额外以 `TokenCell(rootStart,proofTag,rootStart+1)` 读取根起点的 tag。旧 TokenCell 和旧 TaskCore 的首单元由 Entry 唯一性给出 `proofTag=tag`。新根块第一个单元保持这个值，因此直接引入同一 `proofTag` 的新 TokenCell。

由此完成五类实际成功终点图的 append 稳定性，包括所需的外层 Bounded 和 Tagged 包装；旧的数值界不主张保持。

## 8. 本局部结论的边界

已闭合的是对给定成功 parser 矩阵的 PA 内部见证输运：普通语法、封闭语法、sequent、五类 proof-root 及其有界/标签包装。其新增背景区版本允许和证书 induction 的普通 `(1,1,0)` 终点、根字段和外层状态块在一个最终表中共同布局。

仍不能仅凭本文宣称整个条件 (3) 完成。完整 MP 输出还要在实际外层 verifier 图中拼接任务栈、值栈和两个证书流，构造各调度/归约分支的全部 429 列，并选择每个源接受轨迹在 Finish 前的有效前缀。本文解决其中 parser 的成功分支输运，不把这些其余行条件隐含进“parse 正确”。

本地依赖只有 PA 的指数/除余/位算术，实际 Entry 的规范化引理，有限数组的前缀打包归纳，以及源码中逐条展开的固定公式。没有加入“PA 证明 typed parser 总正确”这样的新假设。纸面证明到 Lean 的逐项实现仍是后续工作。
