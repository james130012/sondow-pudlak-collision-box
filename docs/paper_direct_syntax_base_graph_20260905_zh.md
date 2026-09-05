# 从当前公式编码构造普通 SyntaxExactEndpointGraph

日期：2026-09-05。仅作纸面证明，不新增 Lean。

本稿从项、公式的真实前缀 token 编码构造原普通语法 parser 的全部状态及步骤见证。对 binderArity=0 的任意当前 PA 公式 F，输入为 formulaTokens(F)、返回空列表，初始任务为 `(1,0,0)`，得到实际 `compactParserSyntaxExactEndpointGraphDef`，规定燃料严格为 `16*(L+1)^2+8`，其中 L 是公式的自然数 token 数。

证明不从 Nat parser 成功等式推出 PA 图，不使用 PR 可表示性或 typed decoder 的 sound/spec。更一般的 binder、输入后缀和任务续延命题用于归纳；它同样提供 mode=3 工作所需的语法事件顺序，但本稿不处理任何公式变换 mode，也不处理 closed parser 的额外 guard。

## 1. 结论的准确接口

下文短文件名均省略 integration 路径及 `FoundationCompactNumericListedDirect` 前缀。图名指实际固定 `.mkSigma` 公式。长度、数组、有限和均以 PA 中已经建立的商余读取和前缀编码展开。

设 X 为一条在 binder d 下按第 2 节编码的公式，长度 L；R 是任意有限 token 数组，长度 r。PA 可以构造同一 token 表 T、单元位宽 u、容量 N、input/expected 切片及十个 endpoint 坐标，使：

```text
input 的完整块    = [L+r] ++ X ++ R；
expected 的完整块 = [r] ++ R；
taskKind=1，taskBinderArity=d，taskRepeatCount=0；
stateCount=16*(L+r+1)^2+9；
原 SyntaxExactEndpointGraph 的全部合取成立。
```

对合法项 X，同样结论取 taskKind=0。项目所需基础情形为公式、d=0、r=0。

构造允许另外给任意有限 raw token 背景块，并预先指定相容的 input/expected 地址；所有活动块和背景块一并确定最终 N，然后才打包各 boundary。相容指重叠的指定位置要求相同 token；新状态块可统一放在这些指定区域之后。因此本结果可直接与新 proof-root、sequent 及外层状态共同布局，不要求先完成一个封闭成品表再增大 N。

本稿的 PA 定理前提是明确的有限语法分解数据及其逐行构造条件。对一个实际 PA 公式，分解数据由其有限语法树逐构造器写出，不需要 PA 证明任意“外部有效公式”的语义真值。下面将这层分解写清，以免把 Lean 的归纳类型对象偷偷作为 PA 变量。

## 2. 当前项和公式的有限算术语法

`FoundationCompactSyntaxTokenMachine.lean:18–41` 的实际编码如下，X_i 均指子式正文 token：

| 语法 | 编码与条件 |
| --- | --- |
| bound variable | `[0,i]`，i<d |
| free variable | `[1,i]`，任意自然数 i |
| 函数项 | `[2,a,c] ++ X_0 ++ ... ++ X_(a-1)`；a=0 或 2，c=0 或 1；子项 binder 均为 d |
| 正/负关系原子 | `[t,2,c] ++ X_0 ++ X_1`，t=0 或 1，c=0 或 1；两个子项 binder 均为 d |
| verum/falsum | `[2]` 或 `[3]` |
| and/or | `[4]++X_0++X_1` 或 `[5]++X_0++X_1`；两个子公式 binder 为 d |
| all/exs | `[6]++X_0` 或 `[7]++X_0`；子公式 binder 为 d+1 |

函数代码的四个合法对是 `(0,0),(0,1),(2,0),(2,1)`，分别覆盖当前语言的 0、1、加法、乘法；关系代码的两个合法对是 `(2,0),(2,1)`，覆盖等号和小于。这来自 `FoundationCompactArithmeticSymbolCode.lean:16–24` 的实际有限析取，及 Foundation 语言文件中六个构造器的编码定义。引入这些合法性子式时只选择对应数值析取，不调用 decode₂ 的标准模型正确性。

一个内部语法证书可以具体取为有限后序节点表。每行记录：项/公式类别、上述 tag、binder d、原子参数或符号码、至多两个子节点索引，以及该节点的 token 数组和长度。子索引严格小于当前行索引；各行逐项满足上表的 token 拼接方程及 binder 条件。项/公式类别使相同数字 tag 的不同用途保持区分。

节点 token 表也可从子节点表向上构造：写固定头，再按子节点索引依序复制全部正文，用有限前缀打包给新表及长度。于是所有节点代码的存在由对节点索引的 PA 归纳给出。采用完整树而不是共享子图也可以；无需假定 token 长度与节点数相等。

对当前任何有限 PA 项/公式，按其构造器后序列出节点，bound-variable 的原索引范围在相应 binder 行作为 i<d 写入，量词行把 d 更新为 d+1。这给与 `compactArithmeticTermTokens`、`compactArithmeticFormulaTokens` 完全相同的 token 串；没有替换成另一种仅语义等价的语法编码。

## 3. 加强的运行前缀归纳：保留任意 R 和 K

任务是三个自然数 `(kind,binder,repeat)`。记 T_d=(0,d,0)、F_d=(1,d,0)、R_(d,a)=(2,d,a)。K 可以是任意给定的有限三元组数组；下面的前缀不会执行 K 中的任务，因此不要求 K 的标签有效。

对每个合法项 t、公式 F，同步证明存在有限的原始状态/事件数组：

```text
(tokens(t)++R, T_d::K, running)
       -- s_T(t) 个事件 --> (R,K,running)；

(tokens(F)++R, F_d::K, running)
       -- s_F(F) 个事件 --> (R,K,running)。
```

每个事件指定第 5 节的一条实际分支及其 consumedCount，状态的 tokens、task 三元组与状态标志按该分支明确更新。此阶段只构造有限原始数据，不预先假定它们是某个 Nat 机器函数的输出；第 5、7 节直接为它们引入原 StepRows 和所有边界见证。

PA 的归纳谓词是：对节点索引之前的每个节点，针对所有 R、K 均存在上述数组及以下已定的步数、首末内容和事件条件。量词中的 R、K 是有限数组码。这是 PA 的全归纳可用的固定算术谓词，不是只在元语言对子公式做的一次直觉归纳。

### 3.1 repeat 辅助归纳

对 a 个同 binder 的合法项 t_0,...,t_(a-1)，令 Z 为它们的 token 顺序拼接。证明

```text
(Z++R, R_(d,a)::K, running)
       -- 1+sum_i(1+s_T(t_i)) 个事件 --> (R,K,running)。
```

a=0 时，用一次 Repeat 的零分支，tokens 不变，弹掉 Repeat，结束在 `(R,K,running)`。

a>0 时，取 q 满足 a=q+1。一次 Repeat 正分支把当前头换为 `T_d,R_(d,q)`，tokens 不变。对首项应用项的归纳假设，后缀取其余各项编码再接 R，任务尾取 `R_(d,q)::K`。首项结束后，再对剩余 q 项使用 repeat 归纳。总步数为 `1+s_T(t_0)+1+sum_(i>0)(1+s_T(t_i))`，恰为目标式。

repeat 归纳的状态不变量还给：待解析的项编码恰按原顺序位于输入最前部；尾 K 不变；尚余项数恰为 repeatCount。每次正分支中的 decrementedCount 取 q。没有在一步中展开由一个任意大 arity 值指定的整个任务表。

### 3.2 项构造器

bound variable 和 free variable 各一次 Term 事件消费 `[0,i]` 或 `[1,i]`，弹掉 T_d，直接得到目标状态；bound 的 i<d 来自语法证书。

函数头先用一次 Term function 事件消费 `[2,a,c]`，将 T_d 换成 R_(d,a)，然后用第 3.1 节。因此

```text
s_T(variable)=1；
s_T(function)=2+sum_i(1+s_T(t_i))。
```

特别 a=0 的 0/1 常量项需要一次 Term 和一次零 Repeat，总计 2 步；不能误计成只消费函数头的 1 步。

### 3.3 公式构造器

关系原子先用一次 Formula relation 事件消费 `[t,2,c]`，压入 R_(d,2)，再应用 repeat 引理，故其代价同样为 `2+sum_i(1+s_T(t_i))`。

verum/falsum 各一次 Formula constant 事件消费一项并弹掉 F_d，s_F=1。

and/or 的第一步消费连接词头，任务换为 F_d,F_d。先对左子公式应用归纳假设，输入后缀取右子公式编码再接 R，任务尾取 F_d::K；再对右子公式使用后缀 R、尾 K。总计 `1+s_F(left)+s_F(right)`。

量词先消费头，任务换为 F_(d+1)，再对子公式在 binder d+1 下使用归纳假设。总计 `1+s_F(body)`。子过程结束后回到 K，不把 d+1 传播给原 K 中其它任务。

因此每个构造器均从已有较小节点的加强命题得到所需前缀。相邻子前缀的末/首状态拥有相同原始数据，合并时只保留这条共享边界状态的一份，事件数直接相加。

原始数组的有限拼接在 PA 内按元素索引复制：先写第一段所有状态，再写第二段去掉重复首状态后的部分，事件数组则全部串联。有限见证的收集可按已处理节点/数组索引逐项选共同工作宽度并重新打包；这由指数、商余和普通归纳完成，不需要无穷选择。

## 4. token 长度给真实事件数界

设 L_T、L_F 为相应正文自然数 token 数。对第 2 节同一节点表同步归纳，有 L_T≥2、L_F≥1，以及

`s_T≤2*L_T-1`，`s_F≤2*L_F-1`。

变量：L_T=2、s_T=1，界成立。函数或关系原子具有 L=3+sum_i L_i，由项归纳界得到

```text
s=2+sum_i(1+s_i)
 ≤2+sum_i(1+2*L_i-1)
 =2+2*sum_i L_i =2*L-4 ≤2*L-1。
```

这一步把 repeat 正分支的每个额外 1 与子项界中的 -1 精确抵消，不能漏算参数调度。a=0 的空和也满足该计算。PA 中可把减法改写为 s+1≤2L，避免截断减法的歧义。

verum/falsum 的 1=2*1-1。二元式用 L=1+L_0+L_1，得 `s≤2L-3`；量词用 L=1+L_body，得 `s≤2L-2`。从而统一界成立。

取 K=[]。第 s 步后为 `(R,[],running)`，再加一次第 6 节的 Empty 得到 completed(R)。到完成为止的事件数 e=s+1≤2L。原 endpoint 的 inputCount 为 L+r，故

`e≤2L≤16*(L+r+1)^2+8=f`。

这是内部步数界，不是关于编码比特数的界；free-variable 数值、binder 数值可能很大，不因其位长或数值改变上述事件数。规定燃料按整个 parser 输入 L+r 取值，不能在追加 R 后仍保留旧 f(L)。

## 5. 每种原 Step 分支及七个槽的真实赋值

先记一条原始 running 状态为 `(Y,H::K,[0])`，p=|Y|，k=|H::K|≥1。最终布局后，其 task 正文首地址为 b=current.tokensFinish+1；第 j 项 task 的首尾为 b+3j、b+3(j+1)。取

```text
tailCount=k-1；
tailBoundary 的第 j 项=b+3*(j+1)，0≤j≤k-1；
tailBoundarySize=ell(tailBoundary)。
```

boundary 的条目宽度始终是最终 N。即使 k=1，tailCount=0，tailBoundary 也包含一个真实的末地址 current.tasksFinish；它不是 0。

由这些地址，原 SyntaxTaskListUnconsRowsWithSize 的全部六项成立：sourceCount>0；Drop(1)；tail 的 TripleBoundaryRows；以 H 为指定头的 Cons；真实 size；size≤(tailCount+1)N。Drop/Cons 的四端点分别取上述 j、j+1 对应地址，TaskRowEq 用三个原 token 的同值逐位引入。

其余基础行也直接取地址：NatListAt(i) 取正文首地址+i 及下一地址；NatListDrop(c) 在 target index=j 对应 source index=c+j；任务 Drop(c) 把这两个地址乘数换成 3；SameRows 取相同索引；Cons 的新头给三单元 DirectLayout，尾部索引 j 映到 j+1。这些原有界全称都由 PA 索引归纳逐项给出，不使用任何 List realize 的结论。

| 原活动分支 | consumedCount | 原条款与新任务 |
| --- | --- | --- |
| Term bound | 2 | p≥2、At(0,0)、At(1,i)、i<d；ContinueRows 的 Drop(2) 与 tail/next SameTasks |
| Term free | 2 | p≥2、At(0,1)、At(1,i)；同一 ContinueRows，无 freeIndex<d 限制 |
| Term function | 3 | p≥3、At(0,2)、At(1,a)、At(2,c)、对应 ArithmeticFuncCodeValid 析取；Drop(3) 与 Cons(2,d,a) |
| Formula rel/nrel | 3 | p≥3、tag=0/1、At(1,2)、At(2,c)、对应 ArithmeticRelCodeValid 析取；原 TermFunctionRows 的 Drop(3) 与 Cons(2,d,2) |
| Formula constant | 1 | p≥1、tag=2/3；原 TermContinueRows 的 Drop(1) 与 SameTasks |
| Formula binary | 1 | p≥1、tag=4/5；FormulaBinaryRows 的 DropTokens(1)、nextTasks Drop(2)=tail、AtTask(0,1,d,0)、AtTask(1,1,d,0) |
| Formula quantifier | 1 | p≥1、tag=6/7；FormulaQuantifierRows 的 DropTokens(1) 与 Cons(1,d+1,0) |
| Repeat zero | 0 | 当前与下一 running，SameTokens，Uncons(2,d,0)，零析取与 SameTasks(tail,next) |
| Repeat positive | 0 | 当前与下一 running，SameTokens，Uncons(2,d,q+1)，nextTasks Drop(2)=tail，头两项为 (0,d,0)、(2,d,q) |

Term/Formula 首项的 current RunningStatusSlice 由实际状态 `[0]` 给出；每个成功分支所需 next RunningStatusSlice 同样直接给出。所有 tag 及长度不等式来自本次正在处理的编码固定头，即使 R 为空也不失效。

实际 StepRows 的七个槽按 `ParserSyntaxStepFormula.lean` 替换表赋值如下：

| 分支 | slot0,...,slot6 |
| --- | --- |
| Term | d，tailBoundary，tailCount，ell(tailBoundary)，tag，argument/arity，functionCode |
| Formula | d，tailBoundary，tailCount，ell(tailBoundary)，tag，relationArity，relationCode |
| Repeat | d，repeatCount，tailBoundary，tailCount，ell(tailBoundary)，decrementedCount，0 |
| Empty | nextStatusStart+2，nextOutputBoundary，ell(nextOutputBoundary)，0，0，0，0 |
| Done completed | currentStatusStart+2，currentOutputBoundary，ell(currentOutputBoundary)，nextStatusStart+2，nextOutputBoundary，ell(nextOutputBoundary)，r |

Term 变量的 functionCode 未读取，取 0；Formula 的非关系分支不读取 relationArity/relationCode，取 0；零 Repeat 的 decrementedCount 未读取，取 0。不能把活动 binder 或 tailBoundary 一并置零。

原 Step 的第六个 Invalid 分支要求 task kind 不等于 0、1、2；本构造在执行 K 之前只产生这三种头，故不选它。Term/Formula 中的短输入、非法 tag、非法符号、越界 bound-index 失败分支分别被固定头长度、编码分类、上表数值合法性和 i<d 排除。它们不是遗漏的构造器，也无需使未选择的析取成立。普通 free variable 分支完整保留，不施加 closed parser 的额外限制。

这样第 3 节每个事件对应的原 `compactUnifiedParserSyntaxStepRowsDef` 析取都已逐合取获得，使用的所有非逻辑行关系及活动槽均已指定。

## 6. Empty 和 Done：恰好补到 f 个步骤

第 s 个边界状态为 `(R,[],running)`。下一状态保持 tokens=R、tasks=[]，将状态片段从 `[0]` 改为 `[1,1,r]++R`。

原 `ParserEmptyFormula.lean:41` 要求 current/next tasksCount=0、current running、SameTokens，以及 CompletedOutputSameRowsWithSize。令下一 status 起点为 a，outputStart=a+2，output 列表头为 r，正文为 R，终点为 a+3+r；其 UnitBoundary 第 j 项为 a+3+j。取其规范 boundary 和真实 size，就得到原 CompletedStatusPrefix、StructuredList、SameRows 及长度界。这是完成事件，consumedCount=0。

对剩余 f-e 个事件，保持原始状态 `(R,[],completed(R))`；每份状态可以存于不同的连续物理地址。原 DoneGraphRows 要 SameTokens、SameTasks 和完成态的 SameStatusWithSize。前三种列表关系分别比较复制的 R、空任务和两份 R 输出，用第 5 节逐索引端点给出；两个 status 前缀都为 1,1，输出 count 均 r。七槽使用第 5 节的 Done 行，因而每一条补行满足实际 Done 析取。

最终状态序列恰有 f+1 项、恰 f 个相邻步骤。其最后一项位于 state index=f。r=0 时完成状态片段为 `[1,1,0]`，outputBoundary 是唯一条目等于状态终点的一个数字，仍不能设为 0。

## 7. 从原始状态/事件数组构造同一 T,u,N

### 7.1 确定所有原始块，随后一次决定 N

一条 tokens=Y、tasks=K 的 running 状态原始块为

```text
[p] ++ Y ++ [k] ++ 三元组K逐项平铺 ++ [0]。
```

若 status=completed(R)，最后一段改为 `[1,1,r]++R`。前两段不因完成而省略。每条 running 块长度 p+3k+3；每条本次最终 completed 块长度 2r+5。

将 f+1 条状态连续放置，令起点 a_0 已给，a_(i+1)=a_i+第 i 块长度。输入、expected 与有限背景块放在相容指定地址或另行追加。全部原始块的长度不依赖 boundary 大整数，故最终容量 N 可在生成任何 boundary 前确定。

选 u≥1 容纳所有原始单元，包括 free-index、binder 值、repeatCount 和所有列表长度头。有限最大值的存在用已构造数组逐项归纳取得。按单元 j 构造

`T_0=0`，`T_(j+1)=T_j+x_j*2^(j*u)`。

归纳不变量为 T_j<2^(ju)，以及此前每个单元的原 Entry 正确。x_j<2^u 排除进位污染，商余给新 Entry。得到 T；容量外不保留任意高位。

### 7.2 每条 StateCore 的十个局部坐标

第 i 条状态起点为 a_i，tokensCount=p、tasksCount=k。取

```text
start=a_i；tokensFinish=a_i+1+p；
tasksFinish=tokensFinish+1+3k；finish=a_(i+1)；
tokensBoundary[j]=a_i+1+j，0≤j≤p；
tasksBoundary[j]=tokensFinish+1+3j，0≤j≤k。
```

两张 boundary 用条目宽 N 打包；size 取真实 ell。由这些等式直接给两个 ProductSplit、两个 StructuredList、UnitBoundary、TripleBoundary；所有端点在 N 内。边界值≤N<2^N，故 size 分别≤(p+1)N、(k+1)N。这是 `ParserStateFormula.lean:89` 的完整十项合取。

按第 5 节对每个活动尾生成 tailBoundary，并按第 6 节为每份 completed 输出生成独立 outputBoundary。所有 boundary 一律用同一个最终 N；状态宽 u 和 boundary 宽 N 是两种不同参数。

取 stateBoundary[j]=a_j，0≤j≤f+1，同样以 N 打包。对任意 i≤f，index<stateCount=f+1、该 boundary 的第 i、i+1 个 Entry 及刚构造的 StateCore，恰给原 StateAtRows。

### 7.3 实际 27 项步骤存在量与公共幂界

`ParserSyntaxAdjacentStepBoundedFormula.lean:54` 的每行原存在块恰为：current 八坐标及两个 size、next 的同十项、七个槽，共 27 项。其末端是两个 StateAt 加 StepRows，另含 current、next 两个 StatusValidBounded。不能只提供 StepRows 而漏掉这两个 status 有界图。

running status 的四个存在坐标 outputStart、outputBoundary、outputBoundarySize、outputCount 全取 0，直接选择不读取它们的 `[0]` 分支。completed status 按同一次序取实际 outputStart、outputBoundary、ell(outputBoundary)、r，选择两层 1 前缀；其 StructuredList、UnitBoundary、真实 size 和 size≤(r+1)N 均由规范输出块成立。因此两种实际 StatusValid 的所有存在数也都已构造。

可统一选一个明确足够的控制数

`H=1+u+(N+1)*N`，`V=2^H`。

所有原始单元<2^u；所有地址和列表 count≤N；每张 boundary 最多 N+1 项、每项宽 N，所以其数字<2^((N+1)N)；size≤(N+1)N。stateCount≤N，因为这 f+1 个非空状态块已经连续存入容量 N 中。由此每个上述存在数≤V，包含 task binder、七个槽、output 见证和初末态见证。

依照源码的 27 个量词次序引入构造值，得到每个 i<f 的 AdjacentRowBounded，再对 i 引入原有界全称；expDef(V,H) 用真实幂关系。原 AdjacentRowsBoundedGraph 因而完整成立。普通 syntax 图并未额外要求 H≥(N+1)N；本构造主动选此界只是为了统一容纳数值，不修改原公式。

## 8. 初末条件及 ExactEndpoint 的全部十坐标

输入块 `[L+r]++X++R`、expected 块 `[r]++R` 的 UnitBoundary 以各自正文起点加索引构造，取真实 size。这给 EndpointGraph 外壳要求的两个 NatListWitnessRows，包括 expectedCount=0 时的一项 boundary。

初始状态的 tokens 与 input 逐项相同、tasksCount=1、任务第 0 项为 `(taskKind,d,0)`、status 为 `[0]`。按 `ParserInitialFormula.lean:44` 的四个合取给 InitialStateRows。

最后第 f 状态有 completed(R)。取第 6 节的 outputStart、outputBoundary、size，把 expected 与 output 的两份 R 用逐项 SameRows 相连。CompletedStatusPrefix、StructuredList、SameRows、真实 size 及 size≤(r+1)N 正是 `ParserFinalFormula.lean:38` 的 FinalStateRows。

initial 与 final 的两个十坐标加这三个 output 数，共 23 个存在量均≤V；依 `ParserInitialFinalBoundedFormula.lean:88` 引入，得到原 InitialFinalBounded。与 stateCount=f+1 及第 7.3 节 AdjacentRowsBoundedGraph 合取，得到原 SyntaxTraceBoundedGraph。再把 fuel 代入源码的精确项 `16*(inputCount+1)*(inputCount+1)+8`，得到 SyntaxExactBoundedGraph。

最终 `ParserSyntaxExactEndpointFormula.lean` 的十个私有坐标按准确次序为

```text
inputBoundary，L+r，ell(inputBoundary)，
expectedBoundary，r，ell(expectedBoundary)，
stateBoundary，f+1，H，V。
```

与两端 WitnessRows 合取，即为原 20 参数 SyntaxExactEndpointGraph。若调用方需要 EndpointBounded，再取 endpointBound 大于这十个数，依原量词次序引入；这一步没有额外解析义务。

## 9. 已闭合范围和精确限制

本稿纸面闭合当前 PA 语法的普通 parser 基础图：所有项及公式构造器、repeat 的零/正调度、实际成功 Term/Formula 分支、Empty、Done、规定燃料、同表布局、27 项逐步存在量、23 项初末存在量及完整 ExactEndpoint 外壳。任意 binder、后缀的版本一并成立，任务续延版本在处理目标子式后保持 running 并停止于指定尾 K 之前。

项目当前需要的 d=0、R=[]、taskKind=1、taskRepeatCount=0 正是该结论的直接实例。自由变量允许任意自然数；这没有证明封闭性，也没有施加 closed parser 的 free-variable guard。

本稿不声称 mode=3 的变换输出已经正确，不声称新五节点的全部外层 G 安装已经完成，也不从这些有限见证的 PA 存在性推出 p3 的多项式证明长度。它提供了此前缺少的“从明确语法编码出发，取得同一个实际普通 parser 图”的基础证据，以及可供独立否定证明复用的事件/consumedCount/槽接口。
