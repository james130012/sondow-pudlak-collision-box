# 五节点 MP 构造的规定燃料：纸面局部证明

日期：2026-09-05。范围：当前 numeric listed task machine 的外层步数。
本稿不新增 Lean，不声称完成整个 PA 内部条件 (3)，也不将轨迹长度等同于
轨迹公式的证明长度。

结论：当前燃料 `4*(inputTokenCount+1)+8` 对五节点 MP 输出足够。
对任意输入还可给出更直接的停机势函数；对形状匹配的证明树，可给出准确的
遍历步数和 MP 新增的 9 个宏步。原规定燃料无需增加。

## 1. 必须固定的实际对象

源定义均在 `integration/` 下：

- `FoundationCompactNumericListedTaskMachine.lean:25` 开始：机器状态是
  `(((proofTokens,certificateTokens),(tasks,values)),status)`。
- 同文件 `:46` 开始：`compactNumericNodeTransition` 的叶节点、单子节点、
  双子节点分支。
- 同文件 `:711`：`compactNumericRunningStep`；先弹出一个任务，再解析或合并。
- 同文件 `:774`：`compactNumericVerifierStep`；已停机状态保持不变。
- 同文件 `:788`：
  `F=4*(proofTokens.length+certificateTokens.length+1)+8`。
- 同文件 `:793`：初态只有一个 parse 任务，值栈为空，状态为 running。
- `FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix.lean:35`
  开始：实际矩阵固定 fuel 为 `4*(inputTokenCount+1)+8`。
- `FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula.lean:26`
  开始：表格有 fuel 个步骤行，末行的 next state 必须是 accepted。

下文令 P、C 为机器当前未消费的两个自然数 token 列表，K 为任务栈，V 为值栈。
其长度记作 p、c、k、v。初始总 token 数 M=p0+c0。

这里的输入 token 是树与结构证书的原始自然数 token；不能将 sourceTable 的
additive list 编码长度、完整 payload 位数或公式字符数替换进 M。
实际输入切分关系所需的 `inputTokenCount=p0+c0`，现已由原 InputSplit、
初态 StateCore 及两层 CrossEq 的长度方程在 PA 内推出，详见
[输入切分引理](paper_direct_input_split_20260905_zh.md)。这只校准 token 数，
不替代后续规则运行层的矩阵输运。

## 2. 外层宏步与内部计算不能混计

一次 parse 宏步调用节点字段解析器、结构证书节点解析器，并执行叶规则检查或
安排子任务；一次 combine 宏步执行相应规则检查。内部解析器和规则检查的计算
不是每做一次内部操作就消耗一次此处的 F。

因此本稿证明的是当前实际 `compactNumericVerifierStep` 的迭代次数足够。
它没有证明 429 列单步环境的所有见证多项式有界，更没有证明同一单步矩阵在 PA 中
有短证明。把 F 的线性性写成“整个检查过程线性时间”是不成立的推断。

## 3. 解析成功必严格缩短 proof token 列表

需要的局部事实只是后缀关系，无须先证明所有语法解析结果的类型正确性。

`FoundationCompactNumericListedNodeFields.lean:415` 的节点解析器先匹配
`tag :: suffix`，随后在 suffix 上调用下列字段组合：

| proof tag | 依次调用的字段解析器 |
| --- | --- |
| 0、9 | sequent，然后 formula |
| 1 | sequent，然后 closed formula |
| 2、7、8 | sequent |
| 3、4 | sequent，然后两次 formula |
| 5 | sequent，然后 binder arity 为 1 的 formula |
| 6 | sequent，然后 formula，再 term |

每个组成解析器成功时只留下输入的一个后缀。这个事实可直接作如下 PA 归纳证明。

1. 对语法解析状态，固定最初列表 X；维护一个游标 d，满足当前列表为
   `drop(d,X)`，且 `d≤length(X)`。
2. `FoundationCompactSyntaxTokenMachine.lean:148` 的 term 分支只保留当前列表，
   或将其 `drop 2`、`drop 3`；`:179` 的 formula 分支只保留当前列表，
   或将其 `drop 1`、`drop 3`。
3. repeat-frame 分支只修改任务栈，不给剩余 token 列表添加任何元素。
   halted 分支保持原状态；成功结束分支返回当前剩余列表。
4. 若一次分支丢弃 e 项，把游标更新为
   `d'=min(d+e,length(X))`。有限列表的逐行定义直接证明
   `drop(e,drop(d,X))=drop(d',X)`。这可由行索引加法和越界约定证明，
   不需要调用解析器语义正确性。
5. 因而按内部语法运行的迭代次数归纳，其任何成功输出都是 X 的后缀。
   closed-term 版本的变化只是拒绝自由变量，仍只保留或截短 token 列表，
   同一不变量适用。
6. value parser 将已消费部分另存为 `take`，但返回的 suffix 坐标没有改变。
   sequent parser 先去掉个数头，再重复 formula value parser；按重复次数归纳，
   每次后缀仍是初始剩余列表的后缀。
7. 对上表的有限 parser composition 依次应用后缀传递性即可。

以上所需的内部归纳可在固定宽度编码的有限列表上进行：长度是单独坐标，
`drop` 的第 i 行就是原表第 `i+d` 行，追加游标是加法和截断。
这是关于实际分支读写坐标的归纳，而不是以“primitive recursive 所以显然”
替代关系 exactness。

最终，节点解析成功返回字段 f 时，令 `P'=fieldsSuffix(f)`，有

```text
length(P') ≤ length(P)-1。
```

因为外层节点 tag 已经独立消耗一项。空 P 无成功解析分支。
即使后续局部规则检查返回 false，这一长度事实仍成立。

## 4. 一个适用于任意输入的停机势函数

对 running 状态定义

```text
Phi(P,C,K,V)=3*length(P)+length(K)。
```

只比较“本步之前和之后都仍在 running”的转换；失败和 Finish 分支已经停机。
实际分支逐一给出：

| 分支 | proof 剩余长度 p' | 任务栈长度 k' | Phi 的变化 |
| --- | --- | --- | --- |
| 叶节点 parse，tag 0、1、2 | p'≤p-1 | k'=k-1 | 至少下降 4 |
| 单子节点 parse，tag 4—8 | p'≤p-1 | k'=k+1 | 至少下降 2 |
| 双子节点 parse，tag 3、9 | p'≤p-1 | k'=k+2 | 至少下降 1 |
| combine 成功 | p'=p | k'=k-1 | 恰下降 1 |

表中的 k 已包含当前被弹出的头任务。单子节点安排 `[Parse,Combine]`，
双子节点安排 `[Parse,Parse,Combine]`，所以净变化分别为 +1、+2。
parse/combination 失败直接进入 `some false`；K 为空则下一步执行 Finish，
进入 `some true` 或 `some false`。

因此 PA 可用自然数归纳证明下列计数定理：

```text
对满足当前机器分支等式的任意状态序列，
从 running 状态 s 出发，至迟在 Phi(s)+1 步后已经 halted。
```

证明一：对 Phi 强归纳。若第一步 halted，则已完成；否则下一状态的 Phi
至多是原 Phi-1，应用归纳假设，再加第一步，总共至多 Phi+1。
Phi=0 时 K 必为空，下一步就是 Finish。

等价地，可对序列索引 j 维护：如果第 j 状态仍是 running，则此前各状态也
是 running，且 `Phi(s_j)+j≤Phi(s_0)`。取 j=Phi(s_0)+1 导出矛盾。
此前各状态仍在运行的事实使用实际 halted 吸收分支，不是额外可靠性假设。

初态有 k0=1，故至迟 `3*p0+2` 步已停机。而

```text
3*p0+2 ≤ 4*(p0+c0+1)+8 = F。
```

这证明 fuel 不会在机器尚未停机时耗尽，甚至不要求输入编码是一棵合法树。
它只证明停机，绝不把 halted=false 改成 accepted=true。

对 PA 内部使用的准确界限：此处可以证明的是“已有一段满足实际分支等式的
F 步编码运行，其末状态必停机”，以及相应可定义机器迭代的计数定理。
不能仅从此推断任意 429 列算术图都有完整的见证表；该图的局部构造、字段
存在性和图与实际 Step 的内部对应仍须逐项完成。

## 5. 形状匹配树的精确续延不变量

对于证明树 T、形状匹配的结构证书 C，定义遍历代价 S：

```text
S(leaf)=1；
S(unary(T))=S(T)+2；
S(binary(L,R))=S(L)+S(R)+2。
```

这与 `FoundationCompactNumericListedTaskMachine.lean:1069` 的
`compactNumericTreeTaskSteps` 在 shape-matching 分支逐字一致。
现有 `:1782` 的 `compactNumericTreeTask_execute_of_shape` 采用如下加强归纳命题：

给任意 proofSuffix、certificateSuffix、restTasks 和旧值栈 V0，从

```text
(((tokens(T)++proofSuffix,certTokens(C)++certificateSuffix),
  (Parse::restTasks,V0)),running)
```

运行 S(T,C) 步后，恰得到

```text
(((proofSuffix,certificateSuffix),
  (restTasks,(conclusionTokens(T),check(T,C))::V0)),running)。
```

这里 `check(T,C)` 是原规则检查的 Boolean 结果；归纳命题允许它为 false。
它没有把 PA 语法检查提升为 PA 语义反射。

归纳的三个计数步骤如下。

- 叶：一次 parse 消费节点及证书的头部，直接压入一个结论与 Boolean；S=1。
- 单子节点：一次 parse 安排 `Parse,Combine`；把 Combine 连同 restTasks
  作为子树的续延应用归纳假设；再执行一次 combine。共 `1+S(child)+1`。
- 双子节点：一次 parse 安排 `Parse,Parse,Combine`。左子树的 proof/certificate
  suffix 分别包括右子树完整编码；其续延含第二个 Parse 和 Combine。
  执行左子树后，将左结果压在 V0 上；接着执行右子树，值栈头成为
  `[rightResult,leftResult]`；最后 combine 按该顺序取两个值。共
  `1+S(left)+S(right)+1`。

任意上下文的加强形式是必要的。只证明初始空任务栈下的运行，不足以支持
二叉树两个子树的顺序拼接。

PA 内部承载这个计数归纳可以使用节点的有限前序表：每行标明 arity 和一至两个
子节点索引，子树区间真包含于父区间；对区间长度作强归纳。
每个子树的运行前后关系就是上面的四个续延坐标不变量。
将有限递归树“看作 Lean inductive type”本身不能替代这一步的算术编码。
本稿只将其用于计数层；原 parser 的规范读取等式与局部 Boolean 规则等式
仍须在整体内部化中引用已证的对应纸面引理。

## 6. 为什么原燃料足够接受规范输入

令 N(T) 为节点数，I(T) 为非叶节点数，P(T) 为 proof 自然数 token 数。
对树归纳直接得到：

```text
S(T,C)=N(T)+I(T)；
I(T)≤N(T)；
N(T)≤P(T)。
```

最后一式因为每个树节点至少贡献一个独立的规则 tag；节点自己的公式、列表头等
额外 token 均非负。因此

```text
S(T,C)≤2*P(T)。
```

已有 Lean 外部语义对应为
`compactNumericTreeTaskSteps_le_two_mul_proofTokenLength`（同文件 `:2452`）。
本稿的计数推导没有用该外部语义定理替代 PA 内归纳。

在空 suffix、空 restTasks、空旧值栈情形，第 S 步后两个流为空，任务栈为空，
值栈恰有一个 `(conclusion,check)`。第 S+1 步执行 Finish，得到 `some check`。
若树和证书的既定局部验收结果为 true，此时就是 accepted。

之后每一步都保持同一个 halted 状态，因为 `compactNumericVerifierStep`
对 `isSome` 直接返回原状态。故对任意 F≥S+1，第 F 步仍是同一 accepted 状态。
这也解释了 accepted-trace 公式为何可以恰好有 F 行：第 F-1 行的 next state
是第 F 状态，不要求第 F-1 行仍做一次实际解析。

显然 `S+1≤2*P(T)+1≤4*(P(T)+certTokenCount+1)+8`。
不存在末行差一导致燃料不足的问题。

## 7. 五节点 MP 的准确新增步数

使用纸面主稿第 5.1 节的同一树：

```text
cut
├─ wk
│  └─ T_I
└─ and
   ├─ wk
   │  └─ T_A
   └─ closed
```

证书为 `binary(unary(C_I),binary(unary(C_A),leaf))`。
若两个输入证书形状匹配，则输出形状逐节点匹配。

新增五个节点各需一次 parse；其中 cut、and、两个 wk 另各需一次 combine。
所以不是 5 步，而是准确的 9 个外层宏步：

```text
S_out=S_I+S_A+9；
到 Finish 接受为止共 S_I+S_A+10 步。
```

展开核对：两个 wk 各增加 2；closed 增加 1；and 增加 2；根 cut 增加 2。
原有两个子树和证书各遍历一次，未出现树复制。

令 `P_out=P_I+P_A+H`，其中新增 proof 头部 token 数 H≥5。
于是

```text
S_out+1 ≤ 2*P_I+2*P_A+10 ≤ 2*P_out
          ≤ 4*(P_out+C_out+1)+8。
```

真实新增头部含列表和公式字段，H 通常远大于 5，但这里只需要每节点一个 tag。
因此不必重新使用 `29n+128` 的位长账本才能证明燃料充足；位长账本和本节
token 步数账本是不同的局部义务。

## 8. 完成范围与剩余边界

燃料的数值充分性、halted 后补足到 F 步，以及 MP 新增 9 宏步的计数已经有完整
纸面推导。还没有发现当前燃料或末行约定的反例。

使用本结论时必须保留以下边界：

1. “最终接受”为 true 仍需要 MP 各新增节点的实际局部规则 Boolean 均为 true，
   以及两份输入的正确验收结果；停机势函数只保证 halted。
2. 规定 F 使用的 inputTokenCount 与两段实际原始 token 数之和，须由同一输入
   切分关系在 PA 内证明，不能改用另一表格的编码行数。
3. 要证明同一直接谓词的内部 (3)，仍需把实际运行构造成精确的 429 列步骤环境，
   满足每个原有关系、相邻行连接和最后的 `AcceptedConclusionRow`。
4. 本稿不要求其余 19 个外层见证多项式有界。但“无多项式要求”不等于
   可以省去 PA 内的存在性和 exactness 证明。

因此可将“燃料常数是否足够”从未决数学疑点中移除，不能将“完整 accepted-trace
矩阵及 PA 内部条件 (3)”一并标记完成。
