# 从全部局部成功行到原 G 的子运行片段

日期：2026-09-05。本文只作 PA 内纸面证明，不新增 Lean。

已完成各类局部行之后，可以证明：任何原接受矩阵的 Finish 前片段，都能在任意
给定 proof/certificate 后缀、任务尾栈和值尾栈下继续执行，保留同一逐行 G 与真实
CrossEq 接缝。本文还给出新 MP 的燃料算术界，避免把外部树步数界直接当成原
矩阵的界。五个新节点本身的算术图构造和输入载荷账本仍需另行完成。

## 1. 原接受矩阵的每个活动行属于哪个分支

使用 [Finish 前缀稿](paper_direct_finish_prefix_20260905_zh.md) 的结论：
存在 1≤k<F，恰好第 k 行是首次成功 Finish，之前全部当前及下一状态都 running。
之前不存在失败行；其后只有 halted 行。取行号 0,…,k-1，不包括 Finish。

对其中任一行 i，原 G 的四个外层析取为 Halted、Finish、Parse、Combine。
Halted 要求当前状态 tag=1，与 running 矛盾；Finish 的下一状态 tag=1，
也与该行下一状态 running 矛盾。Parse/Combine 的 failed 析取同样使 nextTag=1。
于是只剩 Parse success 或 Combine success，且是原固定公式内部的析取排除。

Parse success 的全部五个活动类别为 Verum、Closed、PAAxiom、one、two；
Combine success 的全部三个活动类别为 simple、allShift、exsCut。
它们分别由 [值栈与非叶行稿](paper_direct_parse_state_transport_20260905_zh.md)、
[叶分支稿](paper_direct_leaf_state_transport_20260905_zh.md)、
[combine 稿](paper_direct_combine_state_transport_20260905_zh.md) 给出完整 429 列输运。
这些引理都保持真实 ChildResult Boolean，包含中途为 0 的结果；本节不必先从
最终接受反推所有中间规则结果都为 1。

## 2. 续延关系及其对完整状态切片的相容性

固定有限 token 列表 R、S，和带实际 TaskCore/ChildResultCore 见证的尾栈 K0、V0。
给 running 状态的内容定义

`Cont(P,C,K,V)=(P++R,C++S,map(eta_R,K)++K0,V++V0,running)`。

下文称整个变换为 continuation。eta_R 在 tag=10 时保留全部任务字段，
否则只给 suffix 追加 R，且 K0 不再次变换。

若两条原 StateCore 的完整原始切片满足 CrossEq，则平列表的长度头先固定两流，
随后 Task/ChildResult 的固定层级游标归纳固定两栈每项的字段、Gamma 和 Boolean。
因此两条原状态具有相同上述内容。对相同内容应用 continuation，结果逐单元相同。
两个原 running 状态的未存储 statusBool 参数可以不同；它不进入结果的原始块。

两条新状态可以放在不同表、不同地址，宽度和辅助边界整数也不必相同。
它们都写入相同的实际长度头、正文及最后 [0]。取这整个共同块的实际 token 长度
为 CrossEq 的长度见证，再从相同单元值逐位引入两宽度之和范围内的位等式，
即可得到新的原 CrossEq。每个 finish≤容量由各自 StateCore 的具体构造提供。

这证明 continuation 与原外层接缝相容；并非把两个不同边界表的整数码强行相等。

## 3. 逐行选择与一张有限矩阵的 PA 构造

从原外层 BoundedRow 的 Entry 唯一提取第 i 行的向量 e_i。第 1 节给其活动类别，
应用对应完整局部引理，得到 e'_i，使原 G(e'_i) 成立，且两端是原两端内容的
同一个 continuation。R、S、K0、V0 在整个片段中固定。

这一步是固定 PA 蕴含 `∀i<k, ∃e'_i, ...`，其中一个行向量用 429 个数编码。
不从无限选择或 Nat 外部运行函数提取证明。

在 PA 内对 i≤k 作归纳，维护以下有限工作矩阵性质：

- 已存 i 行，使用外层宽 U_i、值界 V_i=2^U_i，每个声明单元<2^U_i，
  所有原 Entry 和对应 G 均成立；
- 每行两端是指定源行两端的 continuation；
- 对所有满足 j+1<i 的 j，原 CrossEq 接缝成立；i>0 时首端是原初态的 continuation。

i=0 时使用空矩阵。归纳步先实例化前述存在行。选新外层宽 U'=U_(i+1)≥U_i，
同时容纳本行全部 429 个数，取 V_(i+1)=2^U'；
用已有外层重编码引理搬运旧矩阵的全部声明单元，再追加
本行。旧行的 Read 值均保持，所以旧 G 与接缝仍成立。
如果 i>0，第 2 节以旧第 i-1 行 next 与旧第 i 行 current 的实际 CrossEq，得到
两条新行的原 CrossEq，补上最后接缝。于是完整归纳不变量成立。

各行可以使用独立的内部 token 表和独立内部界；真正写在一张表里的，是每行
完整 429 个参数。原跨行关系正是比较各行所指向的状态切片，未要求两行 token
表的数值相等。因此无需让所有局部引理提前共享一个内部物理表。

最终得到恰好 k 行的新矩阵及全部新接缝。归纳可以逐步提高外层宽，最后不需要
给任意旧见证附加多项式位界。这里证明的是 PA 内的有限存在性；条件 (3) 的
唯一公共长度限制仍是最后输出 inputWidth，而不是这张工作矩阵的位数。

## 4. 子运行片段的准确初末内容

若旧矩阵包含同一个 InitialEnvironment，则初态的内容为

`(P,C,[Parse],[],running)`，其中 Parse=[10,0,0,0,0,0]。

第 3 节片段的首端因此为

`(P++R,C++S,[Parse]++K0,V0,running)`。

原成功 Finish 的前态两流为空、任务栈为空，值栈为单条 `(Gamma,1)`。
新片段末端因此为

`(R,S,K0,[(Gamma,1)]++V0,running)`。

如果源矩阵有 AcceptedConclusionRow(f)，原结果 Gamma 的公式集合为 {f}，
通过同内容复制仍保留该关系。此处 Gamma 可以有重复项；新尾端不是未经证明
规范化成只含一项的 Gamma。新的外围弱化节点可以按原 SetEq/Subset 定义处理它。

由此已经得到直接作用于原算术矩阵的子运行片段引理：给定源接受前提，就能在
外层指定续延下完成它的原子证明部分。该片段本身通常既不是初始矩阵，也不是
接受矩阵，因为它故意保留外层任务和下一输入。不得给它误加这些结论。

## 5. 五节点 MP 的燃料可以只用源矩阵给定上界

这是条件算术命题：假定两个源子运行及五个新节点已经以真实 G 行接齐。
两个源输入的 token 总数 M_I、M_A 是原 AcceptedPayloadMatrix 中的 inputTokenCount。
由它实际安装的燃料项（不是由裸 AcceptedTraceTable）得到

`F_I=4(M_I+1)+8=4M_I+12`，`F_A=4M_A+12`。

令 k_I<F_I、k_A<F_A 为两段 Finish 前行数。五个新节点的宏步分别是 cut 的
parse/combine、两次 wk 的 parse/combine、and 的 parse/combine、closed 的 parse，
共 9 行；再加最终 Finish 一行，共需

`L=k_I+k_A+10≤F_I+F_A+8`。

构造的新原始 token 流包含两份原输入及 H 个新增 token，故

`M_out=M_I+M_A+H`，
`F_out=4M_out+12=F_I+F_A+4H-12`。

五个新增 proof 标签本身就给 H≥5；实际上还包括结构证书标签及各字段。
于是 F_out≥F_I+F_A+8≥L。最后按原 accepted 吸收行引理补 F_out-L 行，
逐条保持接受状态和结论。

这里只用源接受矩阵本来给出的 k_i<F_i，不需要先把外部树的势函数界证明成
任意原矩阵的运行界。M_out 的加法式与 H≥5 则必须来自新规范输入的真实拼接，
不能仅凭新矩阵有九行就推得它。

## 6. 尚未包含在此结论中的 MP 义务

本稿闭合的是全段逐行续延、接缝和上述条件燃料比较。完成原条件 (3) 还需要：

1. 对五个新节点构造准确的 token 流、结构证书、成功 parser 终点和规则见证，
   把本稿的两段源片段安放到指定位置，最后构造原 Finish 行。
2. 在 PA 内把输入公共公式的实际字段长度限制于原 inputWidth，继而建立新
   inputWidth 的多项式账本。外部树的根公式长度结论不能直接充作这一内部引理。
3. 给新输入的同一 canonical 编码、InputSplit、InitialEnvironment，以及最终
   AcceptedConclusionRow，最后引回 P_direct 的 20 个存在量。

因此“全段续延已证”与“内部 MP 已证”仍有明确距离；本稿不把这些剩余义务隐去。
