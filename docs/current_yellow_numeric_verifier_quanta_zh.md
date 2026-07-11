# 把检查员也装进算术里

## 一张黄色方框背后的形式化难题

一份证明交到检查员手里，检查员逐行核对，最后盖下“接受”或“拒绝”的印章。这幅图景看起来已经足够严格：只要检查规则公开，每一步都能复查，错误似乎就无处藏身。

但在当前的下界形式化中，真正困难的问题又向前推进了一层：**不仅证明要被检查，检查员自己的全部动作也必须被翻译成自然数上的确定计算，并证明这种翻译与原检查结果逐点一致。** 实时定理依赖图中的黄色方框，处理的正是这个任务。

这里的目标不是再造一个名字漂亮的接口，也不是把尚未证明的命题塞进参数。它要把公开验证器接收到的 `code`（证明码）和 `formulaCode`（公式码）一路解包为纯数值 token（记号），执行 PA 公理识别和十条证明规则，最后返回同一个布尔结果。运行时只能出现 `Nat`（自然数）、`List Nat`（自然数列表）和有限状态；typed syntax（类型化语法）只能在正确性证明中出现，不能偷偷充当外部输入。

**黄色不是“整个下界已经差最后一步”，而是“当前正在攻克的局部根节点”。** 它前面已有大批绿色基础，后面仍有算术化、PA 内部证明和 Buss-Pudlak 下界等灰色根义务。

## 从归纳公式开始的机器化

黄色节点最先遇到的是 PA 的归纳公理。给定一个公式体 $B(x)$，需要构造的核心公式可以直观写成

$$
B(0) \to \bigl((\forall x\,(B(x)\to B(x+1)))\to \forall x\,B(x)\bigr).
$$

在人类纸面上，这只是一行公式；在验证器内部，它却意味着四条真实代入路径、变量命名空间的移动、开放变量的重新捕获、三次否定、三个析取和两个全称量词。任何一步若只在 Lean 的高层语法对象上“算出来”，却没有对应的纯数值执行图，后续都无法诚实地把验证过程放进 PA。

这一部分现已从黄色任务中移出并转绿。[纯数值 `succInd(body)` 构造](../integration/FoundationCompactNumericSuccIndSentence.lean)要求每个 shift（移位）、substitution（代入）、`fixitr`（变量捕获）和 negation（否定）子机器完整消费输入 token；若公式后面藏着畸形尾部，组合器不会假装成功。Lean 已证明整个函数是 `Primrec`（原始递归），并且对每个规范公式体，其输出逐 token 精确等于原定义的 `succInd(body)`。

这项进展的意义不在于又多了一个可执行程序，而在于切断了一条常见捷径：**“Lean 能执行”不等于“PA 能以所需的定量开销谈论这次执行”。** 原始递归图是通往算术表示的必要桥梁，而逐点等价保证过桥后没有换掉检查器。

## 一个很小的编号，如何展开成很长的公式

黄色节点的关键链条由 `fvSup`（自由变量上界）、`allClosure`（全称闭包）和 candidate-length guard（候选长度守卫）组成。现在三者、标签 `22` 的完整归纳句比较、全部 23 个公理标签、十条局部规则以及两侧节点字段解析均已转绿；黄色工作面已经缩到同步任务栈及燃料证明。理解这次变绿，仍要先看它们共同面对的复杂度陷阱。

设公式中出现自由变量 `&k`。二进制编码只需大约 $\log k$ 个比特写下编号 $k$，但把公式闭合时，朴素算法可能要添加 $k+1$ 个全称量词。于是，一个很短的输入可以要求机器吐出一个按 $k$ 而不是按 $\log k$ 增长的输出。若 $k=2^m$，输入只多出约 $m$ 位，闭包却可能多出约 $2^m$ 层。这不是常数估计不够精细，而是从输入位长到执行长度的指数裂缝。

把它想成一张写着“请打开第十亿号抽屉”的小纸条。纸条很短，但照字面从第一只抽屉数到第十亿只，工作量并不短。`fvSup` 负责读出最大的抽屉编号；`fixitr` 负责把自由变量改写成受量词约束的变量；`allClosure` 再逐层加上全称量词。三者在语义上自然，在位复杂度上却可能失控。

候选长度守卫提供了关键转折。验证器并不是无条件生成庞大闭包，而是在比较归纳公理证书与一个已经给出的候选句。若候选句的公开二进制 `formulaCode`（公式码）只有 $L$ 位，而闭包需要超过 $L$ 层，那么二者绝不可能相等。机器可以先比较 `fvSup` 与候选句真实位长，提前拒绝这条不可能成功的路径；只有守卫通过，才执行变量捕获和全称闭包。

这项优化必须同时满足两种相反要求：它要截断昂贵的失败路径，又不能拒绝任何真正相等的合法候选。新模块先证明把每个 Nat token 重新编码后得到的长度，精确等于原公开公式码位长；随后在纯数值机器中实现守卫。Lean 已检查：对每个规范 `body/candidate`，比较器返回真，当且仅当真实 PA 归纳证书句等于候选句；守卫拒绝分支不会漏掉合法相等情形。

## 为什么不能停在“原始递归”

`Primrec`（原始递归）回答的是“这个函数能否由一组基础递归规则构造”，并不自动回答“它是否在输入位长的多项式时间内运行”。一个原始递归函数仍可能增长得极快。因此，黄色节点需要同时保留两条证据链。

第一条是 extensional equality（外延等价）：对同一个 `code/formulaCode`，纯数值机器与公开验证器必须返回同一结果。第二条是 bit-cost bound（位成本界）：接受和拒绝的全部路径都必须受同一个固定多项式控制，不能只分析成功分支，也不能把辅助见证的长度藏在函数参数中。

**只有“同一结果”和“多项式成本”同时成立，这台数值机器才是后续 `CompactProof(x,y)`（紧凑证明谓词）可以诚实表示的检查器。** 少任何一条，都可能出现一种表面干净的证明：Lean 的公理画像没有项目公设，但真正困难的计算或证书已经被搬到参数之外。

## 黄色方框将怎样变绿

接下来的闭合顺序已经缩窄。纯数值 `fvSup`、候选位长、23 标签合并器、十条局部规则以及 proof/certificate（证明/证书）根节点字段解析都已通过探针。节点解析器只消费父序列、主公式、见证或公理证书，并原样留下子流。当前任务是让有限任务栈调用这两个解析器，同步检查规则与证书形状，把子结论和子布尔结果自底向上交给已完成的局部规则，再证明显式燃料足够；随后汇入公开 verifier（验证器），得到完整原始递归图与逐点结果等式。

这会关闭黄色节点，但不会自动关闭整个下界定理。其后仍须把同一数值图写成算术公式 `CompactProof(x,y)`，证明标准模型语义完全一致；再为被接受的计算构造 PA 内部短证明，验证 Pudlak conditions（普德拉克条件），并在同一公式族、证明系统和长度度量上完成 Buss-Pudlak theorem 5（Buss-Pudlak 第五定理）的形式化。

定理依赖图因此像一份施工剖面图：绿色说明某段钢筋已经由 Lean 内核验收，黄色标出正在浇筑的结构，灰色保留尚未承重的后续部分。**真正可信的“无条件下界”不会来自把整张图染成好看的颜色，而会来自每次变色背后都有一个无隐藏参数、无占位证明、对象坐标一致的 Lean 定理。**

## 项目内核验入口

- [实时下界定理依赖图（DOT）](checked_minproof_theorem_dependency_graph_zh.dot)
- [精炼证明指导书](short_checked_minproof_growth_proof_zh.md)
- [`succInd(body)` 纯数值构造](../integration/FoundationCompactNumericSuccIndSentence.lean)
- [`fvSup` 纯数值自由变量上确界](../integration/FoundationCompactNumericFormulaFvSup.lean)
- [`allClosure` 纯数值迭代全称闭包](../integration/FoundationCompactNumericAllClosure.lean)
- [`fixitr` 纯数值变量捕获](../integration/FoundationCompactNumericFormulaFixitr.lean)
- [候选公式真实 token 位长](../integration/FoundationCompactNumericTokenBitLength.lean)
- [带守卫归纳句构造与比较](../integration/FoundationCompactNumericGuardedInductionSentence.lean)
- [全部 23 标签 PA 公理比较器](../integration/FoundationCompactNumericPAAxiomComparator.lean)
- [十条证明规则纯数值局部检查](../integration/FoundationCompactNumericListedRuleChecks.lean)
- [证明与证书节点字段解析器](../integration/FoundationCompactNumericListedNodeFields.lean)
- [带候选长度守卫的既有成本证明](../integration/FoundationCompactListedGuardedAxiomCost.lean)

本文是 2026 年 7 月 11 日的工程状态说明。它描述已经由当前 Lean 探针核验的局部结果与仍待证明的边界，不把黄色节点或后续灰色节点表述为既成定理。
