# Sondow 同对象桥：数学可行性复核

日期：2026-09-05。结论：已核查实现没有建立关键桥；尚未证明任何可能的桥都不可能。
本次为源代码与数学义务审计，没有新增 Lean 通过声明。

## 精确目标

F_b 是当前 PA 检查器不存在完整载荷长度不超过 b 的矛盾证明这一句子。
G_n = F_{(n+1)^(d*n)}，其中 d 是固定正整数。
在固定 gamma = p/q 的外部假设下，必须构造同一检查器接受的 G_n 证明码，
完整载荷不超过 C*(n+1)^k；C、k 和尾部阈值可以依赖固定 p、q、d，不能随 n 改变。

## 已核查的三个断点

1. 目标不同。
   `FoundationCompactNumericListedDirectFiniteConsistencyTarget.lean` 中
   `compactListedPADirectFiniteConsistencySentence` 是直接证明谓词在矛盾码处的否定。
   `SondowProjectSondowUpperCompilerRoute.lean` 中
   `sidecarSondowCertificateVerifierProofObject` 则证明 BAFormula 系统中的
   polytimeDefinabilityFormula；其大小为 1 的事实不计量当前 certified PA 完整载荷，
   该构造也没有有理性参数。缺少公式转换和定量模拟，不能把这个 1 转交给 G_n。

2. 名为具体证明码编译器的接口并不携带证明码。
   同文件 `SondowFullCertificateConcreteProofCodeCompiler` 仅有
   `codeLength : Nat → Nat` 与 `short_code_from_checked` 两个字段。
   没有 code、conclusion、公开 verifier acceptance，也没有 codeLength 与实际 payload 的等式。
   因此 `pureSondowConcreteCodeLinearUpper_fromHalfDenCheckedTailAndCompiler`
   只给出传入函数的条件上界，不是目标句子的真实短证明构造。
   后续不能凭接口名称或标准公理画像把它记作 M17 完成证据。

3. 重标定不保持现有参数多项式界。
   即使另行得到关于 b 的 C*(b+1)^k 上界，代入 b=(n+1)^(d*n)，
   对固定 C>0、k>=1、d>=1，该上界表达式也不是关于 n 的多项式。
   这说明旧估计不足，不说明所有实际证明都一定这么长。
   相反，log2(b)=d*n*log2(n+1) 是关于 n 的多项式有界量；
   若能获得关于 log b 的完整证明长度界，长度尺度可以匹配，但现有桥没有给出它。
   `FoundationPudlakBussRescaledLowerBoundGate.lean` 已有相关纯增长闸门，
   不能因此视为具体 Pudlak 下界或 Sondow 桥已建立。

## 数学信息为何不足

Sondow 原文给出的相关判据，是 gamma 有理等价于特定对数分数部与积分表达式
最终相等。它没有在该判据中提供本项目的有限一致性证明转换。
来源：https://arxiv.org/abs/math/0209070 （本次已核对作者论文摘要）。
详细原文审读历史见 `foundational_mathematical_validity_paper_proof_zh.md` 第 5、6 节。

即便在 Lean 元理论中知道每个 F_b 为真，也不能由此推出 PA 中有指定长度的证明。
给出 Sondow 证书的短证明，也不自动给出“该证书蕴含 G_n”的短证明。
后者必须单独构造，且不得输入 G_n 的现成证明、目标短证明上界或最终无理性结论。
有理性是允许的条件；条件分支本身不构成循环。利用已成立的最终结论以假推出
任意目标虽可形成逻辑定理，却不能作为独立证明路线的证据。

## 继续推进的门槛

先给出以下任一可审查的数学构造，再扩大桥的形式化：

- 直接 builder：输入固定 p、q、d 和 n，输出当前 G_n 的真实证明码，
  从 Sondow 关系证明接受性，并独立估计完整载荷。
- 分解构造：同一 PA 系统内对源证书句 C_n 和 C_n → G_n 分别给出真实证明，
  两份证明与组合后的完整载荷均有关于外层 n 的固定多项式界。

当前没有找到这一转换。应将 M17 标为“缺少数学归约”，而不是常规编译接线。
这不使现有局部 PA 编译器失效，但它们不能替代缺失的数学论证。

## 扩展候选审计：反射拼接路线

本次进一步逐项展开 `integration/SondowShortProofUpperBridge.lean`，
而非只按文件名或最终定理名称判断。

| 候选 | 实际输入或输出 | 对当前目标的判断 |
| --- | --- | --- |
| `SondowShortProofUpperRemainingObligations` | `partial_accepted_truth`、`trace_package`、`pa_embedding` | 剩余义务的打包，不是义务的构造 |
| `SondowCollapseVerificationBridgeInputs` | `partial_payload_truth`、全局 trace 与嵌入 | 改变接口形式，未消除部分一致性输入 |
| `sondowCollapseVerificationBridgePackage_nonempty_iff_inputs_nonempty` | 两个输入包的非空性等价 | 不证明任一个输入包非空 |
| `SondowNarrowCollapseVerificationBridgeInputs` | 部分一致性接受、两条 trace、合取引入和专用嵌入 | 缩小接口适用范围，仍保留关键输入 |
| `eventual_pa_short_proofs_of_reproof_rationality` | 关于 `sondowReflectionGraftCode` 的 `accepted_certificate` 和根级 `proof_length` 上界 | 未输出当前 direct G_n 的公开检查器接受码及完整载荷界 |

字段定义核查于 `EulerLimit/Certificate.lean`：

- 第 272 行 `PartialConsistencyPayloadTruth.true_all` 要求所有 n 的部分一致性载荷为真。
- 第 908 行 `PartialConsistencyAcceptedTruth.accepted_all` 要求所有 n 的部分一致性码被接受。
- 第 1153 行 `S21VerifierTraceSoundness.short_proof_from_accepting_trace` 直接要求接受事实
  蕴含根级 S21 `proof_length` 不超过 `proof_predicate_formula_size`。
- 第 1240 行附近 `ProofSystemLinearEmbeddingOn.target_le_linear_source` 是根级长度函数
  之间的不等式；其字段没有携带从源系统推导树到当前 certified PA 推导树的算法。

这些定义可以作为条件接口使用，本次没有证明它们自相矛盾。
但若引用该路线声称关键桥已关闭，必须同时交付这些字段的独立实现以及目标、检查器、
度量校准。当前候选的结论不能直接证明这样的校准。

下一步数学工作应明确写出源证书句到 direct G_n 的推导机制；
再次包装输入、把一致性真值当作可短编译的接受轨迹，或只将长度函数换名均不够。

## 纸面构造更新

[统一纸面主稿](../paper/full_paper_proof_working_zh.md) 第 3 节已给出一个替代源证书：
对 log(S_n) 计算显式有理区间，只检查整数轨迹及有理不等式。
固定 p、q 后，gamma=p/q 等价于该证书在无界多个 n 上接受。
它修复源端的有限可检查性，不提供到 G_n 的归约；旧 Prop 接受接口并未因此成为可执行程序。
主稿还给出条件下界的重证、闭公理/MP 序列的 cut 树转换，以及完整数词 S_n 的指数长度障碍。
后续推导以主稿为准，继续遵守纸面完成后才形式化的顺序。
