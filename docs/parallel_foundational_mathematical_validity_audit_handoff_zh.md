# 并行任务交接单：总路线数学有效性审计与纸面证明

将下面代码块整段交给终端 2 的 Codex。该终端只负责数学审计和纸面证明，
不得修改主终端正在推进的 Lean 证明链。

```text
工作目录：
/home/james/code/sondow-pudlak-bigN-audit-20260708/sondow-pudlak-collision-box-bigN-halfden-full-20260708

任务性质：
你是独立的数学审稿人兼证明作者。不要默认项目结论正确，也不要因为 Lean 中存在
同名 structure/theorem 就把数学义务视为已证。先从原始数学定义和一手文献重建
纸面论证，再判断它能否映射到当前 Lean 对象。你的首要职责是发现致命缺陷；只有
每一步都成立时才写成正向证明。

总目标：
对以下 Sondow--Pudlak 对撞路线给出一份可供严格同行评审的、从定义开始的数学判决：

  P_direct(b,y) := 当前公开 PA 检查器接受完整 proof tree + certificate payload，
                    且被证明公式码为 y、完整载荷长度不超过 b；
  F_b := not P_direct(b, falsumCode)；
  rho_d(n) := (n+1)^(d*n)；
  G_n := F_{rho_d(n)}；
  M(n) := G_n 在同一 PA/Hilbert 系统、同一编码和同一完整载荷度量下的最短证明长度。

目标下界：存在固定 d，使最终 (n+1)^n < M(n)。
目标上界：假设 Euler--Mascheroni 常数 gamma 有理，构造同一 G_n 的真实 PA 证明，
并证明其完整载荷长度最终受某个关于外层 n 的固定多项式 U(n) 控制。
只有这两条都对同一 n、同一 G_n、同一检查器和同一长度度量成立，才允许推出碰撞。

先阅读，但只把它们当作待审材料：
1. docs/short_checked_minproof_growth_proof_zh.md
2. docs/checked_minproof_theorem_dependency_graph_zh.dot
3. docs/checked_minproof_appendix_04_pa_quantitative_compiler_zh.dot
4. docs/checked_minproof_appendix_05_pudlak_collision_zh.dot
5. docs/sondow_upper_bound_from_scratch_paper_proof_zh.md
6. docs/pudlak_tail_gap_lower_bound_paper_proof_zh.md
7. integration/FoundationCompactNumericListedDirectFiniteConsistencyTarget.lean
8. integration/FoundationPudlakQuantitativeConditions.lean
9. integration/FoundationPudlakBussRescaledLowerBoundGate.lean
10. integration/FoundationCompactNumericListedDirectProofPredicate.lean
11. integration/FoundationCompactNumericListedDirectProofPredicateExactness.lean
12. integration/FoundationCompactNumericListedDirectBoundedProofWitness.lean
13. integration/FoundationCompactPAQuantitativeCompilerCore.lean
14. integration/FoundationCompactPABoundedFormulaCompiler.lean
15. integration/FoundationCompactPABoundedFormulaCompilerBounds.lean
16. integration/SondowProjectSondowUpperCompilerRoute.lean
17. integration/SondowShortProofUpperBridge.lean
18. EulerLimit/SondowForwardReproof.lean
19. EulerLimit/SondowShortProofReproof.lean
20. EulerLimit/ExternalPudlakRawEncoding.lean

一手文献核验是强制步骤：
1. 找到并阅读 Pudlak 1986 被项目称为 Theorem 3.1 的原文。记录论文题名、期刊、
   年份、页码、定理原文所在页和稳定链接。逐符号抄写其精确假设与结论，但正文
   对单一来源的直接引文不得超过 25 个英文词，其余必须准确转述。
2. 核对项目曾称为 Buss 1994 Theorem 5 的原文。判断它是否真是当前主路线的必要
   输入，还是仅为推广；记录精确适用的理论、公式族、证明系统和长度度量。
3. 找到实际使用的 Sondow 判据原文。精确写明“gamma 有理”到底给出什么整数关系、
   逼近式、整除性或证书；不得把文献没有给出的 PA 短证明桥归给文献。
4. 只用论文原文、正式勘误或权威出版版本作关键结论依据。二手概述只能帮助定位，
   不能支撑核心定理。

第一阶段：完全固定数学对象
在任何证明前，用无歧义的纸面定义写清：
1. PA/Hilbert 推导规则和公理模式；
2. proof object、structural certificate、公开 checker；
3. packedPayloadLength 的精确定义；
4. P_direct(b,y)、F_b、rho_d(n)、G_n、M(n)；
5. 公式中的 n 是数值参数、二进制数词还是公式长度参数；
6. “固定多项式”的变量、次数、系数允许依赖哪些固定对象；
7. 元理论中使用 PA 一致性或标准模型可靠性的准确位置。

必须画一张“对象恒等表”：每条桥的源对象和目标对象都列出 formula family、
proof system、checker、formula code、proof code、length measure、parameterization。
任一栏不完全相同，必须给出双向或所需方向的显式多项式校准定理，不能写“显然同一”。

第二阶段：独立重证 Pudlak 下界
1. 从 Pudlak 原定理的精确版本出发，逐项证明当前 P_direct 满足其条件 (0)--(3)。
2. 每一项都要写出固定多项式和真实构造，不得只写“可计算”“可验证”或“标准”。
3. 条件 (1)/(2) 必须区分：
   - 外部 checker 能接受；
   - PA 内部能证明该接受事实；
   - 该 PA 证明的完整载荷有固定多项式界。
4. 条件 (3) 的 MP 组合必须发生在同一证明系统和同一完整载荷度量上。
5. 证明对角化、代入、数词编码、公式码增长和证明拼接的统一定量界。
6. 从原定理得到的固定正幂下界出发，严格证明选择固定 d 后，
   G_n = F_{rho_d(n)} 最终满足 (n+1)^n < M(n)。写出阈值、指数取整和所有单调性步骤。
7. 检查重标定是否改变公式族、是否错误地把关于 b 的界当成关于其二进制长度的界，
   以及 rho_d(n) 的数词和公式生成成本是否已支付。

第三阶段：独立重证或否决 Sondow 上界桥
这是最高优先级的数学风险，不能因下界证明很长而放到最后。
1. 从“gamma 有理”的见证开始，逐步写出 Sondow 文献实际给出的对象。
2. 明确构造一份同一 G_n = not P_direct(rho_d(n), falsumCode) 的 PA/Hilbert proof object。
3. 明确说明该证明为什么是有限一致性陈述 G_n 的证明，而不是仅证明
   sondowCertificateValidCode(n)、某个积分恒等式、某个整除式或另一个公式。
4. 给出 proof tree、structural certificate、checker acceptance 和完整载荷长度的
   统一固定多项式界。不得从“证书可多项式时间检查”直接跳到“PA 中有多项式短证明”；
   若使用检查计算的 PA 模拟，必须显式构造并计量该模拟。
5. 不得使用 gamma 无理、目标碰撞结论、G_n 无短证明或任何等价事实来构造上界；
   否则属于循环论证。
6. 如果 Sondow 条件只能给 number-theoretic certificate，而没有通向同一 G_n 的逻辑
   归约，必须明确判定“上界桥未成立”，定位最小缺失命题，禁止用命名结构或公设补齐。

第四阶段：反例与压力测试
必须主动尝试推翻自己的证明：
1. 公式族错位测试：把每个中间公式的完整语法写出，检查是否真的等于 G_n。
2. 信息流测试：Sondow 证书包含什么信息，为什么足以证明 PA 在长度 rho_d(n) 内无
   矛盾证明？若不能回答，桥不成立。
3. 替换测试：把“gamma 有理”换成任意可给短证书的命题；若同样推导出 PA 有限一致性
   的短证明，说明论证偷偷使用了一个过强且未证的通用原则。
4. 空真/不可实现测试：检查任何输入包是否因内部字段互相矛盾而根本不可构造。
5. 循环测试：为每个 lemma 标明是否依赖最终 irrationality/collision/lower bound。
6. 度量测试：proof symbols、proof-code bit length、完整 proof+certificate payload 三者
   不得混用；需要的方向必须有显式多项式校准。
7. 一致性测试：区分元理论中的 PA soundness 与 PA 内部 Con(PA)，不得让 PA 证明自身
   一致性。
8. 均匀性测试：多项式必须独立于 n；若依赖有理性见证 p/q，要明确它作为固定常数的
   方式，并检查构造仍然统一。
9. 审稿人测试：以“Euler 常数无理性仍是公开难题”为背景，列出至少十个最强反驳，
   并逐条由证明正文中的具体 lemma 回答；不能靠措辞回答。

第四阶段附加：Wolfram/独立符号验证
Wolfram Language 只能作为独立代数检查器和反例搜索器，不能替代 Lean 内核或 Pudlak
元定理的纸面证明。当前机器未检测到 wolframscript/WolframKernel，因此先生成可复现
脚本；若终端环境后来可用 Wolfram Engine 就运行，否则用已安装的 SymPy 1.14 做等价
的精确检查。禁止用浮点近似支撑定理。
1. 新增 scripts/foundational_mathematical_validity_checks.wls，至少使用：
   - FullSimplify/Refine 检查每个代数改写及其完整 assumptions；
   - Reduce/Resolve 检查可落入实闭域或整数算术的量化子命题；
   - FindInstance[Not[claim], ..., Integers] 主动寻找阈值、取整、单调性和指数选择反例；
   - FindEquationalProof 仅用于确实属于等式逻辑的局部恒等式，并保存 ProofObject。
2. 新增 scripts/foundational_mathematical_validity_checks_sympy.py，精确复现可由 SymPy
   处理的同一组等式、不等式、递推式和有限反例搜索；不得把有限抽样写成证明。
3. 必查项目：rho_d 的取整和单调性、固定正幂到 (n+1)^n 的指数比较、显式阈值、
   每个 payload polynomial 的代入/复合/单调性、公式码长度估计中的加乘幂方向。
4. 对 Wolfram/SymPy 返回 True 的命题，仍须写出纸面证明；对下界最终使用的纯算术
   lemma，再在隔离 Lean gate probe 中内核证明。软件输出只作为第二实现和压力测试。
5. 保存命令、版本、输入、完整输出和未求解表达式到
   docs/foundational_mathematical_validity_computer_check_log_zh.md。未求解、超时或条件分支
   不完整必须标黄，不能解释成通过。
6. Wolfram/SMT/SymPy 不能验证以下核心跳步：PA 内部可证性、Pudlak 定理适用性、
   proof-system/length-measure 恒等、Sondow 证书到 G_n 的逻辑归约。这些只能靠精确
   数学证明、原文核验和 Lean 形式化。

第五阶段：验证纸面证明是否真的可用于 Lean
只有纸面证明闭合后才做这一阶段。
1. 建立“纸面 lemma -> 当前 Lean 定义/端点”映射表。每个纸面 lemma 标记：
   已有内核定理、需要新增形式化、依赖一手文献定理、或尚未证明。
2. 对已有端点运行 #check/#print axioms 或最小 import 探针，确认类型逐字匹配；不能只
   根据名字判断。禁止完整 lake build。
3. 可新增且仅可新增一个隔离探针：
   integration/FoundationSondowPudlakMathematicalValidityGateProbe.lean
   该探针只能组合已有真实定理或形式化纸面中新证的纯数学引理；不得新增 axiom、
   sorry、opaque 输入包或“假设目标桥成立”的 structure。
4. 探针命令：
   flock /tmp/sondow-lean-probe.lock lake env lean \
     integration/FoundationSondowPudlakMathematicalValidityGateProbe.lean \
     -o /tmp/FoundationSondowPudlakMathematicalValidityGateProbe.olean
5. 扫描探针及新增数学文件：
   rg -n "\\b(sorry|admit|axiom)\\b|sorryAx|tail_gap|upper_provider|proof_length|ofSigmaZeroTruth"
6. 报告所有 #print axioms 输出。标准逻辑公理也要如实列出。

交付文件：
1. docs/foundational_mathematical_validity_paper_proof_zh.md
   一篇自足、正常数学论文风格的纸面证明或严格的不可能性/缺口证明。正文先定义、
   再列引理、再证明主定理；不要写项目历史、路线口号或 Lean 开发日志。
2. docs/foundational_mathematical_validity_referee_audit_zh.md
   对象恒等表、文献逐项对应、循环依赖图、反例压力测试和红/黄/绿判决。
3. scripts/foundational_mathematical_validity_checks.wls
4. scripts/foundational_mathematical_validity_checks_sympy.py
5. docs/foundational_mathematical_validity_computer_check_log_zh.md
6. 如且仅如纸面证明闭合，再新增上述 Lean gate probe（数学闸门探针）。

最终判决必须四选一，不得含糊：
A. 下界和 Sondow 上界均严格成立，可进入完整形式化；
B. 下界成立，但 Sondow 到同一 G_n 的上界桥未证明；
C. Pudlak 下界的文献条件或对象校准未成立；
D. 已找到明确反例或逻辑矛盾，当前总路线不可行。

若判决不是 A，不要伪造补丁。给出最小缺失定理的精确陈述，并说明它是合理可证、
需要新数学突破，还是与已知结果冲突。若判决是 A，必须给出逐行可检查的证明和
Lean 映射，不得只给研究计划。

文件协作边界：
- 不修改任何现有 Lean 文件。
- 不修改 docs/short_checked_minproof_growth_proof_zh.md、任何 DOT/PDF、论文或 README。
- 不撤销或整理工作区已有改动。
- 只新增上述审计文档和独立 Wolfram/SymPy 检查脚本；只有达到纸面闭合才新增隔离
  gate probe。
- 不运行完整构建，不推送 GitHub。
- 每完成一个阶段，在终端中简短报告当前判决和证据，便于主终端用 tmux 查看。

质量底线：
- “Lean 接受条件定理”不等于数学前提已构造。
- “公理画像干净”不等于参数来源干净。
- “可计算/可检查”不自动等于“PA 中存在短证明”。
- “公式码相等”必须有语法层等式，不接受自然语言同义。
- 任何未证明步骤必须明确暴露，不得包装、下沉、改名或延期后宣称闭合。
```
