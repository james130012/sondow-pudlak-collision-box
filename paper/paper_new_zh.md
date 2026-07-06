# 欧拉常数无理性的条件性证明复杂度对撞框架

## 摘要

欧拉-马歇罗尼常数 γ 是否无理仍是公开问题。本文不声称给出
γ ∉ ℚ 的无条件证明，而提出一个可审计的条件性证明复杂度框架。其基本思想是：若 γ 有理，则 Sondow 判据可被组织为一个短证明坍缩机制；另一方面，Pudlak-Friedman-Buss 型有限一致性下界给出某些反射/一致性公式族在 PA 中不可短证的下界。本文的工作是把这两侧放入同一个公式编码、同一个证明系统和同一个证明长度度量中，使“短证明上界”和“证明长度下界”真正作用于同一个对象。Lean 4 形式化用于校验这一接口级组合链：在明确列出的外部数学输入与 proof-length calibration（证明长度校准）输入被提供时，形式化定理推出

```math
\neg \mathrm{is\_rational}(\gamma).
```

本文的贡献是将一个原先较模糊的哥德尔加速直觉转化为精确的条件性对撞定理，并将剩余风险集中到少数可审计的外部证书。

关键词：欧拉常数；Sondow 判据；Pudlak 有限一致性；证明复杂度；PA；Lean 4；条件性定理。

## 1. 问题与策略

欧拉常数定义为

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

与 π 和 e 不同，γ 的有理性状态仍未知。Sondow 给出了一类与 γ 有理性相关的积分和乘积判据。粗略地说，这些判据把 γ 的有理性与某些对数乘积的小数部分等式联系起来。若这些等式可被压缩为短证书，则有理性假设会在证明复杂度上产生一种“短路”。

单靠这个观察不能推出无理性。要得到矛盾，还必须有一个下界定理说明同一公式族在同一证明系统和同一长度度量下不可能拥有这样的短证明。自然 Sondow 公式族目前没有可直接引用的成熟证明长度下界。因此本文采用一个更保守的模型路线：将 Sondow 证书与有限一致性或反射载荷组合，使下界侧可以接入 Pudlak-Friedman-Buss 型有限一致性证明长度下界。

这一路线牺牲了一部分“自然公式族”的直接性，但换来一个严谨目标：构造同一 proof-complexity coordinate（证明复杂度坐标）上的上界和下界对撞。

## 2. 三个对象：上界、下界与共同测量盒

本文区分三个对象。

第一，A 表示 Sondow 坍缩侧。它不是一个单独公式，而是有理性假设下产生的短证书机制。其作用是：若 γ ∈ ℚ，则某个由 Sondow 判据导出的证书族可在选定证明系统中被短证明验证。

第二，B 表示 Pudlak-Friedman-Buss 下界侧。它作用于有限一致性或反射型公式族，例如“没有长度不超过 n 的 PA 证明推出矛盾”的有限一致性陈述。该侧的数学来源是证明长度下界，而不是 Sondow 分析本身。

第三，C 是共同测量对象。它必须同时接收 A 的短证明上界和 B 的证明长度下界。若 A 和 B 落在不同编码、不同证明系统或不同长度度量上，就不会产生矛盾。因此真正的核心不是“有一个上界”和“有一个下界”，而是二者能否经由编码与投影落到同一个 C 上。

在 Lean 模型中，这个共同坐标由以下三类对象给出：

```lean
FormulaCode
ProofSystem.PA
ProofLengthMeasure.symbolSize
```

也就是说，所有公式族必须被编码为 `FormulaCode`，所有证明长度必须解释为 PA 中的 symbol-size proof length（符号大小证明长度）。这是本文区别于早期直觉叙述的关键。

### 2.1 核心对撞方程

本文的核心思想可以压缩成一个 proof-length collision（证明长度对撞）模式。设 C_n 是最终共同测量盒中的公式族。若 γ 有理，Sondow 坍缩侧应给出一个上界

```math
\mathrm{Len}_{PA}(C_n)\le U(n),
```

其中 Len_PA 表示 PA symbol-size proof length（PA 符号大小证明长度），U(n) 是由短证书验证机制产生的上界函数。另一方面，Pudlak-Friedman-Buss 下界侧应给出

```math
L(n)\le \mathrm{Len}_{PA}(C_n).
```

若最终校准证明在同一个 C_n 上成立，则前两个不等式先合成为

```math
L(n)\le \mathrm{Len}_{PA}(C_n)\le U(n),
```

从而推出

```math
L(n)\le U(n).
```

这里还需要一个独立的 gap condition（间隙条件）或 growth domination certificate（增长支配证书）。它不是由“Pudlak 侧给出长证明下界”自动推出的；下界本身只说明
`\mathrm{Len}_{PA}(C_n)` 至少为 `L(n)`。要发生对撞，还必须另外证明或作为明确输入给出：Sondow 侧的上界函数 `U(n)` 最终严格小于 Pudlak 侧的下界函数 `L(n)`。也就是说，如果同时对充分大的 n 有

```math
U(n)\lt L(n),
```

则得到矛盾。因此整个计划的实质不是单独证明一个短证书或一个下界，而是证明这两个不等式的中间项真的是同一个对象：

```math
\mathrm{Len}_{PA}^{Sondow}(C_n)
=
\mathrm{Len}_{PA}^{Pudlak}(C_n)
=
\mathrm{proof\_length}\; ProofSystem.PA\; ProofLengthMeasure.symbolSize\; C_n.
```

这就是为什么 proof-length calibration（证明长度校准）在项目中占据中心位置。没有校准，A 和 B 只能分别成立；有了校准，它们才能在 C 中共同测量并发生对撞。

对应到 Lean 形式化，这个推理被拆成三个可审计入口。`EventualStrictGap`
记录额外的最终严格间隙 `U(n) < L(n)`；`EventualLowerBound.toProofLengthGap`
把 Pudlak 侧的 lower-bound certificate（下界证书）转成同一 `C_n` 上的
证明长度下界；`collisionCore_from_lower_upper_gap` 再把同一对象上的上界、
下界和严格间隙组合成矛盾。集成层进一步暴露
`finalPudlakGapCertificate` 和
`not_rational_from_audited_upper_gap_box_collisionCore`，使审计者可以直接检查
“下界、上界、间隙、共同测量”是否都落在同一个 PA symbol-size proof-length
coordinate（PA 符号大小证明长度坐标）上。

### 2.2 为什么 B 能进入 C

Pudlak 下界本来作用在有限一致性或反射公式族 B_n 上，而不是直接作用在 Sondow 分析公式上。本文采用的桥接方式是 payload graft（载荷嫁接）和 local projection（局部投影）。粗略地说，C_n 不是把 A_n 和 B_n 任意拼接，而是一个可检查的代理公式：它携带 Sondow 侧短验证所需的信息，同时其反射载荷投影回 Pudlak 下界所覆盖的有限一致性族。

因此审计者需要检查三件事：

1. formula equality（公式等式）：本地 `FormulaCode` 中的 C_n 与文献侧或源侧的有限一致性公式是否逐点相同，或是否通过已证明 projection（投影）保持证明长度关系；
2. proof-system equality（证明系统等式）：上下界是否都在 `ProofSystem.PA` 中陈述；
3. length-measure equality（长度度量等式）：上下界是否都使用 `ProofLengthMeasure.symbolSize`，而不是一个侧使用行数、另一个侧使用编码位长。

当前 Lean 工作把这三件事拆成 explicit certificate（显式证书）。这避免了一个常见错误：把“B 有下界”和“C 有短证”放在同一段文字里，但没有证明它们可共同测量。

## 3. 条件性主定理

本文的主结果应表述为条件性定理。

**定理 1（接口级 Sondow-Pudlak 对撞定理）。**
假设给定以下输入：

1. Sondow 坍缩输入：若 γ 有理，则 Sondow 侧产生可验证短证书；
2. Pudlak-Friedman-Buss 有限一致性下界输入：下界可实例化到选定有限一致性/反射公式族；
3. 投影与编码输入：外部有限一致性公式族和本地 `FormulaCode` 族逐点相等、等价或存在可控投影；
4. proof-length calibration（证明长度校准）：抽象 `proof_length` 与本地 checked-code proof length（已检查代码证明长度）在相关公式族上相等；
5. payload truth（载荷真值）输入：反射载荷确实表达预期的有限一致性内容。

则 Lean 组合链推出

```math
\neg \mathrm{is\_rational}(\gamma).
```

该定理是条件性的。它没有在 Lean 内部证明 Sondow 判据、Pudlak theorem 5（Pudlak 定理 5）或 PA 证明长度函数本身。它证明的是：一旦这些外部输入以规定接口给出，后续的编码迁移、长度校准、投影和最终矛盾推导可以被机器检查。

### 3.1 形式化 theorem schema（定理模式）

更精确地说，接口级定理具有如下逻辑形状：

```math
\mathcal S\;\wedge\;\mathcal P\;\wedge\;\mathcal E\;\wedge\;\mathcal L\;\wedge\;\mathcal T
\;\Longrightarrow\;
\neg \mathrm{is\_rational}(\gamma).
```

这里：

- 𝒮 是 Sondow collapse certificate（Sondow 坍缩证书）；
- 𝒫 是 Pudlak lower-bound certificate（Pudlák 下界证书）；
- ℰ 是 encoding/projection certificate（编码/投影证书）；
- ℒ 是 proof-length calibration certificate（证明长度校准证书）；
- 𝒯 是 payload truth certificate（载荷真值证书）。

这个模式有一个重要优点：若某个输入还没有内部证明，它不会被隐藏进“显然”或“按定义”里，而是在 theorem（定理）的参数或 axiom audit（公理审计）中显式出现。当前版本的科学主张正是这个 implication（蕴含）已经被 Lean 检查，而不是 ¬ is_rational(γ) 已经无条件证明。

当前公开索引中，Month 5 gap certificate（第 5 月间隙证书）已经把最终 `U/L` 陈述接入 `ProjectComputableGapCertificate`（项目可计算间隙证书）；Month 6 proof-length calibration（第 6 月证明长度校准）则进一步暴露为 `Month6ProofCodeCheckerCalibrationFrontierCertificate`（证明码检查器校准前沿证书）。后者是边界收紧，而不是无条件消除 `proof_length`（证明长度）输入。

Month 7 layer（第 7 月层）进一步压缩 final theorem surface（最终定理表面）。它把最终矛盾分解到 `GenericRationalCollisionInputs`（通用有理性对撞输入）：这是一个不含 `proof_length`（证明长度）的 generic collision skeleton（通用对撞骨架），只表达“有理性给出同一个 measured function（被测函数）的 eventual polynomial upper bound（最终多项式上界）”与“同一个 measured function 上存在 eventual strict gap（最终严格间隙）”不能并存。项目特有的 PA proof-length box（PA 证明长度盒子）只在 instantiation layer（实例化层）接回。Lean 用 `Month7MinimalTheoremSurface`（第 7 月最小定理表面）、`Month7CompletionChecklist`（第 7 月完成检查表）和 `Month7PreMergeAuditCertificate`（第 7 月合并前审计证书）记录这个边界，并把后续工作拆成 `Month8ProofLengthResidualFrontier`（第 8 月证明长度残留前沿）和 `Month8PayloadLiteratureResidualFrontier`（第 8 月载荷/文献残留前沿）。

### 3.2 没有偷偷改弱陈述

本文使用条件性陈述，但没有把目标改成弱结论。最终 Lean 出口的 conclusion（结论）仍是：

```lean
¬ is_rational euler_mascheroni
```

条件性只出现在输入侧。换言之，形式化没有证明“如果某个与 γ 无关的抽象命题为假，则 γ 无理”这种无意义蕴含；它要求的每个输入都对应对撞链中的一个具体职责。若某张证书只证明了较弱的 family equality（族等式）或使用了不同 proof_length convention（证明长度约定），它将无法实例化当前接口，碰撞盒也不会被调用成功。

## 4. 证明思路

证明分为四步。

第一步是 Sondow 上界。假设 γ ∈ ℚ。在 Sondow 判据及其验证桥输入下，有理性假设给出一个短证明坍缩结论。直观上，原本涉及积分、对数乘积和尾部小数部分的判定问题，被压缩成一个有限证书的验证问题。形式化中这一侧不通过展开巨大整数或巨大乘积取得短证，而通过固定定理引用和二进制索引计费。

第二步是下界标准化。Pudlak-Friedman-Buss 型下界通常陈述为某个有限一致性公式族的证明长度下界。为了使其与项目中的公式代码一致，需要证明文献公式族与本地公式族一致，或给出可控投影。形式化工作将这一步拆成 raw encoding certificate（原始编码证书）、rescaling data（重标定数据）和 lower-bound certificate（下界证书）。

第三步是共同测量。上界和下界只有在同一 `proof_length ProofSystem.PA ProofLengthMeasure.symbolSize` 上才可对撞。这里需要两类校准：一类把 strengthened-to-partial（强化到部分）侧的证明长度等式降到具体 family equality（族等式）；另一类把 local Hilbert checked-code（局部 Hilbert 已检查代码）模型与抽象 PA proof length（PA 证明长度）对齐。

最新 Lean 公开层把这一步进一步拆成 proof-code checker frontier（证明码检查器前沿）和 checker calibration frontier（检查器校准前沿）的 `<=>` 等价。公开定理 `month6_project_checked_semantics_iff_checker_calibration_frontier` 说明 project checked-code semantics（项目已检查码语义）与该校准前沿同义；`public_statement_iff_public_completion_computable_gap_checker_calibration_frontier` 则把这个前沿与 Month 5 的可计算 gap certificate（间隙证书）放在同一个项目级 completion statement（闭合陈述）中。

Month 7 final surface（第 7 月最终表面）随后把项目级陈述与纯 order-theoretic contradiction（序关系矛盾）分开。`GenericRationalCollisionInputs.not_rational` 不含 PA proof-length box（PA 证明长度盒子）：它只说同一个 measured function 上的 `L(n) <= U(n)` eventual upper bound（最终上界）与 `U(n) < L(n)` eventual strict gap（最终严格间隙）不能同时由有理性假设推出。剩余的 `proof_length`（证明长度）和 payload（载荷）假设出现在 project instantiation（项目实例化）层，而不是 generic skeleton（通用骨架）本身。

第四步是矛盾。Sondow 侧给出同一公式族的短证明上界，Pudlak 下界侧给出同一公式族的强下界。二者在同一个公式代码、同一个证明系统和同一个长度度量下先推出 `L(n) ≤ U(n)`，再与 gap condition（间隙条件）`U(n) < L(n)` 相冲突。注意这里的 gap condition（间隙条件）不是从 Pudlak 下界自动得出，而是作为独立的 growth domination certificate（增长支配证书）进入对撞盒。因此有理性假设不能与这些输入同时成立，推出

```math
\neg \mathrm{is\_rational}(\gamma).
```

从工程上看，这四步对应一个 compiler-correctness（编译器正确性）问题：Sondow 侧、Pudlak 侧和本地 Hilbert/PA 检查器不是同一语言，因此必须证明翻译不会改变要对撞的长度命题。本文的 Lean 模块正是把这些翻译拆成小的 certificate（证书）并逐一组合。

## 5. Lean 形式化的实质作用

Lean 形式化在本文中有三个实质作用。

第一，它强制所有定理携带输入包。最终出口不是无参数定理，而是需要显式输入：

```lean
SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
```

该定理的类型返回：

```lean
¬ is_rational euler_mascheroni
```

但它需要 Sondow 上界输入和 Pudlak/校准侧输入。这样审计者可以直接从定理类型看出条件边界。

第二，它检查桥接是否真的闭合。近期形式化把两类关键 witness（见证）降到更窄接口：

```lean
StrengthenedToPartialProjectProofLengthExactFamilyLengths
PAHilbertPartialConsistencyMinCheckedExactness
PAHilbertReflectionGraftMinCheckedExactness
```

并提供从 semantic convention（语义约定）到 exact split minChecked（精确拆分最小已检查码长）的转换。因此当前碰撞盒已经可以实际调用，而不是只停留在叙述层。

### 5.1 可复刻的符号对撞检查点

2026 年 7 月 7 日，仓库发布了一个面向审计的 prerelease（预发布）：

```text
fcce697-symbolic-collision-checkpoint
```

该 release（发布）固定到 commit（提交）
`fcce697c60adfe87d4d33515ff965322962fc994`。它的含义是：在不要求计算具体
数值 `N` 的前提下，Lean 已经把 checked lower bound（检查下界）接入
no-fallback target `bigN` certificate（无后备目标大阈值证书），并在同一个
symbolic witness（符号见证）上形成形式化对撞。核心证书给出同一个 `bigN` 上的

```lean
upper.U bigN < measured bigN
measured bigN <= upper.U bigN
False
```

因此该版本适合被引用为 reproducible symbolic collision checkpoint
（可复刻符号对撞检查点）。复刻命令为：

```bash
git clone git@github.com:james130012/sondow-pudlak-collision-box.git
cd sondow-pudlak-collision-box
git checkout fcce697-symbolic-collision-checkpoint
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

这不是 numeric evaluation checkpoint（数值求值检查点）：它没有输出具体自然数
`N`。它证明的是形式化对撞对象已经闭合到一个可审计的 `bigN` witness（大阈值见证），
而后续版本再把该 witness（见证）进一步规范化为
`rejectionExtractor.witness upper.U upper.polynomial 0`（拒绝抽取器见证）。

当前 Lean 公开层已经进一步和项目实例化层分离。项目无关的公开导出路径由下面这些模块给出：

```lean
CertificateBackedCollisionKernel
PublicCollisionAPI
PublicCollisionExportSurface
```

这些模块不导入 CnBox/Sondow/Pudlak 项目路线。项目路线保留在
CnBox-Pudlak 模块中，其中当前面向论文的 source/assembly interface
（源/装配接口）是：

```lean
CnBoxPudlakProjectConcreteFieldIndex
CnBoxPudlakProjectSourceAssemblyReleaseSurface
```

其中 `field_index_canonical_certificate_at` 暴露从 concrete project field
index（具体项目字段索引）和一个被接受的 Sondow 实例到
`CanonicalProofCertificateAt bound n`（规范证明证书）的路线；
`accepted_index_iff_assembly_index` 记录 accepted-source compiler（接受源编译器）
和 budgeted assembly（带预算装配）接口是同一个具体项目义务的等价表示。
这是一条 Lean 检查过的 interface statement（接口陈述），不是最终 concrete
certificate（具体证书）的构造。

当前面向公开论文陈述的项目定理层是：

```lean
SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface
Month1PublicBridgeClosureTheoremLayer
```

它把 concrete route（具体路线）、paper route（论文路线）、release checkpoint
（发布检查点）和 public origin（公开起源）整理为 equivalence（等价）。
该层还暴露 CnBox target/box equation（C_n 盒子目标/盒子方程）、
回到目标公式的 code roundtrip（编码往返）、CnBox payload（C_n 盒子载荷）
与 PA finite-consistency statement（PA 有限一致性陈述）的等价、same-object
closure（同对象闭合）以及 public gap/collision instantiation（公开间隙/对撞实例化）。
因此论文陈述不再只依赖自然语言说“项目 CnBox 对象与公开对撞内核看到的是同一个对象”；
这个识别已经被命名 Lean theorem surface（Lean 定理表面）承载。

Month 2 的 Sondow accepted-certificate surface（Sondow 接受证书表面）进一步把上界侧的公开入口固定为：

```lean
SondowProjectMonth2SondowAcceptedCertificateSurface
SondowProjectMonth2PublicReleaseSmoke
SondowProjectMonth2CanonicalImportSurface
```

其中 accepted predicate（接受谓词）由

```lean
Month2SondowAccepted n
```

固定为 `accepted_certificate (sondowReflectionGraftCode n)`，并由
`month2SondowAccepted_iff_root_accepted` 记录 definitional equivalence（定义等价）。
在 `PublicInfrastructureKit`（公开基础设施包）和 rationality assumption（有理性假设）下，
canonical import surface（规范导入表面）暴露两个面向审计的出口：
`accepted_eventually` 和 `compiler_consumption_after_threshold`。前者给出
eventual accepted certificate（最终接受证书），后者在 audit threshold（审计阈值）之后同时给出
full certificate checks（完整证书检查）、source components（源组件）、compiled certificate（已编译证书）
和 component proof-object validity（组件证明对象有效性）。这仍是 conditional public surface
（条件性公开表面），不是无条件的具体 Sondow witness（Sondow 见证）；它的作用是把 Month 2
的“有理性到接受证书再到编译器消费”陈述变成可单模块导入、可探针复验的 Lean 接口。

Month 3 和 Month 4 进一步闭合下一层公开接口：

```lean
SondowProjectMonth3Month4FinalPublicSurface
SondowProjectMonth3Month4CompletionAuditSurface
```

Month 3 侧把 accepted Sondow object（已接受的 Sondow 对象）推进到
bounded-PA proof predicate interface（有界 PA 证明谓词接口）。更具体地说，
final public surface（最终公开表面）从 paper route（论文路线）加一个 accepted witness
（接受见证）推出 `CanonicalProofCertificateAt bound n`（规范证明证书）、
`CanonicalProofCertificateAccepted bound n`（规范证明证书已接受）和
`boundedPAProofPredicate bound n`（有界 PA 证明谓词），并给出等价式：

```lean
boundedPAProofPredicate bound n ↔ Nonempty (CanonicalProofCertificateAt bound n)
```

同时，checker trace conclusion（检查器跟踪结论）被证明等于
`finiteConsistencyFormula n`（有限一致性公式）。这一步说明 `C_n` 盒子不再只是
codable object（可编码对象），而已经接到 finite-consistency target（有限一致性目标）
和 bounded PA proof-predicate interface（有界 PA 证明谓词接口）。

Month 4 侧把 Pudlak theorem 5（Pudlak 定理 5）的 exact external boundary
（精确外部边界）打包为公开可审计对象。它没有内部证明 Pudlak theorem 5，而是把
literature input（文献输入）、external input boundary（外部输入边界）、
minimal field package（最小字段包）、lower-bound source（下界源）、normal form
（规范形）和 canonical import（规范导入）互相整理为可审计等价链。公开表面暴露了
literature audit statement（文献审计陈述）与 full external-boundary statement
（完整外部边界陈述）的等价、lower-bound source code（下界源编码）与
rescaled Pudlak strengthened finite-consistency code（重标度 Pudlak 强化有限一致性编码）
的等式，以及 raw/rescaled/power-bound code chain（原始/重标度/幂界编码链）。
因此 final completion certificate（最终闭合证书）记录的是：上界侧 accepted object
（接受对象）和下界侧 Pudlak theorem-5 object（Pudlak 定理 5 对象）通过同一个
public project interface（公开项目接口）比较，而不是靠自然语言识别。

这些名字对应的数学含义如下。

`StrengthenedToPartialProjectProofLengthExactFamilyLengths` 负责 strengthened family（强化族）与 partial consistency family（部分一致性族）之间的长度等式。它回答的问题是：Sondow 坍缩产生的 strengthened payload（强化载荷）在降到 partial consistency proxy（部分一致性代理）时，证明长度是否按需要保持。

`PAHilbertPartialConsistencyMinCheckedExactness` 负责 partial consistency side（部分一致性侧）的 minChecked exactness（最小已检查码长精确性）。它回答的问题是：Pudlak 源侧下界所看到的 proof length（证明长度）是否就是本地 checked-code checker（已检查代码检查器）测到的长度。

`PAHilbertReflectionGraftMinCheckedExactness` 负责 reflection graft side（反射嫁接侧）的相同校准。它回答的问题是：反射载荷进入共同测量盒后，是否仍然使用同一个 PA/Hilbert proof-code semantics（PA/Hilbert 证明码语义）。

第三，它给出 axiom audit（公理审计）。当前调用定理的核心依赖包括：

```text
literaturePudlakTheorem5ExternalRescaledLowerBound
literaturePudlakTheorem5ExternalScaleData
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
```

此外还有 `propext`、`Classical.choice`、`Quot.sound` 等 Lean/Mathlib 常规依赖。这个列表是本文信用边界的一部分：它说明当前成果是接口级条件定理，而不是无条件闭合证明。

近期桥接引理还把若干原先容易靠文字认同的表示转换显式化：

```lean
audit_theorem5_certificatePresentation_iff_rescaledPresentation
FormulaCodeHilbertInterpretation.familyExactness_iff_splitCanonicalCertificate
FormulaCodeHilbertInterpretation.localProofCodeConventionCertificate_iff_familyExactness
paper_route_and_accepted_iff_public_completion
public_completion_to_month3_bounded_pa_interface
public_completion_to_month4_full_boundary_interface
month6_project_checked_semantics_iff_checker_calibration_frontier
public_statement_iff_public_completion_computable_gap_checker_calibration_frontier
```

这些是 certificate presentation（证书表示）之间的 equivalence/transport lemma
（等价/传输引理），不是新的数学假设；它们的作用是缩短审计路径，减少对自然语言
“两种陈述等价”的依赖。

## 6. 为什么这不是普通的“条件证明”

本文的条件性不是把难题简单藏进一个总假设中。每个假设都有明确职责。

Sondow 输入负责从 γ 有理性产生上界。Pudlak 输入负责给出有限一致性下界。编码证书负责说明文献公式族与本地公式族是否一致。证明长度校准负责把抽象证明长度与具体 checked-code 模型接上。payload truth 输入负责说明反射载荷的语义。

因此，若未来某一输入被内部证明或由文献完全匹配地提供，它可以单独替换相应字段，而不需要重写整个对撞链。这是接口级形式化的主要价值。

从审计角度说，本文最重要的 claim（主张）不是“所有困难已经解决”，而是“困难已经被局部化”。审计者可以逐张问：

- Pudlak theorem 5（Pudlák 定理 5）的下界是否真的覆盖当前 family（族）？
- 重标定 scale（尺度）是否保持强下界足以压过 Sondow 上界？
- `proof_length` 与 checked-code min size（已检查码最小大小）是否在两个族上逐点相等？
- payload truth（载荷真值）是否表达了预期的一致性/反射内容？

只要这些问题被逐项回答，最终对撞推导不需要重新设计。

## 7. 剩余工作

当前未闭合部分主要有三类。

第一，Pudlak theorem 5 的内部证明。本文目前把它作为外部文献证书进入。若要完全内部化，需要形式化有限一致性下界的证明复杂度文献。

第二，PA/Hilbert proof-length convention（PA/Hilbert 证明长度约定）。当前 `proof_length` 是抽象复杂度函数，相关等式通过可审计 witness 输入。最新形式化已经把剩余边界收紧到 proof-code checker calibration frontier（证明码检查器校准前沿）：也就是说，项目不再只说“有某个校准见证”，而是公开给出 proof-code checker recognition（证明码检查器识别）与 local proof-length code calibration（局部证明长度码校准）之间的等价前沿。完全内部化仍需要构造具体 PA 证明对象、编码器、检查器和最小证明码长度函数，并证明它们与抽象 `proof_length` 一致。

Month 7 进一步澄清了这项任务，但没有把它无条件消灭。最终定理现在可以通过 `Month7MinimalTheoremSurface`（第 7 月最小定理表面）陈述，而 proof-length-specific residue（证明长度特有残留）被隔离为 `Month8ProofLengthResidualFrontier`（第 8 月证明长度残留前沿）。因此后续证明长度任务不是重做对撞核心，而是用具体 proof-object encoding（证明对象编码）、checker exactness（检查器精确性）和 minProofCodeSize calibration（最小证明码长校准）替换这个残留前沿。

第三，最终 Sondow upper-bound witness（Sondow 上界见证）的无参数实例化。解析积分分解、乘积-对数恒等式、尾界和 Sondow forward package（Sondow 前向输入包）已经有 Lean-closed reproof（Lean 闭合重证）路线；项目本地 verifier/compiler framework（验证器/编译器框架）也已经进入可构建的 `SondowProjectLocalS21Kernel` 和 `SondowProjectLocalReflectionGraftVerifier` 接口。Month 2 已经把 `Month2SondowAccepted n`、component certificate（组件证书）、accepted-to-compiled compiler（接受到编译证书的编译器）以及 canonical import surface（规范导入表面）固定下来。当前不应再把 Sondow 接受证书表面或整个 bounded-arithmetic verifier（有界算术验证器）粗略列为外部缺口。更准确地说，剩余的是把最终入口中的

```lean
Nonempty SondowProjectLocalReflectionGraftVerifier
```

以及 Month 2 使用的 `PublicInfrastructureKit`（公开基础设施包）由更底层的 checked-code S²₁ trace calibration（已检查码 S²₁ 跟踪校准）和 PA embedding witness（PA 嵌入见证）完全构造出来，同时内部化 `PartialConsistencyPayloadTruth` 与 `StrengthenedPartialConsistencyPayloadTruth` 的 payload truth（载荷真值）语义。
在 CnBox/Pudlak 侧，剩余的具体任务不是重新设计 generic interface（通用接口）或 public bridge closure layer（公开桥接闭合层），而是向已有 field-index（字段索引）、assembly（装配）、external-gap（外部间隙）和 public-collision（公开对撞）接口填入足够强的最终 concrete witness（具体见证），使其能支撑无条件目标。Month 5 已经把 `Month5UpperBoundFunction`、`Month5LowerBoundFunction`、threshold certificate（阈值证书）和 growth domination certificate（增长支配证书）组织到 `ProjectComputableGapCertificate`（项目可计算间隙证书）周围；后续工作主要是把这些公开证书连接到最终无参数输入，而不是重做 gap statement（间隙陈述）。
更精确地说，当前不应再把 Month 3 bounded-PA assembly interface（第 3 月有界 PA 装配接口）
或 Month 4 theorem-5 external-boundary interface（第 4 月定理 5 外部边界接口）列为未建立的
框架缺口；剩余任务是提供最终 concrete witness（具体见证），使 accepted object（接受对象）、
growth gap（增长间隙）、payload truth（载荷真值）和 proof-length convention（证明长度约定）
都成为无参数、足够强且可内部审计的实例。

互补的残留包是 `Month8PayloadLiteratureResidualFrontier`（第 8 月载荷/文献残留前沿），其中包含 Pudlak literature lower-bound input（Pudlak 文献下界输入）、minimal closure package（最小闭合包）和 strengthened payload-truth input（加强载荷真值输入）。如果要把第 7 月条件性出口继续增强，就必须在 payload/literature side（载荷/文献侧）消除或内部化这个残留包。

这些任务都很重要，但不影响本文当前主张：在明确输入被提供时，接口级对撞链已经机器检查。

### 7.1 当前版本适合怎样公开

当前稿件更接近 public alpha research artifact（公开 alpha 研究制品）配套论文，而不是声称完全解决 γ 无理性的最终论文。适合公开的表述是：

1. 一个 Lean-checked conditional collision theorem（Lean 检查的条件性对撞定理）；
2. 一个清晰的 certificate architecture（证书架构）；
3. 一个可复验的 axiom ledger（公理账本）；
4. 一个把未来工作压缩到少数 witness（见证）的路线图；
5. `fcce697-symbolic-collision-checkpoint` 这样的可复刻 symbolic collision
   checkpoint（符号对撞检查点）。

不适合公开的表述是：无条件证明欧拉常数无理，或已经内部证明 Pudlak theorem 5（Pudlák 定理 5）与 PA proof-length convention（PA 证明长度约定）。这些边界必须保持清楚。

## 8. 结论

本文给出一个条件性证明复杂度对撞框架，用于组织欧拉常数无理性问题中的 Sondow 判据与 Pudlak-Friedman-Buss 有限一致性下界。其核心贡献不是无条件证明 γ 无理，而是证明如下更精确的命题：若 Sondow 有理性坍缩、有限一致性强下界、编码投影和证明长度校准都按指定接口给出，则它们在同一 PA 符号长度坐标上发生矛盾，从而推出 γ 非有理。

这个结果的价值在于把“哥德尔加速”从哲学直觉变成了可审计的公式族对撞问题。它同时给出下一阶段工作的清晰路线：逐一内部化或精确引用外部输入，直到条件性对撞框架收缩为更强的数学定理。

## 参考文献

1. Jonathan Sondow, “Criteria for Irrationality of Euler's Constant,” *Proceedings of the American Mathematical Society*, 131(11), 3335-3344, 2003. arXiv:math/0209070.
2. Samuel R. Buss, “On Gödel's Theorems on Lengths of Proofs I: Number of Lines and Speedup for Arithmetics,” *Journal of Symbolic Logic*, 59(3), 737-756, 1994.
3. Pavel Pudlak, “On the lengths of proofs of finitistic consistency statements in first order theories,” in *Logic Colloquium 1984*.
4. Pavel Pudlak, “Improved bounds to the lengths of proofs of finitistic consistency statements,” in *Logic and Combinatorics*, 1987.
5. Jan Krajicek and Pavel Pudlak, “The Number of Proof Lines and the Size of Proofs in First-Order Logic,” *Archive for Mathematical Logic*, 1988.
6. The Lean 4 and Mathlib projects, project documentation and source libraries.
