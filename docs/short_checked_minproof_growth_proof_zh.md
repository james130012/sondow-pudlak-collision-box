# 最短证明增长下界：精简证明指导书

更新时间：2026-07-15。

## 1. 主控文件

- [主定理依赖图](checked_minproof_theorem_dependency_graph_zh.dot)：只显示全局主路线和唯一当前工作面。
- [主图 PDF](checked_minproof_theorem_dependency_graph_zh.pdf)：低负载阅读版本。
- [附图 01：诚实证明坐标](checked_minproof_appendix_01_syntax_coordinate_zh.dot)。
- [附图 02：解析器与嵌套轨迹](checked_minproof_appendix_02_parser_traces_zh.dot)。
- [附图 03：验证器步骤与 P_direct](checked_minproof_appendix_03_verifier_predicate_zh.dot)。
- [附图 03 PDF](checked_minproof_appendix_03_verifier_predicate_zh.pdf)：当前工作面的低负载版本。
- [附图 04：PA 定量证明编译器](checked_minproof_appendix_04_pa_quantitative_compiler_zh.dot)。
- [附图 04 PDF](checked_minproof_appendix_04_pa_quantitative_compiler_zh.pdf)：当前工作面的低负载版本。
- [附图 05：Pudlak-Buss 下界与对撞](checked_minproof_appendix_05_pudlak_collision_zh.dot)。
- [旧完整审计图](checked_minproof_theorem_dependency_graph_legacy_20260712_zh.dot)：只作历史源码索引，不再作为实时主控图。

DOT 节点固定记录 `node_id`（节点编号）、`status`（状态）、
`endpoint_theorem`（终点定理）、`source`（源码）、`appendix`（所属附图）和
`next_obligation`（下一证明义务）。绿色必须有 Lean 内核证据；黄色只有一个；灰色等待前置；
红色路线不得通向最终结论。

## 2. 最终目标

在同一个 formula family（公式族）、PA checker（PA 检查器）和
full-payload proof length（完整载荷证明长度）上证明：

```text
Sondow：假设 gamma 有理
  -> 构造同一 F_n 的规范 PA 证明
  -> minProof(F_n) <= U(n) eventually；

Buss-Pudlak：
  -> minProof(F_n) > U(n) eventually；

取同一 N：
  U(N) < minProof(F_N) <= U(N)，矛盾。
```

完成标准同时要求：

1. 同一 `n`、同一 `F_n`、同一 checker（检查器）、同一完整载荷度量。
2. 无 `tail_gap`、无 `upper_provider`、无项目级 `proof_length`。
3. 无 `sorryAx`，无 toy PA（玩具 PA），无编码伪影替代数学下界。
4. 下界来自真实 Pudlak-Buss 定量定理；上界来自真实 Sondow 同对象编译器。
5. 最终依赖与公理画像通过独立审计。

## 3. 根部审计结论

本地 Foundation（形式逻辑库）已经提供真实 `Derivation2 PA`（PA 推导树）、诚实二进制编码、
结构证书以及 checker soundness/completeness（检查器可靠性/完备性），但它的普通
`sigma_one_completeness`（Sigma-one 完备性）走 semantic completeness（语义完备性），
不能给统一多项式证明长度。

外部 `formalization-of-bounded-arithmetic` 项目主要采用 model-theoretic formalization
（模型论形式化）。其作者明确指出该方式不能导出关于证明系统自身的证明对象；当前范围也不是
本项目所需的定量 Buss `S²₁`（Buss 有界算术）证明编译器。因此没有现成库可以直接关闭根义务。

结论：必须在真实 Foundation `Derivation2 PA` 上构造 proof-producing compiler
（证明产生编译器），不能继续把证明存在性或长度界包装成参数。

## 4. 已闭合基础

### 4.1 诚实证明坐标

以下对象已经在同一公开检查器上闭合：

- proof tree（证明树）与 structural certificate（结构证书）全部进入载荷。
- accepted code（接受码）能够恢复同公式真实 `Derivation2`。
- 每个真实 `Derivation2` 能产生规范接受码。
- canonical normalization（规范化）不增长载荷，畸形码不能压低最短长度。
- `minListedCertifiedPAProofPayloadLength` 由检查器本身诱导，不依赖项目级 `proof_length`。

精确依赖见附图 01。

### 4.2 可复用的直接算术化部件

语法、位流、状态表、解析器初终态等 146 组局部定理已经通过 Lean。它们是真实可复用库，
但尚未组成完整 `P_direct`。逐 parser branch（解析器分支）无限展开的工作方式已暂停，因为它
能持续产生局部绿点，却不能先证明通往 PA 短证明编译器的根路径。

详细历史证据保存在旧完整审计图；实时状态见附图 02、03。

## 5. 2026-07-12 至 13 闭合里程碑

### 5.1 真实 PA 定量证明产生核心

[FoundationCompactPAQuantitativeCompilerCore.lean](../integration/FoundationCompactPAQuantitativeCompilerCore.lean)
定义 `CertifiedPAProof φ`（带证书 PA 证明）：

```text
derivation  : Derivation2 PA {φ}
certificate : StructuralValidityCertificate
valid       : certificateValid (ofDerivation derivation) certificate
```

它没有 proof existence（证明存在性）、checker soundness（检查器可靠性）或 length bound
（长度界）输入字段。以下构造均产生实际证明对象，并已给出完整载荷界：

1. `ofAxiom`：PA 公理证书生成一节点真实 PA 证明。
2. `specialize`：全称实例化，实际使用 `cut/wk/exs/closed` 推导。
3. `modusPonens`：肯定前件，复用两份真实证明和证书。
4. `conjunction`：合取引入。
5. `existsIntro`：带显式见证项的存在量词引入。
6. `verifier_eq_true`：每个生成对象都被同一公开检查器接受。
7. `payloadLength_eq`：载荷精确等于证明位数加证书位数。

还已构造任意项上的 `t=t`、等式对称性、`t+0=t`、`t*0=0`、`t*1=t` 的真实 PA 证明。

### 5.2 短二进制数词接线

[FoundationCompactPABinaryNumeralCompiler.lean](../integration/FoundationCompactPABinaryNumeralCompiler.lean)
把上述核心接到 `binaryNumeralTerm n`（短二进制数词）上，并证明：

```text
termCode(binaryNumeralTerm n) <= C0 + C1 * Nat.size n；

完整 proof + certificate 载荷
  <= 固定常数 + 192 + 2048 * (C2 + C1 * Nat.size n)^3。
```

公开 checker acceptance（检查器接受）和上述长度界的公理画像都只有：

```text
propext（命题外延）
Classical.choice（经典选择）
Quot.sound（商类型可靠性）
```

无项目公设、无 `sorryAx`。精确依赖见附图 04。

### 5.3 等式传递性编译器

[FoundationCompactPAQuantitativeEqualityTransitivity.lean](../integration/FoundationCompactPAQuantitativeEqualityTransitivity.lean)
已经无条件构造：

```text
输入：CertifiedPAProof(a=b) 与 CertifiedPAProof(b=c)；
输出：CertifiedPAProof(a=c)；
实现：Eq.trans 公理三次实例化 + 两次 modus ponens；
长度：输入载荷、三个项代码和固定语法预算的显式多项式界。
```

公开 checker acceptance（检查器接受）、三次实例化总界和两次 MP 总界均已通过；
公理画像仍只有 `propext`、`Classical.choice`、`Quot.sound`。

### 5.4 加法与乘法函数合同性

[FoundationCompactPAQuantitativeFunctionCongruence.lean](../integration/FoundationCompactPAQuantitativeFunctionCongruence.lean)
已从真实 `Eq.funcExt`（函数等号保持公理）构造 `proveAddCongruence`
和 `proveMulCongruence`。四次实例化、两层合取、一次 MP、公开验证和完整载荷界
均已通过；七个审计端点均只使用标准三项公理。

### 5.5 二进制加法归一化

[FoundationCompactPABinaryNumeralAddition.lean](../integration/FoundationCompactPABinaryNumeralAddition.lean)
按奇偶位递归构造真实 `CertifiedPAProof`（带证书 PA 证明），处理进位、
加法合同性、分配律和等式传递。
[FoundationCompactPABinaryNumeralAdditionBounds.lean](../integration/FoundationCompactPABinaryNumeralAdditionBounds.lean)
从具体语法编码和每个证明构造子的载荷界推出固定多项式，没有调用证明长度神谕或预设编译器界。

联合端点为：

```text
proveBinaryNumeralAddition_checked_polynomial
  : checker(proof of bn(a)+bn(b)=bn(a+b)) = true
    and payloadLength <= P(Nat.size a + Nat.size b).
```

直接探针与定向构建均通过；端点公理画像只有
`propext`、`Classical.choice`、`Quot.sound`。

### 5.6 二进制乘法归一化

[FoundationCompactPABinaryNumeralMultiplication.lean](../integration/FoundationCompactPABinaryNumeralMultiplication.lean)
按右乘数的二进制位递归构造真实 `CertifiedPAProof`（带证书 PA 证明）。
偶位用乘法结合律和交换律将递归积翻倍；奇位用分配律拆分，再调用已闭合的二进制加法归一化。

[FoundationCompactPABinaryNumeralMultiplicationBounds.lean](../integration/FoundationCompactPABinaryNumeralMultiplicationBounds.lean)
证明递归每下降一个二进制位只增加固定局部成本，且奇位中加法器的总输入位宽由乘法总输入位宽线性控制。联合端点为：

```text
proveBinaryNumeralMultiplication_checked_polynomial
  : checker(proof of bn(a)*bn(b)=bn(a*b)) = true
    and payloadLength <= Q(Nat.size a + Nat.size b).
```

直接探针、定向构建和清洁扫描均通过；端点公理画像只有标准三项。

### 5.7 闭算术原子文字编译器

[FoundationCompactPAClosedAtomicCompiler.lean](../integration/FoundationCompactPAClosedAtomicCompiler.lean)
把短二进制数词、加法和乘法组成的任意闭项先归一化，再统一编译六类真原子文字：
`=`、`≠`、`<`、`¬<`、`≤`、`¬≤`。负分支由真实等式输运、严格序不对称、
反自反性和德摩根合取构造，不接受否定结论或证明存在性作为输入。

[FoundationCompactPAClosedAtomicCompilerBounds.lean](../integration/FoundationCompactPAClosedAtomicCompilerBounds.lean)
给出统一端点：

```text
ClosedPAAtomicLiteralBounds.compile_checked_polynomial
  : Truth literal
    -> checker(compile literal) = true
       and payloadLength(compile literal) <= payloadPolynomial literal.
```

直接探针、定向构建和清洁扫描均通过，统一端点公理画像只有标准三项。
`testBit`、`lengthDef` 和有限表关系由基础原子、连接词和有界量词组成，归入下一层，
不再错误地把它们计作基础原子。

### 5.8 有界公式见证编译器

[FoundationCompactPABoundedUniversalPolynomialBounds.lean](../integration/FoundationCompactPABoundedUniversalPolynomialBounds.lean)
把真实有限穷举证明、分支替换、下界反证分支、切割、解除假设和全称引入的完整载荷，
统一压到 bounded-universal certificate（有界全称证书）的诚实编码长度上。

[FoundationCompactPABoundedFormulaCompiler.lean](../integration/FoundationCompactPABoundedFormulaCompiler.lean)
与 [FoundationCompactPABoundedFormulaCompilerBounds.lean](../integration/FoundationCompactPABoundedFormulaCompilerBounds.lean)
随后给出 proof-free（不含现成证明）证书树，递归覆盖原子、合取、析取、存在见证和有限有界全称。
联合端点为：

```text
CheckedClosedBoundedFormulaCertificate.compile_checked_polynomial
  : checker(compile certificate) = true
    and payloadLength(compile certificate)
      <= fixedPolynomial(encodedSize certificate).
```

直接探针、定向构建和禁用依赖扫描均通过；最终公理画像只有标准三项。
无 `tail_gap`、`upper_provider`、项目级 `proof_length`、`sorryAx` 或证明存在性输入。

## 6. 唯一当前义务

`A04.17` 已闭合。黄色主节点仍为 `M10`：同一公开检查器的
`P_direct(bound,y)`（直接验证谓词）。`A03.05e3a--b` 现已全部闭合：固定 93 列
Delta-zero（有界算术）combine 图一方面严格推出公开 `verifierStep`（验证器单步），另一方面从
任意公开非解析 combine 步骤构造同一图的有界见证。

反向端点把规范前后状态、真实任务头、drop-one（删除任务首项）、七种成功规则、精确失败分支，
以及 All/Shift/Exs/Cut（全称/移位/存在/切割）所需的派生公式和逐公式轨迹放入同一
token table（令牌表）。公开规则号 3--9、单前提/双前提栈形及所有失败情况已穷尽分流；没有图存在性、
布局、成功表或界参数。端点探针、定向构建和禁用扫描均通过，公理画像只有
`propext`（命题外延）、`Classical.choice`（经典选择）、`Quot.sound`（商类型可靠性）。

`A03.05e4` 已闭合：固定 429 列 `Sigma-zero`（零阶有界算术）公式统一 halted、finish、parse、
combine（已停止、结束、解析、组合）四类公开单步。任意满足图的行都实现同一公开
`compactNumericVerifierStep`（紧凑数值验证器单步）；反向则从任意真实公开单步规范构造同一公式见证，
并显式锁定状态表、当前切片和下一切片的起止列。总端点、正向精确性、层级与禁用扫描全部通过，
公理画像仅有 `propext`、`Classical.choice`、`Quot.sound`。

当前唯一义务转为 `A03.06`：把初态、逐行 429 列单步公式和终态汇成完整验证轨迹公式。

parse（解析）分支的 successful closed-formula trace（成功封闭公式轨迹）现已闭合：
真实封闭解析与普通解析的唯一差异被证明为局部 free-variable guard（自由变量保护条件），
随后完成相邻步公式、有界行表安装以及 15 变量完整轨迹公式。正向构造、反向重建、
`Sigma-zero`（有界算术层级）与 axiom profile（公理画像）探针均通过；端点只依赖
`propext`、`Classical.choice`、`Quot.sound`。sequent（序列）公式列表的单步也已双向闭合，
并进一步汇入同一个九变量 `Sigma-zero`（有界算术）轨迹公式：该公式不接收
语义列表或解析器状态参数，而是自行重建全部后缀、全部公式值及每一条真实解析轨迹，并严格推出
公开 `compactFormulaTokenValuesRepeat`（公式列表重复解析器）的整体返回等式。首令牌计数与最终后缀的
27 列端点公式现已双向闭合：任意公开 sequent parser（序列解析器）成功结果都会规范构造全部中间后缀、
每条真实 parser trace（解析器轨迹）、唯一共享 token table（令牌表）以及一个覆盖 18 个局部见证的公共界；
反向端点则重建同一个公开返回等式。直接探针通过，公理画像仍仅有 `propext`、`Classical.choice`、
`Quot.sound`，无轨迹、布局、公共界或图存在性输入。proof-root（证明根）的 sequent-only（仅序列）标签
`2/7/8` 也已完成共享表双向端点：46 列 `Sigma-zero`（有界算术）基础图把完整输入、真实根字段、
序列正文、全部公式轨迹与最终后缀锁在同一坐标；37 个局部坐标由一个公开界统一约束。公开解析成功到
有界图、以及有界图到同一公开解析结果的探针均通过。closed-formula parser endpoint（封闭公式解析端点）
也已完成自包含双向有界公式。复用统一 shared table（共享表）后，单公式标签 `0/5/9` 进一步闭合为 57 列
`Sigma-zero` 基础图和 48 个局部坐标的单一公开界；标签与 binder arity（绑定变量元数）、序列最终后缀、
根第一字段和根最终后缀均被同表锁定。其双向语义、公开成功到有界图、层级和禁用依赖探针全部通过，
公理画像仍仅标准三项。proof-root（证明根）标签 `1` 也已按同一 57 列、48 局部坐标结构完成封闭公式
保护条件、双向语义和公开有界入口，且禁用扫描为空。标签 `3/4` 的两公式分支已完成同表双向语义：
两条真实解析轨迹、唯一中间后缀和两次精确拼接均由公开成功结果规范生成，反向严格还原同一公开解析；
并已闭合为 68 列 `Sigma-zero` 基础图及 59 个局部坐标的单一公开界。公式逐点等价、正反入口、层级、
公理画像和禁用扫描全部通过。标签 `6` 的“公式 + 项”分支也已在同样的 68 列、59 局部坐标结构中
完成双向语义与有界闭合：空第二字段、第一字段公式、witness（见证）字段项及两次精确拼接均由同表锁定，
单文件探针、公理画像和禁用扫描全部通过。certificate（证书）成功端的简单标签 `0/2/3`、固定单令牌
PA 标签、函数/关系符号标签 `3/4` 以及带完整公式解析轨迹的归纳标签 `22`，现均已完成共享表双向语义、
单一公开界、`Sigma-zero`（有界算术层级）、公理画像和禁用扫描。四组成功分支现已汇成同一公开公式；
任意成功解析都经 23 个 PA 构造器的穷尽反演进入其中一个分支，公开完整性探针通过。通用
formula/term parser no-output（公式／项解析器无输出）路线也已闭合：自包含有界公式固定公开燃料，编码
初态、每一条真实相邻步和“仍运行或明确失败”的精确终态，并双向等价于公开解析结果 `none`；它不把
燃料耗尽误写成明确失败，探针公理画像仍仅标准三项。certificate-node failure（证书节点失败）现也
已整体闭合：空／非法外标签、空 PA 输入、标签 `3/4` 的短载荷或非法符号码、标签 `22` 的公式无输出、
标签 `>22` 均由一个公开单界公式穷尽，并与真实解析器返回 `none` 双向等价。proof-root
（证明根）的成功与失败总图现已闭合：公开十种标签的成功路线和六类失败路线均有同表有界公式、
可靠性和穷尽完备性；certificate-node（证书节点）两侧亦已闭合。node transition（节点转移）的
十种成功输出与标签不匹配失败现已逐案闭合；固定自然数列表也已编译成直接 `Sigma-zero`（有界算术）公式，
可在不接收外部等式证书的情况下锁定固定 PA 公理句。固定 22 类公理（含 6 个符号实例）、
同一 `Gamma`（推理上下文）成员关系与结果位现已汇成直接 `Sigma-zero` 图，并证明等于公开
`compactAxmRuleCheck`（PA 公理规则检查）的同一布尔返回值。归纳公理分支的
`succInd/fvSup/fixitr/all-closure`（后继归纳式／自由变量上界／变量固定化／全称闭包）现已全部闭合。
完整 `succInd` 由固定零见证、后继见证、否定、析取和量词构造器形成 148 坐标直接图；再与自由变量
上确界和固定全称闭包组合为单一 177 坐标 `Sigma-zero`（有界算术）公式。该公式直接推出与公开
PA 归纳证书完全相同的候选句，规范、层级和语义探针均仅依赖标准三项，无外部结果、隐藏上界或等式证书。
候选句与实际证明节点公式的精确比较、`Gamma`（推理上下文）成员关系及公开结果位现已汇成
184 坐标直接归纳规则公式，并逐点等价于 `compactAxmRuleCheck`。进一步完成了规范非空性：任意真实主体
都能把 25 个公式／见证列表和 12 条可执行变换轨迹装入同一 token table（词元表），构造完整
177 坐标路线；该构造允许附加编码块，因而候选公式和 `Gamma` 不必落入另一坐标。直接探针通过，
公理画像只有标准三项，禁用依赖扫描为空。

`axiomTokens/candidate/Gamma`（公理载荷／候选公式／推理上下文）现已作为第 37--39 块规范安装进
同一张 40 块共享表，闭合 184 坐标归纳规则公式的完整性入口。端点
`exists_compactCanonicalInductionPAAxiomRuleCheck`（规范归纳 PA 公理检查存在性）直接通过，公理画像
只有标准三项，且没有项目级输入。

非叶节点 parse scheduling（解析调度）的基础行图现已闭合：任意一子节点标签 `4--8` 精确生成
`parse :: combine(root) :: tail`，任意二子节点标签 `3/9` 精确生成
`parse :: parse :: combine(root) :: tail`。任意索引任务行、消费一个旧表头并保留完整尾部、根切片与
combine task（合并任务）相等，均已形成直接 `Sigma-zero`（有界算术）公式。现在从真实前后任务行、
真实根布局和精确目标栈直接规范构造 one-parse/two-parse（一次／两次解析）的全部坐标与大小见证，
并得到 39/53 坐标公式的反向入口；本机探针和目标 `.olean` 均通过，公理画像仅标准三项。

叶节点公共状态框架、任务栈 drop-one（删除表头）和结果栈精确压入现已闭合；closed/verum
（闭合／真值）规则已直接得到公开检查器结果。PA 公理叶的固定标签、函数／关系符号标签和归纳标签
也已分别与同一 certificate endpoint（证书端点）联合：证书解析得到的真实 `axiomTokens`
（公理令牌列表）就是规则检查使用的列表。三类联合公式、语义可靠性、层级和禁用依赖探针均通过，
公理画像仅标准三项。

proof/certificate parse failure（证明／证书解析失败）和 tag mismatch（标签不匹配）现已汇成
同一个 29 坐标 `Sigma-zero`（有界算术）分表载荷失败图。状态流、证明解析器和证书解析器可以使用三张
独立规范表；两条 exact cross-table slice equality（精确跨表切片等值）把解析输入锁回真实状态流。
成功证明根和证书节点现都从公开解析结果构造原输入布局；图内 `proofTag`（证明标签）再由解析确定性
校准为真实根标签。三类失败语义到图的反向构造、图到公开 `compactNumericParsePayload = none` 的可靠性，
以及最终逐点 `iff`（当且仅当）均已通过，公理画像仅标准三项，无布局、图存在性或标签输入。

29 坐标分表失败载荷图现已与规范状态更新行合成 48 坐标失败分支，并嵌入当前态／下一态核心、
真实解析任务头，形成 81 坐标 `Sigma-zero`（有界算术）分表失败状态图。正向端点严格重建两份真实状态
布局并推出 `next = compactNumericVerifierStep current`；反向端点从规范前后状态和真实
`compactNumericParsePayload = none`（解析载荷失败）直接构造完整状态图见证。证明解析器、证书解析器
与状态流保持三张独立规范表，两条跨表切片等值负责同输入校准。公式解释、层级、正反构造和禁用依赖探针
均通过，公理画像仅标准三项；旧单表 71 坐标图不再承担当前路线。

公共成功解析与叶栈转移的 68 坐标图、同一证明表上的 Verum（真常元）规则及其完整状态分支现已闭合，
公理画像仅标准三项。解析载荷使用完整当前任务栈 `drop 1`（去掉解析任务后的剩余栈）；证书零标签、目标栈、
目标值及两条下一输入流均由真实节点转移推出，不再作为输入。Closed（闭式公式）叶也已闭合：真实标签零
解析出的 `Gamma`（前提列表）和闭公式，经两条跨表切片等值绑定到独立规范规则表；96 坐标状态公式的
解释、层级、正向可靠性和从真实解析／转移出发的反向构造均通过，公理画像仅标准三项。PA
（皮亚诺算术）公理叶也已闭合为 327 坐标完整状态图：前 68 坐标承担真实解析和栈转移，后 259 坐标承担
同一证书端点与规则表；`Gamma`/候选句/证书三条跨表切片逐位等式锁定同一对象。
fixed/symbol/induction（固定／符号／归纳）三分支均恢复真实 PA 证书并推出公开规则结果，不用只保留
固定公理元数据的统一规则包代替完整证书绑定；公式解释、`Sigma-zero` 层级、正向可靠性以及从真实
`compactNumericNodeTransition`（数值节点转移）反向构造全部通过本机探针和目标 `.olean`，公理画像仅标准三项。
非叶 tag 3--9 的 93 坐标 combine 成功聚合也已闭合：
七个规范构造器均在状态框架内推出 `statusTag = 0`（成功状态标签），正向语义与从真实 combine
transition（合并转移）出发的反向构造均通过；任务栈只消费一次，不重复 `drop`。
one-parse/two-parse 基础行图、tag `3--9` 的解析成功完整状态图和 parse state（解析状态）逐点语义
现均已闭合，并已与 halted/finish/combine（已停止／结束／组合）汇总为完整公开单步有界图。
`A03.05e4` 已转绿；后续工作不再展开单步内部，而从 `A03.06` 的完整轨迹公式继续。

```text
已审计 verifierStep 部件
  -> All/Shift 任务头 + 子结果 + 栈转移（已闭合）
  -> 简单规则真实头接线（已闭合）
  -> 任务栈 drop-one（已闭合）
  -> 真实任务表头（已闭合）
  -> 状态级 combine 正向可靠性（已闭合）
  -> 状态级 combine 反向构造性（已闭合）
  -> 完整单步有界图（当前）
  -> initial + every step + final 的完整验证轨迹公式
  -> P_direct(bound,y)
  -> 标准模型中逐点 iff 同一公开检查器接受。
```

不得恢复逐 parser branch（解析器分支）无限扩张；只汇总最终单步图实际需要的部件。
`P_direct` 闭合后，`A04.18` 才把接受轨迹证书交给已闭合的 A04.17，生成统一多项式长度的真实 PA 证明。

随后按固定顺序推进：

```text
A04.12 等式传递性（已闭合）
  -> A04.13 加法/乘法函数合同性（已闭合）
  -> A04.14 二进制加法归一化（已闭合）
  -> A04.15 二进制乘法归一化（已闭合）
  -> A04.16 闭原子算术编译器（已闭合）
  -> A04.17 有界公式见证编译器（已闭合）
  -> M10 / A03.05--07 同一 P_direct（当前）
  -> A04.18 接受验证轨迹短证明编译器。
```

只有 `A04.18` 闭合后，才进入 Pudlak quantitative conditions (0)-(3)
（Pudlak 定量条件 (0)-(3)）。

## 7. 文献校准

Pudlak 1986 Theorem 3.1（定理 3.1）必须在同一紧凑证明谓词上给出显式固定多项式
`p1,p2,p3,q1,q2`，并完成：

```text
quantitative diagonalization（定量对角化）
bounded proof assembly（有界证明拼接）
consistency/exponent extraction（一致性反证与指数提取）。
```

Buss 1994 Theorem 5（第 5 定理）还要求 time-constructible rescaling
（时间可构造重标定）。不能把一个抽象 super-polynomial gap（超多项式间隙）接口当作该定理。

## 8. 验证方式

开发阶段只运行当前目标的定向探针：

```bash
lake env lean integration/FoundationCompactPAQuantitativeCompilerCore.lean
lake env lean integration/FoundationCompactPABinaryNumeralCompiler.lean
lake env lean integration/FoundationCompactPAQuantitativeEqualityTransitivity.lean
lake env lean integration/FoundationCompactPAQuantitativeFunctionCongruence.lean
lake env lean integration/FoundationCompactPABinaryNumeralAddition.lean
lake env lean integration/FoundationCompactPABinaryNumeralAdditionBounds.lean
lake env lean integration/FoundationCompactPABinaryNumeralMultiplication.lean
lake env lean integration/FoundationCompactPABinaryNumeralMultiplicationBounds.lean
lake env lean integration/FoundationCompactPANegativeOrderBounds.lean
lake env lean integration/FoundationCompactPAClosedAtomicCompiler.lean
lake env lean integration/FoundationCompactPAClosedAtomicCompilerBounds.lean
lake env lean integration/FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds.lean
lake env lean integration/FoundationCompactPABoundedUniversalPolynomialBounds.lean
lake env lean integration/FoundationCompactPABoundedFormulaCompiler.lean
lake env lean integration/FoundationCompactPABoundedFormulaCompilerBounds.lean
lake env lean integration/FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula.lean
lake env lean integration/FoundationCompactNumericListedDirectFormulaShiftExactListRows.lean
lake env lean integration/FoundationCompactNumericListedDirectAllShiftRuleCheck.lean
lake env lean integration/FoundationCompactNumericListedDirectAllShiftCombineRuleRows.lean
lake env lean integration/FoundationCompactNumericListedDirectSimpleCombineTransitionRows.lean
lake env lean integration/FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph.lean
lake env lean integration/FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness.lean
lake build integration.FoundationCompactPAClosedAtomicCompilerBounds
lake build integration.FoundationCompactPABoundedUniversalPolynomialBounds
lake build integration.FoundationCompactPABoundedFormulaCompilerBounds
lake build integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness
```

上述定向探针与定向构建均通过。只有最终根义务全部闭合后才运行全项目构建。

图和指导书只在一个黄色节点整体转绿或路线发生根本变化时更新；不为单个辅助引理频繁重绘。
