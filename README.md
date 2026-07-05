# Sondow-Pudlak 条件性对撞盒

本仓库是一个 Lean 4 研究制品，用于组织围绕 Euler-Mascheroni constant（欧拉-马歇罗尼常数）`gamma` 的 conditional proof-complexity collision framework（条件性证明复杂度对撞框架）。

**当前状态。** 本仓库不声称已经给出 `gamma` irrationality（欧拉常数无理性）的 unconditional proof（无条件证明）。当前最强出口是一个 interface-level conditional collision theorem（接口级条件性对撞定理）：在明确列出的 Sondow collapse（Sondow 坍缩）、Pudlak-Friedman-Buss lower bound（Pudlak-Friedman-Buss 下界）、proof-length calibration（证明长度校准）和 payload truth（载荷真值）输入被提供时，Lean 组合链推出：

```lean
¬ is_rational euler_mascheroni
```

本项目的目标是把剩余 mathematical obligations（数学义务）和 proof-complexity obligations（证明复杂度义务）显式化，而不是把它们藏在成功编译背后。

2026-07-04 的公开同步新增了 Month 1 public bridge closure theorem layer（第 1 月公开桥接闭合定理层）：它把 CnBox/Pudlak project route（C_n 盒子/Pudlak 项目路线）的 concrete route（具体路线）、paper route（论文路线）、release checkpoint（发布检查点）和 public origin（公开起源）整理为 Lean 可检查的 `<=>` 等价层，并暴露 CnBox equation endpoints（C_n 盒子方程端点）、PA finite-consistency payload（PA 有限一致性载荷）、public gap instantiation（公开间隙实例化）和 public collision instantiation（公开对撞实例化）。

2026-07-05 的公开同步新增了 Month 3/Month 4 completion audit surface（第 3/4 月闭合审计表面）：它把 accepted certificate（接受证书）推进到 `CanonicalProofCertificateAt bound n`（规范证明证书）和 `boundedPAProofPredicate bound n`（有界 PA 证明谓词）的同对象接口，同时把 Pudlak theorem 5（Pudlak 定理 5）的 literature input（文献输入）、external boundary（外部边界）、minimal field package（最小字段包）和 canonical import（规范导入）整理为可探针检查的 `<=>` 等价链。

同日后续同步新增了 Month 5/Month 6 theorem index surface（第 5/6 月定理索引表面）：它把最终 `U/L` gap certificate（间隙证书）推进到 `ProjectComputableGapCertificate`（项目可计算间隙证书）和公开 completion checklist（闭合检查表），并把 proof-length internalization（证明长度内部化）的公开边界从普通 checked-code replacement（已检查码替换）收紧到 `Month6ProofCodeCheckerCalibrationFrontierCertificate`（证明码检查器校准前沿证书）。这不是消灭 `proof_length`（证明长度）外部性；它精确标出了剩余边界在 proof-code checker recognition（证明码检查器识别）与 local proof-length code calibration（局部证明长度码校准）之间。

## 优先权、引用与贡献边界

本仓库记录的是 Sondow-Pudlak conditional collision box（Sondow-Pudlak 条件性对撞盒）的 public-alpha timestamp（公开 alpha 时间戳）。如果你使用、改写或继续推进这里的接口、证书结构、Lean 形式化路线或论文表述，请引用本仓库和对应 release（版本发布）；引用信息见 [`CITATION.cff`](CITATION.cff)。

当前已公开的核心贡献包括：

- 一个把 Sondow collapse（Sondow 坍缩）与 Pudlak-Friedman-Buss finite-consistency lower bound（有限一致性下界）放入共同 proof-length coordinate（证明长度坐标）的 certificate architecture（证书架构）；
- 一个 Lean-checked interface-level theorem（Lean 检查的接口级定理），在显式输入下推出 `¬ is_rational euler_mascheroni`；
- 一个明确的 axiom ledger（公理账本）和 audit boundary（审计边界），说明哪些 witness（见证）已经机器检查组合，哪些仍是 external/abstract inputs（外部/抽象输入）。
- 一个 public bridge closure layer（公开桥接闭合层），把 CnBox equation endpoints（C_n 盒子方程端点）、same-object closure（同对象闭合）和公开 gap/collision endpoints（间隙/对撞端点）放在单一可探针入口中。
- 一个 Month 3/Month 4 public completion layer（第 3/4 月公开闭合层），把 accepted Sondow object（已接受的 Sondow 对象）、bounded PA proof predicate（有界 PA 证明谓词）和 Pudlak theorem-5 exact external boundary（Pudlak 定理 5 精确外部边界）接到同一个 `PublicCompletionCertificate`（公开闭合证书）中。
- 一个 Month 5/Month 6 public theorem index（第 5/6 月公开定理索引），把 computable gap certificate（可计算间隙证书）、growth domination threshold（增长支配阈值）和 proof-code checker calibration frontier（证明码检查器校准前沿）整理成可 `#check` 和 `#print axioms` 的公开 theorem surface（定理表面）。

贡献者可以提交 pull request（拉取请求）继续内部化 witness（见证）或改进文档，但不应把当前 public-alpha 版本表述为已经无条件证明 γ 无理。任何基于本项目的后续工作都应清楚区分：本仓库已经给出的 interface/collision architecture（接口/对撞架构），以及后续作者新增闭合的 external witness（外部见证）或 internal proof（内部证明）。

## 主要入口

- 英文论文草稿：[`paper/paper_new_en.md`](paper/paper_new_en.md)
- 中文论文草稿：[`paper/paper_new_zh.md`](paper/paper_new_zh.md)
- 当前状态：[`STATUS.md`](STATUS.md)
- 公理账本：[`AXIOM_LEDGER.md`](AXIOM_LEDGER.md)
- 审计指南：[`docs/audit_guide.md`](docs/audit_guide.md)
- 主要可调用对撞盒入口：

```lean
SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
```

该入口定义在：

```text
integration/SondowProjectPudlakInstantiation.lean
```

- Month 1 公开桥接闭合入口：

```text
integration/SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface.lean
```

- Month 3/Month 4 公开闭合审计入口：

```text
integration/SondowProjectMonth3Month4CompletionAuditSurface.lean
```

- Month 5/Month 6 公开定理索引入口：

```text
integration/SondowProjectMonth5Month6TheoremIndexSurface.lean
```

## 构建

本仓库固定使用 Lean `v4.31.0`。

日常审计可先跑轻量探针，避免启动完整构建：

```bash
lake exe cache get
lake env lean -o bounded_arithmetic_lab/.lake/build/lib/lean/BoundedArithmeticLab.olean bounded_arithmetic_lab/BoundedArithmeticLab.lean
lake env lean --stdin <<'EOF'
import BoundedArithmeticLab.PublicCollisionExportSurface
open BoundedArithmeticLab
#check PublicCollisionExportSurface.collision
#check PublicCollisionAPI.collision_from_checklist
EOF
```

完整构建可作为较重的最终检查：

```bash
lake exe cache get
lake build EulerLimit.StrengthenedConsistency
lake build EulerLimit.ProjectionBridge
lake build integration.SondowProjectPudlakInstantiation
```

上述模块构建完成后，源文件探针也应能运行，例如：

```bash
lake env lean integration/SondowProjectPudlakInstantiation.lean
```

## 审计

在引用某个出口为 fully formalized（完全形式化）之前，应检查其 assumptions（假设）和 axiom dependencies（公理依赖）：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#check SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
#print axioms SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

新的公开桥接闭合层可用下面的入口审计：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface
open SondowMainCheckedCodeBridge.SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface

#check Month1PublicBridgeClosureTheoremLayer
#check Month1PublicBridgeClosureTheoremLayer.concrete_iff_public_origin
#check Month1PublicBridgeClosureTheoremLayer.target_eq_box_formula
#check Month1PublicBridgeClosureTheoremLayer.carries_iff_pa_finite_consistency
#check Month1PublicBridgeClosureTheoremLayer.public_gap_instantiation
EOF
```

Month 3/Month 4 公开闭合层可用下面的入口审计：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth3Month4CompletionAuditSurface
open SondowMainCheckedCodeBridge.SondowProjectMonth3Month4CompletionAuditSurface

#check PublicCompletionCertificate
#check paper_route_and_accepted_iff_public_completion
#check exactFamily_checklist_and_accepted_iff_public_completion
#check public_completion_to_month3_bounded_pa_interface
#check public_completion_to_month4_full_boundary_interface
#check public_completion_to_public_gap_instantiation
#check public_completion_not_main_rationality
EOF
```

Month 5/Month 6 公开间隙与校准前沿可用下面的入口审计：

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth5Month6TheoremIndexSurface
open SondowMainCheckedCodeBridge.SondowProjectMonth5Month6TheoremIndexSurface

#check public_statement_iff_public_completion_computable_gap_checker_calibration_frontier
#check month6_project_checked_semantics_iff_checker_calibration_frontier
#check month6_proof_code_checker_frontier_iff_checker_calibration_frontier
#print axioms public_statement_iff_public_completion_computable_gap_checker_calibration_frontier
EOF
```

当前核心 external or abstract inputs（外部或抽象输入）列在 [`AXIOM_LEDGER.md`](AXIOM_LEDGER.md) 中。最近一次本地审计显示主要依赖为：

```text
literaturePudlakTheorem5ExternalRescaledLowerBound
literaturePudlakTheorem5ExternalScaleData
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

此外还有 `propext`、`Classical.choice`、`Quot.sound` 等 Lean/Mathlib（Lean/数学库）常规依赖。

## 已形式化内容

- formula families（公式族）通过 `FormulaCode` 组织。
- common proof system（共同证明系统）固定为 `ProofSystem.PA`。
- proof-length measure（证明长度度量）固定为 `ProofLengthMeasure.symbolSize`。
- 对撞盒出口已经可调用，并在显式输入下返回目标结论 `¬ is_rational euler_mascheroni`。
- Sondow analytic side（Sondow 解析侧）已有 Lean-closed reproof（Lean 闭合重证）路线，包括 product-log identity（乘积-对数恒等式）、decomposition（分解）、tail estimates（尾界）和 Sondow forward package（Sondow 前向输入包）。
- project-local verifier/compiler framework（项目本地验证器/编译器框架）已经进入可构建接口，例如 `SondowProjectLocalS21Kernel` 和 `SondowProjectLocalReflectionGraftVerifier`。
- 从 semantic proof-length conventions（语义证明长度约定）到 exact split minChecked witnesses（精确拆分最小已检查码长见证）的桥接已经由 Lean 检查。
- `Month1PublicBridgeClosureTheoremLayer`（第 1 月公开桥接闭合定理层）把 concrete route（具体路线）、paper route（论文路线）、release checkpoint（发布检查点）和 public origin（公开起源）互相连接为 `<=>` 等价，并给出 CnBox target/box equation（目标/盒子方程）、code roundtrip（编码往返）和 PA finite-consistency payload equivalence（PA 有限一致性载荷等价）的公开入口。
- Month 2 Sondow accepted-certificate surface（第 2 月 Sondow 接受证书表面）已经固定 `Month2SondowAccepted n`、component certificates（组件证书）和 accepted-to-compiled compiler（接受到编译证书的编译器）。公开审计入口是 `SondowProjectMonth2CanonicalImportSurface`，其中 `accepted_eventually` 和 `compiler_consumption_after_threshold` 可用 targeted probe（定向探针）复验。
- Month 3 bounded PA assembly surface（第 3 月有界 PA 装配表面）已经把 accepted witness（接受见证）连接到 source size（源大小）、assembled size（装配大小）、`CanonicalProofCertificateAt bound n`（规范证明证书）和 `boundedPAProofPredicate bound n`（有界 PA 证明谓词），并检查 checker trace conclusion（检查器跟踪结论）就是 `finiteConsistencyFormula n`（有限一致性公式）。
- Month 4 Pudlak theorem-5 exact boundary surface（第 4 月 Pudlak 定理 5 精确边界表面）已经把 raw code（原始编码）、rescaled code（重标度编码）、power-bound code（幂界编码）、lower-bound source（下界源）和 canonical import（规范导入）组织成可审计的 `<=>` 等价链。`SondowProjectMonth3Month4CompletionAuditSurface` 把 Month 3 和 Month 4 结论合并为单一 `PublicCompletionCertificate`（公开闭合证书）。
- Month 5 gap certificate surface（第 5 月间隙证书表面）已经固定 `Month5UpperBoundFunction`（上界函数）、`Month5LowerBoundFunction`（下界函数）、threshold certificate（阈值证书）和 `ProjectComputableGapCertificate`（项目可计算间隙证书）的公开等价出口。
- Month 6 proof-length calibration surface（第 6 月证明长度校准表面）已经把 project checked-code semantics（项目已检查码语义）等价推进到 `Month6ProofCodeCheckerCalibrationFrontierCertificate`（证明码检查器校准前沿证书），公开 theorem（定理）为 `month6_project_checked_semantics_iff_checker_calibration_frontier`。

## 尚未完全内部化内容

当前剩余边界不是“整个 Sondow 侧未完成”。更精确地说，未完全内部化的是：

- Pudlak theorem 5（Pudlak 定理 5）/ Pudlak-Friedman-Buss finite-consistency proof-length lower bounds（有限一致性证明长度下界）。
- abstract `proof_length`（抽象证明长度）到 checked-code/minProofCodeSize semantics（已检查代码/最小证明码大小语义）的无条件 proof-length convention（证明长度约定）。当前已经把该边界收紧到 proof-code checker calibration frontier（证明码检查器校准前沿），但还没有从第一性原理构造 PA/Hilbert proof object（PA/Hilbert 证明对象）、checker exactness（检查器精确性）和 minProofCodeSize（最小证明码长）等价。
- `PartialConsistencyPayloadTruth` 和 `StrengthenedPartialConsistencyPayloadTruth` 对应的 payload truth（载荷真值）语义。
- 最终上界入口中的 `Nonempty SondowProjectLocalReflectionGraftVerifier` 和 Month 2 使用的 `PublicInfrastructureKit` 仍需从 lower-level checked-code S21 trace calibrations（低层已检查码 S21 跟踪校准）和 PA embedding witness（PA 嵌入见证）完全构造为无参数实例。
- Month 3/Month 4 公开闭合层不把 Pudlak theorem 5（Pudlak 定理 5）或无参数 Sondow verifier（Sondow 验证器）变成无条件定理；Month 5/Month 6 公开层把最终 gap growth domination（间隙增长支配）和 proof-length calibration frontier（证明长度校准前沿）接入同一个可审计接口，但仍保留上述外部或抽象输入。

## 公开状态

本仓库适合作为 public-alpha research artifact（公开 alpha 研究制品）引用。合适的说法是：这里给出了一个 Lean-checked conditional collision theorem（Lean 检查的条件性对撞定理）、明确的 certificate architecture（证书架构）和 axiom ledger（公理账本）。不合适的说法是：这里已经无条件证明了 Euler-Mascheroni constant（欧拉-马歇罗尼常数）的无理性。

## 许可证

代码以 Apache-2.0 发布。论文文本和文档请按引用方式署名；见 [`CITATION.cff`](CITATION.cff)。

---

# English Translation

# Sondow-Pudlak Conditional Collision Box

This repository is a Lean 4 research artifact for a conditional proof-complexity collision framework around the Euler-Mascheroni constant `gamma`.

**Current status.** This repository does not claim an unconditional proof of the irrationality of `gamma`. The current strongest endpoint is an interface-level conditional collision theorem: under explicitly listed Sondow collapse, Pudlak-Friedman-Buss lower-bound, proof-length calibration, and payload-truth inputs, the Lean composition derives:

```lean
¬ is_rational euler_mascheroni
```

The goal of this project is to make the remaining mathematical and proof-complexity obligations explicit, not to hide them behind successful compilation.

The 2026-07-04 public sync adds the Month 1 public bridge closure theorem layer.
It organizes the CnBox/Pudlak project route so that the concrete route, paper
route, release checkpoint, and public origin are connected by Lean-checked
equivalences, and it exposes the CnBox equation endpoints, the PA finite
consistency payload, the public gap instantiation, and the public collision
instantiation.

The 2026-07-05 public sync adds the Month 3/Month 4 completion audit surface.
It advances the accepted certificate to the same-object interface containing
`CanonicalProofCertificateAt bound n` and `boundedPAProofPredicate bound n`,
and it packages the Pudlak theorem-5 literature input, external boundary,
minimal field package, and canonical import as a probeable equivalence chain.

The later 2026-07-05 sync adds the Month 5/Month 6 theorem index surface. It
connects the final `U/L` gap certificate to `ProjectComputableGapCertificate`
and the public completion checklist, and tightens the proof-length
internalization boundary from ordinary checked-code replacement to
`Month6ProofCodeCheckerCalibrationFrontierCertificate`. This does not eliminate
the abstract `proof_length`; it marks the remaining boundary at the interface
between proof-code checker recognition and local proof-length code calibration.

## Priority, Citation, and Contribution Boundary

This repository records a public-alpha timestamp for the Sondow-Pudlak conditional collision box. If you use, adapt, or extend the interfaces, certificate architecture, Lean formalization route, or paper exposition in this repository, please cite this repository and the corresponding release; see [`CITATION.cff`](CITATION.cff).

The core public contributions at this stage are:

- a certificate architecture that places Sondow collapse and Pudlak-Friedman-Buss finite-consistency lower bounds on a common proof-length coordinate;
- a Lean-checked interface-level theorem deriving `¬ is_rational euler_mascheroni` under explicit inputs;
- an axiom ledger and audit boundary explaining which witnesses are machine-checked in the composition and which remain external or abstract inputs.
- a public bridge closure layer that places the CnBox equation endpoints, same-object closure, and public gap/collision endpoints behind a single probeable entry point.
- a Month 3/Month 4 public completion layer connecting the accepted Sondow object, the bounded PA proof predicate, and the Pudlak theorem-5 exact external boundary in one `PublicCompletionCertificate`.
- a Month 5/Month 6 public theorem index that exposes the computable gap certificate, growth-domination threshold, and proof-code checker calibration frontier through `#check` and `#print axioms` friendly theorem names.

Contributors may submit pull requests to internalize witnesses or improve the documentation, but this public-alpha version should not be described as an unconditional proof of the irrationality of γ. Any follow-up work based on this project should distinguish the interface/collision architecture provided here from any external witness or internal proof newly closed by later authors.

## Main Entry Points

- Paper draft, English: [`paper/paper_new_en.md`](paper/paper_new_en.md)
- Paper draft, Chinese: [`paper/paper_new_zh.md`](paper/paper_new_zh.md)
- Current status: [`STATUS.md`](STATUS.md)
- Axiom ledger: [`AXIOM_LEDGER.md`](AXIOM_LEDGER.md)
- Audit guide: [`docs/audit_guide.md`](docs/audit_guide.md)
- Main callable collision-box endpoint:

```lean
SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
```

The endpoint is defined in:

```text
integration/SondowProjectPudlakInstantiation.lean
```

- Month 1 public bridge closure entry:

```text
integration/SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface.lean
```

- Month 3/Month 4 public completion audit entry:

```text
integration/SondowProjectMonth3Month4CompletionAuditSurface.lean
```

- Month 5/Month 6 public theorem index entry:

```text
integration/SondowProjectMonth5Month6TheoremIndexSurface.lean
```

## Build

The repository is pinned to Lean `v4.31.0`.

For day-to-day audits, run lightweight probes before starting a full build:

```bash
lake exe cache get
lake env lean -o bounded_arithmetic_lab/.lake/build/lib/lean/BoundedArithmeticLab.olean bounded_arithmetic_lab/BoundedArithmeticLab.lean
lake env lean --stdin <<'EOF'
import BoundedArithmeticLab.PublicCollisionExportSurface
open BoundedArithmeticLab
#check PublicCollisionExportSurface.collision
#check PublicCollisionAPI.collision_from_checklist
EOF
```

The full build remains the heavier final check:

```bash
lake exe cache get
lake build EulerLimit.StrengthenedConsistency
lake build EulerLimit.ProjectionBridge
lake build integration.SondowProjectPudlakInstantiation
```

After these modules have been built, source-file probes such as the following are also expected to work:

```bash
lake env lean integration/SondowProjectPudlakInstantiation.lean
```

## Audit

Before citing an endpoint as fully formalized, inspect its assumptions and axiom dependencies:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#check SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
#print axioms SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

The new public bridge closure layer can be audited through:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface
open SondowMainCheckedCodeBridge.SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface

#check Month1PublicBridgeClosureTheoremLayer
#check Month1PublicBridgeClosureTheoremLayer.concrete_iff_public_origin
#check Month1PublicBridgeClosureTheoremLayer.target_eq_box_formula
#check Month1PublicBridgeClosureTheoremLayer.carries_iff_pa_finite_consistency
#check Month1PublicBridgeClosureTheoremLayer.public_gap_instantiation
EOF
```

The Month 3/Month 4 public completion layer can be audited through:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth3Month4CompletionAuditSurface
open SondowMainCheckedCodeBridge.SondowProjectMonth3Month4CompletionAuditSurface

#check PublicCompletionCertificate
#check paper_route_and_accepted_iff_public_completion
#check exactFamily_checklist_and_accepted_iff_public_completion
#check public_completion_to_month3_bounded_pa_interface
#check public_completion_to_month4_full_boundary_interface
#check public_completion_to_public_gap_instantiation
#check public_completion_not_main_rationality
EOF
```

The Month 5/Month 6 public gap and calibration frontier can be audited through:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth5Month6TheoremIndexSurface
open SondowMainCheckedCodeBridge.SondowProjectMonth5Month6TheoremIndexSurface

#check public_statement_iff_public_completion_computable_gap_checker_calibration_frontier
#check month6_project_checked_semantics_iff_checker_calibration_frontier
#check month6_proof_code_checker_frontier_iff_checker_calibration_frontier
#print axioms public_statement_iff_public_completion_computable_gap_checker_calibration_frontier
EOF
```

The current core external or abstract inputs are listed in [`AXIOM_LEDGER.md`](AXIOM_LEDGER.md). The latest local audit reports the following main dependencies:

```text
literaturePudlakTheorem5ExternalRescaledLowerBound
literaturePudlakTheorem5ExternalScaleData
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

It also depends on standard Lean/Mathlib principles such as `propext`, `Classical.choice`, and `Quot.sound`.

## What Is Formalized

- Formula families are organized through `FormulaCode`.
- The common proof system is fixed as `ProofSystem.PA`.
- The proof-length measure is fixed as `ProofLengthMeasure.symbolSize`.
- The collision-box endpoint is callable and returns the intended conclusion `¬ is_rational euler_mascheroni` under explicit inputs.
- The Sondow analytic side has a Lean-closed reproof route, including the product-log identity, decomposition, tail estimates, and the Sondow forward package.
- The project-local verifier/compiler framework is present in buildable interfaces such as `SondowProjectLocalS21Kernel` and `SondowProjectLocalReflectionGraftVerifier`.
- The bridge from semantic proof-length conventions to exact split minChecked witnesses is machine checked.
- `Month1PublicBridgeClosureTheoremLayer` connects the concrete route, paper route, release checkpoint, and public origin by equivalences, and exposes public entries for the CnBox target/box equation, code roundtrip, and PA finite-consistency payload equivalence.
- The Month 2 Sondow accepted-certificate surface fixes `Month2SondowAccepted n`, the component certificates, and the accepted-to-compiled compiler. The public audit entry is `SondowProjectMonth2CanonicalImportSurface`, whose `accepted_eventually` and `compiler_consumption_after_threshold` endpoints can be checked with targeted probes.
- The Month 3 bounded PA assembly surface connects an accepted witness to source size, assembled size, `CanonicalProofCertificateAt bound n`, and `boundedPAProofPredicate bound n`, and checks that the checker-trace conclusion is exactly `finiteConsistencyFormula n`.
- The Month 4 Pudlak theorem-5 exact boundary surface organizes raw code, rescaled code, power-bound code, the lower-bound source, and the canonical import into an auditable equivalence chain. `SondowProjectMonth3Month4CompletionAuditSurface` combines the Month 3 and Month 4 conclusions into one `PublicCompletionCertificate`.
- The Month 5 gap certificate surface fixes `Month5UpperBoundFunction`, `Month5LowerBoundFunction`, the threshold certificate, and the public equivalence endpoint for `ProjectComputableGapCertificate`.
- The Month 6 proof-length calibration surface advances project checked-code semantics to `Month6ProofCodeCheckerCalibrationFrontierCertificate`; the public theorem name is `month6_project_checked_semantics_iff_checker_calibration_frontier`.

## What Is Not Yet Fully Internalized

The remaining boundary is not that the whole Sondow side is unfinished. More precisely, the pieces not yet fully internalized are:

- Pudlak theorem 5 / Pudlak-Friedman-Buss finite-consistency proof-length lower bounds.
- The unconditional proof-length convention identifying the abstract `proof_length` with checked-code/minProofCodeSize semantics. This boundary has now been tightened to the proof-code checker calibration frontier, but PA/Hilbert proof objects, checker exactness, and minProofCodeSize equivalence have not yet been constructed from first principles.
- The payload-truth semantics represented by `PartialConsistencyPayloadTruth` and `StrengthenedPartialConsistencyPayloadTruth`.
- The final upper-side input `Nonempty SondowProjectLocalReflectionGraftVerifier` and the `PublicInfrastructureKit` used by the Month 2 surface, which still need to be constructed parameter-free from lower-level checked-code S21 trace calibrations and a PA embedding witness.
- The Month 3/Month 4 public completion layer does not turn Pudlak theorem 5 or the parameter-free Sondow verifier into unconditional theorems. The Month 5/Month 6 public layer connects final gap growth domination and the proof-length calibration frontier behind one auditable interface, while keeping the external or abstract inputs visible.

## Public Status

This repository is suitable as a public-alpha research artifact. The appropriate claim is that it provides a Lean-checked conditional collision theorem, an explicit certificate architecture, and an axiom ledger. The inappropriate claim is that it already proves the irrationality of the Euler-Mascheroni constant unconditionally.

## License

Code is released under Apache-2.0. Paper text and documentation should be cited with attribution; see [`CITATION.cff`](CITATION.cff).
