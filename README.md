# Sondow-Pudlak 条件性对撞盒

本仓库是一个 Lean 4 研究制品，用于组织围绕 Euler-Mascheroni constant（欧拉-马歇罗尼常数）`gamma` 的 conditional proof-complexity collision framework（条件性证明复杂度对撞框架）。

**当前状态。** 本仓库不声称已经给出 `gamma` irrationality（欧拉常数无理性）的 unconditional proof（无条件证明）。当前最强出口是一个 interface-level conditional collision theorem（接口级条件性对撞定理）：在明确列出的 Sondow collapse（Sondow 坍缩）、Pudlak-Friedman-Buss lower bound（Pudlak-Friedman-Buss 下界）、proof-length calibration（证明长度校准）和 payload truth（载荷真值）输入被提供时，Lean 组合链推出：

```lean
¬ is_rational euler_mascheroni
```

本项目的目标是把剩余 mathematical obligations（数学义务）和 proof-complexity obligations（证明复杂度义务）显式化，而不是把它们藏在成功编译背后。

## 优先权、引用与贡献边界

本仓库记录的是 Sondow-Pudlak conditional collision box（Sondow-Pudlak 条件性对撞盒）的 public-alpha timestamp（公开 alpha 时间戳）。如果你使用、改写或继续推进这里的接口、证书结构、Lean 形式化路线或论文表述，请引用本仓库和对应 release（版本发布）；引用信息见 [`CITATION.cff`](CITATION.cff)。

当前已公开的核心贡献包括：

- 一个把 Sondow collapse（Sondow 坍缩）与 Pudlak-Friedman-Buss finite-consistency lower bound（有限一致性下界）放入共同 proof-length coordinate（证明长度坐标）的 certificate architecture（证书架构）；
- 一个 Lean-checked interface-level theorem（Lean 检查的接口级定理），在显式输入下推出 `¬ is_rational euler_mascheroni`；
- 一个明确的 axiom ledger（公理账本）和 audit boundary（审计边界），说明哪些 witness（见证）已经机器检查组合，哪些仍是 external/abstract inputs（外部/抽象输入）。

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

## 尚未完全内部化内容

当前剩余边界不是“整个 Sondow 侧未完成”。更精确地说，未完全内部化的是：

- Pudlak theorem 5（Pudlak 定理 5）/ Pudlak-Friedman-Buss finite-consistency proof-length lower bounds（有限一致性证明长度下界）。
- abstract `proof_length`（抽象证明长度）到 checked-code/minProofCodeSize semantics（已检查代码/最小证明码大小语义）的无条件 proof-length convention（证明长度约定）。
- `PartialConsistencyPayloadTruth` 和 `StrengthenedPartialConsistencyPayloadTruth` 对应的 payload truth（载荷真值）语义。
- 最终上界入口中的 `Nonempty SondowProjectLocalReflectionGraftVerifier` 仍需从 lower-level checked-code S21 trace calibrations（低层已检查码 S21 跟踪校准）和 PA embedding witness（PA 嵌入见证）完全构造为无参数实例。

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

## Priority, Citation, and Contribution Boundary

This repository records a public-alpha timestamp for the Sondow-Pudlak conditional collision box. If you use, adapt, or extend the interfaces, certificate architecture, Lean formalization route, or paper exposition in this repository, please cite this repository and the corresponding release; see [`CITATION.cff`](CITATION.cff).

The core public contributions at this stage are:

- a certificate architecture that places Sondow collapse and Pudlak-Friedman-Buss finite-consistency lower bounds on a common proof-length coordinate;
- a Lean-checked interface-level theorem deriving `¬ is_rational euler_mascheroni` under explicit inputs;
- an axiom ledger and audit boundary explaining which witnesses are machine-checked in the composition and which remain external or abstract inputs.

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

## What Is Not Yet Fully Internalized

The remaining boundary is not that the whole Sondow side is unfinished. More precisely, the pieces not yet fully internalized are:

- Pudlak theorem 5 / Pudlak-Friedman-Buss finite-consistency proof-length lower bounds.
- The unconditional proof-length convention identifying the abstract `proof_length` with checked-code/minProofCodeSize semantics.
- The payload-truth semantics represented by `PartialConsistencyPayloadTruth` and `StrengthenedPartialConsistencyPayloadTruth`.
- The final upper-side input `Nonempty SondowProjectLocalReflectionGraftVerifier`, which still needs to be constructed parameter-free from lower-level checked-code S21 trace calibrations and a PA embedding witness.

## Public Status

This repository is suitable as a public-alpha research artifact. The appropriate claim is that it provides a Lean-checked conditional collision theorem, an explicit certificate architecture, and an axiom ledger. The inappropriate claim is that it already proves the irrationality of the Euler-Mascheroni constant unconditionally.

## License

Code is released under Apache-2.0. Paper text and documentation should be cited with attribution; see [`CITATION.cff`](CITATION.cff).
