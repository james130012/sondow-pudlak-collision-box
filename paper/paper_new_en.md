# An Existential Sondow-Pudlak Threshold Verified in Lean 4

James^1,*

^1 Independent researcher.

*Correspondence: through the public repository issue tracker unless a journal
submission address is supplied.

## Abstract

The irrationality of the Euler-Mascheroni constant remains open.  This paper
does not claim to settle that problem.  It isolates and verifies, in Lean 4, a
specific proof-complexity threshold theorem arising in the Sondow-Pudlak route.
Under explicit S21 proof-length recognition data, verifier traces for the
Sondow and partial-consistency families, a rational-branch Sondow parameter,
partial-consistency truth, source-minChecked calibration, and the
Buss-Pudlak time-constructible rescaling theorem, Lean proves that the final
project-length endpoint returns a natural number `N` and that the same `N`
satisfies the required source-side strict gap.  The finite Sondow prefix is
also identified with a MiniHilbert `minProofCodeSize` prefix, and a companion
handoff theorem identifies the later numerical route as
`max upper.upperN (thresholdOf upper.U upper.polynomial)`.  The result is an
existential formal theorem about the large threshold.  It is not a printed
decimal value of `N`, and it is not an unconditional proof that
`gamma` is irrational.

## 1. Introduction

Let

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right)
```

be the Euler-Mascheroni constant.  Sondow's criterion gives a way of
turning the rationality hypothesis for `gamma` into structured arithmetic
certificates.  The Pudlak-Friedman-Buss proof-complexity line gives lower
bounds for finite consistency statements.  A Sondow-Pudlak collision argument
can be meaningful only after both sides have been placed in one proof-length
coordinate, with the same measured proof objects, the same proof-code
semantics, and the same finite-prefix conventions.

The contribution of the present artifact is a machine-checked endpoint in this
coordinate problem.  The large `N` formula is no longer a planning statement:
the release checked here contains a Lean theorem proving the existence of the
threshold and the strict inequality at that threshold.  The theorem is
conditional in the standard mathematical sense that it is quantified over
explicit input packages.  These packages are part of the statement, not hidden
claims of unconditional availability.

The boundary is essential.  The paper proves an existential theorem for the
large threshold in the current formal route.  It does not extract a decimal
natural number.  It does not remove every residual proof-complexity input in
the wider project.  It does not prove the irrationality of `gamma`.

## 2. Formal Coordinate

The main source file is

```text
integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

The release studied in this draft is

```text
bigN-nature-paper-20260708
```

at commit

```text
c26cd1d2b3abbc6c3584ab5c2afbd1e953d3cacd
```

Let

```lean
h := hrec.toLocalProofCodeSemanticsPackage.toCanonicalCalibrationPackage
```

be the canonical calibration package obtained from an
`S21GraftProofLengthRecognitionTheorem`.  The measured source function in the
main theorem is

```lean
sourceLength m :=
  ((h.sondow_proofs.conjIntro h.partial_proofs)
    |>.rightConjElim
    |>.minCheckedCodeSize m)
```

Thus the lower side is not an arbitrary numerical function.  It is the
MiniHilbert checked-code measurement obtained after conjunction introduction
and right-conjunction elimination on the Sondow and partial-consistency proof
families.

For a rational-branch parameter

```lean
rat : MainSondowRationalParameter
```

the half-denominator tail threshold is

```lean
sondowThreshold := max 3 ((rat.q.den + 1) / 2)
```

and the finite Sondow prefix coefficient is

```lean
sondowPrefixCoeff :=
  natPrefixMax h.sondow_proofs.length sondowThreshold
```

The generated target upper coefficient in the endpoint is

```lean
max 17 sondowPrefixCoeff + 8
```

with degree `1`.  This is the coefficient that appears in the source-side
strict gap.

## 3. Main Theorem

The formal theorem used as the main endpoint is

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

It has the following mathematical content.

**Theorem 1 (source-calibrated existential big-N endpoint).**  Fix internal
Pudlak scale data.  Assume:

1. an `S21GraftProofLengthRecognitionTheorem`;
2. verifier-trace soundness for `sondowCertificateValidCode`;
3. verifier-trace soundness for `partialConsistencyCode`;
4. a rational-branch parameter `rat : MainSondowRationalParameter`;
5. `PartialConsistencyAcceptedTruth`;
6. strict monotonicity of the time-constructible bound;
7. nonzero Pudlak exponent;
8. a `MiniHilbert.PartialConsistencySourceMinCheckedCalibration` for the
   conjunction proof family;
9. `BussPudlakTimeConstructibleRescalingTheorem`.

Then, with `sourceLength`, `sondowThreshold`, and `sondowPrefixCoeff` as above,
the final project-length search endpoint returns a natural number `N` such
that

```lean
∃ N : Nat,
  endpointN = N ∧
  N =
    semanticStrongNatLowerBoundClassicalMonomialSearchWitness
      sourceLength hsource (max 17 sondowPrefixCoeff + 8) 1 0 ∧
  (max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

where `hsource : SemanticStrongNatLowerBound sourceLength` is not a separate
input.  It is derived inside the theorem from the source-minChecked
calibration and the Buss-Pudlak rescaling theorem.

The theorem is existential and noncomputable at this stage: the witness is the
classical object

```lean
semanticStrongNatLowerBoundClassicalMonomialSearchWitness
```

This suffices for the formal `∃ N : Nat` theorem and for the strict inequality
at `N`.  It does not provide an executable decimal expansion of `N`.

## 4. Proof Architecture

The Lean proof decomposes the endpoint into four audited components.

**Sondow tail.**  From the rational-branch parameter, the reproof Sondow tail
is accepted from

```lean
max 3 ((rat.q.den + 1) / 2)
```

onward.  The corresponding constructor is

```lean
mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
```

**Finite prefix.**  The remaining prefix is not ignored.  It is measured by
`natPrefixMax` and then contributes to the linear upper coefficient
`max 17 sondowPrefixCoeff + 8`.

**MiniHilbert rewrite.**  The finite prefix is identified with genuine
MiniHilbert proof-code semantics by

```lean
S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
```

where

```lean
s21SondowMiniHilbertMinProofCodeSizePrefixMax hrec threshold
```

is the prefix maximum of `minProofCodeSize` over the Sondow certificate-valid
codes generated by the recognition theorem.

**Source lower bound.**  The theorem does not assume a naked
`SemanticStrongNatLowerBound`.  It builds that lower bound from

```lean
PartialConsistencySourceMinCheckedCalibration
BussPudlakTimeConstructibleRescalingTheorem
```

and then applies the semantic-strong search witness theorem to the generated
linear monomial.

Together these components prove that the endpoint and the source lower-bound
witness name the same natural number, and that the generated linear monomial
is strictly below `sourceLength` at that number.

## 5. The Half-Denominator Boundary

The half-denominator threshold is a genuine improvement over a full-denominator
tail, but it leaves a real finite-prefix boundary.  The project proves the
obstruction

```lean
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

which says that the checked-prefix premise below

```lean
max 3 ((rat.q.den + 1) / 2)
```

is not automatic from the rational parameter and the current accepted-code
semantics.  In particular, the prefix contains index `0`, while no
rational-parameter full Sondow certificate is accepted there because the
denominator is positive.

This obstruction is part of the mathematical statement.  Removing it from the
paper would change the theorem from a checked result into an unproved stronger
claim.

## 6. Numerical Handoff

The companion numerical handoff theorem is in

```text
integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

and is named

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

It proves that, once a tail-gap threshold function satisfies

```lean
(proof_length_tail_gap.gap_for_polynomial_upper U hU).threshold =
  thresholdOf U hU
```

the final computed collision index in the C-line root route is

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

This is the correct entry point for a later printed natural number.  A decimal
`N` requires an actual computation of `thresholdOf upper.U upper.polynomial`,
or an equivalent executable witness.  Adding another prose-level endpoint
would not solve the numerical problem.

## 7. Claims and Non-Claims

| Statement | Status | Lean evidence |
| --- | --- | --- |
| Existence of `N : Nat` for the source-calibrated endpoint | Proved | `projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax` |
| Strict source-side gap at the same `N` | Proved | same theorem |
| Derivation of `SemanticStrongNatLowerBound` from source-minChecked calibration and Buss-Pudlak rescaling | Proved inside the main theorem | same theorem |
| Sondow finite prefix rewritten to MiniHilbert `minProofCodeSize` | Proved | `S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax` |
| Half-denominator checked-prefix premise is automatic | False in the current semantics | `not_sondowCheckedHalfDenPrefix_of_rationalParameter` |
| C-line numerical endpoint reduced to `max upper.upperN (thresholdOf ...)` | Proved | `finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf` |
| Decimal value of `N` | Not completed | needs executable `thresholdOf` or witness extraction |
| Unconditional irrationality of `gamma` | Not claimed | outside the theorem |

## 8. Reproducibility and Audit Protocol

The repository pins Lean and Mathlib as follows:

```text
leanprover/lean4:v4.31.0
mathlib v4.31.0
```

A clean reproduction from the public release is:

```bash
git clone https://github.com/james130012/sondow-pudlak-collision-box.git
cd sondow-pudlak-collision-box
git checkout bigN-nature-paper-20260708
lake exe cache get
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

Reviewers who want targeted theorem probes should first build the corresponding
modules so that the `.olean` files are available to `lake env lean --stdin`:

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
lake build integration.SondowProjectMonth11Month12HardResidualElimination
```

They can then run:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

#check projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
#check S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
#check not_sondowCheckedHalfDenPrefix_of_rationalParameter
EOF
```

and:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth11Month12HardResidualElimination

open SondowMainCheckedCodeBridge.SondowProjectMonth11Month12HardResidualElimination

#check finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
EOF
```

The paper source should also pass:

```bash
git diff --check
```

The wider project contains older conditional collision endpoints whose axiom
boundary is documented in `AXIOM_LEDGER.md`.  The main theorem of this paper is
more specific: it removes the abstract `SemanticStrongNatLowerBound` premise
from the publishable big-`N` endpoint, but it still depends on the explicit
recognition, verifier-trace, rational-branch, partial-truth, calibration, and
rescaling inputs listed in Theorem 1.

## 9. Data and Code Availability

No empirical datasets are used.  The mathematical artifact consists of the
Lean source tree, the pinned Lake configuration, and the paper sources in this
repository.

The code is available at:

```text
https://github.com/james130012/sondow-pudlak-collision-box
```

The release audited by this draft is:

```text
https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-nature-paper-20260708
```

For journal submission, the accepted commit and generated paper artifacts
should be archived in a DOI-minting repository.  The GitHub release is suitable
for public audit, but it is not a permanent archival substitute.

## 10. References

1. Sondow, J. Criteria for irrationality of Euler's constant. *Proceedings of
   the American Mathematical Society* **131**, 3335-3344 (2003).
2. Buss, S. R. On Godel's theorems on lengths of proofs I: number of lines and
   speedup for arithmetics. *Journal of Symbolic Logic* **59**, 737-756 (1994).
3. Pudlak, P. On the lengths of proofs of finitistic consistency statements in
   first order theories. In *Logic Colloquium 1984* (1986).
4. Pudlak, P. Improved bounds to the lengths of proofs of finitistic
   consistency statements. In *Logic and Combinatorics* (1987).
5. Krajicek, J. and Pudlak, P. The number of proof lines and the size of proofs
   in first-order logic. *Archive for Mathematical Logic* (1988).
6. de Moura, L. and Ullrich, S. The Lean 4 theorem prover and programming
   language. In *Automated Deduction - CADE 28* (2021).

## 11. Declarations

No external funding is declared in this draft.  The author declares no
competing interests.  AI-assisted editing was used to reorganize the
manuscript; all mathematical claims in the paper are tied to the Lean source
files and theorem names listed above.
