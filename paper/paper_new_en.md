# A Lean-Checked Existential Threshold for Sondow-Pudlak Proof Lengths

James^1,*

^1 Independent researcher.
*Correspondence: through the public repository issue tracker unless a journal
submission address is supplied.

## Summary

The irrationality of the Euler-Mascheroni constant remains open. Sondow's criterion converts the rationality hypothesis into a family of checkable arithmetic certificates, while the Pudlak-Friedman-Buss line gives proof-length lower bounds for finite consistency statements. We report a Lean 4 checked Sondow-Pudlak proof-length artifact: from explicit S21 proof-length recognition data, Sondow and partial verifier traces, the half-denominator Sondow tail, partial-consistency truth, source-minChecked calibration, and Buss-Pudlak rescaling, Lean proves that the final project-length endpoint returns a natural-number threshold `N` and that the required source-side strict gap holds at that same `N`. This is not an unconditional proof of the irrationality of Euler's constant, and it is not a decimal extraction of `N`; it is a reproducible formal certificate for the existence of the large threshold required by the current route.

## Main Text

### Problem

The Euler-Mascheroni constant is

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

The purpose of the project is not to assert a solution to this open problem in prose. It is to place the Sondow certificate upper side and the Pudlak proof-length lower side in one formal measurement coordinate. The result reported here is an intermediate but substantive formal endpoint: in the current source-calibrated proof-length route, a final threshold `N` exists.

The boundary of the claim is as follows.

1. Proved: given the root inputs listed in this paper, Lean constructs `N : Nat` and proves the target inequality.
2. Not proved: a fully expanded decimal natural number `N = ...`.
3. Not claimed: an unconditional theorem `¬ is_rational euler_mascheroni`.

This distinction is central to the audit. An existential threshold theorem can be a serious machine-checked result, but it must not be repackaged as numeric extraction or as a final irrationality proof.

### Formal Result

The main formal entry point is in

```text
integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

The theorem is

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

Its audited conclusion has the following shape:

```lean
∃ N : Nat,
  endpointN = N ∧
  N =
    semanticStrongNatLowerBoundClassicalMonomialSearchWitness
      sourceLength hsource (max 17 sondowPrefixCoeff + 8) 1 0 ∧
  (max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

Here `sourceLength` is not arbitrary. It is the checker measurement obtained from conjunction introduction followed by right-conjunction elimination on the Sondow and partial-consistency proof families:

```lean
sourceLength m :=
  ((h.sondow_proofs.conjIntro h.partial_proofs)
    |>.rightConjElim
    |>.minCheckedCodeSize m)
```

Likewise, `sondowPrefixCoeff` is not a supplied constant. It is the maximum of a real finite prefix:

```lean
sondowThreshold := max 3 ((rat.q.den + 1) / 2)
sondowPrefixCoeff := natPrefixMax h.sondow_proofs.length sondowThreshold
```

Thus the Lean theorem proves an existential threshold with a traceable origin: the endpoint returns the same `N` as the lower-bound witness, and the strict lower-bound inequality holds at that point.

### Root Inputs

The construction starts from two root inputs.

The first root is the S21/Sondow proof-length recognition side, represented by

```lean
S21GraftProofLengthRecognitionTheorem
```

and transported through `toLocalProofCodeSemanticsPackage` and `toCanonicalCalibrationPackage`. The current bridge rewrites the finite-prefix maximum into MiniHilbert proof-code semantics:

```lean
s21SondowMiniHilbertMinProofCodeSizePrefixMax

S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
```

This step matters because it moves the residual finite prefix from an abstract proof-family length field to `minProofCodeSize`. It does not compute the final decimal value, but it moves the numeric task onto genuine proof-code semantics.

The second root is the earlier proof-length tail-gap model. The numerical entry point for the final C-line root route is in

```text
integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

The theorem is

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

It reduces the final computed collision index to

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

This is the true entry point for the later decimal `N`: one must construct and evaluate `thresholdOf`, not add another outer interface.

### Claim Boundary

Table 1 gives the audited boundary of the manuscript.

| Item | Status | Machine-checked entry |
| --- | --- | --- |
| Existence of `N : Nat` | Proved | `projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax` |
| Source-side strict gap at `N` | Proved | same theorem |
| Sondow finite prefix rewritten to MiniHilbert `minProofCodeSize` | Proved | `S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax` |
| Tail-gap numerical entry reduced to `max upper.upperN (thresholdOf ...)` | Proved | `finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf` |
| Printed decimal value of `N` | Not completed | requires computable `thresholdOf` or executable witness |
| Unconditional irrationality of `gamma` | Not claimed | outside this manuscript's conclusion |

### Half-Denominator Residual

The half-denominator Sondow tail gives the threshold

```lean
max 3 ((rat.q.den + 1) / 2)
```

Under stronger checked-prefix hypotheses, the corresponding endpoint can be reduced further to

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

However, `rat.q.den` belongs to the rationality branch. It cannot be discarded as a known external constant without additional construction. The project also proves the finite-prefix obstruction

```lean
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

showing that the checked-prefix premise is not automatic from the rational parameter. This obstruction is part of the theorem boundary; hiding it as "obvious" would change the result.

### Reproducibility

The artifact fixes Lean and Mathlib versions:

```text
leanprover/lean4:v4.31.0
mathlib v4.31.0
```

The minimum reproduction sequence is:

```bash
git clone https://github.com/james130012/sondow-pudlak-collision-box.git
cd sondow-pudlak-collision-box
git checkout codex/month9-10-internal-lower-machine-continuation
lake exe cache get
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

The older public collision endpoint can be checked with a lightweight probe:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#check SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

The new Month 11/12 theorems are primarily reproduced by source-file type checking. Reviewers who need to print their theorem types through `#check` should first build the two modules:

```bash
lake build integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
lake build integration.SondowProjectMonth11Month12HardResidualElimination
```

and then import the corresponding modules through `lake env lean --stdin`. A full module build replays a large integration dependency chain and is significantly slower than direct source-file checking.

### Why the Decimal N is Still Open

The existential result uses a Prop-level strong lower bound:

```lean
SemanticStrongNatLowerBound
```

Lean obtains a witness through

```lean
semanticStrongNatLowerBoundClassicalMonomialSearchWitness
```

This is enough to prove `∃ N : Nat`, but it is not an executable search procedure. To print a natural number, the development must supply one of the following:

1. a computable `thresholdOf upper.U upper.polynomial` and a proof that it equals the tail-gap threshold; or
2. an executable rejection extractor with genuine `extractor.witness` and `extractor.cutoff`.

The contribution of this manuscript is to close the existential threshold and to reduce the numeric route to these two genuine computational entry points.

## References

1. Sondow, J. Criteria for irrationality of Euler's constant. *Proceedings of the American Mathematical Society* **131**, 3335-3344 (2003).
2. Buss, S. R. On Godel's theorems on lengths of proofs I: number of lines and speedup for arithmetics. *Journal of Symbolic Logic* **59**, 737-756 (1994).
3. Pudlak, P. On the lengths of proofs of finitistic consistency statements in first order theories. In *Logic Colloquium 1984* (1986).
4. Pudlak, P. Improved bounds to the lengths of proofs of finitistic consistency statements. In *Logic and Combinatorics* (1987).
5. Krajicek, J. & Pudlak, P. The number of proof lines and the size of proofs in first-order logic. *Archive for Mathematical Logic* (1988).
6. de Moura, L. & Ullrich, S. The Lean 4 theorem prover and programming language. *Automated Deduction - CADE 28* (2021).

## Methods

### Formal Environment

All formal claims are checked in Lean 4 using the repository-pinned toolchain:

```text
leanprover/lean4:v4.31.0
```

The Lake package is `euler_limit`; Mathlib is pinned at revision `v4.31.0` in `lakefile.toml`.

### Verification Protocol

The primary verification protocol is Lean source-file elaboration:

```bash
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

The first command checks the existential big-`N` endpoint and the MiniHilbert prefix bridges. The second checks the tail-gap `thresholdOf` handoff theorem.

Patch-integrity and whitespace checks are run with:

```bash
git diff --check
```

### Axiom and Assumption Audit

The manuscript separates formal composition from remaining mathematical inputs. The older public collision endpoint still depends on explicitly listed external or abstract inputs, including literature Pudlak lower-bound content, payload truth, and root `proof_length`. These dependencies are documented in `AXIOM_LEDGER.md`.

The existential big-`N` theorem removes the abstract `SemanticStrongNatLowerBound` premise from the publishable endpoint by deriving it from:

```lean
PartialConsistencySourceMinCheckedCalibration
BussPudlakTimeConstructibleRescalingTheorem
```

It does not remove all global project assumptions. In particular, the recognition theorem and verifier traces remain explicit inputs.

### AI-Assisted Manuscript Preparation

AI-assisted editing was used to reorganize the manuscript and prepare reproducibility instructions. The mathematical and formal claims reported here are tied to Lean source files and are checked by the commands above; no AI-generated mathematical assertion is used as a substitute for a Lean theorem.

## Data Availability

No empirical datasets were generated or analysed. The minimum material needed to verify the claims is the Lean source tree, the pinned Lake configuration, and the paper source files in this repository.

## Code Availability

The source code is available at:

```text
https://github.com/james130012/sondow-pudlak-collision-box
```

The current audit branch is:

```text
codex/month9-10-internal-lower-machine-continuation
```

For journal submission, the exact accepted commit should be archived in a DOI-minting repository such as Zenodo or Code Ocean, and this section should be updated with the DOI. A GitHub branch or tag is sufficient for immediate public audit, but it is not a substitute for a permanent journal archive.

## Acknowledgements

No external funding is declared in this draft.

## Author Contributions

J. designed the formal route, implemented the Lean development, prepared the manuscript, and is responsible for the repository release unless additional contributors are added before submission.

## Competing Interests

The author declares no competing interests in this draft.

## Additional Information

Correspondence and requests for materials should be directed through the public repository until a journal submission address is supplied. Supplementary information should include the exact release tag, commit hash, `#print axioms` transcript, and generated PDF/HTML audit artifacts for the submitted version.
