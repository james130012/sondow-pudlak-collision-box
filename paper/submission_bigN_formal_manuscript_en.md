# A Clean Lean-Checked Collision Threshold in a Sondow-Pudlak Program

## Abstract

We present a Lean 4 checked collision theorem in a Sondow-Pudlak
proof-complexity program for the Euler-Mascheroni constant. The theorem is
conditional on a clean checker input and a clean measured upper provider. Under
these inputs, the rationality branch computes an explicit collision threshold

```lean
N = max upperN threshold
```

where `upperN` is the upper-tail cutoff and `threshold` is the tail-gap
threshold for the same checked route. Lean then proves the contradiction on the
rationality branch, yielding `¬ is_rational euler_mascheroni` relative to the
clean input package. The audited axiom profile of the submission theorem is
`[propext, Classical.choice, Quot.sound]`; it does not contain
`partial_consistency_payload`, `proof_length`, or
`strengthened_partial_consistency_payload`. Formula-level half-denominator and
decimal numerical refinements are deliberately left for later work.

## 1. Introduction

Let

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac{1}{k}-\log n\right)
```

be the Euler-Mascheroni constant. Its irrationality remains open. The present
paper does not claim an unconditional proof of irrationality. It reports a
machine-checked clean collision theorem: once the upper side and the lower
tail-gap side are supplied in the same proof-length-free checker coordinate,
Lean computes the rational-branch collision number and derives the contradiction.

The point of the result is not a large decimal value of `N`. The point is that
`N` is defined by the formal route itself:

```lean
N = max upperN threshold
```

and that the theorem carrying this statement has no dependence on the old
project-level residual constants that previously weakened the formula-level
presentation.

## 2. Formal Artifact

The audited release is:

```text
bigN-halfden-full-20260708
commit 2a7458c253aae4050a0a3a18424abea952d26bc3
```

Release URL:

```text
https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-halfden-full-20260708
```

The clean submission route is isolated in:

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

The main theorem is:

```lean
cleanUpperProvider_submissionRoute
```

It depends on the proof-length-axiom-free checker endpoint developed in:

```text
integration/SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint.lean
```

## 3. Main Theorem

In Lean, the theorem has the following shape:

```lean
theorem cleanUpperProvider_submissionRoute
    (input : ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (upper_provider :
      input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    (∀ hrat : is_rational euler_mascheroni,
      computedCollisionNOfRationality hrat =
        max upperN threshold) ∧
      ¬ is_rational euler_mascheroni
```

The displayed statement suppresses namespace and projection detail. The exact
Lean theorem expands `upperN` as the cutoff returned by
`checkedSearchUpperTail` and expands `threshold` as the threshold returned by
`input.tail_gap.gap_for_polynomial_upper` for the same clean upper tail.

Thus the theorem does two things at once:

1. It identifies the rational-branch computed collision number with
   `max upperN threshold`.
2. It proves that the rational branch is impossible under the same clean input
   package.

This is the correct theorem to use as the current manuscript's central result.

## 4. Why The Old Formula Route Is Not The Main Result

The release also contains older half-denominator formula work involving the
visible expression

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

Those endpoints are mathematically useful, but their current Lean axiom profile
still contains the project-level residual constants:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

For that reason they are not used as the main submission theorem. Presenting
them as the main result would make the paper less credible, not more. The clean
paper therefore takes the proof-level/collision-level theorem as primary and
treats formula-level and numerical refinements as later work.

The file also contains a clean downstream half-denominator interface:

```lean
cleanHalfDenUpperProvider_submissionRoute
```

This theorem is clean, but it requires a clean upstream half-denominator upper
provider. The existing old formula endpoints do not yet supply that provider
without the project-level residual constants.

## 5. Axiom Audit

The main audit commands are:

```bash
lake build integration.SondowProjectBigNCleanSubmissionRoute
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNCleanSubmissionRoute
open SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute

#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#print axioms cleanUpperProvider_submissionRoute
#print axioms cleanComputedBigN_eq_tailGapMax
#print axioms cleanProvider_not_rational
EOF
```

Observed axiom output:

```text
[propext, Classical.choice, Quot.sound]
```

No project-level residual constant appears in the clean route.

## 6. Reproducibility

The clean route can be reproduced with:

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

The detailed audit report is:

```text
docs/clean_submission_route_audit_20260708_zh.md
```

## 7. Scope Of The Claim

What is proved:

1. A clean Lean-checked collision route.
2. A formal rational-branch collision number
   `N = max upperN threshold`.
3. A contradiction on the rationality branch under the same clean input package.
4. A clean axiom profile excluding the three project-level residual constants.

What is not claimed:

1. An unconditional proof of the irrationality of `gamma`.
2. A decimal extraction of `N`.
3. A completed clean upstream proof of the half-denominator formula-level
   cutoff.

This is the version that maximizes the credibility of the current manuscript:
the theorem is clean, the collision number is explicit at the correct formal
level, and the remaining formula-level refinements are stated as future work.
