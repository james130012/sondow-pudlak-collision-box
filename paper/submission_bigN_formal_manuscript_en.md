# A Formal Collision Theorem for Euler's Constant in the Sondow-Pudlak Program

## Abstract

We prove a Lean 4 formalized collision theorem for Euler's constant in a
Sondow-Pudlak proof-complexity program. In a fixed proof-checker measurement
coordinate, if the same measured function is equipped with a formal polynomial
upper provider, then the rationality branch computes a collision number equal
to the maximum of the upper-tail cutoff and the tail-gap threshold. At that
same natural number, Lean derives incompatible inequalities from the upper-tail
certificate and the strict tail-gap certificate. Consequently, relative to this
formal input package, Lean proves `¬ is_rational euler_mascheroni`. The main
theorem is `cleanUpperProvider_submissionRoute`; its source and audit record
are publicly reproducible.

Keywords: Euler-Mascheroni constant; Sondow criterion; Pudlak lower bounds;
proof complexity; formalized mathematics; Lean.

## 1. Introduction

Let

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac{1}{k}-\log n\right)
```

be Euler's constant. Its irrationality is a classical open problem. Sondow's
criterion transforms the rationality hypothesis for `γ` into arithmetic
certificates, while finite-consistency lower bounds in proof complexity impose
constraints from the other side. A collision argument asks that these two
pieces be placed in one proof-code measurement coordinate, so that an upper
estimate and a strict lower estimate can be compared at a single natural
number.

This paper formalizes the collision core of that program. We fix one checker
measurement coordinate in Lean. Given an upper provider for the same measured
function, Lean computes the collision number in the rationality branch and
proves that the upper-tail certificate and the strict tail-gap certificate
apply at the same point.

More precisely, let `input` be the checker-side input and let `upper_provider`
be an upper provider in the same coordinate. For

```lean
h : is_rational euler_mascheroni
```

write

```lean
N(h) = computedCollisionNOfRationality h.
```

Let `upperN(h)` be the cutoff supplied by the upper-tail certificate, and let
`threshold(h)` be the threshold supplied by the tail-gap structure for that
same upper tail. The main theorem may be summarized as

```lean
N(h) = max upperN(h) threshold(h)
```

and the same formal input package proves

```lean
¬ is_rational euler_mascheroni.
```

The result is a conditional formal collision theorem: once the common measured
checker coordinate and upper provider are supplied as Lean inputs, it states
exactly how the collision point is computed and how the contradiction occurs at
that point. Decimal extraction of the threshold is not claimed in this
manuscript.

## 2. Formal Setting

### 2.1 The Common Measurement Coordinate

The checker-side object used by the main theorem is

```lean
ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data
```

It packages a PA Hilbert-style proof-checker semantics, finite search, a
rejection extractor, and a tail-gap certificate for one measured function. The
common coordinate is essential: the upper and strict lower estimates must refer
to the same measured function in order to collide at one natural number.

### 2.2 Upper Tails And Tail Gaps

The second input is an upper provider in the same measurement coordinate,
denoted here by `UpperProvider(input)`. Under a rationality-branch proof `h`,
it returns an upper-tail certificate. This certificate contains a
polynomially bounded function `U`, a cutoff `upperN(h)`, and a formal proof
that the measured function is controlled by `U` after that cutoff. The exact
Lean type is available through the source link in Section 3.

The same `input` sends this `U` to the tail-gap structure and obtains a
threshold `threshold(h)`. The natural collision candidate is therefore

```lean
max upperN(h) threshold(h).
```

## 3. Main Theorem

The Lean theorem is named

```lean
cleanUpperProvider_submissionRoute
```

and is defined in:

[integration/SondowProjectBigNCleanSubmissionRoute.lean](https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean)

Suppressing namespaces and some projections, its shape is

```lean
theorem cleanUpperProvider_submissionRoute
    (input : ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (upper_provider : UpperProvider input) :
    (∀ hrat : is_rational euler_mascheroni,
      computedCollisionNOfRationality hrat =
        max upperN threshold) ∧
      ¬ is_rational euler_mascheroni
```

The exact Lean statement expands `upperN` as the cutoff returned by
`checkedSearchUpperTail` and expands `threshold` as the value returned by
`input.tail_gap.gap_for_polynomial_upper`. The first component identifies the
collision point; the second component gives the rationality-branch
contradiction.

## 4. Proof

The proof combines two formal theorems.

**Lemma 4.1 (collision-number computation).** For every rationality-branch
proof `h`,

```lean
computedCollisionNOfRationality h =
  max upperN(h) threshold(h).
```

The corresponding Lean theorem is

```lean
cleanComputedBigN_eq_tailGapMax
```

It states that the natural number computed by the formal program is exactly the
maximum of the upper-tail cutoff and the tail-gap threshold.

**Lemma 4.2 (same-point contradiction).** Let
`N = computedCollisionNOfRationality h`. By Lemma 4.1, `N ≥ upperN(h)` and
`N ≥ threshold(h)`. The first inequality activates the upper-tail certificate
at `N`; the second activates the tail-gap certificate at the same `N`. Thus the
same measured function satisfies an upper control and a strict opposite
inequality at one point, which is impossible.

In Lean the contradiction is exposed through

```lean
cleanProvider_not_rational
```

and the `not_rational` field of the checker input package. Combining Lemma 4.1
and Lemma 4.2 gives `cleanUpperProvider_submissionRoute`.

## 5. Formal Artifact And Reproducibility

Repository:

<https://github.com/james130012/sondow-pudlak-collision-box>

Release accompanying this manuscript:

<https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/clean-bigN-submission-polished-20260708>

Main theorem source:

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean>

Audit records:

- English: <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_en.md>
- Chinese: <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_zh.md>

The main theorem can be rebuilt with

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

The theorem and its axiom profile can be checked by

```bash
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

The observed axiom output for the main theorem is

```text
[propext, Classical.choice, Quot.sound]
```

## 6. Conclusion

This paper gives a reproducible Lean formalized collision theorem: in a common
proof-checker measurement coordinate, the rationality branch has collision
number `max upperN threshold`, and at that same natural number the upper and
strict lower certificates contradict each other. The result packages the
central Sondow-Pudlak collision mechanism as a clear, checkable, and citable
formal theorem.

Numerical extraction of the threshold can be pursued separately. The
contribution of this manuscript is the completed Lean-checked formal collision
core.

## References

1. J. Sondow, Criteria for irrationality of Euler's constant, *Proceedings of
   the American Mathematical Society* 131 (2003), 3335-3344.
2. S. R. Buss, On Godel's theorems on lengths of proofs I: Number of lines and
   speedup for arithmetics, *Journal of Symbolic Logic* 59 (1994), 737-756.
3. P. Pudlak, On the lengths of proofs of finitistic consistency statements in
   first order theories, in *Logic Colloquium 1984*, North-Holland, 1986.
4. L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming
   language, in *Automated Deduction - CADE 28*, 2021.
