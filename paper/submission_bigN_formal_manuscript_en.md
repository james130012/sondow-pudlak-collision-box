# A Parameter-Closed Formal Collision Theorem in the Sondow-Pudlak Program

Author: James

## Abstract

We present a Lean 4 formal collision theorem in the Sondow-Pudlak program for
the Euler-Mascheroni constant.  Let `minCheckedCodeSize n` denote the minimal
checked proof-code size in a fixed PA-Hilbert checker coordinate.  The main
theorem removes the explicit `upper_provider`, `tail_gap`, and
`eventually_strict_length` parameters from the public theorem surface.  The
remaining input is the monomial growth statement that for every natural
`coeff, degree`, after the explicit threshold
`thresholdOfMonomial coeff degree`,

```lean
coeff * (n + 1)^degree < minCheckedCodeSize n.
```

Under this input, Lean proves the formula-level collision index

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree
```

and derives the formal contradiction theorem
`¬ is_rational euler_mascheroni`.  The theorem name, reproduction command, and
residual-constant audit are recorded in Sections 4 and 5; the observed axiom
profile contains only standard Lean/Mathlib logical dependencies.

Keywords: Euler-Mascheroni constant; Sondow criterion; Pudlak lower bounds;
proof length; formalized mathematics; Lean.

## 1. Introduction

The irrationality of the Euler-Mascheroni constant

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac{1}{k}-\log n\right)
```

is a classical open problem.  Sondow-type criteria transform a rationality
assumption into arithmetic upper certificates, while Pudlak-type
proof-complexity lower bounds impose constraints from the proof-length side.
If both sides are placed in the same checker coordinate, the intended collision
has the form

```math
M(N)\le U(N)<M(N).
```

This paper formalizes the collision core with a cleaner parameter surface than
the earlier route.  The previous intermediate theorem exposed an
`upper_provider` and a `tail_gap` directly.  The present endpoint pushes these
objects upstream and replaces them, at the public theorem boundary, by the
explicit monomial growth obligation

```math
T(c,d)\le n\quad\Longrightarrow\quad
c(n+1)^d<\operatorname{minCheckedCodeSize}(n).
```

Here `T(c,d)` is the Lean term `thresholdOfMonomial c d`.

The result should not be read as a decimal extraction of `N` or as the final
unconditional proof of the irrationality of `gamma`.  Its contribution is the
Lean-checked formula-level collision index, the same-point contradiction, and a
clean axiom profile under a clearly stated growth input.

## 2. Formal Setting

Fix a PA-Hilbert checker coordinate.  For formal proof families `left_family`
and `right_family`, Lean forms the conjunction-introduction family and then
right-eliminates it.  The measured function is

```lean
M n =
  ((left_family.conjIntro right_family)
    |>.rightConjElim
    |>.minCheckedCodeSize n)
```

The Sondow-side generated upper data are compressed into

```lean
upper_data =
  projectLengthConjIntroLengthAddTwoNatPowerUpperData
    left_family right_family left_data right_data
```

with natural monomial envelope parameters `upper_data.coeff` and
`upper_data.degree`.  The collision index is

```lean
bigN =
  thresholdOfMonomial upper_data.coeff upper_data.degree.
```

The load-bearing input is

```lean
monomial_lt_lengthCodeAt_after :
  ∀ coeff degree n : Nat,
    thresholdOfMonomial coeff degree ≤ n →
      coeff * (n + 1)^degree < M n
```

which is the remaining proof-complexity growth obligation.

## 3. The Collision

Let

```math
c=\texttt{upper\_data.coeff},\qquad
d=\texttt{upper\_data.degree},\qquad
N=T(c,d).
```

The monomial growth input gives

```math
c(N+1)^d<M(N).
```

The generated upper side is bounded at the same index by the same monomial
envelope:

```math
U(N)\le c(N+1)^d.
```

Therefore

```math
U(N)<M(N).
```

The checker endpoint simultaneously returns the opposite comparison at the
same index:

```math
M(N)\le U(N).
```

Thus

```math
M(N)\le U(N)<M(N),
```

which is impossible.  Lean also records the programmatic formula for the
index:

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree.
```

## 4. Main Theorem

The Lean theorem is

```lean
singletonMonomialLowerBound_submissionRoute
```

Source:

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNParameterClosureAudit.lean>

Suppressing namespaces and projections, its content is:

```lean
theorem singletonMonomialLowerBound_submissionRoute
    -- other explicit arguments are shown in the source file
    (thresholdOfMonomial : Nat → Nat → Nat)
    (monomial_lt_lengthCodeAt_after :
      ∀ coeff degree n : Nat,
        thresholdOfMonomial coeff degree ≤ n →
          coeff * (n + 1)^degree < minCheckedCodeSize n) :
    bigN = thresholdOfMonomial upper_data.coeff upper_data.degree ∧
      ¬ is_rational euler_mascheroni
```

The comment line refers to the two proof families, strict time-bound data,
natural-power upper data, and polynomial-boundedness certificates for the
length functions.  The theorem surface does not expose `upper_provider`,
`tail_gap`, or `eventually_strict_length`.

## 5. Formal Audit

Reproduction commands:

```bash
lake exe cache get
lake build integration.SondowProjectBigNParameterClosureAudit
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNParameterClosureAudit
open SondowMainCheckedCodeBridge.SondowProjectBigNParameterClosureAudit

#check singletonMonomialLowerBound_submissionRoute
#print axioms singletonMonomialLowerBound_submissionRoute
EOF
```

Observed axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

The following project-level residual constants do not occur:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

Audit reports:

- English: <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/parameter_closure_audit_20260708_en.md>
- Chinese: <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/parameter_closure_audit_20260708_zh.md>

Repository:

<https://github.com/james130012/sondow-pudlak-collision-box>

## 6. Conclusion

We have formalized a parameter-closed collision theorem in Lean.  The earlier
explicit `upper_provider`, `tail_gap`, and `eventually_strict_length` inputs no
longer appear on the main theorem surface.  The current endpoint exposes a
single monomial growth obligation and, under that obligation, proves the
formula-level large `N` and the same-point collision contradiction.

The next task is to close the monomial growth theorem itself.  The older
half-denominator refinement and decimal extraction of the threshold can then be
developed as later refinements.

## References

1. J. Sondow, Criteria for irrationality of Euler's constant, *Proceedings of
   the American Mathematical Society* 131 (2003), 3335-3344.
2. S. R. Buss, On Godel's theorems on lengths of proofs I: Number of lines and
   speedup for arithmetics, *Journal of Symbolic Logic* 59 (1994), 737-756.
3. P. Pudlak, On the lengths of proofs of finitistic consistency statements in
   first order theories, in *Logic Colloquium 1984*, North-Holland, 1986.
4. L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming
   language, in *Automated Deduction - CADE 28*, 2021.
