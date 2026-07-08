# A Lean-Checked Sondow-Pudlak Existential Big-N Certificate

## Abstract

This paper reports a Lean 4 checked existential big-`N` certificate in the Sondow-Pudlak project. The current verified development is no longer only an outer interface or a route diagram. From the proof-length recognition package, the Sondow and partial verifier traces, the half-denominator Sondow tail, partial-consistency truth, source-minChecked calibration, and Buss-Pudlak rescaling, Lean proves that the final project-length endpoint computes some natural number `N` and that the required source-side strict gap holds at that `N`.

The main Lean theorem is:

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

Its conclusion has the following shape:

```lean
∃ N : Nat,
  endpointN = N ∧
  N =
    semanticStrongNatLowerBoundClassicalMonomialSearchWitness
      sourceLength hsource (max 17 sondowPrefixCoeff + 8) 1 0 ∧
  (max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

Thus the existential big `N` is closed in Lean. What is not yet closed is the expansion of this `N` into a printed decimal natural number. In short, the present result is an existence theorem, not a numeric extraction theorem.

The paper also records the current normal form for the numeric route. In the old proof-length tail-gap model, with the S²₁/PudlakPA root proof-length inputs exposed, the final computed collision index reduces to

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

The remaining numeric task is therefore concrete: compute or construct this `thresholdOf`, and remove the residual dependence on rational-parameter denominators and finite prefixes.

Keywords: Euler-Mascheroni constant; Sondow criterion; Pudlak finite consistency; proof length; Lean 4; existential big N; formal verification.

## 1. Problem and Boundary

The Euler-Mascheroni constant is

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

Whether γ is rational remains open. Sondow's criterion connects rationality of γ to a family of checkable certificate conditions. The Pudlak-Friedman-Buss line gives proof-length lower bounds for finite consistency statements. The project goal is to put these two sources into one formal measurement coordinate so that the upper and lower sides meet at the same large `N`.

The claim of this paper is bounded as follows.

1. Proved: in the current source-calibrated proof-length recognition route, there exists a natural number `N`; the final endpoint returns this `N`; and the source-side strict inequality holds at this `N`.
2. Proved: this `N` is not an arbitrary placeholder. It is the `semanticStrongNatLowerBoundClassicalMonomialSearchWitness`, or, in the more explicit tail-gap route, it reduces to `max upperN thresholdOf(...)`.
3. Not proved: a fully expanded decimal natural number `N = ...`.
4. Not claimed: an unconditional proof that γ is irrational.

This distinction is essential. The existential big `N` is already a Lean-checked result. The explicit natural number `N` is a later computation and construction task.

## 2. Main Formal Theorem

The main entry point of the proof checkpoint is:

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

The theorem consumes the following main inputs.

1. `hrec : S21GraftProofLengthRecognitionTheorem`, the S²₁ proof-length recognition package.
2. `sondowTrace` and `partialTrace`, the two verifier trace soundness inputs.
3. `rat : MainSondowRationalParameter`, the Sondow rational parameter in the rationality branch.
4. `partialTruth : PartialConsistencyAcceptedTruth`.
5. `time_bound_strict` and `exponent_ne_zero`.
6. `source_minChecked_calibration`, calibrating the partial-consistency source proof length to `minCheckedCodeSize`.
7. `buss_pudlak_rescaling`, which turns the Buss-Pudlak rescaling input into a semantic strong lower bound.

Inside the theorem Lean constructs:

```lean
h :=
  hrec.toLocalProofCodeSemanticsPackage.toCanonicalCalibrationPackage

sondowThreshold :=
  max 3 ((rat.q.den + 1) / 2)

sondowPrefixCoeff :=
  natPrefixMax h.sondow_proofs.length sondowThreshold

sourceLength m :=
  ((h.sondow_proofs.conjIntro h.partial_proofs)
    |>.rightConjElim
    |>.minCheckedCodeSize m)
```

It then proves the existence of `N : Nat` such that the final endpoint returns `N` and

```lean
(max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

This is a conclusion about the actual formal proof objects. It is not a prose assertion that such an index ought to exist.

## 3. The Two Root Inputs

The construction starts from two real roots.

The first root is the S²₁/Sondow proof-length side. The relevant bridge theorems include:

```lean
SondowReflectionGraftRootProofLengthConvention.ofRootS21AndPudlakPA

sondowReflectionGraftRootProofLengthConvention_nonempty_of_rootS21_pudlakPA

sondowReflectionGraftTailVerificationBridge_of_mainEventualCompiler_rootS21_pudlakPA_and_rationalParameter
```

These results split the Sondow reflection-graft proof-length convention into S²₁ root calibration and Pudlak/PA root calibration. The root assumption is not hidden inside a single opaque package.

The second root is the older proof-length tail-gap model. At the final C-line root route it gives:

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max
```

This theorem reduces the final computed collision index to:

```lean
max upper.upperN
  (proof_length_tail_gap.gap_for_polynomial_upper
    upper.U upper.polynomial).threshold
```

The current numeric route further exposes this threshold as an explicit function:

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

with target shape:

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

This is the natural-number entry point that remains to be computed.

## 4. Existential Big N Versus Numeric Big N

The existential big `N` and the numeric big `N` live at different levels.

The existence theorem is closed because `SemanticStrongNatLowerBound` gives a strong lower bound of the form `∃ᶠ n in atTop`. Lean extracts a witness satisfying the target monomial inequality by:

```lean
semanticStrongNatLowerBoundClassicalMonomialSearchWitness
```

This is enough to prove:

```lean
∃ N : Nat, endpointN = N ∧ ...
```

It does not print a natural number. The reason is structural: `SemanticStrongNatLowerBound` is a Prop-level lower bound, not an executable search procedure.

To obtain a numeric `N`, the route must use stronger computable data, for example:

1. an explicit tail-gap provider, followed by evaluation of `thresholdOf upper.U upper.polynomial`; or
2. an executable rejection extractor, followed by evaluation of

```lean
extractor.witness upper.U upper.polynomial upper.upperN
```

The current Lean development has reduced the final natural-number task to these genuine computation entries. The remaining work is to construct their contents, not to add another outer wrapper.

## 5. The Half-Denominator Residual

The half-denominator Sondow tail gives the sharper threshold:

```lean
max 3 ((rat.q.den + 1) / 2)
```

Under one-higher-power or checked-prefix hypotheses, the corresponding endpoint reduces to:

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

This expression still depends on `rat.q.den`. Since `rat : MainSondowRationalParameter` belongs to the rationality branch, and the goal is to contradict that branch, `rat.q.den` cannot simply be treated as an external known constant.

The development also proves the finite-prefix obstruction:

```lean
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

This shows that the accepted/checked prefix premise is not automatic from the rational parameter. It is a real finite-prefix obstruction and should not be packaged away as obvious.

## 6. Reproducible Version

The Lean proof checkpoint was released as:

```text
bigN-existence-20260708
```

at commit:

```text
69f5ef28b0f1b62ff7276314423ce4f806c50d0c
```

That version contains the Lean proof of the existential big `N` and was checked with:

```bash
git diff --check
lake env lean integration/SondowProjectS21Kernel.lean
lake env lean integration/SondowProjectMonth11Month12HardResidualElimination.lean
lake env lean integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

The `ProjectLengthTargetUpperEndpoint.lean` check reports two pre-existing `unnecessarySimpa` linter warnings and no Lean errors.

The audit-paper release for this revision is:

```text
bigN-existence-paper-20260708
```

That tag is the download point for the updated paper sources and PDF/HTML assets. It does not change the Lean proof-checkpoint boundary above; it synchronizes the exposition and the latest `thresholdOf` numeric handoff theorem with the existential big-`N` state.

## 7. Audit Checklist

An expert audit should focus on the following points.

1. The main theorem really returns `∃ N : Nat`; it is not merely an outer nonempty interface.
2. `source_minChecked_calibration.semanticStrongNatLowerBound_of_rescaling` really connects Buss-Pudlak rescaling to `sourceLength`.
3. `sondowThreshold` and `sondowPrefixCoeff` come from actual proof-family lengths, not from artificial constants.
4. The S²₁ root calibration and Pudlak/PA root calibration are combined through the split-root constructor.
5. In the numeric route, `thresholdOf` or `extractor.witness` must be an actual algorithm, not another use of `Classical.choose`.

These points separate the proved existential statement from the still-open numeric extraction.

## 8. Remaining Natural-N Route

The next work should focus on two real residuals.

First, construct an explicit tail-gap provider. If one supplies

```lean
thresholdOf :
  ∀ U : Nat → Real, is_polynomial_bound U → Nat
```

and proves that it is the old proof-length tail-gap threshold, then the final natural number is:

```lean
max upper.upperN (thresholdOf upper.U upper.polynomial)
```

Second, construct an executable rejection extractor. If one supplies genuine `extractor.witness` and `extractor.cutoff` functions and proves finite candidate rejection, the final natural number can be computed directly from the witness function.

Both routes start from real structure. Neither route is solved by adding interfaces alone; the substantive work is the construction of the computable threshold or witness.

## 9. Conclusion

The current Lean project proves an existential big `N`: the final project-length endpoint returns a natural number `N`; this `N` is the source-calibrated lower-bound witness; and the required strict source-side gap holds at that point.

This is already an independent formal checkpoint. The existential big `N` is machine checked. The next step is not to repackage the result, but to compute a concrete natural number through either the `thresholdOf` route or the executable `extractor.witness` route.

The current version is therefore best stated as a Lean-checked Sondow-Pudlak source-calibrated existential big-N certificate. It is not a final unconditional proof of the irrationality of γ, and it is not the final numeric `N`; but it moves the existence of big `N` from a route diagram into a reproducible machine-checked theorem.

## References

1. Jonathan Sondow, “Criteria for Irrationality of Euler's Constant,” *Proceedings of the American Mathematical Society*, 131(11), 3335-3344, 2003. arXiv:math/0209070.
2. Samuel R. Buss, “On Gödel's Theorems on Lengths of Proofs I: Number of Lines and Speedup for Arithmetics,” *Journal of Symbolic Logic*, 59(3), 737-756, 1994.
3. Pavel Pudlak, “On the lengths of proofs of finitistic consistency statements in first order theories,” in *Logic Colloquium 1984*.
4. Pavel Pudlak, “Improved bounds to the lengths of proofs of finitistic consistency statements,” in *Logic and Combinatorics*, 1987.
5. Jan Krajicek and Pavel Pudlak, “The Number of Proof Lines and the Size of Proofs in First-Order Logic,” *Archive for Mathematical Logic*, 1988.
6. The Lean 4 and Mathlib projects, project documentation and source libraries.
