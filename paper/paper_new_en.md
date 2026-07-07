# A Lean-Checked Sondow-Pudlak Symbolic Collision Certificate

## Abstract

This paper reports a Lean 4 checked Sondow-Pudlak symbolic collision certificate. Given the formal interfaces for a checked lower bound, an explicit target upper bound, scale data, and checker/project-length semantics, Lean routes both sides to the same fallback-free `bigN` and proves

```lean
upper.U bigN < measured bigN
measured bigN ≤ upper.U bigN
False
```

This is not an informal collision described outside the proof assistant: `bigN`, `measured`, `upper.U`, and the two opposite inequalities occur in one Lean theorem. A further computation-facing normal form proves that this `bigN` is exactly

```lean
rejectionExtractor.witness upper.U upper.polynomial 0
```

Thus the current result does not merely assume the existence of some large threshold. It identifies the formal witness with the checker rejection extractor at threshold zero.

The paper does not claim an unconditional proof that the Euler-Mascheroni constant γ is irrational, and it does not claim to print a concrete numeric value of `N`. The precise claim is that, inside the project checked-lower interface, the formal collision core between the Sondow upper side and the Pudlak-type lower side is closed and reproducible.

Keywords: Euler-Mascheroni constant; Sondow criterion; Pudlak finite consistency; proof complexity; Peano Arithmetic; Lean 4; symbolic collision.

## 1. Problem and Target

The Euler-Mascheroni constant is

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

Whether γ is rational remains open. Sondow's criterion relates rationality of γ to integral, product, and fractional-part conditions. The Pudlak-Friedman-Buss line of work gives proof-length lower bounds for finite consistency statements. This project studies whether these two sources can be made to collide on one formal measurement coordinate.

A valid collision requires three facts.

1. The upper side must supply an eventual upper bound for a measured function.
2. The lower side must supply a strict lower or gap statement for the same measured function.
3. Both sides must use the same `bigN` and the same checker/project-length semantics.

The first two facts are not enough in isolation. If the upper and lower bounds measure different objects, no contradiction follows. The formal contribution is to turn the phrase “the same object” into a Lean-checkable theorem.

## 2. The Common Measurement Object

The common measurement object has three layers.

The first is the formula/code layer. All formula families to be compared must enter the same local code family; otherwise the Pudlak lower side and the Sondow certificate side are not jointly measurable.

The second is the checker layer. The project uses a local Hilbert/PA-style proof checker to connect proof objects and formula codes. The relevant quantity is not an informal text length but the minimum checked-code size or project length recognized by the checker.

The third is the gap/search layer. For each polynomial upper bound, the lower-side rejection extractor supplies a witness at which the strict gap holds. The current endpoint fixes the target cutoff at zero, giving a fallback-free search witness.

In this coordinate, the collision has the form

```math
U(N) < M(N) \quad\text{and}\quad M(N) \le U(N).
```

Here `M` is the formal `measured` function, `U` is `upper.U`, and `N` is the same `bigN`. Together the two inequalities prove `False`.

## 3. Current Main Result

The current main result is summarized by the Lean theorem

```lean
projectLengthExplicitTargetUpperSearchBigNCertificate_of_checkedLowerBound_noFallback
```

It constructs the target-upper search `bigN` certificate directly from

```lean
InternalPudlakTheorem5CheckedPowerBoundLowerBound
```

The theorem consumes the following main inputs.

1. `scale_data`: scaling, power-bound coding, and related monotonicity data.
2. `left_family` and `right_family`: proof families used to build the conjunction-introduction route and the right target family.
3. `lengthCodeAt`: the function connecting the lower-side measurement to the project minimum checked-code size.
4. `checked_lower`: the checked interface for the Pudlak-type power-bound lower bound.
5. Polynomial-bound certificates for the lengths of the two proof families.
6. Strict monotonicity of the time bound and nonzero exponent data.

From these inputs the theorem returns one certificate package at the same `bigN`:

```lean
upper.upperN = 0
concreteFrontier.lower_search.rejectionExtractor.witness
  upper.U upper.polynomial upper.upperN = bigN
PAHilbertAcceptedProofCodeForFormulaCode
  (concretePAHilbertPowerBoundChecker scale_data)
  (scale_data.powerBoundRawCode bigN)
  bigN
scale_data.powerBoundRawCode bigN =
  strengthenedPartialConsistencyCode (scale_data.scale bigN)
upper.U bigN < measured bigN
measured bigN ≤ upper.U bigN
False
```

This shows that the checked lower bound is no longer sitting at the level of prose or an outer interface. It is connected to the explicit target-upper fallback-free contradiction package.

## 4. Normal Form for `bigN`

The follow-up theorem

```lean
projectLengthExplicitTargetUpperSearchBigN_of_checkedLowerBound_noFallback_eq_rejectionExtractorWitness_zero
```

proves the computation-facing exactness statement

```lean
bigN =
  concreteFrontier.lower_search.rejectionExtractor.witness
    upper.U upper.polynomial 0
```

This matters because it removes the residual ambiguity between an existential witness and the computation route. The current `bigN` is the lower-search rejection-extractor witness for `upper.U` and `upper.polynomial` at threshold zero.

Thus the remaining issue is numeric evaluation, not symbolic identification. To print an actual natural number `N`, one still has to unfold executable data for `upper.U`, `upper.polynomial`, `scale_data`, and the rejection extractor. But the formal object has already been calibrated to the unique computation entry point.

## 5. Reproducible Checkpoint

The repository published the prerelease

```text
fcce697-symbolic-collision-checkpoint
```

It is pinned to commit

```text
fcce697c60adfe87d4d33515ff965322962fc994
```

This checkpoint reproduces the fact that the same `bigN` carries the two opposite inequalities and therefore `False`. It is not a numeric-`N` checkpoint, and it is not an irrationality theorem for γ. It is a symbolic collision checkpoint.

An expert audit should read it as follows.

1. The collision kernel is machine checked.
2. The checked-lower route is connected to the fallback-free target-upper route.
3. The future computation target for `bigN` is normalized to a rejection-extractor witness.
4. A concrete natural number `N` has not yet been printed.

## 6. Relation to the Irrationality Route

The result should not be packaged as an unconditional proof of the irrationality of γ. The accurate relationship is the following.

The Sondow side is responsible for producing a short-certificate route from a rationality assumption. The Pudlak side is responsible for lower bounds for a finite-consistency or reflection family. The checker/project-length route proves that the two sides act on the same measured function.

The part that is now closed is the formal collision core most vulnerable to a logical mismatch: the same `bigN`, the same `measured` function, and the same `upper.U` are used for both inequalities. What remains is to turn all external mathematical inputs into parameter-free internal witnesses and to evaluate the final `bigN` as a concrete natural number.

Thus the present result narrows the remaining program to two tasks.

1. Construct or cite sufficiently strong external mathematical inputs and align them with the checked-lower interface.
2. Unfold the rejection-extractor witness to obtain a numeric `N`.

## 7. Axiom and Input Boundary

The credit boundary has two parts.

The first part consists of standard Lean/Mathlib logical dependencies such as `propext`, `Classical.choice`, and `Quot.sound`.

The second part consists of project interface inputs: the checked lower bound, scale data, proof families, length coding, and polynomial-bound certificates. These are not hidden conclusions. They appear explicitly in the theorem type.

For an expert audit, the relevant questions are:

1. Do the inputs faithfully express the intended Sondow/Pudlak mathematics?
2. Are the inputs strong enough to produce the checked lower bound required by the theorem?
3. Can the inputs be made into parameter-free witnesses?
4. Can the rejection-extractor witness be effectively evaluated?

## 8. Remaining Work

The remaining work should not be described as “whether the collision core closes.” A more accurate list is:

First, numeric `N` extraction. The current `bigN` is proved equal to the rejection-extractor witness, but that witness has not yet been expanded into a concrete natural number.

Second, external-to-internal calibration. The Sondow criterion, the Pudlak-type lower bound, and payload semantics must continue to be moved from literature statements or project interfaces into parameter-free Lean witnesses.

Third, publication-grade audit. A formal paper should stabilize theorem names, release tags, axiom audits, and reproduction steps in an appendix, while avoiding internal construction labels as mathematical structure.

These tasks are substantial, but they are distinct from the question whether the present development already contains a same-`bigN` formal collision. That fact is supported by the Lean theorem and the reproducible checkpoint above.

## 9. Conclusion

The current project establishes a precise formal result: a checked lower bound can directly produce a fallback-free target-upper `bigN` certificate, and at that same `bigN` Lean proves

```lean
upper.U bigN < measured bigN
measured bigN ≤ upper.U bigN
False
```

The same `bigN` is then identified with the rejection-extractor witness at threshold zero. This connects the symbolic collision core to the future numeric-evaluation entry point.

Accordingly, the current version is best described as a reproducible, Lean-checked Sondow-Pudlak symbolic collision checkpoint. It is not a final unconditional proof of the irrationality of γ, but it has moved the collision core from a conceptual route to a machine-checked same-object contradiction certificate.

## References

1. Jonathan Sondow, “Criteria for Irrationality of Euler's Constant,” *Proceedings of the American Mathematical Society*, 131(11), 3335-3344, 2003. arXiv:math/0209070.
2. Samuel R. Buss, “On Gödel's Theorems on Lengths of Proofs I: Number of Lines and Speedup for Arithmetics,” *Journal of Symbolic Logic*, 59(3), 737-756, 1994.
3. Pavel Pudlak, “On the lengths of proofs of finitistic consistency statements in first order theories,” in *Logic Colloquium 1984*.
4. Pavel Pudlak, “Improved bounds to the lengths of proofs of finitistic consistency statements,” in *Logic and Combinatorics*, 1987.
5. Jan Krajicek and Pavel Pudlak, “The Number of Proof Lines and the Size of Proofs in First-Order Logic,” *Archive for Mathematical Logic*, 1988.
6. The Lean 4 and Mathlib projects, project documentation and source libraries.
