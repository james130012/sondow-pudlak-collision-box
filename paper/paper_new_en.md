# A Conditional Proof-Complexity Collision Framework for the Irrationality of Euler's Constant

## Abstract

The irrationality of the Euler-Mascheroni constant γ remains open. This paper does not claim an unconditional proof of γ ∉ ℚ. Instead, it formulates a conditional proof-complexity framework in which Sondow's criterion supplies a rationality-to-short-proof collapse, while Pudlak-Friedman-Buss finite consistency lower bounds supply a long-proof obstruction. The central point is not merely to have an upper bound and a lower bound, but to place both on the same formula family, in the same proof system, and under the same proof-length measure. A Lean 4 formalization checks the interface-level composition: once the stated external mathematical inputs and proof-length calibration witnesses are supplied, the formal chain derives

```math
\neg \mathrm{is\_rational}(\gamma).
```

The contribution is to turn a broad Gödel-speedup heuristic into a precise conditional collision theorem, with the remaining mathematical risks isolated in explicit certificates.

Keywords: Euler-Mascheroni constant; Sondow criterion; Pudlak finite consistency; proof complexity; Peano Arithmetic; Lean 4; conditional theorem.

## 1. The Problem and the Strategy

The Euler-Mascheroni constant is

```math
\gamma=\lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac1k-\log n\right).
```

Unlike π and e, the arithmetic status of γ is unknown. Sondow's work gives integral and product criteria related to the rationality of γ. In broad terms, these criteria connect rationality of γ with eventual identities involving fractional parts of logarithmic products. If such identities can be represented by compressed certificates, then the rationality hypothesis may induce a proof-length collapse.

This observation alone cannot prove irrationality. A contradiction requires a lower bound for the same formula family, in the same formal system, and under the same length measure. At present there is no standard proof-complexity lower bound for the natural Sondow certificate family itself. Therefore this paper follows a more conservative model route: the Sondow certificate is combined with a finite-consistency or reflection payload, allowing the lower-bound side to use Pudlak-Friedman-Buss finite consistency lower bounds.

This route is less natural than proving a lower bound for the native Sondow family, but it has a precise target: a collision between a short-proof upper bound and a long-proof lower bound on one common proof-complexity coordinate.

## 2. The Three Objects: Upper Bound, Lower Bound, and Common Box

We separate three objects.

First, A denotes the Sondow collapse side. It is not a single formula, but a mechanism by which the assumption γ ∈ ℚ yields a family of short, checkable certificates.

Second, B denotes the Pudlak-Friedman-Buss lower-bound side. It acts on finite consistency or reflection formulas, such as statements asserting that there is no PA proof of contradiction of length at most n. This side comes from proof-length lower bounds, not from Sondow's analysis.

Third, C is the common measurement object. It must receive both the short-proof upper bound from A and the lower bound from B. If the two sides live in different encodings, proof systems, or length measures, no contradiction follows. The core question is therefore whether both sides can be projected to the same C.

In the Lean model this common coordinate is represented by:

```lean
FormulaCode
ProofSystem.PA
ProofLengthMeasure.symbolSize
```

All formula families are encoded as `FormulaCode`; all proof lengths are interpreted as PA symbol-size proof lengths. This is the main difference between the present framework and an informal Gödel-speedup narrative.

### 2.1 The Core Collision Equation

The central idea can be compressed into a proof-length collision pattern. Let C_n be the final family in the common measurement box. Under the rationality assumption, the Sondow-collapse side is expected to give an upper bound

```math
\mathrm{Len}_{PA}(C_n)\le U(n),
```

where Len_PA denotes PA symbol-size proof length and U(n) is the bound produced by the short-certificate verification mechanism. On the other hand, the Pudlak-Friedman-Buss lower-bound side is expected to give

```math
L(n)\le \mathrm{Len}_{PA}(C_n).
```

If the calibrations identify the middle term as the same object, and if for all sufficiently large n,

```math
U(n)<L(n),
```

then a contradiction follows. Thus the real content of the project is not merely to exhibit one upper bound and one lower bound, but to prove that their middle term is literally the same proof-length coordinate:

```math
\mathrm{Len}_{PA}^{Sondow}(C_n)
=
\mathrm{Len}_{PA}^{Pudlak}(C_n)
=
\mathrm{proof\_length}\; ProofSystem.PA\; ProofLengthMeasure.symbolSize\; C_n.
```

This explains why proof-length calibration is central. Without calibration, the upper and lower bounds may both be true but incomparable. With calibration, they become statements about the same object and can collide.

### 2.2 How B Enters C

The Pudlak lower bound is naturally about finite-consistency or reflection formulas B_n, not about the native Sondow analytic formulas. The bridge used here is payload grafting and local projection. Informally, C_n is not an arbitrary conjunction of A_n and B_n. It is a checkable proxy formula carrying the information needed for the Sondow short verification while its reflection payload projects back to the finite-consistency family covered by the Pudlak lower bound.

An audit of this step has to check three facts.

1. Formula equality: the local `FormulaCode` family C_n must agree pointwise with the source-side finite-consistency family, or a proved projection must preserve the relevant proof-length relation.
2. Proof-system equality: both sides must be stated in `ProofSystem.PA`.
3. Length-measure equality: both sides must use `ProofLengthMeasure.symbolSize`; it is not acceptable for one side to use number of lines and the other to use encoded bit length.

The current Lean development separates these facts into explicit certificates. This avoids the common mistake of putting “B has a lower bound” and “C has a short proof” in the same paragraph without proving that they are jointly measurable.

## 3. The Conditional Main Theorem

The main theorem should be read conditionally.

**Theorem 1, interface-level Sondow-Pudlak collision.**
Assume the following inputs are provided.

1. A Sondow collapse input: under γ ∈ ℚ, the Sondow side produces verifiable short certificates.
2. A Pudlak-Friedman-Buss finite consistency lower-bound input, instantiated for the selected finite-consistency or reflection family.
3. Encoding and projection inputs, showing that the external finite-consistency family agrees with, is equivalent to, or projects to the local `FormulaCode` family.
4. Proof-length calibration inputs, identifying the abstract `proof_length` with the relevant checked-code proof-length models on the formula families used in the collision.
5. Payload-truth inputs, ensuring that the reflection payload expresses the intended finite-consistency content.

Then the Lean composition derives

```math
\neg \mathrm{is\_rational}(\gamma).
```

This is a conditional theorem. It does not internally prove Sondow's criterion, Pudlak's Theorem 5, or the PA proof-length function from first principles. It proves that, once these inputs are supplied in the required interfaces, the subsequent encoding transfers, length calibrations, projections, and final contradiction are machine checked.

### 3.1 Formal Theorem Schema

More precisely, the interface-level theorem has the following logical form:

```math
\mathcal S\;\wedge\;\mathcal P\;\wedge\;\mathcal E\;\wedge\;\mathcal L\;\wedge\;\mathcal T
\;\Longrightarrow\;
\neg \mathrm{is\_rational}(\gamma).
```

Here:

- 𝒮 is the Sondow collapse certificate;
- 𝒫 is the Pudlak lower-bound certificate;
- ℰ is the encoding/projection certificate;
- ℒ is the proof-length calibration certificate;
- 𝒯 is the payload-truth certificate.

The point of this schema is that unfinished inputs are not hidden inside words such as “obvious” or “by definition.” They appear either as theorem parameters or in the axiom audit. The present scientific claim is that this implication is Lean checked, not that ¬ is_rational(γ) has been proved unconditionally.

### 3.2 No Hidden Weakening of the Statement

Although the theorem is conditional, the target conclusion is not weakened. The final Lean endpoint still concludes:

```lean
¬ is_rational euler_mascheroni
```

The conditionality is entirely on the input side. In particular, the formalization does not prove a vacuous implication unrelated to γ. Each input has a concrete role in the collision chain. If a certificate proves only a weaker family equality or uses a different proof-length convention, it cannot instantiate the current interface and the collision box cannot be called.

## 4. Proof Outline

The proof has four steps.

The first step is the Sondow upper bound. Assume γ ∈ ℚ. Under the Sondow criterion and the verification bridge, rationality yields a short-proof collapse. Informally, a decision problem involving integrals, logarithmic products, and eventual fractional-part identities is replaced by the verification of a finite certificate. In the formal model the shortness is not obtained by hiding huge integers or products in one line; it is accounted for through fixed theorem references and binary indices.

The second step is lower-bound standardization. Pudlak-Friedman-Buss lower bounds are usually stated for finite consistency families. To use them in the present framework, the formula family appearing in the literature must be identified with, or projected to, the local formula-code family. The formalization separates this into raw encoding certificates, rescaling data, and lower-bound certificates.

The third step is common measurement. The upper and lower sides collide only if both are stated in terms of the same
```lean
proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
```
coordinate. This requires two kinds of calibration. One reduces the strengthened-to-partial side to exact family equalities. The other aligns the local Hilbert checked-code model with the abstract PA proof length on the relevant formula families.

The fourth step is contradiction. The Sondow side supplies a short-proof upper bound for the common family, and the Pudlak side supplies a strong lower bound for the same family. Since both are now in the same code, system, and measure, they are incompatible. Hence the rationality hypothesis is impossible under the stated inputs, and

```math
\neg \mathrm{is\_rational}(\gamma)
```

follows.

From an engineering viewpoint, these four steps form a compiler-correctness problem. The Sondow side, the Pudlak side, and the local Hilbert/PA checker are not written in the same language. One must prove that translation between them preserves the proof-length statement that is supposed to collide. The Lean modules split these translations into small certificates and compose them.

## 5. The Role of Lean Formalization

Lean plays three substantive roles in this paper.

First, it forces all exits to carry their assumptions. The final endpoint is not a parameter-free theorem. The current callable theorem is:

```lean
SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
```

Its conclusion is:

```lean
¬ is_rational euler_mascheroni
```

but the theorem consumes explicit Sondow-side and Pudlak-calibration-side inputs. Thus the conditional boundary is visible in the theorem type.

Second, Lean checks that the bridges really compose. Recent formalization reduces the central witnesses to narrower interfaces:

```lean
StrengthenedToPartialProjectProofLengthExactFamilyLengths
PAHilbertPartialConsistencyMinCheckedExactness
PAHilbertReflectionGraftMinCheckedExactness
```

It also provides a conversion from semantic proof-length conventions to the exact split-minChecked input. Thus the collision box is callable, not merely described informally.

The mathematical roles of these names are as follows.

`StrengthenedToPartialProjectProofLengthExactFamilyLengths` calibrates the strengthened family against the partial-consistency family. It answers the question: when the strengthened payload produced by the Sondow-collapse side is lowered to the partial-consistency proxy, is the required proof-length equality preserved?

`PAHilbertPartialConsistencyMinCheckedExactness` calibrates the partial-consistency side. It answers the question: is the proof length seen by the Pudlak source-side lower bound the same length measured by the local checked-code checker?

`PAHilbertReflectionGraftMinCheckedExactness` provides the analogous calibration for the reflection-graft side. It answers the question: after the reflection payload enters the common measurement box, is it still measured by the same PA/Hilbert proof-code semantics?

Third, Lean provides an axiom audit. The current callable theorem depends essentially on:

```text
literaturePudlakTheorem5ExternalRescaledLowerBound
literaturePudlakTheorem5ExternalScaleData
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
```

In addition, it uses standard Lean/Mathlib principles such as `propext`, `Classical.choice`, and `Quot.sound`. This list is part of the scientific boundary of the result: the theorem is an interface-level conditional theorem, not a closed unconditional proof.

## 6. Why the Conditionality Is Structured

The conditionality in this paper is not a single opaque assumption. Each input has a specific mathematical responsibility.

The Sondow input creates the upper bound from rationality. The Pudlak input supplies the finite-consistency lower bound. Encoding certificates ensure that the literature formula family and the local formula family are the same object or are related by a controlled projection. Proof-length calibration connects the abstract complexity coordinate with concrete checked-code models. Payload truth gives semantic content to the reflection payload.

Consequently, if one of these inputs is later proved internally or matched exactly by a published theorem, it can be replaced locally without changing the entire collision chain. This modularity is the main value of the interface-level formalization.

From the audit perspective, the main claim is not that every hard theorem has already been proved. The claim is that the hard points have been localized. A reviewer can now ask the following questions one certificate at a time:

- Does Pudlak's Theorem 5 cover the current formula family?
- Does the rescaling preserve a lower bound strong enough to beat the Sondow upper bound?
- Is `proof_length` pointwise equal to checked-code minimum size on the two relevant families?
- Does the payload-truth certificate express the intended consistency or reflection content?

Once these questions are answered, the final collision argument does not need to be redesigned.

## 7. Remaining Work

Three major tasks remain.

First, Pudlak's Theorem 5 is currently treated as an external literature certificate. Fully internalizing it would require a formal development of the proof-complexity lower-bound literature for finite consistency statements.

Second, the PA/Hilbert proof-length convention is not yet internalized from first principles. The current `proof_length` is an abstract complexity function, and its relevant equalities enter through auditable witnesses. A full internalization would construct PA proof objects, encoders, checkers, and minimum proof-code size functions, and then prove their equivalence to the abstract proof length.

Third, the remaining task on the upper-bound side is the parameter-free instantiation of the final short-verification witness. The analytic integral decomposition, the product-log identity, the tail estimates, and the Sondow forward package already have a Lean-closed reproof route. The project-local verifier/compiler framework is also present in the buildable interfaces `SondowProjectLocalS21Kernel` and `SondowProjectLocalReflectionGraftVerifier`. Thus it would be inaccurate to list the Sondow analytic side, or the entire bounded-arithmetic verifier, as a remaining external gap. More precisely, what remains is to construct the final input

```lean
Nonempty SondowProjectLocalReflectionGraftVerifier
```

from lower-level checked-code S²₁ trace calibrations and a PA embedding witness, and to internalize the payload-truth semantics represented by `PartialConsistencyPayloadTruth` and `StrengthenedPartialConsistencyPayloadTruth`.

These tasks do not undermine the present theorem. They define exactly what must be done to turn the interface-level conditional collision into a stronger mathematical result.

### 7.1 Appropriate Public Status of the Current Version

The present manuscript is best read as the paper accompanying a public-alpha research artifact, not as a final unconditional solution of the irrationality of γ. The appropriate public claims are:

1. a Lean-checked conditional collision theorem;
2. a precise certificate architecture;
3. a reproducible axiom ledger;
4. a roadmap reducing future work to a small number of explicit witnesses.

The inappropriate claims are: an unconditional proof of the irrationality of Euler's constant, or an internal Lean proof of Pudlak's Theorem 5 and the PA proof-length convention. These boundaries must remain explicit.

## 8. Conclusion

This paper presents a conditional proof-complexity collision framework for Euler's constant. Its core contribution is not an unconditional proof of γ ∉ ℚ, but the following precise conditional claim: if the Sondow rationality collapse, the finite-consistency lower bound, the encoding projections, and the proof-length calibrations are supplied in the specified interfaces, then they are incompatible on the same PA symbol-size proof-length coordinate, and the Lean-checked composition derives ¬ is_rational(γ).

The value of the result is that it turns a broad Gödel-speedup intuition into an auditable formula-family collision problem. It also gives a clear roadmap for future work: internalize or precisely cite each external input until the conditional framework contracts into a stronger theorem.

## References

1. Jonathan Sondow, “Criteria for Irrationality of Euler's Constant,” *Proceedings of the American Mathematical Society*, 131(11), 3335-3344, 2003. arXiv:math/0209070.
2. Samuel R. Buss, “On Gödel's Theorems on Lengths of Proofs I: Number of Lines and Speedup for Arithmetics,” *Journal of Symbolic Logic*, 59(3), 737-756, 1994.
3. Pavel Pudlak, “On the lengths of proofs of finitistic consistency statements in first order theories,” in *Logic Colloquium 1984*.
4. Pavel Pudlak, “Improved bounds to the lengths of proofs of finitistic consistency statements,” in *Logic and Combinatorics*, 1987.
5. Jan Krajicek and Pavel Pudlak, “The Number of Proof Lines and the Size of Proofs in First-Order Logic,” *Archive for Mathematical Logic*, 1988.
6. The Lean 4 and Mathlib projects, project documentation and source libraries.
