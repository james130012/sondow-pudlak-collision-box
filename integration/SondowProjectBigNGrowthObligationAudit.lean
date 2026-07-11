import integration.SondowProjectBigNParameterClosureAudit

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectBigNGrowthObligationAudit

open Filter
open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth11PAHilbertCheckerSurface

universe u v w q

/--
Pointwise upper bound for the checked length used by the current
`singletonMonomialLowerBound_submissionRoute` object.

The target checked size is not an unconstrained hard-length function: it is the
minimum checked code size of a concrete right-conjunction elimination proof
family.  The concrete proof already has length

`left_family.length m + right_family.length m + 3`,

so the minimum checked code size is bounded above by that expression.
-/
theorem conjRightMinCheckedCodeSize_le_explicitLength
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (m : Nat) :
    ((left_family.conjIntro right_family)
      |>.rightConjElim
      |>.minCheckedCodeSize m) ≤
      left_family.length m + right_family.length m + 3 := by
  calc
    ((left_family.conjIntro right_family)
      |>.rightConjElim
      |>.minCheckedCodeSize m)
        = ((left_family.conjIntro right_family)
          |>.rightConjElim
          |>.minLength m) := by
            rw [_root_.MiniHilbert.ConcreteProofFamily.minCheckedCodeSize_eq_minLength]
    _ ≤ (left_family.conjIntro right_family).minLength m + 2 := by
            exact (left_family.conjIntro right_family).minLength_rightConjElim_le m
    _ ≤ (left_family.length m + right_family.length m + 1) + 2 := by
            exact Nat.add_le_add_right
              (left_family.minLength_conjIntro_le right_family m) 2
    _ = left_family.length m + right_family.length m + 3 := by
            omega

/--
Polynomial upper bound for the same checked-length object whenever the two
input proof families have polynomial length.

This is the formal obstruction to using this object as a super-polynomial
Pudlak lower-bound function: in the current conjunction-source route the object
is already polynomially bounded from above.
-/
theorem conjRightMinCheckedCodeSize_polynomial_of_component_polynomial
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length)) :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real
        (fun m : Nat =>
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))) := by
  exact _root_.is_polynomial_bound_of_le
    (g := _root_.MiniHilbert.nat_bound_as_real
      (fun m : Nat => left_family.length m + right_family.length m + 3))
    (by
      intro m
      have hle :=
        conjRightMinCheckedCodeSize_le_explicitLength
          left_family right_family m
      have hleReal :
          (((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m) : Real) ≤
            (left_family.length m + right_family.length m + 3 : Nat) := by
        exact_mod_cast hle
      simpa [_root_.MiniHilbert.nat_bound_as_real] using hleReal)
    (_root_.MiniHilbert.is_polynomial_bound_nat_add_add_const
      left_length_polynomial right_length_polynomial 3)

/--
Any Nat-valued function which is polynomially bounded from above cannot
eventually dominate every Nat-coefficient monomial.

This is the paper-level obstruction behind the failed
`thresholdOfMonomial` target: once the carrier is already polynomially bounded,
choosing the same degree and a natural coefficient above the upper coefficient
forces

`C * (n + 1)^k < lengthCodeAt n <= c * (n + 1)^k <= C * (n + 1)^k`.
-/
theorem monomialDomination_impossible_of_polynomial_bound
    (lengthCodeAt : Nat → Nat)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real lengthCodeAt))
    (thresholdOfMonomial : Nat → Nat → Nat)
    (monomial_lt_lengthCodeAt_after :
      ∀ coeff degree n : Nat,
        thresholdOfMonomial coeff degree ≤ n →
          coeff * (n + 1) ^ degree < lengthCodeAt n) :
    False := by
  classical
  rcases hpoly.nonneg_coefficient with ⟨c, k, _hc_nonneg, hupper⟩
  let C : Nat := Classical.choose (exists_nat_ge c)
  have hC : c ≤ (C : Real) :=
    Classical.choose_spec (exists_nat_ge c)
  let n : Nat := thresholdOfMonomial C k
  have hlowerNat :
      C * (n + 1) ^ k < lengthCodeAt n :=
    monomial_lt_lengthCodeAt_after C k n le_rfl
  have hlowerReal :
      ((C * (n + 1) ^ k : Nat) : Real) <
        (lengthCodeAt n : Real) := by
    exact_mod_cast hlowerNat
  have hupperReal :
      (lengthCodeAt n : Real) ≤ c * ((n : Real) + 1) ^ k := by
    simpa [_root_.MiniHilbert.nat_bound_as_real] using hupper n
  have hpow_nonneg : 0 ≤ ((n : Real) + 1) ^ k := by
    positivity
  have hupperCoeff :
      c * ((n : Real) + 1) ^ k ≤
        (C : Real) * ((n : Real) + 1) ^ k :=
    mul_le_mul_of_nonneg_right hC hpow_nonneg
  have hmonomialCast :
      ((C * (n + 1) ^ k : Nat) : Real) =
        (C : Real) * ((n : Real) + 1) ^ k := by
    simp [Nat.cast_mul, Nat.cast_pow, Nat.cast_add]
  have hself :
      (C : Real) * ((n : Real) + 1) ^ k <
        (C : Real) * ((n : Real) + 1) ^ k := by
    calc
      (C : Real) * ((n : Real) + 1) ^ k
          = ((C * (n + 1) ^ k : Nat) : Real) := hmonomialCast.symm
      _ < (lengthCodeAt n : Real) := hlowerReal
      _ ≤ c * ((n : Real) + 1) ^ k := hupperReal
      _ ≤ (C : Real) * ((n : Real) + 1) ^ k := hupperCoeff
  exact (lt_irrefl ((C : Real) * ((n : Real) + 1) ^ k)) hself

/--
Direct rejection of the old singleton monomial obligation on the current
conjunction-source carrier.

This theorem matches the input shape of
`singletonMonomialLowerBound_submissionRoute`: the requested
`thresholdOfMonomial`/`monomial_lt_lengthCodeAt_after` package cannot exist for
the concrete `rightConjElim.minCheckedCodeSize` carrier, because that carrier is
already polynomially bounded by the lengths of the two component proof families.
-/
theorem singletonMonomialLowerBound_conjSource_obligation_impossible
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (thresholdOfMonomial : Nat → Nat → Nat)
    (monomial_lt_lengthCodeAt_after :
      ∀ coeff degree n : Nat,
        thresholdOfMonomial coeff degree ≤ n →
          coeff * (n + 1) ^ degree <
            ((left_family.conjIntro right_family)
              |>.rightConjElim
              |>.minCheckedCodeSize n)) :
    False :=
  monomialDomination_impossible_of_polynomial_bound
    (fun n : Nat =>
      ((left_family.conjIntro right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize n))
    (conjRightMinCheckedCodeSize_polynomial_of_component_polynomial
      left_family right_family left_length_polynomial right_length_polynomial)
    thresholdOfMonomial
    monomial_lt_lengthCodeAt_after

/--
Self-collision audit for the old `eventually_strict_length` shape on the current
conjunction-source coordinate.

If `lengthCodeAt` is definitionally the current conjunction-source
`minCheckedCodeSize`, then the component-polynomial hypotheses make
`lengthCodeAt` polynomially bounded.  Applying an
`eventually_strict_length` assumption to `U = lengthCodeAt` would force
eventually `lengthCodeAt m < lengthCodeAt m`, which is impossible at `atTop`.

This does not refute a genuine Pudlak lower bound on a different hard family.
It only proves that the present `conj-source` checked-length coordinate cannot
be the super-polynomial lower-bound carrier.
-/
theorem eventuallyStrictLength_conjSource_impossible
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (eventually_strict_length :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∀ᶠ m in atTop, U m < (lengthCodeAt m : Real))
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length)) :
    False := by
  have hpoly_conj :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real
          (fun m : Nat =>
            ((left_family.conjIntro right_family)
              |>.rightConjElim
              |>.minCheckedCodeSize m))) :=
    conjRightMinCheckedCodeSize_polynomial_of_component_polynomial
      left_family right_family left_length_polynomial right_length_polynomial
  have hpoly_lengthCodeAt :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real lengthCodeAt) := by
    exact _root_.is_polynomial_bound_of_le
      (g := _root_.MiniHilbert.nat_bound_as_real
        (fun m : Nat =>
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m)))
      (by
        intro m
        rw [_root_.MiniHilbert.nat_bound_as_real,
          _root_.MiniHilbert.nat_bound_as_real,
          lengthCodeAt_eq_conj_source m])
      hpoly_conj
  have hstrict :=
    eventually_strict_length
      (_root_.MiniHilbert.nat_bound_as_real lengthCodeAt)
      hpoly_lengthCodeAt
  have hfalse : ∀ᶠ _m in (atTop : Filter Nat), False :=
    hstrict.mono (by
      intro m hm
      exact (lt_irrefl ((lengthCodeAt m : Nat) : Real))
        (by
          simp [_root_.MiniHilbert.nat_bound_as_real] at hm))
  rw [Filter.eventually_false_iff_eq_bot] at hfalse
  exact False.elim (atTop_neBot.ne hfalse)

/--
Positive replacement target.

The current project already has a coherent route once the lower-bound carrier is
the actual PA proof length of the theorem-5 power-bound family.  A computable
finite-search/no-small-code core gives a search-gap certificate: for every
polynomial upper `U` and every requested lower cutoff `N`, it computes a witness
`w >= N` with `U w < actualProofLengthMeasured scale_data w`.

This is weaker than a tail statement `forall n >= threshold`, but it is exactly
what the generic collision core needs against an eventual upper bound.
-/
theorem actualProofLength_searchGap_candidateCarrier
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured core.scale_data)) ∧
      ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        U (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
            |>.gap_for_polynomial_upper U hU).witness N) <
          actualProofLengthMeasured core.scale_data
            (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
              |>.gap_for_polynomial_upper U hU).witness N) := by
  refine ⟨⟨actualProofLengthGapOfComputableFiniteSearchNoSmallCore core⟩, ?_⟩
  intro U hU N
  exact actualProofLengthGapOfComputableFiniteSearchNoSmallCore_strict_at_witness
    core U hU N

/--
Lower-level construction audit.

The objects `checker`, `enumeration`, `extractor`, and `exactness` are not Lean
kernel axioms.  They are the next-layer project certificates.  Once they are
supplied, Lean constructs the computable finite-search/no-small-code core used
by `actualProofLength_searchGap_candidateCarrier`.
-/
theorem checkerExtractorExactness_to_computableNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  ⟨extractor.toComputableFiniteSearchNoSmallCore exactness⟩

/--
Same lower-level construction, but pushed directly to the search-gap carrier.
This is the clean replacement for the impossible conjunction-source
tail-growth route: after `extractor` and proof-length `exactness` are supplied,
the actual PA proof length has the required search-witness gap.
-/
theorem checkerExtractorExactness_to_actualProofLength_searchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    let core := extractor.toComputableFiniteSearchNoSmallCore exactness
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured core.scale_data)) ∧
      ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        U (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
            |>.gap_for_polynomial_upper U hU).witness N) <
          actualProofLengthMeasured core.scale_data
            (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
              |>.gap_for_polynomial_upper U hU).witness N) := by
  exact actualProofLength_searchGap_candidateCarrier
    (extractor.toComputableFiniteSearchNoSmallCore exactness)

/--
The constant-piece replacement for the old project-level transfer inputs.

This does not make the inputs into Lean axioms.  It records the lower-level
contract: the same `extractor + exactness`, together with constant-cost
projection data, simultaneously supplies the no-small-code core and the
computable project-gap transfer.
-/
theorem constantPieces_feed_core_and_gapTransfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} ∧
      Nonempty
        (InternalPudlakTheorem5ComputableProjectGapTransfer
          scale_data checker.toProofCodeSemantics
          enumeration.toSmallCodeSearch) :=
  extractor.same_constant_pieces_feed_checker_extractor_core_and_gap_transfer
    exactness strengthened_to_partial partial_to_graft

/--
Month 11-12 checker handoff audit.

If a `PAHilbertCheckerExactnessCore` is supplied, Lean projects it to the
theorem-5 computable finite-search/no-small-code core, and therefore to the
actual-proof-length search-gap carrier.  The important qualification is that
this theorem is conditional on the supplied `PAHilbertCheckerExactnessCore`; it
does not claim that the exactness core has already been constructed from no
project-level assumptions.
-/
theorem paHilbertCheckerExactnessCore_to_actualProofLength_searchGap
    (core : PAHilbertCheckerExactnessCore.{q}) :
    let noSmallCore :=
      PAHilbertCheckerExactnessCore_to_InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
        core
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured noSmallCore.scale_data)) ∧
      ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        U (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore noSmallCore)
            |>.gap_for_polynomial_upper U hU).witness N) <
          actualProofLengthMeasured noSmallCore.scale_data
            (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore noSmallCore)
              |>.gap_for_polynomial_upper U hU).witness N) := by
  exact actualProofLength_searchGap_candidateCarrier
    (PAHilbertCheckerExactnessCore_to_InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
      core)

end SondowProjectBigNGrowthObligationAudit
end SondowMainCheckedCodeBridge
