import integration.SondowProjectMonth11Month12HardResidualElimination

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth11Month12ActualTransportExactness

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth11Month12HardResidualElimination

/-- Actual proof-length transport only.  This file deliberately does not state
or use any equality between checked proof-code length and the project scale. -/
theorem your_actual_transport_theorem
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    ActualProofLengthGapTransportBlocker checker where
  checked_eq_actual := by
    intro n
    simpa [actualProofLengthMeasured,
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (family.proof_length_eq_minProofCodeSizeAt n).symm

/-! ## Proof-length-free project-length transport -/

/-- The same checker raw-code family measured by
`ProofCodeSemantics.projectLength`, without referring to root `proof_length`.
This is the proof-length-free replacement target that sits next to the actual
transport theorem above. -/
noncomputable def checkerProjectLengthMeasured
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data)
    (fallback : _root_.FormulaCode → Nat) :
    Nat → Real :=
  fun n =>
    checker.toProofCodeSemantics.projectLength fallback
      (scale_data.powerBoundRawCode n)

/-- On the theorem-5 raw-code family, the checker project-length semantics is
exactly the checked minimum proof-code-size measurement. -/
theorem checkerProjectLengthMeasured_eq_checked
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat) (n : Nat) :
    checkerProjectLengthMeasured scale_data checker fallback n =
      month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics n := by
  rw [checkerProjectLengthMeasured,
    _root_.ProofCodeSemantics.projectLength_eq_minProofCodeSize]
  rfl

/-- Exact residual equivalence: on the theorem-5 raw-code family, transporting
the checker `projectLength` measurement to the actual root `proof_length`
measurement is the same obligation as transporting the checked
`minProofCodeSize` measurement to actual proof length.  This keeps the final
proof-length residual as a single pointwise exactness theorem. -/
theorem checkerProjectLength_eq_actual_iff_checked_eq_actual
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat) :
    (∀ n : Nat,
      checkerProjectLengthMeasured scale_data checker fallback n =
        actualProofLengthMeasured scale_data n) ↔
      Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data checker.toProofCodeSemantics := by
  constructor
  · intro h
    exact
      { checked_eq_actual := by
          intro n
          exact
            (checkerProjectLengthMeasured_eq_checked
              (scale_data := scale_data) (checker := checker)
              fallback n).symm.trans (h n) }
  · intro bridge n
    exact
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n).trans
        (bridge.checked_eq_actual n)

/-- Forward form of the exact residual equivalence, useful when the
proof-length calibration is supplied as checked `minProofCodeSize` exactness. -/
theorem checkerProjectLength_eq_actual_of_checked_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data checker.toProofCodeSemantics)
    (n : Nat) :
    checkerProjectLengthMeasured scale_data checker fallback n =
      actualProofLengthMeasured scale_data n :=
  (checkerProjectLength_eq_actual_iff_checked_eq_actual
    (scale_data := scale_data) (checker := checker) fallback).2 bridge n

/-- Construct the computable search gap for the checker project-length route
directly from the finite-search rejection extractor.  No actual
`proof_length` transport is used here. -/
def checkerProjectLengthGapConstructor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration) :
    ComputableSearchGapCertificate
      (checkerProjectLengthMeasured scale_data checker fallback) :=
  transportComputableSearchGap
    (fun n =>
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n).symm)
    (checked_minProofCodeSize_gap_constructor extractor)

theorem checkerProjectLengthGapConstructor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((checkerProjectLengthGapConstructor fallback extractor)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

/-- Checklist showing that the Month 11-12 finite-search artefacts already
produce a proof-length-free project-length gap, while the actual proof-length
route remains isolated in `your_actual_transport_theorem`. -/
structure CheckerProjectLengthTransportChecklist : Prop where
  projectLengthEqChecked :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ checker :
        InternalPudlakTheorem5CheckerSemantics.{0} scale_data,
        ∀ fallback : _root_.FormulaCode → Nat,
          ∀ n : Nat,
            checkerProjectLengthMeasured scale_data checker fallback n =
              month9_month10_checkedProofCodeMeasured
                scale_data checker.toProofCodeSemantics n
  finiteSearchGapAtProjectLength :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ checker :
        InternalPudlakTheorem5CheckerSemantics.{0} scale_data,
        ∀ enumeration :
          InternalPudlakTheorem5CheckerFiniteEnumeration checker,
          ∀ fallback : _root_.FormulaCode → Nat,
            ∀ extractor :
              InternalPudlakTheorem5CheckerComputableRejectionExtractor
                checker enumeration,
              Nonempty
                { projectGap : ComputableSearchGapCertificate
                    (checkerProjectLengthMeasured scale_data checker fallback) //
                  ∀ U : Nat → Real,
                    ∀ hU : _root_.is_polynomial_bound U,
                      ∀ N : Nat,
                        (projectGap.gap_for_polynomial_upper U hU).witness N =
                          extractor.witness U hU N }

theorem checker_project_length_transport_checklist :
    CheckerProjectLengthTransportChecklist where
  projectLengthEqChecked := by
    intro scale_data checker fallback n
    exact
      checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n
  finiteSearchGapAtProjectLength := by
    intro scale_data checker enumeration fallback extractor
    exact
      ⟨⟨checkerProjectLengthGapConstructor fallback extractor, by
        intro U hU N
        exact
          checkerProjectLengthGapConstructor_witness_eq
            fallback extractor U hU N⟩⟩

/-! ## Project-length direct collision endpoint -/

/-- Transport a checked upper provider to the checker project-length measured
function.  This keeps the upper side on the same object as the gap side. -/
def checkerProjectLengthUpperProviderOfChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    Month9Month10AbstractMeasuredUpperProvider
      (checkerProjectLengthMeasured scale_data checker fallback) :=
  Month9Month10AbstractMeasuredUpperProvider.transportEq
    (fun n =>
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n).symm)
    checked_upper

/-- Direct collision endpoint over the checker project-length semantics.  This
is the same proof-length-free measured route as the checked endpoint, expressed
through the concrete proof-code semantic replacement for root `proof_length`. -/
def checkerProjectLengthDirectEndpointOfCheckedUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured scale_data checker fallback) where
  gap := checkerProjectLengthGapConstructor fallback extractor
  upper_provider :=
    checkerProjectLengthUpperProviderOfChecked fallback checked_upper

theorem checkerProjectLengthDirectEndpoint_computed_n_eq_extractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper).computedCollisionNOfRationality hrat =
      extractor.witness
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality hrat).U
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).polynomial
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).upperN := by
  calc
    (checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper).computedCollisionNOfRationality
          hrat =
        (((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).gap).gap_for_polynomial_upper
          ((checkerProjectLengthDirectEndpointOfCheckedUpper
            fallback extractor checked_upper).upperTailOfRationality hrat).U
          ((checkerProjectLengthDirectEndpointOfCheckedUpper
            fallback extractor checked_upper).upperTailOfRationality
              hrat).polynomial).witness
          ((checkerProjectLengthDirectEndpointOfCheckedUpper
            fallback extractor checked_upper).upperTailOfRationality
              hrat).upperN :=
      (checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper).computedCollisionN_eq_searchGapWitness
          hrat
    _ = extractor.witness
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality hrat).U
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).polynomial
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).upperN := by
      exact
        checkerProjectLengthGapConstructor_witness_eq
          fallback extractor _ _ _

theorem checkerProjectLengthDirectEndpoint_computed_n_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (checkerProjectLengthDirectEndpointOfCheckedUpper
    fallback extractor checked_upper).computed_n_contradiction hrat

/-- Full same-object trace for the checker project-length route.  The computed
`n` is the finite-search witness selected by the rejection extractor, and both
inequalities are stated over the same checker project-length measurement.  The
last equality records that this object is definitionally transported from the
checked min-proof-code-size measurement, not from root `proof_length`. -/
theorem checkerProjectLengthDirectEndpoint_computedN_trace_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let endpoint :=
        checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper
      let upper := endpoint.upperTailOfRationality hrat
      let n := endpoint.computedCollisionNOfRationality hrat
      n = extractor.witness upper.U upper.polynomial upper.upperN ∧
        upper.upperN ≤ n ∧
          upper.U n <
              checkerProjectLengthMeasured scale_data checker fallback n ∧
            checkerProjectLengthMeasured scale_data checker fallback n ≤
                upper.U n ∧
              checkerProjectLengthMeasured scale_data checker fallback n =
                  month9_month10_checkedProofCodeMeasured
                    scale_data checker.toProofCodeSemantics n ∧
                False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  refine ⟨?_, ?_⟩
  · intro hrat
    let endpoint :=
      checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper
    let upper := endpoint.upperTailOfRationality hrat
    let n := endpoint.computedCollisionNOfRationality hrat
    have hn :
        n = extractor.witness upper.U upper.polynomial upper.upperN := by
      dsimp [n, upper, endpoint]
      exact
        checkerProjectLengthDirectEndpoint_computed_n_eq_extractorWitness
          fallback extractor checked_upper hrat
    have hge : upper.upperN ≤ n := by
      dsimp [n, upper, endpoint]
      exact
        (checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).computedCollisionN_ge_upperN hrat
    have hlower :
        upper.U n <
          checkerProjectLengthMeasured scale_data checker fallback n := by
      dsimp [n, upper, endpoint]
      exact
        (checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).lower_at_computedCollisionN hrat
    have hupper :
        checkerProjectLengthMeasured scale_data checker fallback n ≤
          upper.U n := by
      dsimp [n, upper, endpoint]
      exact
        (checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upper_at_computedCollisionN hrat
    have hchecked :
        checkerProjectLengthMeasured scale_data checker fallback n =
          month9_month10_checkedProofCodeMeasured
            scale_data checker.toProofCodeSemantics n :=
      checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n
    exact
      ⟨hn, ⟨hge, ⟨hlower, ⟨hupper, ⟨hchecked,
        (not_lt_of_ge hupper) hlower⟩⟩⟩⟩⟩
  · intro hrat
    exact
      checkerProjectLengthDirectEndpoint_computed_n_contradiction
        fallback extractor checked_upper hrat

/-- Under the single exact residual bridge, the same computable witness used by
the checker `projectLength` endpoint becomes an actual root-`proof_length`
collision witness.  This theorem does not create a new search procedure: it
audits that the computed `n` is preserved while only the measured function is
transported through the exactness bridge. -/
theorem checkerProjectLengthDirectEndpoint_actual_bridge_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data checker.toProofCodeSemantics) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let endpoint :=
        checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper
      let upper := endpoint.upperTailOfRationality hrat
      let n := endpoint.computedCollisionNOfRationality hrat
      n = extractor.witness upper.U upper.polynomial upper.upperN ∧
        upper.upperN ≤ n ∧
          upper.U n < actualProofLengthMeasured scale_data n ∧
            actualProofLengthMeasured scale_data n ≤ upper.U n ∧
              checkerProjectLengthMeasured scale_data checker fallback n =
                actualProofLengthMeasured scale_data n ∧
                False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  refine ⟨?_, ?_⟩
  · intro hrat
    let endpoint :=
      checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper
    let upper := endpoint.upperTailOfRationality hrat
    let n := endpoint.computedCollisionNOfRationality hrat
    have hn :
        n = extractor.witness upper.U upper.polynomial upper.upperN := by
      dsimp [n, upper, endpoint]
      exact
        checkerProjectLengthDirectEndpoint_computed_n_eq_extractorWitness
          fallback extractor checked_upper hrat
    have hge : upper.upperN ≤ n := by
      dsimp [n, upper, endpoint]
      exact endpoint.computedCollisionN_ge_upperN hrat
    have hproject_lower :
        upper.U n <
          checkerProjectLengthMeasured scale_data checker fallback n := by
      dsimp [n, upper, endpoint]
      exact endpoint.lower_at_computedCollisionN hrat
    have hproject_upper :
        checkerProjectLengthMeasured scale_data checker fallback n ≤
          upper.U n := by
      dsimp [n, upper, endpoint]
      exact endpoint.upper_at_computedCollisionN hrat
    have hactual :
        checkerProjectLengthMeasured scale_data checker fallback n =
          actualProofLengthMeasured scale_data n :=
      checkerProjectLength_eq_actual_of_checked_bridge
        fallback bridge n
    have hactual_lower :
        upper.U n < actualProofLengthMeasured scale_data n := by
      simpa [hactual] using hproject_lower
    have hactual_upper :
        actualProofLengthMeasured scale_data n ≤ upper.U n := by
      simpa [hactual] using hproject_upper
    exact
      ⟨hn, hge, hactual_lower, hactual_upper, hactual,
        (not_lt_of_ge hactual_upper) hactual_lower⟩
  · exact
      (checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper).not_rational

/-- Full finite-search lower-witness trace for the checker project-length
endpoint.  This is the proof-length-free concrete route: the computed collision
index is the rejection extractor's lower-search witness, and the same witness
carries the cutoff, candidate rejection, no-small proof-code fact, checked
minimum-size inequality, and final contradiction. -/
theorem checkerProjectLengthDirectEndpoint_full_lower_search_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper
    let upper := endpoint.upperTailOfRationality hrat
    let w :=
      extractor.computedLowerSearchWitness
        upper.U upper.polynomial upper.upperN
    endpoint.computedCollisionNOfRationality hrat = w.n ∧
      w.n = extractor.witness upper.U upper.polynomial upper.upperN ∧
      w.K = extractor.cutoff upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ w.n ∧
      upper.U w.n < (w.K : Real) ∧
      (∀ c : checker.toProofCodeSemantics.Code,
        c ∈ enumeration.toSmallCodeSearch.candidates w.n w.K →
          ¬ checker.toProofCodeSemantics.checks c
            (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : checker.toProofCodeSemantics.Code,
        checker.toProofCodeSemantics.checks c
          (scale_data.powerBoundRawCode w.n) →
          upper.U w.n < (checker.toProofCodeSemantics.size c : Real)) ∧
      (checker.toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
        upper.U w.n ∧
      upper.U w.n <
        checkerProjectLengthMeasured scale_data checker fallback w.n ∧
      checkerProjectLengthMeasured scale_data checker fallback w.n ≤
        upper.U w.n ∧
      False := by
  let endpoint :=
    checkerProjectLengthDirectEndpointOfCheckedUpper
      fallback extractor checked_upper
  let upper := endpoint.upperTailOfRationality hrat
  let w :=
    extractor.computedLowerSearchWitness
      upper.U upper.polynomial upper.upperN
  have hn_extractor :
      endpoint.computedCollisionNOfRationality hrat =
        extractor.witness upper.U upper.polynomial upper.upperN := by
    dsimp [endpoint, upper]
    exact
      checkerProjectLengthDirectEndpoint_computed_n_eq_extractorWitness
        fallback extractor checked_upper hrat
  have hw_n :
      w.n = extractor.witness upper.U upper.polynomial upper.upperN := by
    dsimp [w]
    rfl
  have hcomputed : endpoint.computedCollisionNOfRationality hrat = w.n :=
    hn_extractor.trans hw_n.symm
  have hlower :
      upper.U w.n <
        checkerProjectLengthMeasured scale_data checker fallback w.n := by
    simpa [hcomputed]
      using endpoint.lower_at_computedCollisionN hrat
  have hupper :
      checkerProjectLengthMeasured scale_data checker fallback w.n ≤
        upper.U w.n := by
    simpa [hcomputed]
      using endpoint.upper_at_computedCollisionN hrat
  exact
    ⟨hcomputed,
      hw_n,
      rfl,
      w.n_ge,
      w.cutoff_gt,
      w.rejects_candidates,
      w.no_small_at_n,
      w.minProofCodeSize_gt,
      hlower,
      hupper,
      (not_lt_of_ge hupper) hlower⟩

theorem checkerProjectLengthDirectEndpoint_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (checkerProjectLengthDirectEndpointOfCheckedUpper
    fallback extractor checked_upper).not_rational

end SondowProjectMonth11Month12ActualTransportExactness
end SondowMainCheckedCodeBridge
