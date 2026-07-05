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
