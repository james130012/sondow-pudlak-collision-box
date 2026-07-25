import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-! # Formula-code sum bound for a singleton valuation context -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace FoundationCompactPAValuationContextSingletonCodeBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds

theorem valuationContext_formulaCodeSum_le_singleton
    (vars : Finset Nat) (valuation : Nat -> Nat) (numericBound : Nat)
    (hvariables : vars ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    formulaCodeSum (valuationContext vars valuation) <=
      valuationContextFormulaCodeSumEnvelope 1 numericBound
        (binaryTermCode (&0 : ValuationTerm)).length := by
  have hcard : vars.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall coordinate, coordinate ∈ vars ->
      valuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    have hsingleton := hvariables hcoordinate
    simp only [Finset.mem_singleton] at hsingleton
    subst coordinate
    exact hvaluation
  have htermCodes : forall coordinate, coordinate ∈ vars ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro coordinate hcoordinate
    have hsingleton := hvariables hcoordinate
    simp only [Finset.mem_singleton] at hsingleton
    subst coordinate
    exact le_rfl
  exact valuationContext_formulaCodeSum_le_uniform vars valuation 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes

#print axioms valuationContext_formulaCodeSum_le_singleton

end FoundationCompactPAValuationContextSingletonCodeBound
