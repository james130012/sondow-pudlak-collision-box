import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-! # Generic transparent payload equation for a hybrid bounded universal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridBoundedUniversalTransparentPayload

open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationTermCompiler

noncomputable def hybridBoundedUniversalTransparentPayloadEnvelope
    (valuation : Nat -> Nat) (boundSource : ValuationTerm)
    (body : ArithmeticSemiformula Nat 1)
    (branches : CheckedHybridValuationUniversalBranches valuation body
      (termValue valuation boundSource)) : Nat :=
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundSource) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation boundSource
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (hybridBranchesStructuralPayloadEnvelope bound outerVariables branches)
  compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound
    (Rew.bShift boundSource) body
    (compileShiftedBoundEqualityPayloadResource valuation outerVariables
      boundSource)
    branchResource

theorem hybridBoundedUniversal_structuralPayload_eq_transparent
    (valuation : Nat -> Nat) (boundSource : ValuationTerm)
    (body : ArithmeticSemiformula Nat 1)
    (branches : CheckedHybridValuationUniversalBranches valuation body
      (termValue valuation boundSource)) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
          boundSource body branches) =
      hybridBoundedUniversalTransparentPayloadEnvelope valuation boundSource
        body branches := by
  rfl

#print axioms hybridBoundedUniversal_structuralPayload_eq_transparent

end FoundationCompactPAHybridBoundedUniversalTransparentPayload
