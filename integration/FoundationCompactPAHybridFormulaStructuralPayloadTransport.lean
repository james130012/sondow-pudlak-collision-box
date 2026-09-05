import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-! # Structural payload invariance under valuation-index transport -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 60000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridFormulaStructuralPayloadTransport

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler

theorem hybridFormulaStructuralPayloadBound_valuation_transport
    (sourceValuation targetValuation : Nat -> Nat)
    (h : sourceValuation = targetValuation) (formula : ValuationFormula)
    (certificate : CheckedHybridValuationBoundedFormulaCertificate
      sourceValuation formula) :
    hybridFormulaStructuralPayloadBound (h ▸ certificate) =
      hybridFormulaStructuralPayloadBound certificate := by
  subst targetValuation
  rfl

#print axioms hybridFormulaStructuralPayloadBound_valuation_transport

end FoundationCompactPAHybridFormulaStructuralPayloadTransport
