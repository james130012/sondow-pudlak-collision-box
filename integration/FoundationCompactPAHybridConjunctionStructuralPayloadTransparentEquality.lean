import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Definitional transparency of hybrid conjunction payload
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 80000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds

theorem hybridFormulaStructuralPayloadBound_conjunction_eq_transparent
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate) =
      transparentHybridConjunctionPayloadEnvelope valuation left right
        (hybridFormulaStructuralPayloadBound leftCertificate)
        (hybridFormulaStructuralPayloadBound rightCertificate) := by
  rfl

#print axioms hybridFormulaStructuralPayloadBound_conjunction_eq_transparent

end FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
