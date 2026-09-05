import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-! # Structural payload invariance under branch-index transport -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 60000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridBranchesStructuralPayloadTransport

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate

theorem hybridBranchesStructuralPayloadEnvelope_transport
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat) (body : ArithmeticSemiformula Nat 1)
    (sourceBound targetBound : Nat) (h : sourceBound = targetBound)
    (branches : CheckedHybridValuationUniversalBranches valuation body
      sourceBound) :
    hybridBranchesStructuralPayloadEnvelope totalBound outerVariables
        (h ▸ branches) =
      hybridBranchesStructuralPayloadEnvelope totalBound outerVariables
        branches := by
  subst targetBound
  rfl

#print axioms hybridBranchesStructuralPayloadEnvelope_transport

end FoundationCompactPAHybridBranchesStructuralPayloadTransport
