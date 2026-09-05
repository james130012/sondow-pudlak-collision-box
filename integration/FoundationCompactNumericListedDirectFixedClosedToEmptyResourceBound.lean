import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

/-! # Transport fixed closed direct bounds to empty-context resource bounds -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

noncomputable def fixedResourceEmptyContextProofOfClosedDirectFormulaBound
    {formula : ValuationFormula} {resource : Nat}
    (bound : ClosedDirectFormulaBound formula resource) :
    FixedResourceEmptyContextProof formula resource :=
  { proof := bound.proof
    payloadLength_le := bound.payloadLength_le }

opaque fixedResourceEmptyContextProofOfFixedClosedDirectFormulaBound
    {formula : ValuationFormula} {payloadResource codeResource : Nat}
    (bound : FixedClosedDirectFormulaBound formula payloadResource
      codeResource) :
    FixedResourceEmptyContextProof formula payloadResource := by
  have hcontext : valuationContext formula.freeVariables
      parserFixedZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [bound.closed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext bound.proof
  refine { proof := proof, payloadLength_le := ?_ }
  dsimp only [proof]
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact bound.payloadLength_le

#print axioms fixedResourceEmptyContextProofOfClosedDirectFormulaBound
#print axioms fixedResourceEmptyContextProofOfFixedClosedDirectFormulaBound

end FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound
