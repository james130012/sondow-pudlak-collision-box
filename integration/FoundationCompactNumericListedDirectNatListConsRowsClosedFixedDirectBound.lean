import integration.FoundationCompactNumericListedDirectNatListConsRowsClosedFixedBound
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

/-! # Fixed empty-context direct bound for natural-list cons rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 140000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsClosedFixedDirectBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsClosedCertificate
open FoundationCompactNumericListedDirectNatListConsRowsClosedFixedBound
open FoundationCompactNumericListedDirectNatListConsRowsClosedFormulaClosed
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

noncomputable def compactAdditiveNatListConsRowsClosedFixedDirectBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htargetCount : targetCount <= numericBound)
    (hhead : head <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    FixedClosedDirectFormulaBound
      (compactAdditiveNatListConsRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head)
      (natListConsRowsClosedFullyFixedPayloadPolynomial numericBound bitBound)
      (natListConsRowsClosedFullyFixedPayloadPolynomial numericBound
        bitBound) := by
  let formula := compactAdditiveNatListConsRowsClosedFormula tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount head
  let certificate := compactAdditiveNatListConsRowsClosedCertificate tokenTable
    width tokenCount sourceBoundary sourceCount targetBoundary targetCount head
    hcount headData tailRows
  have hstructural : hybridFormulaStructuralPayloadBound certificate <=
      natListConsRowsClosedFullyFixedPayloadPolynomial numericBound
        bitBound := by
    dsimp only [certificate]
    exact compactAdditiveNatListConsRowsClosedCertificate_payload_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head numericBound bitBound hwidth htokenCount htargetCount
      hhead htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize hcount headData tailRows
  have hpayload : certificate.compile.payloadLength <=
      natListConsRowsClosedFullyFixedPayloadPolynomial numericBound
        bitBound :=
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      hstructural
  have hclosed : formula.freeVariables = ∅ := by
    dsimp only [formula]
    exact compactAdditiveNatListConsRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head
  have hcontext : valuationContext formula.freeVariables
      natListConsRowsTailUniversalZeroValuation =
        (∅ : Finset ValuationFormula) := by
    rw [hclosed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext certificate.compile
  have hproof : proof.payloadLength <=
      natListConsRowsClosedFullyFixedPayloadPolynomial numericBound
        bitBound := by
    dsimp only [proof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hpayload
  exact fixedClosedDirectFormulaBoundOfEmptyProof proof _ hproof hclosed

#print axioms compactAdditiveNatListConsRowsClosedFixedDirectBound

end FoundationCompactNumericListedDirectNatListConsRowsClosedFixedDirectBound
