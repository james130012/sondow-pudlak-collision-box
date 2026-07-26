import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail14FullyFixedBound

/-! # Fully fixed open-index tail 13--21 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail13FullyFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepTail14FullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

noncomputable def compactSequentFormulaStepTail13FullyFixedResultOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound)
    (hrowIndex : rowIndex <= numericBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    CompactSequentFormulaStepAtValuationFixedResult
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepTail13Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail13FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
      (compactSequentFormulaStepTail13FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row) := by
  let valuation := extendValuation rowIndex zeroValuation
  let leaves := compactSequentFormulaStepOpenEntryFullyFixedLeavesOfData
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount rowIndex valueBound numericBound bitBound data hrowIndex
    htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let tail14 := compactSequentFormulaStepTail14FullyFixedResultOfData tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    valueBound numericBound bitBound data hrowIndex htokenCount hsuffixBoundary
    hvalueBoundary hvalueBound
  let syntaxResource :=
    compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound data.row
  have hleftConclusion :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      leaves.nextFinish.proof
  have hleftCode :
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm suffixBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
            (&0 : ValuationTerm))
          (shortBinaryNumeralTerm data.row.next.finish))).length <=
        compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
          tokenCount valueBound :=
    hleftConclusion.trans leaves.nextFinish.payloadLength_le
  have hleftVariables :
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
          (&0 : ValuationTerm))
        (shortBinaryNumeralTerm data.row.next.finish)).freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      compactSequentFormulaStepIndexSecondSuccessorTermAtValuation_freeVariables_subset_singleton
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hvaluation : valuation 0 <= numericBound := by
    simpa only [valuation, extendValuation_zero] using hrowIndex
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial
    omega
  have hcontextEnvelope :
      FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
          1 numericBound (binaryTermCode (&0 : ValuationTerm)).length <=
        syntaxResource := by
    unfold syntaxResource
      compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial
      compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
    omega
  have hcodeEnvelope :
      compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
          tokenCount valueBound +
        compactSequentFormulaStepTail14FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource
    rw [compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial]
    unfold compactSequentFormulaStepTail10FullyFixedCodePolynomial
      compactSequentFormulaStepTail11FullyFixedCodePolynomial
      compactSequentFormulaStepTail12FullyFixedCodePolynomial
      compactSequentFormulaStepTail13FullyFixedCodePolynomial
    omega
  let result := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.nextFinish tail14 hleftCode hleftVariables hvaluation hpositive
    hcontextEnvelope hcodeEnvelope
  simpa only [compactSequentFormulaStepTail13Formula,
    compactSequentFormulaStepTail13FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail13FullyFixedCodePolynomial,
    syntaxResource] using result

#print axioms compactSequentFormulaStepTail13FullyFixedResultOfData

end FoundationCompactNumericListedDirectSequentFormulaStepTail13FullyFixedBound
