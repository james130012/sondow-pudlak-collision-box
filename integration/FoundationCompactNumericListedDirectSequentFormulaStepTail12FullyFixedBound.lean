import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail13FullyFixedBound

/-! # Fully fixed open-index tail 12--21 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail12FullyFixedBound

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
open FoundationCompactNumericListedDirectSequentFormulaStepTail13FullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

noncomputable def compactSequentFormulaStepTail12FullyFixedResultOfData
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
      (compactSequentFormulaStepTail12Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail12FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
      (compactSequentFormulaStepTail12FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row) := by
  let valuation := extendValuation rowIndex zeroValuation
  let leaves := compactSequentFormulaStepOpenEntryFullyFixedLeavesOfData
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount rowIndex valueBound numericBound bitBound data hrowIndex
    htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let tail13 := compactSequentFormulaStepTail13FullyFixedResultOfData tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    valueBound numericBound bitBound data hrowIndex htokenCount hsuffixBoundary
    hvalueBoundary hvalueBound
  let syntaxResource :=
    compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound data.row
  have hleftConclusion :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      leaves.nextStart.proof
  have hleftCode :
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm suffixBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (compactSequentFormulaStepIndexSuccessorTermAtValuation
            (&0 : ValuationTerm))
          (shortBinaryNumeralTerm data.row.next.start))).length <=
        compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
          tokenCount valueBound :=
    hleftConclusion.trans leaves.nextStart.payloadLength_le
  have hleftVariables :
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (compactSequentFormulaStepIndexSuccessorTermAtValuation
          (&0 : ValuationTerm))
        (shortBinaryNumeralTerm data.row.next.start)).freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      compactSequentFormulaStepIndexSuccessorTermAtValuation_freeVariables_subset_singleton
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
        compactSequentFormulaStepTail13FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row +
        (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource
    rw [compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial]
    unfold compactSequentFormulaStepTail10FullyFixedCodePolynomial
      compactSequentFormulaStepTail11FullyFixedCodePolynomial
      compactSequentFormulaStepTail12FullyFixedCodePolynomial
    omega
  let result := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.nextStart tail13 hleftCode hleftVariables hvaluation hpositive
    hcontextEnvelope hcodeEnvelope
  simpa only [compactSequentFormulaStepTail12Formula,
    compactSequentFormulaStepTail12FullyFixedPayloadPolynomial,
    compactSequentFormulaStepTail12FullyFixedCodePolynomial,
    syntaxResource] using result

#print axioms compactSequentFormulaStepTail12FullyFixedResultOfData

end FoundationCompactNumericListedDirectSequentFormulaStepTail12FullyFixedBound
