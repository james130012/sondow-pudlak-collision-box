import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds

/-! # Fully fixed open-index tail 15--21 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail15FullyFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationContextSingletonCodeBound
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail16AtValuationFullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources

noncomputable def compactSequentFormulaStepTail15FullyFixedResultOfData
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
      (compactSequentFormulaStepTail15Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail15FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
      (compactSequentFormulaStepTail15FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row) := by
  let valuation := extendValuation rowIndex zeroValuation
  let leaves := compactSequentFormulaStepOpenEntryFullyFixedLeavesOfData
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount rowIndex valueBound numericBound bitBound data hrowIndex
    htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let tail16 :=
    compactSequentFormulaStepTail16AtValuationFullyFixedBoundOfGraph valuation
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex data.row data.graph
  let tail16Result :=
    compactSequentFormulaStepTail16FullyFixedResultOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      data.row data.graph
  let syntaxResource :=
    compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound data.row
  have hleftConclusion :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      leaves.valueFinish.proof
  have hleftCode :
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm valueBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (compactSequentFormulaStepIndexSuccessorTermAtValuation
            (&0 : ValuationTerm))
          (shortBinaryNumeralTerm data.row.value.finish))).length <=
        compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
          tokenCount valueBound :=
    hleftConclusion.trans leaves.valueFinish.payloadLength_le
  have hrightCode :
      (binaryFormulaCode
        (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
          tokenCount suffixCount valueCount data.row)).length <=
        compactSequentFormulaStepTail16FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount data.row := by
    rw [<- compactSequentFormulaStepTail16Formula_eq_direct]
    exact tail16Result.codeLength_le
  have hleftVariables :
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm valueBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (compactSequentFormulaStepIndexSuccessorTermAtValuation
          (&0 : ValuationTerm))
        (shortBinaryNumeralTerm data.row.value.finish)).freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      compactSequentFormulaStepIndexSuccessorTermAtValuation_freeVariables_subset_singleton
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hrightClosed :
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount data.row).freeVariables = ∅ := by
    rw [<- compactSequentFormulaStepTail16Formula_eq_direct]
    exact compactSequentFormulaStepTail16Formula_freeVariables_eq_empty tokenTable
      width tokenCount suffixCount valueCount data.row
  have hrightVariables :
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount data.row).freeVariables ⊆ {0} := by
    rw [hrightClosed]
    simp
  have hvariables :
      (compactSequentFormulaStepTail15Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount
        data.row).freeVariables ⊆ {0} := by
    unfold compactSequentFormulaStepTail15Formula
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hleftVariables hrightVariables
  have hrawCode := binaryFormulaCode_and_length_le_local
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm data.row.value.finish))
    (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
      tokenCount suffixCount valueCount data.row)
  have hconjunctionCode :
      (binaryFormulaCode
        (compactSequentFormulaStepTail15Formula tokenTable width tokenCount
          suffixBoundary suffixCount valueBoundary valueCount data.row)).length <=
        compactSequentFormulaStepTail15FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row := by
    unfold compactSequentFormulaStepTail15Formula
      compactSequentFormulaStepTail15FullyFixedCodePolynomial
    omega
  have hleftSyntax :
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm valueBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (compactSequentFormulaStepIndexSuccessorTermAtValuation
            (&0 : ValuationTerm))
          (shortBinaryNumeralTerm data.row.value.finish))).length <=
        syntaxResource := hleftCode.trans (by
    unfold syntaxResource
    rw [compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial]
    unfold compactSequentFormulaStepTail10FullyFixedCodePolynomial
      compactSequentFormulaStepTail11FullyFixedCodePolynomial
      compactSequentFormulaStepTail12FullyFixedCodePolynomial
      compactSequentFormulaStepTail13FullyFixedCodePolynomial
      compactSequentFormulaStepTail14FullyFixedCodePolynomial
      compactSequentFormulaStepTail15FullyFixedCodePolynomial
    omega)
  have hrightSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
          tokenCount suffixCount valueCount data.row)).length <= syntaxResource :=
    hrightCode.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail10FullyFixedCodePolynomial
        compactSequentFormulaStepTail11FullyFixedCodePolynomial
        compactSequentFormulaStepTail12FullyFixedCodePolynomial
        compactSequentFormulaStepTail13FullyFixedCodePolynomial
        compactSequentFormulaStepTail14FullyFixedCodePolynomial
        compactSequentFormulaStepTail15FullyFixedCodePolynomial
      omega)
  have hconjunctionSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail15Formula tokenTable width tokenCount
          suffixBoundary suffixCount valueBoundary valueCount data.row)).length <=
        syntaxResource := hconjunctionCode.trans (by
    unfold syntaxResource
    rw [compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial]
    unfold compactSequentFormulaStepTail10FullyFixedCodePolynomial
      compactSequentFormulaStepTail11FullyFixedCodePolynomial
      compactSequentFormulaStepTail12FullyFixedCodePolynomial
      compactSequentFormulaStepTail13FullyFixedCodePolynomial
      compactSequentFormulaStepTail14FullyFixedCodePolynomial
    omega)
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial
    omega
  have hvaluation : valuation 0 <= numericBound := by
    simpa only [valuation, extendValuation_zero] using hrowIndex
  have hcontextBase := valuationContext_formulaCodeSum_le_singleton
    (compactSequentFormulaStepTail15Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount data.row).freeVariables
    valuation numericBound hvariables hvaluation
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext
            (compactSequentFormulaStepTail15Formula tokenTable width tokenCount
              suffixBoundary suffixCount valueBoundary valueCount
              data.row).freeVariables valuation) <= syntaxResource :=
    hcontextBase.trans (by
      unfold syntaxResource
        compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial
        compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
      omega)
  let bound := compactSequentFormulaStepAtValuationFixedConjunction
    leaves.valueFinish tail16 syntaxResource hpositive hcontext hleftSyntax
    hrightSyntax hconjunctionSyntax
  refine ⟨?_, hconjunctionCode, hvariables⟩
  simpa only [compactSequentFormulaStepTail15Formula,
    compactSequentFormulaStepTail15FullyFixedPayloadPolynomial,
    syntaxResource] using bound

#print axioms compactSequentFormulaStepTail15FullyFixedResultOfData

end FoundationCompactNumericListedDirectSequentFormulaStepTail15FullyFixedBound
