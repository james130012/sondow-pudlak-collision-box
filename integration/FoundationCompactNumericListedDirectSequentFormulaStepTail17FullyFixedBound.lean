import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail18FullyFixedBound

/-! # Fully fixed closed tail 17--21 of one sequent-formula step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedRowParserLeaves

noncomputable def compactSequentFormulaStepTail17FullyFixedResultOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    CompactSequentFormulaStepFixedResult
      (compactSequentFormulaStepTail17Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail17FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row)
      (compactSequentFormulaStepTail17FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
  let rowParser :=
    compactSequentFormulaStepTail16FixedRowParserLeavesOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
      hgraph
  let tail18Result :=
    compactSequentFormulaStepTail18FullyFixedResultOfGraph tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    row hgraph
  let tail18 := tail18Result.bound
  let syntaxResource :=
    compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount row
  have hleftCode :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      rowParser.next.proof
  have hleftLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16NextFormula tokenTable width tokenCount
          row)).length <=
        FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds.compactSequentFormulaStepNatListRowsPayloadPolynomial
          tokenTable width tokenCount := by
    simpa only [compactSequentFormulaStepTail16NextFormula] using
      hleftCode.trans rowParser.next.payloadLength_le
  have hrightLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail18Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        compactSequentFormulaStepTail18FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount row := by
    exact tail18Result.codeLength_le
  have hleftSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16NextFormula tokenTable width tokenCount
          row)).length <= syntaxResource := hleftLeaf.trans (by
    unfold syntaxResource
    rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
    omega)
  have hrightSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail18Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    hrightLeaf.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail18FullyFixedCodePolynomial
        compactSequentFormulaStepTail19FullyFixedCodePolynomial
      omega)
  have hraw := binaryFormulaCode_and_length_le_local
    (compactSequentFormulaStepTail16NextFormula tokenTable width tokenCount row)
    (compactSequentFormulaStepTail18Formula tokenTable width tokenCount suffixCount
      valueCount row)
  have hconjunctionCode :
      (binaryFormulaCode
        (compactSequentFormulaStepTail17Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        compactSequentFormulaStepTail17FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount row := by
    unfold compactSequentFormulaStepTail17Formula
      compactSequentFormulaStepTail17FullyFixedCodePolynomial
    omega
  have hconjunctionSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail17Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    hconjunctionCode.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail17FullyFixedCodePolynomial
        compactSequentFormulaStepTail18FullyFixedCodePolynomial
        compactSequentFormulaStepTail19FullyFixedCodePolynomial
      omega)
  let bound : ClosedDirectFormulaBound
      (compactSequentFormulaStepTail17Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail17FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
    simpa only [compactSequentFormulaStepTail17Formula,
      compactSequentFormulaStepTail16NextFormula,
      compactSequentFormulaStepTail17FullyFixedPayloadPolynomial,
      syntaxResource] using
      compactSequentFormulaStepFixedClosedConjunction rowParser.next tail18
        syntaxResource hleftSyntax hrightSyntax hconjunctionSyntax
  exact { bound := bound, codeLength_le := hconjunctionCode }

noncomputable def compactSequentFormulaStepTail17FullyFixedBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ClosedDirectFormulaBound
      (compactSequentFormulaStepTail17Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail17FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) :=
  (compactSequentFormulaStepTail17FullyFixedResultOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
    hgraph).bound

#print axioms compactSequentFormulaStepTail17FullyFixedBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
