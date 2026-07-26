import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail19FullyFixedBound

/-! # Fully fixed closed tail 18--21 of one sequent-formula step -/

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

noncomputable def compactSequentFormulaStepTail18FullyFixedResultOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    CompactSequentFormulaStepFixedResult
      (compactSequentFormulaStepTail18Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail18FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row)
      (compactSequentFormulaStepTail18FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
  let rowParser :=
    compactSequentFormulaStepTail16FixedRowParserLeavesOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
      hgraph
  let tail19Result :=
    compactSequentFormulaStepTail19FullyFixedResultOfGraph tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    row hgraph
  let tail19 := tail19Result.bound
  let syntaxResource :=
    compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount row
  have hleftCode :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      rowParser.value.proof
  have hleftLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16ValueFormula tokenTable width tokenCount
          row)).length <=
        FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds.compactSequentFormulaStepNatListRowsPayloadPolynomial
          tokenTable width tokenCount := by
    simpa only [compactSequentFormulaStepTail16ValueFormula] using
      hleftCode.trans rowParser.value.payloadLength_le
  have hrightLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail19Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        compactSequentFormulaStepTail19FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount row := by
    exact tail19Result.codeLength_le
  have hleftSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16ValueFormula tokenTable width tokenCount
          row)).length <= syntaxResource := hleftLeaf.trans (by
    unfold syntaxResource
    rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
    omega)
  have hrightSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail19Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    hrightLeaf.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail19FullyFixedCodePolynomial
      omega)
  have hraw := binaryFormulaCode_and_length_le_local
    (compactSequentFormulaStepTail16ValueFormula tokenTable width tokenCount row)
    (compactSequentFormulaStepTail19Formula tokenTable width tokenCount suffixCount
      valueCount row)
  have hconjunctionCode :
      (binaryFormulaCode
        (compactSequentFormulaStepTail18Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        compactSequentFormulaStepTail18FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount row := by
    unfold compactSequentFormulaStepTail18Formula
      compactSequentFormulaStepTail18FullyFixedCodePolynomial
    omega
  have hconjunctionSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail18Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    hconjunctionCode.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail18FullyFixedCodePolynomial
        compactSequentFormulaStepTail19FullyFixedCodePolynomial
      omega)
  let bound : ClosedDirectFormulaBound
      (compactSequentFormulaStepTail18Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail18FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
    simpa only [compactSequentFormulaStepTail18Formula,
      compactSequentFormulaStepTail16ValueFormula,
      compactSequentFormulaStepTail18FullyFixedPayloadPolynomial,
      syntaxResource] using
      compactSequentFormulaStepFixedClosedConjunction rowParser.value tail19
        syntaxResource hleftSyntax hrightSyntax hconjunctionSyntax
  exact { bound := bound, codeLength_le := hconjunctionCode }

noncomputable def compactSequentFormulaStepTail18FullyFixedBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ClosedDirectFormulaBound
      (compactSequentFormulaStepTail18Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail18FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) :=
  (compactSequentFormulaStepTail18FullyFixedResultOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
    hgraph).bound

#print axioms compactSequentFormulaStepTail18FullyFixedBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
