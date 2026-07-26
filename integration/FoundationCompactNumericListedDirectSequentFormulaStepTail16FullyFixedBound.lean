import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail17FullyFixedBound

/-! # Fully fixed closed tail 16--21 of one sequent-formula step -/

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
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedRowParserLeaves

noncomputable def compactSequentFormulaStepTail16FullyFixedResultOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    CompactSequentFormulaStepFixedResult
      (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail16FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row)
      (compactSequentFormulaStepTail16FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
  let rowParser :=
    compactSequentFormulaStepTail16FixedRowParserLeavesOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
      hgraph
  let tail17Result :=
    compactSequentFormulaStepTail17FullyFixedResultOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
      hgraph
  let tail17 := tail17Result.bound
  let syntaxResource :=
    compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount row
  have hleftCode :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      rowParser.current.proof
  have hleftLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16CurrentFormula tokenTable width tokenCount
          row)).length <=
        FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds.compactSequentFormulaStepNatListRowsPayloadPolynomial
          tokenTable width tokenCount := by
    simpa only [compactSequentFormulaStepTail16CurrentFormula] using
      hleftCode.trans rowParser.current.payloadLength_le
  have hrightLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail17Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        compactSequentFormulaStepTail17FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount row :=
    tail17Result.codeLength_le
  have hleftSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16CurrentFormula tokenTable width tokenCount
          row)).length <= syntaxResource := hleftLeaf.trans (by
    unfold syntaxResource
    rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
    omega)
  have hrightSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail17Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    hrightLeaf.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail17FullyFixedCodePolynomial
        compactSequentFormulaStepTail18FullyFixedCodePolynomial
        compactSequentFormulaStepTail19FullyFixedCodePolynomial
      omega)
  have hraw := binaryFormulaCode_and_length_le_local
    (compactSequentFormulaStepTail16CurrentFormula tokenTable width tokenCount row)
    (compactSequentFormulaStepTail17Formula tokenTable width tokenCount suffixCount
      valueCount row)
  have hconjunctionCode :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        compactSequentFormulaStepTail16FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount row := by
    unfold compactSequentFormulaStepTail16Formula
      compactSequentFormulaStepTail16FullyFixedCodePolynomial
    omega
  have hconjunctionSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    hconjunctionCode.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail16FullyFixedCodePolynomial
        compactSequentFormulaStepTail17FullyFixedCodePolynomial
        compactSequentFormulaStepTail18FullyFixedCodePolynomial
        compactSequentFormulaStepTail19FullyFixedCodePolynomial
      omega)
  let bound : ClosedDirectFormulaBound
      (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail16FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
    simpa only [compactSequentFormulaStepTail16Formula,
      compactSequentFormulaStepTail16CurrentFormula,
      compactSequentFormulaStepTail16FullyFixedPayloadPolynomial,
      syntaxResource] using
      compactSequentFormulaStepFixedClosedConjunction rowParser.current tail17
        syntaxResource hleftSyntax hrightSyntax hconjunctionSyntax
  exact { bound := bound, codeLength_le := hconjunctionCode }

noncomputable def
    compactSequentFormulaStepTail16FullyFixedEmptyBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ClosedDirectFormulaBound
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount row)
      (compactSequentFormulaStepTail16FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
  rw [<- compactSequentFormulaStepTail16Formula_eq_direct]
  exact (compactSequentFormulaStepTail16FullyFixedResultOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
    hgraph).bound

#print axioms
  compactSequentFormulaStepTail16FullyFixedEmptyBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
