import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedResources

/-! # Fully fixed closed tail 19--21 of one sequent-formula step -/

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
open FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedOfGraph

noncomputable def compactSequentFormulaStepTail19FullyFixedResultOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    CompactSequentFormulaStepFixedResult
      (compactSequentFormulaStepTail19Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail19FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row)
      (compactSequentFormulaStepTail19FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
  let rowParser :=
    compactSequentFormulaStepTail16FixedRowParserLeavesOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
      hgraph
  let tail20 := compactSequentFormulaStepTail20FullyFixedBoundOfGraph tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    row hgraph
  let syntaxResource :=
    compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount row
  have hleftCode :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      rowParser.parser.proof
  have hrightCode :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      tail20.proof
  have hleftPayload := rowParser.parser.payloadLength_le
  have hrightPayload := tail20.payloadLength_le
  have hleftLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16ParserFormula tokenTable width tokenCount
          row)).length <=
        FoundationCompactNumericListedDirectSequentFormulaStepParserFullyFixedBound.compactSequentFormulaStepParserFullyFixedPayloadPolynomial
          tokenTable width tokenCount row.parserStateBoundary
          (FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactFuel
            row.current.count + 1)
          row.current.boundary row.current.count row.next.boundary row.next.count
          row.parserTableWidth row.parserValueBound := by
    simpa only [compactSequentFormulaStepTail16ParserFormula] using
      hleftCode.trans hleftPayload
  have hrightLeaf :
      (binaryFormulaCode
        (compactSequentFormulaStepTail20Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedBound.compactSequentFormulaStepTail20FullyFixedPayloadPolynomial
          tokenTable width tokenCount suffixCount valueCount row := by
    simpa only [compactSequentFormulaStepTail20Formula] using
      hrightCode.trans hrightPayload
  have hleftSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16ParserFormula tokenTable width tokenCount
          row)).length <= syntaxResource := by
    exact hleftLeaf.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      omega)
  have hrightSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail20Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource := by
    exact hrightLeaf.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      omega)
  have hraw := binaryFormulaCode_and_length_le_local
    (compactSequentFormulaStepTail16ParserFormula tokenTable width tokenCount row)
    (compactSequentFormulaStepTail20Formula tokenTable width tokenCount suffixCount
      valueCount row)
  have hconjunctionCode :
      (binaryFormulaCode
        (compactSequentFormulaStepTail19Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
        compactSequentFormulaStepTail19FullyFixedCodePolynomial tokenTable width
          tokenCount suffixCount valueCount row := by
    unfold compactSequentFormulaStepTail19Formula
      compactSequentFormulaStepTail19FullyFixedCodePolynomial
    omega
  have hconjunctionSyntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail19Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    hconjunctionCode.trans (by
      unfold syntaxResource
      rw [compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial]
      unfold compactSequentFormulaStepTail19FullyFixedCodePolynomial
      omega)
  let bound : ClosedDirectFormulaBound
      (compactSequentFormulaStepTail19Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail19FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
    simpa only [compactSequentFormulaStepTail19Formula,
      compactSequentFormulaStepTail16ParserFormula,
      compactSequentFormulaStepTail20Formula,
      compactSequentFormulaStepTail19FullyFixedPayloadPolynomial,
      syntaxResource] using
      compactSequentFormulaStepFixedClosedConjunction rowParser.parser tail20
        syntaxResource hleftSyntax hrightSyntax hconjunctionSyntax
  exact { bound := bound, codeLength_le := hconjunctionCode }

noncomputable def compactSequentFormulaStepTail19FullyFixedBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ClosedDirectFormulaBound
      (compactSequentFormulaStepTail19Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail19FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) :=
  (compactSequentFormulaStepTail19FullyFixedResultOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
    hgraph).bound

#print axioms compactSequentFormulaStepTail19FullyFixedBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
