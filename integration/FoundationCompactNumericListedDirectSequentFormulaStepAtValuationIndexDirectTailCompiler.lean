import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompilerCore

/-! # Closed conjuncts 16--21 of the open-index sequent-step compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport

def compactSequentFormulaStepDirectTail16AtValuationIndex
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.current.start row.current.count row.current.finish
      row.current.boundary row.current.boundarySize ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.next.start row.next.count row.next.finish row.next.boundary
      row.next.boundarySize ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.value.start row.value.count row.value.finish row.value.boundary
      row.value.boundarySize ⋏
  (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
      row.parserStateBoundary row.current.boundary
      row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound ⋏
  (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
      row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count
      row.current.start row.current.finish row.current.count ⋏
    “!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1”))))

noncomputable def
    compactSequentFormulaStepDirectTail16AtValuationIndexBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ExactContextBoundedProof
      (extendValuation rowIndex
        FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation)
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount row) := by
  rcases hgraph with
    ⟨_, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _,
      hcurrentRows, hnextRows, hvalueRows,
      hparser, happend, hcount⟩
  let valuation := extendValuation rowIndex
    FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation
  let proof16 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepNatListWitnessRowsPublicBound tokenTable width
      tokenCount row.current.start row.current.count row.current.finish
      row.current.boundary row.current.boundarySize hcurrentRows)
  let proof17 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepNatListWitnessRowsPublicBound tokenTable width
      tokenCount row.next.start row.next.count row.next.finish
      row.next.boundary row.next.boundarySize hnextRows)
  let proof18 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepNatListWitnessRowsPublicBound tokenTable width
      tokenCount row.value.start row.value.count row.value.finish
      row.value.boundary row.value.boundarySize hvalueRows)
  let parserStateCount := compactParserSyntaxExactFuel row.current.count + 1
  have hparser' : CompactParserSyntaxExactBoundedGraph tokenTable width
      tokenCount row.parserStateBoundary parserStateCount
      row.current.boundary row.current.count row.next.boundary row.next.count
      1 0 0 row.parserTableWidth row.parserValueBound := by
    simpa [parserStateCount, compactParserSyntaxExactFuel] using hparser
  let parserBound := compactSequentFormulaStepParserClosedDirectBoundOfGraph
    tokenTable width tokenCount row.parserStateBoundary parserStateCount
    row.current.boundary row.current.count row.next.boundary row.next.count
    row.parserTableWidth row.parserValueBound hparser'
  let parserEmpty : EmptyContextBoundedProof
      (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
        row.parserStateBoundary row.current.boundary row.current.count
        row.next.boundary row.next.count row.parserTableWidth
        row.parserValueBound) :=
    { resource :=
        compactSequentFormulaStepParserClosedDirectPayloadEnvelope tokenTable
          width tokenCount row.parserStateBoundary parserStateCount
          row.current.boundary row.current.count row.next.boundary
          row.next.count row.parserTableWidth row.parserValueBound
      proof := parserBound.proof
      payloadLength_le := parserBound.payloadLength_le }
  let proof19 :=
    ExactContextBoundedProof.ofEmpty (valuation := valuation) parserEmpty
  let proof20 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepNatListAppendSlicesPublicBound tokenTable width
      tokenCount row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count row.current.start
      row.current.finish row.current.count happend)
  let proof21 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepSuccessorCountPublicBound suffixCount valueCount
      hcount)
  let tail20 := ExactContextBoundedProof.conjunction proof20 proof21
  let tail19 := ExactContextBoundedProof.conjunction proof19 tail20
  let tail18 := ExactContextBoundedProof.conjunction proof18 tail19
  let tail17 := ExactContextBoundedProof.conjunction proof17 tail18
  let assembled := ExactContextBoundedProof.conjunction proof16 tail17
  simpa only [compactSequentFormulaStepDirectTail16AtValuationIndex] using
    assembled

#print axioms
  compactSequentFormulaStepDirectTail16AtValuationIndexBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
