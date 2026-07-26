import integration.FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedOfGraph
import integration.FoundationCompactNumericListedDirectSequentFormulaStepParserFullyFixedBound

/-! # Fixed row and parser leaves 16--19 -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedRowParserLeaves

open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedOfGraph
open FoundationCompactNumericListedDirectSequentFormulaStepParserFullyFixedBound

structure CompactSequentFormulaStepTail16FixedRowParserLeaves
    (tokenTable width tokenCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) where
  current : ClosedDirectFormulaBound
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.current.start row.current.count row.current.finish
      row.current.boundary row.current.boundarySize)
    (compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount)
  next : ClosedDirectFormulaBound
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.next.start row.next.count row.next.finish row.next.boundary
      row.next.boundarySize)
    (compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount)
  value : ClosedDirectFormulaBound
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.value.start row.value.count row.value.finish row.value.boundary
      row.value.boundarySize)
    (compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount)
  parser : ClosedDirectFormulaBound
    (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
      row.parserStateBoundary row.current.boundary row.current.count
      row.next.boundary row.next.count row.parserTableWidth
      row.parserValueBound)
    (compactSequentFormulaStepParserFullyFixedPayloadPolynomial tokenTable width
      tokenCount row.parserStateBoundary
      (compactParserSyntaxExactFuel row.current.count + 1)
      row.current.boundary row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound)

noncomputable def compactSequentFormulaStepTail16FixedRowParserLeavesOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    CompactSequentFormulaStepTail16FixedRowParserLeaves tokenTable width
      tokenCount row := by
  let rowBounds :=
    compactSequentFormulaStepNatListRowsFullyFixedBoundsOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      row hgraph
  rcases hgraph with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hparser,
      _, _⟩
  let parserStateCount := compactParserSyntaxExactFuel row.current.count + 1
  have hparser' : CompactParserSyntaxExactBoundedGraph tokenTable width
      tokenCount row.parserStateBoundary parserStateCount
      row.current.boundary row.current.count row.next.boundary row.next.count
      1 0 0 row.parserTableWidth row.parserValueBound := by
    simpa [parserStateCount, compactParserSyntaxExactFuel] using hparser
  let parserBound :=
    compactSequentFormulaStepParserFullyFixedClosedDirectBoundOfGraph
      tokenTable width tokenCount row.parserStateBoundary parserStateCount
      row.current.boundary row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound hparser'
  exact
    { current := rowBounds.current
      next := rowBounds.next
      value := rowBounds.value
      parser :=
        { proof := parserBound.proof
          payloadLength_le := by
            simpa only [parserStateCount] using parserBound.payloadLength_le } }

#print axioms compactSequentFormulaStepTail16FixedRowParserLeavesOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedRowParserLeaves
