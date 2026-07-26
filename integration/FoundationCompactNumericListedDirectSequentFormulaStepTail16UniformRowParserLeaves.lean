import integration.FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedOfGraph
import integration.FoundationCompactNumericListedDirectSequentFormulaStepParserUniformResourceBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

/-! # Row and parser leaves with one explicit public resource -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformRowParserLeaves

open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedOfGraph
open FoundationCompactNumericListedDirectSequentFormulaStepParserUniformResourceBound

def compactSequentFormulaStepParserUniformNumericBound
    (tokenTable width tokenCount valueBound : Nat) : Nat :=
  tokenTable + width + tokenCount + valueBound +
    (compactParserSyntaxExactFuel valueBound + 1) +
    (tokenCount + 1) * tokenCount + 2

def compactSequentFormulaStepParserUniformBitBound
    (tokenTable width tokenCount valueBound : Nat) : Nat :=
  let numericBound :=
    compactSequentFormulaStepParserUniformNumericBound tokenTable width
      tokenCount valueBound
  numericBound + Nat.size numericBound + 1

theorem compactParserSyntaxExactFuel_mono_public
    {small large : Nat} (h : small <= large) :
    compactParserSyntaxExactFuel small <=
      compactParserSyntaxExactFuel large := by
  unfold compactParserSyntaxExactFuel
  gcongr

structure CompactSequentFormulaStepTail16UniformRowParserLeaves
    (tokenTable width tokenCount valueBound : Nat)
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
    (compactSequentFormulaStepParserUniformPayloadPolynomial tokenCount
      valueBound
      (compactSequentFormulaStepParserUniformNumericBound tokenTable width
        tokenCount valueBound)
      (compactSequentFormulaStepParserUniformBitBound tokenTable width
        tokenCount valueBound))

noncomputable def compactSequentFormulaStepTail16UniformRowParserLeavesOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    CompactSequentFormulaStepTail16UniformRowParserLeaves tokenTable width
      tokenCount valueBound data.row := by
  let row := data.row
  let rowBounds :=
    compactSequentFormulaStepNatListRowsFullyFixedBoundsOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      row data.graph
  let numericBound :=
    compactSequentFormulaStepParserUniformNumericBound tokenTable width
      tokenCount valueBound
  let bitBound :=
    compactSequentFormulaStepParserUniformBitBound tokenTable width tokenCount
      valueBound
  have hparserValue : row.parserValueBound <= valueBound :=
    data.values_le 0
  have hparserTableWidth : row.parserTableWidth <= valueBound :=
    data.values_le 1
  have hparserStateBoundary : row.parserStateBoundary <= valueBound :=
    data.values_le 2
  have hnextCount : row.next.count <= valueBound := data.values_le 9
  have hnextBoundary : row.next.boundary <= valueBound := data.values_le 10
  have hcurrentCount : row.current.count <= valueBound := data.values_le 14
  have hcurrentBoundary : row.current.boundary <= valueBound := data.values_le 15
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound compactSequentFormulaStepParserUniformNumericBound
    omega
  have hwidth : width <= numericBound := by
    unfold numericBound compactSequentFormulaStepParserUniformNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound compactSequentFormulaStepParserUniformNumericBound
    omega
  have huniformNumeric : valueBound <= numericBound := by
    unfold numericBound compactSequentFormulaStepParserUniformNumericBound
    omega
  have hstateBoundary : row.parserStateBoundary <= numericBound :=
    hparserStateBoundary.trans huniformNumeric
  have hinputBoundary : row.current.boundary <= numericBound :=
    hcurrentBoundary.trans huniformNumeric
  have hinputCount : row.current.count <= numericBound :=
    hcurrentCount.trans huniformNumeric
  have hexpectedBoundary : row.next.boundary <= numericBound :=
    hnextBoundary.trans huniformNumeric
  have hexpectedCount : row.next.count <= numericBound :=
    hnextCount.trans huniformNumeric
  have hfuelUniform := compactParserSyntaxExactFuel_mono_public hcurrentCount
  have hfuel : compactParserSyntaxExactFuel row.current.count <= numericBound :=
    hfuelUniform.trans (by
      unfold numericBound compactSequentFormulaStepParserUniformNumericBound
      omega)
  have hstateCount : compactParserSyntaxExactFuel row.current.count + 1 <=
      numericBound := by
    have hmono := Nat.add_le_add_right hfuelUniform 1
    exact hmono.trans (by
      unfold numericBound compactSequentFormulaStepParserUniformNumericBound
      omega)
  have harea : (tokenCount + 1) * tokenCount <= numericBound := by
    unfold numericBound compactSequentFormulaStepParserUniformNumericBound
    omega
  have huniformSucc : valueBound + 1 <= numericBound := by
    unfold numericBound compactSequentFormulaStepParserUniformNumericBound
    omega
  have hnumericBit : numericBound <= bitBound := by
    change numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have hnumericSize : Nat.size numericBound <= bitBound := by
    change Nat.size numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have hbitPositive : 1 <= bitBound := by
    change 1 <= numericBound + Nat.size numericBound + 1
    omega
  have hgraph := data.graph
  rcases hgraph with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hparser,
      _, _⟩
  let parserStateCount := compactParserSyntaxExactFuel row.current.count + 1
  have hparser' : CompactParserSyntaxExactBoundedGraph tokenTable width
      tokenCount row.parserStateBoundary parserStateCount row.current.boundary
      row.current.count row.next.boundary row.next.count 1 0 0
      row.parserTableWidth row.parserValueBound := by
    simpa [parserStateCount, compactParserSyntaxExactFuel] using hparser
  let parserBound :=
    compactSequentFormulaStepParserUniformClosedDirectBoundOfGraph tokenTable
      width tokenCount row.parserStateBoundary parserStateCount
      row.current.boundary row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound valueBound numericBound bitBound
      hparserTableWidth hparserValue hparser' htokenTable hwidth htokenCount
      hstateBoundary hstateCount hfuel hinputBoundary hinputCount
      hexpectedBoundary hexpectedCount harea huniformSucc hnumericBit
      hnumericSize hbitPositive
  exact
    { current := rowBounds.current
      next := rowBounds.next
      value := rowBounds.value
      parser :=
        { proof := parserBound.proof
          payloadLength_le := by
            simpa only [row, numericBound, bitBound, parserStateCount] using
              parserBound.payloadLength_le } }

#print axioms compactParserSyntaxExactFuel_mono_public
#print axioms compactSequentFormulaStepTail16UniformRowParserLeavesOfData

end FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformRowParserLeaves
