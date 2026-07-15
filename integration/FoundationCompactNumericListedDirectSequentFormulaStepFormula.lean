import integration.FoundationCompactNumericListedDirectParserSyntaxExactFormula
import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectNatListAppendSlices

/-!
# One exact nested formula-parser step for sequent parsing

One outer row selects the current suffix, the next suffix, and the parsed
formula value from two list-of-lists boundary tables.  Each selected flat list
has a self-contained witness layout.  The public formula-parser trace runs from
the current suffix to the next suffix, and exact append slices identify the
consumed prefix with the selected formula value.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaStepFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectParserSyntaxExactFormula

structure CompactSequentNatListRowCoordinates where
  start : Nat
  finish : Nat
  boundary : Nat
  count : Nat
  boundarySize : Nat

structure CompactSequentFormulaStepCoordinates where
  current : CompactSequentNatListRowCoordinates
  next : CompactSequentNatListRowCoordinates
  value : CompactSequentNatListRowCoordinates
  parserStateBoundary : Nat
  parserTableWidth : Nat
  parserValueBound : Nat

def CompactSequentFormulaStepGraph
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Prop :=
  row.current.start ≤ tokenCount ∧
    row.current.finish ≤ tokenCount ∧
    row.current.count ≤ tokenCount ∧
    row.next.start ≤ tokenCount ∧
    row.next.finish ≤ tokenCount ∧
    row.next.count ≤ tokenCount ∧
    row.value.start ≤ tokenCount ∧
    row.value.finish ≤ tokenCount ∧
    row.value.count ≤ tokenCount ∧
    CompactFixedWidthEntry suffixBoundary tokenCount index
      row.current.start ∧
    CompactFixedWidthEntry suffixBoundary tokenCount (index + 1)
      row.current.finish ∧
    CompactFixedWidthEntry suffixBoundary tokenCount (index + 1)
      row.next.start ∧
    CompactFixedWidthEntry suffixBoundary tokenCount (index + 2)
      row.next.finish ∧
    CompactFixedWidthEntry valueBoundary tokenCount index
      row.value.start ∧
    CompactFixedWidthEntry valueBoundary tokenCount (index + 1)
      row.value.finish ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount row.current.start row.current.count
        row.current.finish row.current.boundary row.current.boundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount row.next.start row.next.count
        row.next.finish row.next.boundary row.next.boundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount row.value.start row.value.count
        row.value.finish row.value.boundary row.value.boundarySize ∧
    CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount row.parserStateBoundary
      (16 * (row.current.count + 1) * (row.current.count + 1) + 8 + 1)
      row.current.boundary row.current.count
      row.next.boundary row.next.count
      1 0 0 row.parserTableWidth row.parserValueBound ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
      row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count
      row.current.start row.current.finish row.current.count ∧
    suffixCount = valueCount + 1

def compactSequentFormulaStepDef : 𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount index
      currentStart currentFinish currentBoundary currentCount currentBoundarySize
      nextStart nextFinish nextBoundary nextCount nextBoundarySize
      valueStart valueFinish valueInnerBoundary valueInnerCount valueBoundarySize
      parserStateBoundary parserTableWidth parserValueBound.
    currentStart ≤ tokenCount ∧
    currentFinish ≤ tokenCount ∧
    currentCount ≤ tokenCount ∧
    nextStart ≤ tokenCount ∧
    nextFinish ≤ tokenCount ∧
    nextCount ≤ tokenCount ∧
    valueStart ≤ tokenCount ∧
    valueFinish ≤ tokenCount ∧
    valueInnerCount ≤ tokenCount ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount index currentStart ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount (index + 1) currentFinish ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount (index + 1) nextStart ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount (index + 2) nextFinish ∧
    !(compactFixedWidthEntryDef)
      valueBoundary tokenCount index valueStart ∧
    !(compactFixedWidthEntryDef)
      valueBoundary tokenCount (index + 1) valueFinish ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount currentStart currentCount currentFinish
      currentBoundary currentBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount nextStart nextCount nextFinish
      nextBoundary nextBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount valueStart valueInnerCount valueFinish
      valueInnerBoundary valueBoundarySize ∧
    !(compactParserSyntaxExactBoundedGraphDef)
      tokenTable width tokenCount parserStateBoundary
      (16 * (currentCount + 1) * (currentCount + 1) + 8 + 1)
      currentBoundary currentCount nextBoundary nextCount
      1 0 0 parserTableWidth parserValueBound ∧
    !(compactAdditiveNatListAppendSlicesDef)
      tokenTable width tokenCount
      valueStart valueFinish valueInnerCount
      nextStart nextFinish nextCount
      currentStart currentFinish currentCount ∧
    suffixCount = valueCount + 1”

def compactSequentFormulaStepEnvironment
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Fin 26 → Nat :=
  ![tokenTable, width, tokenCount, suffixBoundary, suffixCount,
    valueBoundary, valueCount, index,
    row.current.start, row.current.finish, row.current.boundary,
    row.current.count, row.current.boundarySize,
    row.next.start, row.next.finish, row.next.boundary,
    row.next.count, row.next.boundarySize,
    row.value.start, row.value.finish, row.value.boundary,
    row.value.count, row.value.boundarySize,
    row.parserStateBoundary, row.parserTableWidth, row.parserValueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactSequentFormulaStepDef_spec
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepDef.val.Evalb
        (compactSequentFormulaStepEnvironment
          tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount index row) ↔
      CompactSequentFormulaStepGraph
        tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount index row := by
  let env := compactSequentFormulaStepEnvironment
    tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount index row
  change compactSequentFormulaStepDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #8, #11, #9,
          #10, #12]) =
        ![tokenTable, width, tokenCount, row.current.start,
          row.current.count, row.current.finish,
          row.current.boundary, row.current.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnextEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #13, #16, #14,
          #15, #17]) =
        ![tokenTable, width, tokenCount, row.next.start,
          row.next.count, row.next.finish,
          row.next.boundary, row.next.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hvalueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #18, #21, #19,
          #20, #22]) =
        ![tokenTable, width, tokenCount, row.value.start,
          row.value.count, row.value.finish,
          row.value.boundary, row.value.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hparserEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #23,
          ‘(16 * (#11 + 1) * (#11 + 1) + 8 + 1)’,
          #10, #11, #15, #16,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 26),
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26),
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26), #24, #25]) =
        ![tokenTable, width, tokenCount, row.parserStateBoundary,
          16 * (row.current.count + 1) * (row.current.count + 1) + 8 + 1,
          row.current.boundary, row.current.count,
          row.next.boundary, row.next.count,
          1, 0, 0, row.parserTableWidth, row.parserValueBound] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env, compactSequentFormulaStepEnvironment]
  have happendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
          #18, #19, #21, #13, #14, #16, #8, #9, #11]) =
        ![tokenTable, width, tokenCount,
          row.value.start, row.value.finish, row.value.count,
          row.next.start, row.next.finish, row.next.count,
          row.current.start, row.current.finish, row.current.count] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcurrentSpec := compactAdditiveNatListWitnessRowsDef_spec
    tokenTable width tokenCount row.current.start row.current.count
      row.current.finish row.current.boundary row.current.boundarySize
  have hnextSpec := compactAdditiveNatListWitnessRowsDef_spec
    tokenTable width tokenCount row.next.start row.next.count
      row.next.finish row.next.boundary row.next.boundarySize
  have hvalueSpec := compactAdditiveNatListWitnessRowsDef_spec
    tokenTable width tokenCount row.value.start row.value.count
      row.value.finish row.value.boundary row.value.boundarySize
  have hparserSpec := compactParserSyntaxExactBoundedGraphDef_spec
    tokenTable width tokenCount row.parserStateBoundary
    (16 * (row.current.count + 1) * (row.current.count + 1) + 8 + 1)
    row.current.boundary row.current.count row.next.boundary row.next.count
    1 0 0 row.parserTableWidth row.parserValueBound
  have happendSpec := compactAdditiveNatListAppendSlicesDef_spec
    tokenTable width tokenCount
    row.value.start row.value.finish row.value.count
    row.next.start row.next.finish row.next.count
    row.current.start row.current.finish row.current.count
  have hcurrentEval :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #8, #11, #9,
            #10, #12]) Empty.elim)
          compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount row.current.start row.current.count
            row.current.finish row.current.boundary
            row.current.boundarySize := by
    rw [hcurrentEnv]
    exact hcurrentSpec
  have hnextEval :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #13, #16, #14,
            #15, #17]) Empty.elim)
          compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount row.next.start row.next.count
            row.next.finish row.next.boundary row.next.boundarySize := by
    rw [hnextEnv]
    exact hnextSpec
  have hvalueEval :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #18, #21, #19,
            #20, #22]) Empty.elim)
          compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount row.value.start row.value.count
            row.value.finish row.value.boundary row.value.boundarySize := by
    rw [hvalueEnv]
    exact hvalueSpec
  have hparserEval :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #23,
            ‘(16 * (#11 + 1) * (#11 + 1) + 8 + 1)’,
            #10, #11, #15, #16,
            (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 26),
            (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26),
            (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26), #24, #25])
          Empty.elim) compactParserSyntaxExactBoundedGraphDef.val ↔
        CompactParserSyntaxExactBoundedGraph
          tokenTable width tokenCount row.parserStateBoundary
          (16 * (row.current.count + 1) * (row.current.count + 1) + 8 + 1)
          row.current.boundary row.current.count
          row.next.boundary row.next.count
          1 0 0 row.parserTableWidth row.parserValueBound := by
    rw [hparserEnv]
    exact hparserSpec
  have happendEval :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
            #18, #19, #21, #13, #14, #16, #8, #9, #11]) Empty.elim)
          compactAdditiveNatListAppendSlicesDef.val ↔
        CompactAdditiveNatListAppendSlices
          tokenTable width tokenCount
          row.value.start row.value.finish row.value.count
          row.next.start row.next.finish row.next.count
          row.current.start row.current.finish row.current.count := by
    rw [happendEnv]
    exact happendSpec
  simp (config := { zeta := false })
    [compactSequentFormulaStepDef, CompactSequentFormulaStepGraph,
      hcurrentEval, hnextEval, hvalueEval, hparserEval, happendEval]
  simp [env, compactSequentFormulaStepEnvironment]
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rfl

theorem compactSequentFormulaStepDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaStepDef.val := by
  simp [compactSequentFormulaStepDef]

#print axioms compactSequentFormulaStepDef_spec
#print axioms compactSequentFormulaStepDef_sigmaZero

end FoundationCompactNumericListedDirectSequentFormulaStepFormula
