import integration.FoundationCompactNumericListedDirectSequentFormulaStepFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidity

/-!
# Bounded universal formula for nested sequent formula-parser steps

Eighteen local row values are explicitly bounded by one power-of-two value
bound.  Every row uses the exact public formula-parser trace and the same outer
suffix and value boundary tables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula

open FoundationCompactNumericListedDirectSequentFormulaStepFormula

def compactSequentFormulaStepRowOfValues
    (currentStart currentFinish currentBoundary currentCount currentBoundarySize
      nextStart nextFinish nextBoundary nextCount nextBoundarySize
      valueStart valueFinish valueInnerBoundary valueInnerCount valueBoundarySize
      parserStateBoundary parserTableWidth parserValueBound : Nat) :
    CompactSequentFormulaStepCoordinates :=
  { current :=
      { start := currentStart
        finish := currentFinish
        boundary := currentBoundary
        count := currentCount
        boundarySize := currentBoundarySize }
    next :=
      { start := nextStart
        finish := nextFinish
        boundary := nextBoundary
        count := nextCount
        boundarySize := nextBoundarySize }
    value :=
      { start := valueStart
        finish := valueFinish
        boundary := valueInnerBoundary
        count := valueInnerCount
        boundarySize := valueBoundarySize }
    parserStateBoundary := parserStateBoundary
    parserTableWidth := parserTableWidth
    parserValueBound := parserValueBound }

def CompactSequentFormulaStepRowBounded
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex valueBound : Nat) : Prop :=
  ∃ currentStart, currentStart ≤ valueBound ∧
  ∃ currentFinish, currentFinish ≤ valueBound ∧
  ∃ currentBoundary, currentBoundary ≤ valueBound ∧
  ∃ currentCount, currentCount ≤ valueBound ∧
  ∃ currentBoundarySize, currentBoundarySize ≤ valueBound ∧
  ∃ nextStart, nextStart ≤ valueBound ∧
  ∃ nextFinish, nextFinish ≤ valueBound ∧
  ∃ nextBoundary, nextBoundary ≤ valueBound ∧
  ∃ nextCount, nextCount ≤ valueBound ∧
  ∃ nextBoundarySize, nextBoundarySize ≤ valueBound ∧
  ∃ valueStart, valueStart ≤ valueBound ∧
  ∃ valueFinish, valueFinish ≤ valueBound ∧
  ∃ valueInnerBoundary, valueInnerBoundary ≤ valueBound ∧
  ∃ valueInnerCount, valueInnerCount ≤ valueBound ∧
  ∃ valueBoundarySize, valueBoundarySize ≤ valueBound ∧
  ∃ parserStateBoundary, parserStateBoundary ≤ valueBound ∧
  ∃ parserTableWidth, parserTableWidth ≤ valueBound ∧
  ∃ parserValueBound, parserValueBound ≤ valueBound ∧
    CompactSequentFormulaStepGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex
        (compactSequentFormulaStepRowOfValues
          currentStart currentFinish currentBoundary currentCount
          currentBoundarySize nextStart nextFinish nextBoundary nextCount
          nextBoundarySize valueStart valueFinish valueInnerBoundary
          valueInnerCount valueBoundarySize parserStateBoundary
          parserTableWidth parserValueBound)

def CompactSequentFormulaStepRowsBoundedGraph
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowCount tableWidth valueBound : Nat) : Prop :=
  valueBound = 2 ^ tableWidth ∧
    ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount rowIndex valueBound

def compactSequentFormulaStepRowBoundedSubstitutionLift
    {Variable : Type*} {targetArity : Nat} :
    (depth : Nat) -> ArithmeticSemiterm Variable targetArity ->
      ArithmeticSemiterm Variable (targetArity + depth)
  | 0, term => term
  | depth + 1, term =>
      Rew.bShift
        (compactSequentFormulaStepRowBoundedSubstitutionLift depth term)

def compactSequentFormulaStepRowBoundedWitnessFormula
    {Variable : Type*} {sourceArity : Nat}
    (bound : ArithmeticSemiterm Variable sourceArity) :
    (depth : Nat) ->
      ArithmeticSemiformula Variable (sourceArity + depth) ->
      ArithmeticSemiformula Variable sourceArity
  | 0, body => body
  | depth + 1, body =>
      compactSequentFormulaStepRowBoundedWitnessFormula bound depth
        (body.bexsLTSucc
          (compactSequentFormulaStepRowBoundedSubstitutionLift depth bound))

def compactSequentFormulaStepRowBoundedEmptyRawTerms :
    Fin 26 -> ArithmeticSemiterm Empty 27 :=
  ![(#18 : ArithmeticSemiterm Empty 27), #19, #20, #21, #22, #23, #24,
    #25, #17, #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5,
    #4, #3, #2, #1, #0]

def compactSequentFormulaStepRowBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 27 :=
  compactSequentFormulaStepDef.val ⇜
    compactSequentFormulaStepRowBoundedEmptyRawTerms

def compactSequentFormulaStepRowBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 9 :=
  compactSequentFormulaStepRowBoundedWitnessFormula
    (#8 : ArithmeticSemiterm Empty 9) 18
    compactSequentFormulaStepRowBoundedEmptyRawTerminal

theorem compactSequentFormulaStepRowBoundedEmptyRawBody_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaStepRowBoundedEmptyRawBody := by
  simp [compactSequentFormulaStepRowBoundedEmptyRawBody,
    compactSequentFormulaStepRowBoundedWitnessFormula,
    compactSequentFormulaStepRowBoundedSubstitutionLift,
    compactSequentFormulaStepRowBoundedEmptyRawTerminal,
    compactSequentFormulaStepRowBoundedEmptyRawTerms]

def compactSequentFormulaStepRowBoundedDef : 𝚺₀.Semisentence 9 :=
  .mkSigma compactSequentFormulaStepRowBoundedEmptyRawBody
    compactSequentFormulaStepRowBoundedEmptyRawBody_sigmaZero

def compactSequentFormulaStepRowsBoundedGraphDef : 𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowCount tableWidth valueBound.
    !expDef valueBound tableWidth ∧
    ∀ rowIndex < rowCount,
      !(compactSequentFormulaStepRowBoundedDef)
        tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex valueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactSequentFormulaStepRowBoundedDef_spec
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex valueBound : Nat) :
    compactSequentFormulaStepRowBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, suffixBoundary, suffixCount,
          valueBoundary, valueCount, rowIndex, valueBound] ↔
      CompactSequentFormulaStepRowBounded
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount rowIndex valueBound := by
  have hrow
      (parserValueBound parserTableWidth parserStateBoundary
        valueBoundarySize valueInnerCount valueInnerBoundary valueFinish
        valueStart nextBoundarySize nextCount nextBoundary nextFinish nextStart
        currentBoundarySize currentCount currentBoundary currentFinish
        currentStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![parserValueBound, parserTableWidth, parserStateBoundary,
                valueBoundarySize, valueInnerCount, valueInnerBoundary,
                valueFinish, valueStart, nextBoundarySize, nextCount,
                nextBoundary, nextFinish, nextStart, currentBoundarySize,
                currentCount, currentBoundary, currentFinish, currentStart,
                tokenTable, width, tokenCount, suffixBoundary, suffixCount,
                valueBoundary, valueCount, rowIndex, valueBound]
              Empty.elim ∘
            ![(#18 : Semiterm ℒₒᵣ Empty 27), #19, #20, #21, #22,
              #23, #24, #25, #17, #16, #15, #14, #13, #12, #11,
              #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactSequentFormulaStepDef.val ↔
        CompactSequentFormulaStepGraph
          tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount rowIndex
            (compactSequentFormulaStepRowOfValues
              currentStart currentFinish currentBoundary currentCount
              currentBoundarySize nextStart nextFinish nextBoundary nextCount
              nextBoundarySize valueStart valueFinish valueInnerBoundary
              valueInnerCount valueBoundarySize parserStateBoundary
              parserTableWidth parserValueBound) := by
    have henv :
        (Semiterm.val
            ![parserValueBound, parserTableWidth, parserStateBoundary,
              valueBoundarySize, valueInnerCount, valueInnerBoundary,
              valueFinish, valueStart, nextBoundarySize, nextCount,
              nextBoundary, nextFinish, nextStart, currentBoundarySize,
              currentCount, currentBoundary, currentFinish, currentStart,
              tokenTable, width, tokenCount, suffixBoundary, suffixCount,
              valueBoundary, valueCount, rowIndex, valueBound]
            Empty.elim ∘
          ![(#18 : Semiterm ℒₒᵣ Empty 27), #19, #20, #21, #22,
            #23, #24, #25, #17, #16, #15, #14, #13, #12, #11,
            #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactSequentFormulaStepEnvironment
            tokenTable width tokenCount suffixBoundary suffixCount
              valueBoundary valueCount rowIndex
              (compactSequentFormulaStepRowOfValues
                currentStart currentFinish currentBoundary currentCount
                currentBoundarySize nextStart nextFinish nextBoundary nextCount
                nextBoundarySize valueStart valueFinish valueInnerBoundary
                valueInnerCount valueBoundarySize parserStateBoundary
                parserTableWidth parserValueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactSequentFormulaStepDef_spec
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex _
  simp [compactSequentFormulaStepRowBoundedDef,
    compactSequentFormulaStepRowBoundedEmptyRawBody,
    compactSequentFormulaStepRowBoundedWitnessFormula,
    compactSequentFormulaStepRowBoundedSubstitutionLift,
    compactSequentFormulaStepRowBoundedEmptyRawTerminal,
    compactSequentFormulaStepRowBoundedEmptyRawTerms,
    CompactSequentFormulaStepRowBounded, hrow]

@[simp] theorem compactSequentFormulaStepRowsBoundedGraphDef_spec
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowCount tableWidth valueBound : Nat) :
    compactSequentFormulaStepRowsBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, suffixBoundary, suffixCount,
          valueBoundary, valueCount, rowCount, tableWidth, valueBound] ↔
      CompactSequentFormulaStepRowsBoundedGraph
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount rowCount tableWidth valueBound := by
  have hrow (rowIndex : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![rowIndex, tokenTable, width, tokenCount, suffixBoundary,
                suffixCount, valueBoundary, valueCount, rowCount,
                tableWidth, valueBound]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 11), #2, #3, #4, #5, #6,
              #7, #0, #10])
          Empty.elim) compactSequentFormulaStepRowBoundedDef.val ↔
        CompactSequentFormulaStepRowBounded
          tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount rowIndex valueBound := by
    have henv :
        (Semiterm.val
            ![rowIndex, tokenTable, width, tokenCount, suffixBoundary,
              suffixCount, valueBoundary, valueCount, rowCount,
              tableWidth, valueBound]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 11), #2, #3, #4, #5, #6,
            #7, #0, #10]) =
          ![tokenTable, width, tokenCount, suffixBoundary, suffixCount,
            valueBoundary, valueCount, rowIndex, valueBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactSequentFormulaStepRowBoundedDef_spec
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex valueBound
  simp [compactSequentFormulaStepRowsBoundedGraphDef,
    CompactSequentFormulaStepRowsBoundedGraph, hrow]

theorem compactSequentFormulaStepRowBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaStepRowBoundedDef.val := by
  exact compactSequentFormulaStepRowBoundedDef.sigma_prop

theorem compactSequentFormulaStepRowsBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaStepRowsBoundedGraphDef.val := by
  simp [compactSequentFormulaStepRowsBoundedGraphDef]

#print axioms compactSequentFormulaStepRowBoundedDef_spec
#print axioms compactSequentFormulaStepRowsBoundedGraphDef_spec
#print axioms compactSequentFormulaStepRowBoundedDef_sigmaZero
#print axioms compactSequentFormulaStepRowsBoundedGraphDef_sigmaZero

end FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
