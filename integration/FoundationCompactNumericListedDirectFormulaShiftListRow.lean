import integration.FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula
import integration.FoundationCompactNumericListedDirectNatListWitnessRows

/-!
# One exact formula-shift list row

One row ties an input formula, its defaulted shifted candidate, a success bit,
and the complete unconditional transform trace to the same outer-list index.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaShiftListRow

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula
open FoundationCompactNumericListedDirectNatListWitnessRows

def CompactFormulaShiftListRow
    (tokenTable width tokenCount
      sourceBoundary candidateBoundary successTable formulaCount index
      emptyStart emptyFinish emptyBoundary
      sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
        sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
        candidateInnerBoundary candidateBoundarySize
      stateBoundary stateCount tableWidth valueBound successValue : Nat)
    (finalCoordinates : CompactFormulaTransformStateRowCoordinates)
    (finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Prop :=
  index < formulaCount ∧
    CompactFixedWidthEntry
      sourceBoundary tokenCount index sourceStart ∧
    CompactFixedWidthEntry
      sourceBoundary tokenCount (index + 1) sourceFinish ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount sourceStart sourceInnerCount sourceFinish
        sourceInnerBoundary sourceBoundarySize ∧
    CompactFixedWidthEntry
      candidateBoundary tokenCount index candidateStart ∧
    CompactFixedWidthEntry
      candidateBoundary tokenCount (index + 1) candidateFinish ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount candidateStart candidateInnerCount
        candidateFinish candidateInnerBoundary candidateBoundarySize ∧
    CompactFixedWidthEntry successTable tokenCount index successValue ∧
    CompactFormulaTransformTotalOutcomeRows
      tokenTable width tokenCount stateBoundary stateCount 1
      emptyStart emptyFinish 0
      sourceInnerBoundary sourceInnerCount
      candidateInnerBoundary candidateInnerCount
      emptyBoundary 0 tableWidth valueBound successValue
      finalCoordinates finalSizeWitness

def compactFormulaShiftListRowDef : 𝚺₀.Semisentence 40 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary candidateBoundary successTable formulaCount index
      emptyStart emptyFinish emptyBoundary
      sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
        sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
        candidateInnerBoundary candidateBoundarySize
      stateBoundary stateCount tableWidth valueBound successValue
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      finalParserTokensBoundarySize finalParserTasksBoundarySize
      finalOutputBoundarySize.
    index < formulaCount ∧
    !(compactFixedWidthEntryDef)
      sourceBoundary tokenCount index sourceStart ∧
    !(compactFixedWidthEntryDef)
      sourceBoundary tokenCount (index + 1) sourceFinish ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount sourceStart sourceInnerCount sourceFinish
        sourceInnerBoundary sourceBoundarySize ∧
    !(compactFixedWidthEntryDef)
      candidateBoundary tokenCount index candidateStart ∧
    !(compactFixedWidthEntryDef)
      candidateBoundary tokenCount (index + 1) candidateFinish ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount candidateStart candidateInnerCount
        candidateFinish candidateInnerBoundary candidateBoundarySize ∧
    !(compactFixedWidthEntryDef)
      successTable tokenCount index successValue ∧
    !(compactFormulaTransformTotalOutcomeRowsDef)
      tokenTable width tokenCount stateBoundary stateCount 1
      emptyStart emptyFinish 0
      sourceInnerBoundary sourceInnerCount
      candidateInnerBoundary candidateInnerCount
      emptyBoundary 0 tableWidth valueBound successValue
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      finalParserTokensBoundarySize finalParserTasksBoundarySize
      finalOutputBoundarySize”

def compactFormulaShiftListRowEnvironment
    (tokenTable width tokenCount
      sourceBoundary candidateBoundary successTable formulaCount index
      emptyStart emptyFinish emptyBoundary
      sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
        sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
        candidateInnerBoundary candidateBoundarySize
      stateBoundary stateCount tableWidth valueBound successValue : Nat)
    (finalCoordinates : CompactFormulaTransformStateRowCoordinates)
    (finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 40 → Nat :=
  ![tokenTable, width, tokenCount,
    sourceBoundary, candidateBoundary, successTable, formulaCount, index,
    emptyStart, emptyFinish, emptyBoundary,
    sourceStart, sourceFinish, sourceInnerCount, sourceInnerBoundary,
    sourceBoundarySize,
    candidateStart, candidateFinish, candidateInnerCount,
    candidateInnerBoundary, candidateBoundarySize,
    stateBoundary, stateCount, tableWidth, valueBound, successValue,
    finalCoordinates.start, finalCoordinates.finish,
    finalCoordinates.parserFinish,
    finalCoordinates.parserTokensFinish,
    finalCoordinates.parserTasksFinish,
    finalCoordinates.parserTokensBoundary,
    finalCoordinates.parserTokensCount,
    finalCoordinates.parserTasksBoundary,
    finalCoordinates.parserTasksCount,
    finalCoordinates.outputBoundary, finalCoordinates.outputCount,
    finalSizeWitness.parserTokensBoundarySize,
    finalSizeWitness.parserTasksBoundarySize,
    finalSizeWitness.outputBoundarySize]

set_option maxRecDepth 4096 in
@[simp] theorem compactFormulaShiftListRowDef_spec
    (tokenTable width tokenCount
      sourceBoundary candidateBoundary successTable formulaCount index
      emptyStart emptyFinish emptyBoundary
      sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
        sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
        candidateInnerBoundary candidateBoundarySize
      stateBoundary stateCount tableWidth valueBound successValue : Nat)
    (finalCoordinates : CompactFormulaTransformStateRowCoordinates)
    (finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaShiftListRowDef.val.Evalb
        (compactFormulaShiftListRowEnvironment
          tokenTable width tokenCount
          sourceBoundary candidateBoundary successTable formulaCount index
          emptyStart emptyFinish emptyBoundary
          sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
            sourceBoundarySize
          candidateStart candidateFinish candidateInnerCount
            candidateInnerBoundary candidateBoundarySize
          stateBoundary stateCount tableWidth valueBound successValue
          finalCoordinates finalSizeWitness) ↔
      CompactFormulaShiftListRow
        tokenTable width tokenCount
        sourceBoundary candidateBoundary successTable formulaCount index
        emptyStart emptyFinish emptyBoundary
        sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
          sourceBoundarySize
        candidateStart candidateFinish candidateInnerCount
          candidateInnerBoundary candidateBoundarySize
        stateBoundary stateCount tableWidth valueBound successValue
        finalCoordinates finalSizeWitness := by
  let env := compactFormulaShiftListRowEnvironment
    tokenTable width tokenCount
    sourceBoundary candidateBoundary successTable formulaCount index
    emptyStart emptyFinish emptyBoundary
    sourceStart sourceFinish sourceInnerCount sourceInnerBoundary
      sourceBoundarySize
    candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize
    stateBoundary stateCount tableWidth valueBound successValue
    finalCoordinates finalSizeWitness
  change compactFormulaShiftListRowDef.val.Evalb env ↔ _
  have hsourceStartEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 40), #2, #7, #11]) =
        ![sourceBoundary, tokenCount, index, sourceStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsourceFinishEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 40), #2,
          (‘(#7 + 1)’ : Semiterm ℒₒᵣ Empty 40), #12]) =
        ![sourceBoundary, tokenCount, index + 1, sourceFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsourceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2,
          #11, #13, #12, #14, #15]) =
        ![tokenTable, width, tokenCount,
          sourceStart, sourceInnerCount, sourceFinish,
          sourceInnerBoundary, sourceBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcandidateStartEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#4 : Semiterm ℒₒᵣ Empty 40), #2, #7, #16]) =
        ![candidateBoundary, tokenCount, index, candidateStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcandidateFinishEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#4 : Semiterm ℒₒᵣ Empty 40), #2,
          (‘(#7 + 1)’ : Semiterm ℒₒᵣ Empty 40), #17]) =
        ![candidateBoundary, tokenCount, index + 1, candidateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcandidateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2,
          #16, #18, #17, #19, #20]) =
        ![tokenTable, width, tokenCount,
          candidateStart, candidateInnerCount, candidateFinish,
          candidateInnerBoundary, candidateBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#5 : Semiterm ℒₒᵣ Empty 40), #2, #7, #25]) =
        ![successTable, tokenCount, index, successValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have houtcomeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #21, #22,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 40),
          #8, #9, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 40),
          #14, #13, #19, #18, #10,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 40),
          #23, #24, #25,
          #26, #27, #28, #29, #30, #31, #32, #33, #34, #35, #36,
          #37, #38, #39]) =
        compactFormulaTransformTotalOutcomeRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount 1
          emptyStart emptyFinish 0
          sourceInnerBoundary sourceInnerCount
          candidateInnerBoundary candidateInnerCount
          emptyBoundary 0 tableWidth valueBound successValue
          finalCoordinates finalSizeWitness := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hindexValue : env 7 = index := rfl
  have hformulaCountValue : env 6 = formulaCount := rfl
  simp [compactFormulaShiftListRowDef, CompactFormulaShiftListRow,
    hsourceStartEnv, hsourceFinishEnv, hsourceEnv,
    hcandidateStartEnv, hcandidateFinishEnv, hcandidateEnv,
    hsuccessEnv, houtcomeEnv, hindexValue, hformulaCountValue]

@[simp] theorem compactFormulaShiftListRowDef_eval
    (env : Fin 40 → Nat) :
    compactFormulaShiftListRowDef.val.Evalb env ↔
      CompactFormulaShiftListRow
        (env 0) (env 1) (env 2)
        (env 3) (env 4) (env 5) (env 6) (env 7)
        (env 8) (env 9) (env 10)
        (env 11) (env 12) (env 13) (env 14) (env 15)
        (env 16) (env 17) (env 18) (env 19) (env 20)
        (env 21) (env 22) (env 23) (env 24) (env 25)
        (compactFormulaTransformStateRowCoordinatesOf
          (env 26) (env 27) (env 28) (env 29) (env 30)
          (env 31) (env 32) (env 33) (env 34) (env 35) (env 36))
        { parserTokensBoundarySize := env 37
          parserTasksBoundarySize := env 38
          outputBoundarySize := env 39 } := by
  let finalCoordinates := compactFormulaTransformStateRowCoordinatesOf
    (env 26) (env 27) (env 28) (env 29) (env 30)
    (env 31) (env 32) (env 33) (env 34) (env 35) (env 36)
  let finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness :=
    { parserTokensBoundarySize := env 37
      parserTasksBoundarySize := env 38
      outputBoundarySize := env 39 }
  change compactFormulaShiftListRowDef.val.Evalb env ↔
    CompactFormulaShiftListRow
      (env 0) (env 1) (env 2)
      (env 3) (env 4) (env 5) (env 6) (env 7)
      (env 8) (env 9) (env 10)
      (env 11) (env 12) (env 13) (env 14) (env 15)
      (env 16) (env 17) (env 18) (env 19) (env 20)
      (env 21) (env 22) (env 23) (env 24) (env 25)
      finalCoordinates finalSizeWitness
  have henv : compactFormulaShiftListRowEnvironment
      (env 0) (env 1) (env 2)
      (env 3) (env 4) (env 5) (env 6) (env 7)
      (env 8) (env 9) (env 10)
      (env 11) (env 12) (env 13) (env 14) (env 15)
      (env 16) (env 17) (env 18) (env 19) (env 20)
      (env 21) (env 22) (env 23) (env 24) (env 25)
      finalCoordinates finalSizeWitness = env := by
    funext coordinate
    fin_cases coordinate <;>
      rfl
  rw [← henv]
  exact compactFormulaShiftListRowDef_spec
    (env 0) (env 1) (env 2)
    (env 3) (env 4) (env 5) (env 6) (env 7)
    (env 8) (env 9) (env 10)
    (env 11) (env 12) (env 13) (env 14) (env 15)
    (env 16) (env 17) (env 18) (env 19) (env 20)
    (env 21) (env 22) (env 23) (env 24) (env 25)
    finalCoordinates finalSizeWitness

theorem compactFormulaShiftListRowDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaShiftListRowDef.val := by
  simp [compactFormulaShiftListRowDef]

#print axioms compactFormulaShiftListRowDef_spec
#print axioms compactFormulaShiftListRowDef_eval
#print axioms compactFormulaShiftListRowDef_sigmaZero

end FoundationCompactNumericListedDirectFormulaShiftListRow
