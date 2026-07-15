import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRows
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
import integration.FoundationCompactNumericListedDirectParserInitialFormula
import integration.FoundationCompactNumericListedDirectParserFinalFormula

/-!
# Bounded initial and final rows for a formula-transform trace

The formula selects rows `0` and `fuel`, fixes the genuine transform initial
state, verifies parser completion with a supplied suffix, and checks the
emitted output against a supplied natural-token list.  Every witness is an
explicit bounded arithmetic coordinate; the executable transform is not used
as an opaque atom.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula

open FoundationCompactParserDirectTrace
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedOutputSameRows
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

structure CompactFormulaTransformInitialFinalWitnessCoordinates where
  initialCoordinates : CompactFormulaTransformStateRowCoordinates
  initialSizeWitness : CompactFormulaTransformStateCoreSizeWitness
  finalCoordinates : CompactFormulaTransformStateRowCoordinates
  finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness
  finalParserOutputStart : Nat
  finalParserOutputBoundary : Nat
  finalParserOutputBoundarySize : Nat

def CompactFormulaTransformInitialFinalRows
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) : Prop :=
  stateCount = fuel + 1 ∧
    CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount 0
        witness.initialCoordinates witness.initialSizeWitness ∧
    CompactUnifiedParserInitialStateRows
      tokenTable width tokenCount witness.initialCoordinates.parser
        inputBoundary inputCount 1 binderArity 0 ∧
    witness.initialCoordinates.outputCount = 0 ∧
    CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount fuel
        witness.finalCoordinates witness.finalSizeWitness ∧
    CompactUnifiedParserFinalStateRows
      tokenTable width tokenCount witness.finalCoordinates.parser
        expectedSuffixBoundary expectedSuffixCount
        witness.finalParserOutputStart witness.finalParserOutputBoundary
        witness.finalParserOutputBoundarySize ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        expectedOutputBoundary expectedOutputCount
        witness.finalCoordinates.outputBoundary
        witness.finalCoordinates.outputCount

def compactFormulaTransformInitialFinalRowsDef :
    𝚺₀.Semisentence 44 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      initialStart initialFinish initialParserFinish
      initialParserTokensFinish initialParserTasksFinish
      initialParserTokensBoundary initialParserTokensCount
      initialParserTasksBoundary initialParserTasksCount
      initialOutputBoundary initialOutputCount
      initialParserTokensBoundarySize initialParserTasksBoundarySize
      initialOutputBoundarySize
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      finalParserTokensBoundarySize finalParserTasksBoundarySize
      finalOutputBoundarySize
      finalParserOutputStart finalParserOutputBoundary
      finalParserOutputBoundarySize.
    stateCount = fuel + 1 ∧
    !(compactFormulaTransformStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount 0
      initialStart initialFinish initialParserFinish
      initialParserTokensFinish initialParserTasksFinish
      initialParserTokensBoundary initialParserTokensCount
      initialParserTasksBoundary initialParserTasksCount
      initialOutputBoundary initialOutputCount
      initialParserTokensBoundarySize initialParserTasksBoundarySize
      initialOutputBoundarySize ∧
    !(compactUnifiedParserInitialStateRowsDef)
      tokenTable width tokenCount
      initialStart initialParserFinish
      initialParserTokensFinish initialParserTasksFinish
      initialParserTokensBoundary initialParserTokensCount
      initialParserTasksBoundary initialParserTasksCount
      inputBoundary inputCount 1 binderArity 0 ∧
    initialOutputCount = 0 ∧
    !(compactFormulaTransformStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      finalParserTokensBoundarySize finalParserTasksBoundarySize
      finalOutputBoundarySize ∧
    !(compactUnifiedParserFinalStateRowsDef)
      tokenTable width tokenCount
      finalStart finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      expectedSuffixBoundary expectedSuffixCount
      finalParserOutputStart finalParserOutputBoundary
      finalParserOutputBoundarySize ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
      expectedOutputBoundary expectedOutputCount
      finalOutputBoundary finalOutputCount”

def compactFormulaTransformInitialFinalRowsEnvironment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 44 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
    inputBoundary, inputCount, expectedOutputBoundary, expectedOutputCount,
    expectedSuffixBoundary, expectedSuffixCount, binderArity,
    witness.initialCoordinates.start,
    witness.initialCoordinates.finish,
    witness.initialCoordinates.parserFinish,
    witness.initialCoordinates.parserTokensFinish,
    witness.initialCoordinates.parserTasksFinish,
    witness.initialCoordinates.parserTokensBoundary,
    witness.initialCoordinates.parserTokensCount,
    witness.initialCoordinates.parserTasksBoundary,
    witness.initialCoordinates.parserTasksCount,
    witness.initialCoordinates.outputBoundary,
    witness.initialCoordinates.outputCount,
    witness.initialSizeWitness.parserTokensBoundarySize,
    witness.initialSizeWitness.parserTasksBoundarySize,
    witness.initialSizeWitness.outputBoundarySize,
    witness.finalCoordinates.start,
    witness.finalCoordinates.finish,
    witness.finalCoordinates.parserFinish,
    witness.finalCoordinates.parserTokensFinish,
    witness.finalCoordinates.parserTasksFinish,
    witness.finalCoordinates.parserTokensBoundary,
    witness.finalCoordinates.parserTokensCount,
    witness.finalCoordinates.parserTasksBoundary,
    witness.finalCoordinates.parserTasksCount,
    witness.finalCoordinates.outputBoundary,
    witness.finalCoordinates.outputCount,
    witness.finalSizeWitness.parserTokensBoundarySize,
    witness.finalSizeWitness.parserTasksBoundarySize,
    witness.finalSizeWitness.outputBoundarySize,
    witness.finalParserOutputStart,
    witness.finalParserOutputBoundary,
    witness.finalParserOutputBoundarySize]

@[simp] theorem compactFormulaTransformInitialFinalRowsDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialFinalRowsDef.val.Evalb
        (compactFormulaTransformInitialFinalRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity witness) ↔
      CompactFormulaTransformInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness := by
  let env := compactFormulaTransformInitialFinalRowsEnvironment
    tokenTable width tokenCount stateBoundary stateCount fuel
    inputBoundary inputCount expectedOutputBoundary expectedOutputCount
    expectedSuffixBoundary expectedSuffixCount binderArity witness
  change compactFormulaTransformInitialFinalRowsDef.val.Evalb env ↔ _
  have hinitialAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 44), #1, #2, #3, #4,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 44),
          #13, #14, #15, #16, #17, #18, #19, #20, #21, #22, #23,
          #24, #25, #26]) =
        compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount 0
            witness.initialCoordinates witness.initialSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hinitialParserEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 44), #1, #2,
          #13, #15, #16, #17, #18, #19, #20, #21,
          #6, #7, (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 44),
          #12, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 44)]) =
        compactUnifiedParserInitialStateRowsEnvironment
          tokenTable width tokenCount witness.initialCoordinates.parser
            inputBoundary inputCount 1 binderArity 0 := by
    funext index
    fin_cases index <;> rfl
  have hfinalAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 44), #1, #2, #3, #4, #5,
          #27, #28, #29, #30, #31, #32, #33, #34, #35, #36, #37,
          #38, #39, #40]) =
        compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
            witness.finalCoordinates witness.finalSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hfinalParserEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 44), #1, #2,
          #27, #29, #30, #31, #32, #33, #34, #35,
          #10, #11, #41, #42, #43]) =
        compactUnifiedParserFinalStateRowsEnvironment
          tokenTable width tokenCount witness.finalCoordinates.parser
            expectedSuffixBoundary expectedSuffixCount
            witness.finalParserOutputStart witness.finalParserOutputBoundary
            witness.finalParserOutputBoundarySize := by
    funext index
    fin_cases index <;> rfl
  have houtputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 44), #1, #2,
          #8, #9, #36, #37]) =
        ![tokenTable, width, tokenCount,
          expectedOutputBoundary, expectedOutputCount,
          witness.finalCoordinates.outputBoundary,
          witness.finalCoordinates.outputCount] := by
    funext index
    fin_cases index <;> rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  have hinitialOutputCountValue :
      env 23 = witness.initialCoordinates.outputCount := rfl
  simp [compactFormulaTransformInitialFinalRowsDef,
    CompactFormulaTransformInitialFinalRows,
    hinitialAtEnv, hinitialParserEnv, hfinalAtEnv, hfinalParserEnv,
    houtputEnv, hstateCountValue, hfuelValue,
    hinitialOutputCountValue]

theorem compactFormulaTransformInitialFinalRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformInitialFinalRowsDef.val := by
  simp [compactFormulaTransformInitialFinalRowsDef]

theorem exists_compactFormulaTransformInitialFinalRows_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedOutputBoundary expectedSuffixBoundary
      binderArity : Nat}
    {states : List CompactFormulaTransformState}
    {input expectedOutput expectedSuffix : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hexpectedSuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedSuffixBoundary expectedSuffix) :
    (∃ witness,
        CompactFormulaTransformInitialFinalRows
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary input.length
          expectedOutputBoundary expectedOutput.length
          expectedSuffixBoundary expectedSuffix.length binderArity witness) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          compactFormulaTransformInitialState binderArity input ∧
        (states.getI fuel).1.2.2 = some (some expectedSuffix) ∧
        (states.getI fuel).2 = expectedOutput := by
  constructor
  · rintro ⟨witness, hstateCount, hinitialAt, hinitialParser,
      hinitialOutputCount, hfinalAt, hfinalParser, hfinalOutputRows⟩
    have hlength : states.length = fuel + 1 :=
      hcount.trans hstateCount
    have hzero : 0 < states.length := by omega
    have hfuel : fuel < states.length := by omega
    let initialStatusWitness :=
      compactBinaryNatStatusValidityWitnessOf 0 0 0 0
    have hinitialStatus : CompactBinaryNatStatusValidRows
        tokenTable width tokenCount
          witness.initialCoordinates.parserTasksFinish
          witness.initialCoordinates.parserFinish initialStatusWitness :=
      Or.inl hinitialParser.2.2.2
    rcases CompactFormulaTransformStateCoreGraph.realizeWithStatus
        hinitialAt.2.2.2 hinitialStatus with
      ⟨initialDecoded, hinitialDecodedLayout⟩
    have hinitialParserEq : initialDecoded.1 =
        (input, [(1, binderArity, 0)], none) :=
      (compactUnifiedParserInitialStateRows_iff
        hinput hinitialDecodedLayout.parserLayout).mp hinitialParser
    have hinitialOutputLength : initialDecoded.2.length = 0 := by
      exact hinitialDecodedLayout.outputCount_eq.symm.trans
        hinitialOutputCount
    have hinitialOutput : initialDecoded.2 = [] :=
      List.eq_nil_of_length_eq_zero hinitialOutputLength
    have hinitialDecoded : initialDecoded =
        compactFormulaTransformInitialState binderArity input := by
      apply Prod.ext
      · simpa [compactFormulaTransformInitialState,
          compactFormulaParserInitialState, compactFormulaTask] using
            hinitialParserEq
      · simpa [compactFormulaTransformInitialState] using hinitialOutput
    rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
        hrows hzero with
      ⟨actualInitialCoordinates, actualInitialSizeWitness,
        hactualInitialAt, hactualInitialLayout⟩
    have hinitialStart : actualInitialCoordinates.start =
        witness.initialCoordinates.start :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualInitialAt.2.1).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hinitialAt.2.1).symm
    have hactualInitialDecoded : states.getI 0 = initialDecoded :=
      (CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
        hinitialStart hinitialDecodedLayout hactualInitialLayout).1
    have hinitialState : states.getI 0 =
        compactFormulaTransformInitialState binderArity input :=
      hactualInitialDecoded.trans hinitialDecoded
    have hfinalParserCopy := hfinalParser
    change CompactBinaryNatCompletedOutputSameRowsWithSize
      tokenTable width tokenCount
        witness.finalCoordinates.parserTasksFinish
        witness.finalCoordinates.parserFinish
        expectedSuffixBoundary expectedSuffix.length
        witness.finalParserOutputStart witness.finalParserOutputBoundary
        witness.finalParserOutputBoundarySize at hfinalParser
    rcases hfinalParser with
      ⟨⟨hfinalPrefix, hfinalSuffixLayout, hfinalSuffixSameRows⟩,
        hfinalSuffixSizeEq, hfinalSuffixSizeBound⟩
    have hfinalSuffixUnit : CompactAdditiveUnitBoundaryRows
        tokenCount expectedSuffix.length
          witness.finalParserOutputBoundary :=
      CompactAdditiveNatListSameRows.targetUnitBoundaryRows
        hfinalSuffixSameRows
    let finalStatusWitness := compactBinaryNatStatusValidityWitnessOf
      witness.finalParserOutputStart witness.finalParserOutputBoundary
      witness.finalParserOutputBoundarySize expectedSuffix.length
    have hfinalStatusRows : CompactBinaryNatStatusValidRows
        tokenTable width tokenCount
          witness.finalCoordinates.parserTasksFinish
          witness.finalCoordinates.parserFinish finalStatusWitness :=
      Or.inr (Or.inr
        ⟨hfinalPrefix, hfinalSuffixLayout, hfinalSuffixUnit,
          hfinalSuffixSizeEq, hfinalSuffixSizeBound⟩)
    rcases CompactFormulaTransformStateCoreGraph.realizeWithStatus
        hfinalAt.2.2.2 hfinalStatusRows with
      ⟨finalDecoded, hfinalDecodedLayout⟩
    have hfinalStatus : finalDecoded.1.2.2 =
        some (some expectedSuffix) :=
      (exists_compactUnifiedParserFinalStateRows_iff
        hexpectedSuffix hfinalDecodedLayout.parserLayout).mp
          ⟨witness.finalParserOutputStart,
            witness.finalParserOutputBoundary,
            witness.finalParserOutputBoundarySize, hfinalParserCopy⟩
    have hfinalOutputRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          expectedOutputBoundary expectedOutput.length
          witness.finalCoordinates.outputBoundary finalDecoded.2.length := by
      simpa only [hfinalDecodedLayout.outputCount_eq] using
        hfinalOutputRows
    have hfinalOutput : finalDecoded.2 = expectedOutput :=
      hfinalOutputRows'.eq_of_rows
        hexpectedOutput hfinalDecodedLayout.outputRows
    rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
        hrows hfuel with
      ⟨actualFinalCoordinates, actualFinalSizeWitness,
        hactualFinalAt, hactualFinalLayout⟩
    have hfinalStart : actualFinalCoordinates.start =
        witness.finalCoordinates.start :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualFinalAt.2.1).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hfinalAt.2.1).symm
    have hactualFinalDecoded : states.getI fuel = finalDecoded :=
      (CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
        hfinalStart hfinalDecodedLayout hactualFinalLayout).1
    refine ⟨hlength, hinitialState, ?_, ?_⟩
    · simpa only [hactualFinalDecoded] using hfinalStatus
    · simpa only [hactualFinalDecoded] using hfinalOutput
  · rintro ⟨hlength, hinitialState, hfinalStatus, hfinalOutput⟩
    have hstateCount : stateCount = fuel + 1 :=
      hcount.symm.trans hlength
    have hzero : 0 < states.length := by omega
    have hfuel : fuel < states.length := by omega
    rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
        hrows hzero with
      ⟨initialCoordinates, initialSizeWitness,
        hinitialAtTyped, hinitialLayout⟩
    rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
        hrows hfuel with
      ⟨finalCoordinates, finalSizeWitness,
        hfinalAtTyped, hfinalLayout⟩
    have hinitialParserState : (states.getI 0).1 =
        (input, [(1, binderArity, 0)], none) := by
      rw [hinitialState]
      rfl
    have hinitialParser : CompactUnifiedParserInitialStateRows
        tokenTable width tokenCount initialCoordinates.parser
          inputBoundary input.length 1 binderArity 0 :=
      (compactUnifiedParserInitialStateRows_iff
        hinput hinitialLayout.parserLayout).mpr hinitialParserState
    have hinitialOutputCount : initialCoordinates.outputCount = 0 := by
      rw [hinitialLayout.outputCount_eq, hinitialState]
      rfl
    rcases (exists_compactUnifiedParserFinalStateRows_iff
        hexpectedSuffix hfinalLayout.parserLayout).mpr hfinalStatus with
      ⟨finalParserOutputStart, finalParserOutputBoundary,
        finalParserOutputBoundarySize, hfinalParser⟩
    have hfinalOutputSameTyped : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          expectedOutputBoundary expectedOutput.length
          finalCoordinates.outputBoundary (states.getI fuel).2.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hexpectedOutput hfinalLayout.outputRows hfinalOutput
    have hfinalOutputSame : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          expectedOutputBoundary expectedOutput.length
          finalCoordinates.outputBoundary finalCoordinates.outputCount := by
      simpa only [hfinalLayout.outputCount_eq] using
        hfinalOutputSameTyped
    let witness : CompactFormulaTransformInitialFinalWitnessCoordinates :=
      { initialCoordinates := initialCoordinates
        initialSizeWitness := initialSizeWitness
        finalCoordinates := finalCoordinates
        finalSizeWitness := finalSizeWitness
        finalParserOutputStart := finalParserOutputStart
        finalParserOutputBoundary := finalParserOutputBoundary
        finalParserOutputBoundarySize := finalParserOutputBoundarySize }
    refine ⟨witness, hstateCount, ?_, hinitialParser,
      hinitialOutputCount, ?_, hfinalParser, hfinalOutputSame⟩
    · simpa only [hcount] using hinitialAtTyped
    · simpa only [hcount] using hfinalAtTyped

theorem exists_compactFormulaTransformInitialFinalFormula_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedOutputBoundary expectedSuffixBoundary
      binderArity : Nat}
    {states : List CompactFormulaTransformState}
    {input expectedOutput expectedSuffix : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hexpectedSuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedSuffixBoundary expectedSuffix) :
    (∃ witness,
        compactFormulaTransformInitialFinalRowsDef.val.Evalb
          (compactFormulaTransformInitialFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary input.length
            expectedOutputBoundary expectedOutput.length
            expectedSuffixBoundary expectedSuffix.length binderArity
            witness)) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          compactFormulaTransformInitialState binderArity input ∧
        (states.getI fuel).1.2.2 = some (some expectedSuffix) ∧
        (states.getI fuel).2 = expectedOutput := by
  simp only [compactFormulaTransformInitialFinalRowsDef_spec]
  exact exists_compactFormulaTransformInitialFinalRows_iff
    hcount hrows hinput hexpectedOutput hexpectedSuffix

#print axioms compactFormulaTransformInitialFinalRowsDef_spec
#print axioms compactFormulaTransformInitialFinalRowsDef_sigmaZero
#print axioms exists_compactFormulaTransformInitialFinalRows_iff
#print axioms exists_compactFormulaTransformInitialFinalFormula_iff

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
