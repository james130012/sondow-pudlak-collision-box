import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformFinalDefaultFormula

/-!
# Total initial and final rows for a formula-transform trace

The endpoint relation fixes the genuine transform initial state and reads the
state at `fuel` with the public `Option.getD []` convention.  Unlike the older
successful-final relation, it is total on arbitrary numeric inputs: running,
failed, and completed-with-suffix states all produce the empty output.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalFormula

open FoundationCompactParserDirectTrace
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformExactFormula
open FoundationCompactNumericListedDirectFormulaTransformFinalDefaultFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula

def CompactFormulaTransformInitialDefaultFinalRows
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat)
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
    CompactFormulaTransformFinalGetDOutputRows
      tokenTable width tokenCount witness.finalCoordinates
        expectedOutputBoundary expectedOutputCount emptyBoundary
        tableWidth valueBound ∧
    witness.finalParserOutputStart = 0 ∧
    witness.finalParserOutputBoundary = 0 ∧
    witness.finalParserOutputBoundarySize = 0

def compactFormulaTransformInitialDefaultFinalRowsDef :
    𝚺₀.Semisentence 45 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound
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
      reservedOutputStart reservedOutputBoundary reservedOutputBoundarySize.
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
    !(compactFormulaTransformFinalGetDOutputRowsDef)
      tokenTable width tokenCount
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      expectedOutputBoundary expectedOutputCount emptyBoundary
      tableWidth valueBound ∧
    reservedOutputStart = 0 ∧
    reservedOutputBoundary = 0 ∧
    reservedOutputBoundarySize = 0”

def compactFormulaTransformInitialDefaultFinalRowsEnvironment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 45 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
    inputBoundary, inputCount, expectedOutputBoundary, expectedOutputCount,
    emptyBoundary, binderArity, tableWidth, valueBound,
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

@[simp] theorem compactFormulaTransformInitialDefaultFinalRowsDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialDefaultFinalRowsDef.val.Evalb
        (compactFormulaTransformInitialDefaultFinalRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          emptyBoundary binderArity tableWidth valueBound witness) ↔
      CompactFormulaTransformInitialDefaultFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound witness := by
  let env := compactFormulaTransformInitialDefaultFinalRowsEnvironment
    tokenTable width tokenCount stateBoundary stateCount fuel
    inputBoundary inputCount expectedOutputBoundary expectedOutputCount
    emptyBoundary binderArity tableWidth valueBound witness
  change compactFormulaTransformInitialDefaultFinalRowsDef.val.Evalb env ↔ _
  have hinitialAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 45), #1, #2, #3, #4,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 45),
          #14, #15, #16, #17, #18, #19, #20, #21, #22, #23, #24,
          #25, #26, #27]) =
        compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount 0
            witness.initialCoordinates witness.initialSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hinitialParserEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 45), #1, #2,
          #14, #16, #17, #18, #19, #20, #21, #22,
          #6, #7, (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 45),
          #11, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 45)]) =
        compactUnifiedParserInitialStateRowsEnvironment
          tokenTable width tokenCount witness.initialCoordinates.parser
            inputBoundary inputCount 1 binderArity 0 := by
    funext index
    fin_cases index <;> rfl
  have hfinalAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 45), #1, #2, #3, #4, #5,
          #28, #29, #30, #31, #32, #33, #34, #35, #36, #37, #38,
          #39, #40, #41]) =
        compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
            witness.finalCoordinates witness.finalSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hfinalDefaultEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 45), #1, #2,
          #28, #29, #30, #31, #32, #33, #34, #35, #36, #37, #38,
          #8, #9, #10, #12, #13]) =
        compactFormulaTransformFinalGetDOutputRowsEnvironment
          tokenTable width tokenCount witness.finalCoordinates
            expectedOutputBoundary expectedOutputCount emptyBoundary
            tableWidth valueBound := by
    funext index
    fin_cases index <;> rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  have hinitialOutputCountValue :
      env 24 = witness.initialCoordinates.outputCount := rfl
  have hreservedOutputStartValue :
      env 42 = witness.finalParserOutputStart := rfl
  have hreservedOutputBoundaryValue :
      env 43 = witness.finalParserOutputBoundary := rfl
  have hreservedOutputBoundarySizeValue :
      env 44 = witness.finalParserOutputBoundarySize := rfl
  simp [compactFormulaTransformInitialDefaultFinalRowsDef,
    CompactFormulaTransformInitialDefaultFinalRows,
    hinitialAtEnv, hinitialParserEnv, hfinalAtEnv, hfinalDefaultEnv,
    hstateCountValue, hfuelValue, hinitialOutputCountValue,
    hreservedOutputStartValue, hreservedOutputBoundaryValue,
    hreservedOutputBoundarySizeValue]

theorem compactFormulaTransformInitialDefaultFinalRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformInitialDefaultFinalRowsDef.val := by
  simp [compactFormulaTransformInitialDefaultFinalRowsDef]

theorem CompactFormulaTransformInitialDefaultFinalRows.decode
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedOutputBoundary emptyBoundary binderArity
      tableWidth valueBound : Nat}
    {input expectedOutput : List Nat}
    {witness : CompactFormulaTransformInitialFinalWitnessCoordinates}
    (hrows : CompactFormulaTransformInitialDefaultFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound witness)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    ∃ initialDecoded finalDecoded : CompactFormulaTransformState,
      initialDecoded =
        compactFormulaTransformInitialState binderArity input ∧
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount witness.initialCoordinates
          initialDecoded ∧
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount witness.finalCoordinates
          finalDecoded ∧
      expectedOutput =
        (compactExactFormulaTransformResult
          (compactFormulaTransformStateOutput finalDecoded)).getD [] := by
  rcases hrows with
    ⟨_hstateCount, hinitialAt, hinitialParser,
      hinitialOutputCount, hfinalAt, hfinalDefault,
      _hreservedStart, _hreservedBoundary, _hreservedBoundarySize⟩
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
  rcases CompactFormulaTransformStateCoreGraph.realizeWithStatusBounded
      hfinalAt.2.2.2 hfinalDefault.2.1 with
    ⟨finalDecoded, hfinalDecodedLayout⟩
  have hfinalResult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformStateOutput finalDecoded)).getD [] :=
    (compactFormulaTransformFinalGetDOutputRows_iff
      hexpectedOutput hempty hfinalDecodedLayout harea hvalueBound).mp
        hfinalDefault
  exact ⟨initialDecoded, finalDecoded, hinitialDecoded,
    hinitialDecodedLayout, hfinalDecodedLayout, hfinalResult⟩

theorem exists_compactFormulaTransformInitialDefaultFinalRows_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedOutputBoundary emptyBoundary binderArity
      tableWidth valueBound : Nat}
    {states : List CompactFormulaTransformState}
    {input expectedOutput : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (∃ witness,
        CompactFormulaTransformInitialDefaultFinalRows
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary input.length
          expectedOutputBoundary expectedOutput.length
          emptyBoundary binderArity tableWidth valueBound witness) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          compactFormulaTransformInitialState binderArity input ∧
        expectedOutput =
          (compactExactFormulaTransformResult
            (compactFormulaTransformStateOutput
              (states.getI fuel))).getD [] := by
  constructor
  · rintro ⟨witness, hstateCount, hinitialAt, hinitialParser,
      hinitialOutputCount, hfinalAt, hfinalDefault,
      _hreservedStart, _hreservedBoundary, _hreservedBoundarySize⟩
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
    rcases CompactFormulaTransformStateCoreGraph.realizeWithStatusBounded
        hfinalAt.2.2.2 hfinalDefault.2.1 with
      ⟨finalDecoded, hfinalDecodedLayout⟩
    have hfinalResult : expectedOutput =
        (compactExactFormulaTransformResult
          (compactFormulaTransformStateOutput finalDecoded)).getD [] :=
      (compactFormulaTransformFinalGetDOutputRows_iff
        hexpectedOutput hempty hfinalDecodedLayout harea hvalueBound).mp
          hfinalDefault
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
    refine ⟨hlength, hinitialState, ?_⟩
    simpa only [hactualFinalDecoded] using hfinalResult
  · rintro ⟨hlength, hinitialState, hfinalResult⟩
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
    have hfinalDefault : CompactFormulaTransformFinalGetDOutputRows
        tokenTable width tokenCount finalCoordinates
          expectedOutputBoundary expectedOutput.length emptyBoundary
          tableWidth valueBound :=
      (compactFormulaTransformFinalGetDOutputRows_iff
        hexpectedOutput hempty hfinalLayout harea hvalueBound).mpr
          hfinalResult
    let witness : CompactFormulaTransformInitialFinalWitnessCoordinates :=
      { initialCoordinates := initialCoordinates
        initialSizeWitness := initialSizeWitness
        finalCoordinates := finalCoordinates
        finalSizeWitness := finalSizeWitness
        finalParserOutputStart := 0
        finalParserOutputBoundary := 0
        finalParserOutputBoundarySize := 0 }
    refine ⟨witness, hstateCount, ?_, hinitialParser,
      hinitialOutputCount, ?_, hfinalDefault, rfl, rfl, rfl⟩
    · simpa only [hcount] using hinitialAtTyped
    · simpa only [hcount] using hfinalAtTyped

theorem exists_compactFormulaTransformInitialDefaultFinalFormula_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedOutputBoundary emptyBoundary binderArity
      tableWidth valueBound : Nat}
    {states : List CompactFormulaTransformState}
    {input expectedOutput : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (∃ witness,
        compactFormulaTransformInitialDefaultFinalRowsDef.val.Evalb
          (compactFormulaTransformInitialDefaultFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary input.length
            expectedOutputBoundary expectedOutput.length
            emptyBoundary binderArity tableWidth valueBound witness)) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          compactFormulaTransformInitialState binderArity input ∧
        expectedOutput =
          (compactExactFormulaTransformResult
            (compactFormulaTransformStateOutput
              (states.getI fuel))).getD [] := by
  simp only [compactFormulaTransformInitialDefaultFinalRowsDef_spec]
  exact exists_compactFormulaTransformInitialDefaultFinalRows_iff
    hcount hrows hinput hexpectedOutput hempty harea hvalueBound

#print axioms compactFormulaTransformInitialDefaultFinalRowsDef_spec
#print axioms compactFormulaTransformInitialDefaultFinalRowsDef_sigmaZero
#print axioms CompactFormulaTransformInitialDefaultFinalRows.decode
#print axioms exists_compactFormulaTransformInitialDefaultFinalRows_iff
#print axioms exists_compactFormulaTransformInitialDefaultFinalFormula_iff

end FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalFormula
