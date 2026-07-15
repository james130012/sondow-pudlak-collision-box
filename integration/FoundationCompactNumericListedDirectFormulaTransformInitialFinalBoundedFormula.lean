import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula

/-!
# Bounded witness closure for formula-transform endpoints

All thirty-one coordinates used by the exact initial/final relation are
quantified below one explicit value bound.  The resulting predicate remains a
handwritten Delta-zero arithmetic formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula

def compactFormulaTransformInitialFinalWitnessOfValues
    (initialStart initialFinish initialParserFinish
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
      finalParserOutputBoundarySize : Nat) :
    CompactFormulaTransformInitialFinalWitnessCoordinates :=
  { initialCoordinates :=
      compactFormulaTransformStateRowCoordinatesOf
        initialStart initialFinish initialParserFinish
        initialParserTokensFinish initialParserTasksFinish
        initialParserTokensBoundary initialParserTokensCount
        initialParserTasksBoundary initialParserTasksCount
        initialOutputBoundary initialOutputCount
    initialSizeWitness :=
      { parserTokensBoundarySize := initialParserTokensBoundarySize
        parserTasksBoundarySize := initialParserTasksBoundarySize
        outputBoundarySize := initialOutputBoundarySize }
    finalCoordinates :=
      compactFormulaTransformStateRowCoordinatesOf
        finalStart finalFinish finalParserFinish
        finalParserTokensFinish finalParserTasksFinish
        finalParserTokensBoundary finalParserTokensCount
        finalParserTasksBoundary finalParserTasksCount
        finalOutputBoundary finalOutputCount
    finalSizeWitness :=
      { parserTokensBoundarySize := finalParserTokensBoundarySize
        parserTasksBoundarySize := finalParserTasksBoundarySize
        outputBoundarySize := finalOutputBoundarySize }
    finalParserOutputStart := finalParserOutputStart
    finalParserOutputBoundary := finalParserOutputBoundary
    finalParserOutputBoundarySize := finalParserOutputBoundarySize }

def compactFormulaTransformInitialFinalWitnessValues
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    List Nat :=
  [witness.initialCoordinates.start,
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

def compactFormulaTransformInitialFinalWitnessDynamicWidth
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) : Nat :=
  ((compactFormulaTransformInitialFinalWitnessValues witness).map Nat.size).sum

theorem compactFormulaTransformInitialFinalWitnessValue_size_le_dynamic
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    {value : Nat}
    (hvalue : value ∈
      compactFormulaTransformInitialFinalWitnessValues witness) :
    Nat.size value ≤
      compactFormulaTransformInitialFinalWitnessDynamicWidth witness := by
  have hsize : Nat.size value ∈
      (compactFormulaTransformInitialFinalWitnessValues witness).map
        Nat.size :=
    List.mem_map.mpr ⟨value, hvalue, rfl⟩
  simpa [compactFormulaTransformInitialFinalWitnessDynamicWidth] using
    List.single_le_sum (by simp) _ hsize

def CompactFormulaTransformInitialFinalBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    Prop :=
  ∃ initialStart, initialStart ≤ valueBound ∧
  ∃ initialFinish, initialFinish ≤ valueBound ∧
  ∃ initialParserFinish, initialParserFinish ≤ valueBound ∧
  ∃ initialParserTokensFinish, initialParserTokensFinish ≤ valueBound ∧
  ∃ initialParserTasksFinish, initialParserTasksFinish ≤ valueBound ∧
  ∃ initialParserTokensBoundary,
      initialParserTokensBoundary ≤ valueBound ∧
  ∃ initialParserTokensCount, initialParserTokensCount ≤ valueBound ∧
  ∃ initialParserTasksBoundary,
      initialParserTasksBoundary ≤ valueBound ∧
  ∃ initialParserTasksCount, initialParserTasksCount ≤ valueBound ∧
  ∃ initialOutputBoundary, initialOutputBoundary ≤ valueBound ∧
  ∃ initialOutputCount, initialOutputCount ≤ valueBound ∧
  ∃ initialParserTokensBoundarySize,
      initialParserTokensBoundarySize ≤ valueBound ∧
  ∃ initialParserTasksBoundarySize,
      initialParserTasksBoundarySize ≤ valueBound ∧
  ∃ initialOutputBoundarySize, initialOutputBoundarySize ≤ valueBound ∧
  ∃ finalStart, finalStart ≤ valueBound ∧
  ∃ finalFinish, finalFinish ≤ valueBound ∧
  ∃ finalParserFinish, finalParserFinish ≤ valueBound ∧
  ∃ finalParserTokensFinish, finalParserTokensFinish ≤ valueBound ∧
  ∃ finalParserTasksFinish, finalParserTasksFinish ≤ valueBound ∧
  ∃ finalParserTokensBoundary, finalParserTokensBoundary ≤ valueBound ∧
  ∃ finalParserTokensCount, finalParserTokensCount ≤ valueBound ∧
  ∃ finalParserTasksBoundary, finalParserTasksBoundary ≤ valueBound ∧
  ∃ finalParserTasksCount, finalParserTasksCount ≤ valueBound ∧
  ∃ finalOutputBoundary, finalOutputBoundary ≤ valueBound ∧
  ∃ finalOutputCount, finalOutputCount ≤ valueBound ∧
  ∃ finalParserTokensBoundarySize,
      finalParserTokensBoundarySize ≤ valueBound ∧
  ∃ finalParserTasksBoundarySize,
      finalParserTasksBoundarySize ≤ valueBound ∧
  ∃ finalOutputBoundarySize, finalOutputBoundarySize ≤ valueBound ∧
  ∃ finalParserOutputStart, finalParserOutputStart ≤ valueBound ∧
  ∃ finalParserOutputBoundary, finalParserOutputBoundary ≤ valueBound ∧
  ∃ finalParserOutputBoundarySize,
      finalParserOutputBoundarySize ≤ valueBound ∧
    CompactFormulaTransformInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      (compactFormulaTransformInitialFinalWitnessOfValues
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
        finalParserOutputBoundarySize)

def compactFormulaTransformInitialFinalBoundedDef :
    𝚺₀.Semisentence 14 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound.
    ∃ initialStart <⁺ valueBound,
    ∃ initialFinish <⁺ valueBound,
    ∃ initialParserFinish <⁺ valueBound,
    ∃ initialParserTokensFinish <⁺ valueBound,
    ∃ initialParserTasksFinish <⁺ valueBound,
    ∃ initialParserTokensBoundary <⁺ valueBound,
    ∃ initialParserTokensCount <⁺ valueBound,
    ∃ initialParserTasksBoundary <⁺ valueBound,
    ∃ initialParserTasksCount <⁺ valueBound,
    ∃ initialOutputBoundary <⁺ valueBound,
    ∃ initialOutputCount <⁺ valueBound,
    ∃ initialParserTokensBoundarySize <⁺ valueBound,
    ∃ initialParserTasksBoundarySize <⁺ valueBound,
    ∃ initialOutputBoundarySize <⁺ valueBound,
    ∃ finalStart <⁺ valueBound,
    ∃ finalFinish <⁺ valueBound,
    ∃ finalParserFinish <⁺ valueBound,
    ∃ finalParserTokensFinish <⁺ valueBound,
    ∃ finalParserTasksFinish <⁺ valueBound,
    ∃ finalParserTokensBoundary <⁺ valueBound,
    ∃ finalParserTokensCount <⁺ valueBound,
    ∃ finalParserTasksBoundary <⁺ valueBound,
    ∃ finalParserTasksCount <⁺ valueBound,
    ∃ finalOutputBoundary <⁺ valueBound,
    ∃ finalOutputCount <⁺ valueBound,
    ∃ finalParserTokensBoundarySize <⁺ valueBound,
    ∃ finalParserTasksBoundarySize <⁺ valueBound,
    ∃ finalOutputBoundarySize <⁺ valueBound,
    ∃ finalParserOutputStart <⁺ valueBound,
    ∃ finalParserOutputBoundary <⁺ valueBound,
    ∃ finalParserOutputBoundarySize <⁺ valueBound,
      !(compactFormulaTransformInitialFinalRowsDef)
        tokenTable width tokenCount stateBoundary stateCount fuel
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
        finalParserOutputBoundarySize”

set_option maxRecDepth 2048 in
@[simp] theorem compactFormulaTransformInitialFinalBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    compactFormulaTransformInitialFinalBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, expectedSuffixBoundary, expectedSuffixCount,
          binderArity, valueBound] ↔
      CompactFormulaTransformInitialFinalBounded
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound := by
  have hrelation
      (finalParserOutputBoundarySize finalParserOutputBoundary
        finalParserOutputStart finalOutputBoundarySize
        finalParserTasksBoundarySize finalParserTokensBoundarySize
        finalOutputCount finalOutputBoundary finalParserTasksCount
        finalParserTasksBoundary finalParserTokensCount
        finalParserTokensBoundary finalParserTasksFinish
        finalParserTokensFinish finalParserFinish finalFinish finalStart
        initialOutputBoundarySize initialParserTasksBoundarySize
        initialParserTokensBoundarySize initialOutputCount
        initialOutputBoundary initialParserTasksCount
        initialParserTasksBoundary initialParserTokensCount
        initialParserTokensBoundary initialParserTasksFinish
        initialParserTokensFinish initialParserFinish initialFinish
        initialStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![finalParserOutputBoundarySize, finalParserOutputBoundary,
                finalParserOutputStart, finalOutputBoundarySize,
                finalParserTasksBoundarySize,
                finalParserTokensBoundarySize, finalOutputCount,
                finalOutputBoundary, finalParserTasksCount,
                finalParserTasksBoundary, finalParserTokensCount,
                finalParserTokensBoundary, finalParserTasksFinish,
                finalParserTokensFinish, finalParserFinish, finalFinish,
                finalStart, initialOutputBoundarySize,
                initialParserTasksBoundarySize,
                initialParserTokensBoundarySize, initialOutputCount,
                initialOutputBoundary, initialParserTasksCount,
                initialParserTasksBoundary, initialParserTokensCount,
                initialParserTokensBoundary, initialParserTasksFinish,
                initialParserTokensFinish, initialParserFinish,
                initialFinish, initialStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                fuel, inputBoundary, inputCount, expectedOutputBoundary,
                expectedOutputCount, expectedSuffixBoundary,
                expectedSuffixCount, binderArity, valueBound]
              Empty.elim ∘
            ![(#31 : Semiterm ℒₒᵣ Empty 45), #32, #33, #34, #35, #36,
              #37, #38, #39, #40, #41, #42, #43,
              #30, #29, #28, #27, #26, #25, #24, #23, #22, #21, #20,
              #19, #18, #17,
              #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6,
              #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactFormulaTransformInitialFinalRowsDef.val ↔
      CompactFormulaTransformInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity
        (compactFormulaTransformInitialFinalWitnessOfValues
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
          finalParserOutputBoundarySize) := by
    have henv :
        (Semiterm.val
            ![finalParserOutputBoundarySize, finalParserOutputBoundary,
              finalParserOutputStart, finalOutputBoundarySize,
              finalParserTasksBoundarySize,
              finalParserTokensBoundarySize, finalOutputCount,
              finalOutputBoundary, finalParserTasksCount,
              finalParserTasksBoundary, finalParserTokensCount,
              finalParserTokensBoundary, finalParserTasksFinish,
              finalParserTokensFinish, finalParserFinish, finalFinish,
              finalStart, initialOutputBoundarySize,
              initialParserTasksBoundarySize,
              initialParserTokensBoundarySize, initialOutputCount,
              initialOutputBoundary, initialParserTasksCount,
              initialParserTasksBoundary, initialParserTokensCount,
              initialParserTokensBoundary, initialParserTasksFinish,
              initialParserTokensFinish, initialParserFinish,
              initialFinish, initialStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              fuel, inputBoundary, inputCount, expectedOutputBoundary,
              expectedOutputCount, expectedSuffixBoundary,
              expectedSuffixCount, binderArity, valueBound]
            Empty.elim ∘
          ![(#31 : Semiterm ℒₒᵣ Empty 45), #32, #33, #34, #35, #36,
            #37, #38, #39, #40, #41, #42, #43,
            #30, #29, #28, #27, #26, #25, #24, #23, #22, #21, #20,
            #19, #18, #17,
            #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6,
            #5, #4, #3, #2, #1, #0]) =
          compactFormulaTransformInitialFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedOutputBoundary
            expectedOutputCount expectedSuffixBoundary expectedSuffixCount
            binderArity
            (compactFormulaTransformInitialFinalWitnessOfValues
              initialStart initialFinish initialParserFinish
              initialParserTokensFinish initialParserTasksFinish
              initialParserTokensBoundary initialParserTokensCount
              initialParserTasksBoundary initialParserTasksCount
              initialOutputBoundary initialOutputCount
              initialParserTokensBoundarySize
              initialParserTasksBoundarySize initialOutputBoundarySize
              finalStart finalFinish finalParserFinish
              finalParserTokensFinish finalParserTasksFinish
              finalParserTokensBoundary finalParserTokensCount
              finalParserTasksBoundary finalParserTasksCount
              finalOutputBoundary finalOutputCount
              finalParserTokensBoundarySize finalParserTasksBoundarySize
              finalOutputBoundarySize finalParserOutputStart
              finalParserOutputBoundary finalParserOutputBoundarySize) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFormulaTransformInitialFinalRowsDef_spec
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity _
  simp [compactFormulaTransformInitialFinalBoundedDef,
    CompactFormulaTransformInitialFinalBounded, hrelation]

theorem compactFormulaTransformInitialFinalBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformInitialFinalBoundedDef.val := by
  simp [compactFormulaTransformInitialFinalBoundedDef]

theorem CompactFormulaTransformInitialFinalBounded.exists_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat}
    (hbounded : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :
    ∃ witness,
      CompactFormulaTransformInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness := by
  rcases hbounded with
    ⟨initialStart, _hinitialStart,
      initialFinish, _hinitialFinish,
      initialParserFinish, _hinitialParserFinish,
      initialParserTokensFinish, _hinitialParserTokensFinish,
      initialParserTasksFinish, _hinitialParserTasksFinish,
      initialParserTokensBoundary, _hinitialParserTokensBoundary,
      initialParserTokensCount, _hinitialParserTokensCount,
      initialParserTasksBoundary, _hinitialParserTasksBoundary,
      initialParserTasksCount, _hinitialParserTasksCount,
      initialOutputBoundary, _hinitialOutputBoundary,
      initialOutputCount, _hinitialOutputCount,
      initialParserTokensBoundarySize,
        _hinitialParserTokensBoundarySize,
      initialParserTasksBoundarySize,
        _hinitialParserTasksBoundarySize,
      initialOutputBoundarySize, _hinitialOutputBoundarySize,
      finalStart, _hfinalStart,
      finalFinish, _hfinalFinish,
      finalParserFinish, _hfinalParserFinish,
      finalParserTokensFinish, _hfinalParserTokensFinish,
      finalParserTasksFinish, _hfinalParserTasksFinish,
      finalParserTokensBoundary, _hfinalParserTokensBoundary,
      finalParserTokensCount, _hfinalParserTokensCount,
      finalParserTasksBoundary, _hfinalParserTasksBoundary,
      finalParserTasksCount, _hfinalParserTasksCount,
      finalOutputBoundary, _hfinalOutputBoundary,
      finalOutputCount, _hfinalOutputCount,
      finalParserTokensBoundarySize, _hfinalParserTokensBoundarySize,
      finalParserTasksBoundarySize, _hfinalParserTasksBoundarySize,
      finalOutputBoundarySize, _hfinalOutputBoundarySize,
      finalParserOutputStart, _hfinalParserOutputStart,
      finalParserOutputBoundary, _hfinalParserOutputBoundary,
      finalParserOutputBoundarySize, _hfinalParserOutputBoundarySize,
      hrelation⟩
  exact
    ⟨compactFormulaTransformInitialFinalWitnessOfValues
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
      finalParserOutputBoundarySize,
    hrelation⟩

theorem CompactFormulaTransformInitialFinalBounded.of_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity tableWidth : Nat}
    {witness : CompactFormulaTransformInitialFinalWitnessCoordinates}
    (hwidth :
      compactFormulaTransformInitialFinalWitnessDynamicWidth witness ≤
        tableWidth)
    (hrelation : CompactFormulaTransformInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness) :
    CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈
        compactFormulaTransformInitialFinalWitnessValues witness) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp
      ((compactFormulaTransformInitialFinalWitnessValue_size_le_dynamic
        witness hvalue).trans hwidth)).le
  unfold CompactFormulaTransformInitialFinalBounded
  refine ⟨
    witness.initialCoordinates.start, ?_,
    witness.initialCoordinates.finish, ?_,
    witness.initialCoordinates.parserFinish, ?_,
    witness.initialCoordinates.parserTokensFinish, ?_,
    witness.initialCoordinates.parserTasksFinish, ?_,
    witness.initialCoordinates.parserTokensBoundary, ?_,
    witness.initialCoordinates.parserTokensCount, ?_,
    witness.initialCoordinates.parserTasksBoundary, ?_,
    witness.initialCoordinates.parserTasksCount, ?_,
    witness.initialCoordinates.outputBoundary, ?_,
    witness.initialCoordinates.outputCount, ?_,
    witness.initialSizeWitness.parserTokensBoundarySize, ?_,
    witness.initialSizeWitness.parserTasksBoundarySize, ?_,
    witness.initialSizeWitness.outputBoundarySize, ?_,
    witness.finalCoordinates.start, ?_,
    witness.finalCoordinates.finish, ?_,
    witness.finalCoordinates.parserFinish, ?_,
    witness.finalCoordinates.parserTokensFinish, ?_,
    witness.finalCoordinates.parserTasksFinish, ?_,
    witness.finalCoordinates.parserTokensBoundary, ?_,
    witness.finalCoordinates.parserTokensCount, ?_,
    witness.finalCoordinates.parserTasksBoundary, ?_,
    witness.finalCoordinates.parserTasksCount, ?_,
    witness.finalCoordinates.outputBoundary, ?_,
    witness.finalCoordinates.outputCount, ?_,
    witness.finalSizeWitness.parserTokensBoundarySize, ?_,
    witness.finalSizeWitness.parserTasksBoundarySize, ?_,
    witness.finalSizeWitness.outputBoundarySize, ?_,
    witness.finalParserOutputStart, ?_,
    witness.finalParserOutputBoundary, ?_,
    witness.finalParserOutputBoundarySize, ?_, ?_⟩
  all_goals
    first
    | apply hall
      simp [compactFormulaTransformInitialFinalWitnessValues]
    | simpa [compactFormulaTransformInitialFinalWitnessOfValues,
        compactFormulaTransformStateRowCoordinatesOf] using hrelation

#print axioms compactFormulaTransformInitialFinalBoundedDef_spec
#print axioms compactFormulaTransformInitialFinalBoundedDef_sigmaZero
#print axioms compactFormulaTransformInitialFinalWitnessValue_size_le_dynamic
#print axioms CompactFormulaTransformInitialFinalBounded.exists_witness
#print axioms CompactFormulaTransformInitialFinalBounded.of_witness

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
