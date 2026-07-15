import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalFormula

/-!
# Bounded witness closure for total formula-transform endpoints

All endpoint coordinates are quantified below the same power-of-two bound
used by the total final-status graph.  The three legacy successful-final
coordinates are retained only as zero-valued padding, so no unused arbitrary
witness survives this closure.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalBoundedFormula

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalFormula

def CompactFormulaTransformInitialDefaultFinalBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat) : Prop :=
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
    CompactFormulaTransformInitialDefaultFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound
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

def compactFormulaTransformInitialDefaultFinalBoundedDef :
    𝚺₀.Semisentence 14 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound.
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
      !(compactFormulaTransformInitialDefaultFinalRowsDef)
        tokenTable width tokenCount stateBoundary stateCount fuel
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
        finalParserOutputStart finalParserOutputBoundary
        finalParserOutputBoundarySize”

set_option maxRecDepth 2048 in
@[simp] theorem compactFormulaTransformInitialDefaultFinalBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat) :
    compactFormulaTransformInitialDefaultFinalBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptyBoundary, binderArity,
          tableWidth, valueBound] ↔
      CompactFormulaTransformInitialDefaultFinalBounded
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound := by
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
                expectedOutputCount, emptyBoundary, binderArity,
                tableWidth, valueBound]
              Empty.elim ∘
            ![(#31 : Semiterm ℒₒᵣ Empty 45), #32, #33, #34, #35, #36,
              #37, #38, #39, #40, #41, #42, #43, #44,
              #30, #29, #28, #27, #26, #25, #24, #23, #22, #21, #20,
              #19, #18, #17, #16, #15, #14, #13, #12, #11, #10, #9,
              #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactFormulaTransformInitialDefaultFinalRowsDef.val ↔
      CompactFormulaTransformInitialDefaultFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound
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
              expectedOutputCount, emptyBoundary, binderArity,
              tableWidth, valueBound]
            Empty.elim ∘
          ![(#31 : Semiterm ℒₒᵣ Empty 45), #32, #33, #34, #35, #36,
            #37, #38, #39, #40, #41, #42, #43, #44,
            #30, #29, #28, #27, #26, #25, #24, #23, #22, #21, #20,
            #19, #18, #17, #16, #15, #14, #13, #12, #11, #10, #9,
            #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactFormulaTransformInitialDefaultFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedOutputBoundary
            expectedOutputCount emptyBoundary binderArity tableWidth
            valueBound
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
    exact compactFormulaTransformInitialDefaultFinalRowsDef_spec
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound _
  simp [compactFormulaTransformInitialDefaultFinalBoundedDef,
    CompactFormulaTransformInitialDefaultFinalBounded, hrelation]

theorem compactFormulaTransformInitialDefaultFinalBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformInitialDefaultFinalBoundedDef.val := by
  simp [compactFormulaTransformInitialDefaultFinalBoundedDef]

theorem CompactFormulaTransformInitialDefaultFinalBounded.exists_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat}
    (hbounded : CompactFormulaTransformInitialDefaultFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound) :
    ∃ witness,
      CompactFormulaTransformInitialDefaultFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound witness := by
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

theorem CompactFormulaTransformInitialDefaultFinalBounded.of_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth : Nat}
    {witness : CompactFormulaTransformInitialFinalWitnessCoordinates}
    (hwidth :
      compactFormulaTransformInitialFinalWitnessDynamicWidth witness ≤
        tableWidth)
    (hrelation : CompactFormulaTransformInitialDefaultFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth (2 ^ tableWidth) witness) :
    CompactFormulaTransformInitialDefaultFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈
        compactFormulaTransformInitialFinalWitnessValues witness) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp
      ((compactFormulaTransformInitialFinalWitnessValue_size_le_dynamic
        witness hvalue).trans hwidth)).le
  unfold CompactFormulaTransformInitialDefaultFinalBounded
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
        compactFormulaTransformStateRowCoordinatesOf]
        using hrelation

#print axioms compactFormulaTransformInitialDefaultFinalBoundedDef_spec
#print axioms compactFormulaTransformInitialDefaultFinalBoundedDef_sigmaZero
#print axioms CompactFormulaTransformInitialDefaultFinalBounded.exists_witness
#print axioms CompactFormulaTransformInitialDefaultFinalBounded.of_witness

end FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalBoundedFormula
