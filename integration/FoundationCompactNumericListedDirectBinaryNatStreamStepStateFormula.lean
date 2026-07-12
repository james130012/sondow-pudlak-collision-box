import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepRealization

/-!
# One bounded formula for a realized binary-natural stream step

Two pure numeric state-core formulas and the four-branch step formula share one
token table and their displayed coordinates.  The resulting 35-variable
Delta-zero formula is exactly equivalent to a pair of typed state layouts whose
states are related by `binaryNatStreamStep`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula

open FoundationCompactBinaryNatStreamMachine
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepRealization

def compactBinaryNatStreamStepStateGraphDef : 𝚺₀.Semisentence 35 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    !(compactBinaryNatStreamStateCoreGraphDef)
      tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize ∧
    !(compactBinaryNatStreamStateCoreGraphDef)
      tokenTable width tokenCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount
      nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize ∧
    !(compactBinaryNatStreamStepGraphRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount”

def compactBinaryNatStreamStepStateFormulaEnvironment
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : Fin 35 → Nat :=
  ![tokenTable, width, tokenCount,
    currentStart, currentFinish, currentBitsFinish, currentDecodedFinish,
    currentBitsBoundary, currentBitsCount,
    currentDecodedBoundary, currentDecodedCount,
    currentBitsBoundarySize, currentDecodedBoundarySize,
    nextStart, nextFinish, nextBitsFinish, nextDecodedFinish,
    nextBitsBoundary, nextBitsCount, nextDecodedBoundary, nextDecodedCount,
    nextBitsBoundarySize, nextDecodedBoundarySize,
    branch, payload, digitCount, token, consumed,
    sourceOutputStart, sourceOutputBoundary, sourceOutputBoundarySize,
    targetOutputStart, targetOutputBoundary, targetOutputBoundarySize,
    outputCount]

@[simp] theorem compactBinaryNatStreamStepStateGraphDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamStepStateGraphDef.val.Evalb
        (compactBinaryNatStreamStepStateFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          currentBitsBoundarySize currentDecodedBoundarySize
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          nextBitsBoundarySize nextDecodedBoundarySize
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactBinaryNatStreamStepStateGraph tokenTable width tokenCount
        (compactBinaryNatStreamStateRowCoordinatesOf
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount)
        (compactBinaryNatStreamStateRowCoordinatesOf
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount)
        { bitsBoundarySize := currentBitsBoundarySize
          decodedBoundarySize := currentDecodedBoundarySize }
        { bitsBoundarySize := nextBitsBoundarySize
          decodedBoundarySize := nextDecodedBoundarySize }
        (compactBinaryNatStreamStepWitnessCoordinatesOf
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  let env := compactBinaryNatStreamStepStateFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentBitsFinish currentDecodedFinish
    currentBitsBoundary currentBitsCount
    currentDecodedBoundary currentDecodedCount
    currentBitsBoundarySize currentDecodedBoundarySize
    nextStart nextFinish nextBitsFinish nextDecodedFinish
    nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
    nextBitsBoundarySize nextDecodedBoundarySize
    branch payload digitCount token consumed
    sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
    outputCount
  change compactBinaryNatStreamStepStateGraphDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 35), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10, #11, #12]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentFinish, currentBitsFinish,
          currentDecodedFinish, currentBitsBoundary, currentBitsCount,
          currentDecodedBoundary, currentDecodedCount,
          currentBitsBoundarySize, currentDecodedBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hnextEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 35), #1, #2,
          #13, #14, #15, #16, #17, #18, #19, #20, #21, #22]) =
        ![tokenTable, width, tokenCount,
          nextStart, nextFinish, nextBitsFinish, nextDecodedFinish,
          nextBitsBoundary, nextBitsCount,
          nextDecodedBoundary, nextDecodedCount,
          nextBitsBoundarySize, nextDecodedBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hstepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 35), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #13, #14, #15, #16, #17, #18, #19, #20,
          #23, #24, #25, #26, #27, #28, #29, #30,
          #31, #32, #33, #34]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentFinish, currentBitsFinish,
          currentDecodedFinish, currentBitsBoundary, currentBitsCount,
          currentDecodedBoundary, currentDecodedCount,
          nextStart, nextFinish, nextBitsFinish, nextDecodedFinish,
          nextBitsBoundary, nextBitsCount,
          nextDecodedBoundary, nextDecodedCount,
          branch, payload, digitCount, token, consumed,
          sourceOutputStart, sourceOutputBoundary, sourceOutputBoundarySize,
          targetOutputStart, targetOutputBoundary, targetOutputBoundarySize,
          outputCount] := by
    funext index
    fin_cases index <;> rfl
  have hcurrentSpec :
      compactBinaryNatStreamStateCoreGraphDef.val.Evalb
          ![tokenTable, width, tokenCount,
            currentStart, currentFinish, currentBitsFinish,
            currentDecodedFinish, currentBitsBoundary, currentBitsCount,
            currentDecodedBoundary, currentDecodedCount,
            currentBitsBoundarySize, currentDecodedBoundarySize] ↔
        CompactBinaryNatStreamStateCoreGraph tokenTable width tokenCount
          (compactBinaryNatStreamStateRowCoordinatesOf
            currentStart currentFinish currentBitsFinish currentDecodedFinish
            currentBitsBoundary currentBitsCount
            currentDecodedBoundary currentDecodedCount)
          { bitsBoundarySize := currentBitsBoundarySize
            decodedBoundarySize := currentDecodedBoundarySize } := by
    simpa only [compactBinaryNatStreamStateCoreFormulaEnvironment] using
      compactBinaryNatStreamStateCoreGraphDef_spec
        tokenTable width tokenCount
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize
  have hnextSpec :
      compactBinaryNatStreamStateCoreGraphDef.val.Evalb
          ![tokenTable, width, tokenCount,
            nextStart, nextFinish, nextBitsFinish, nextDecodedFinish,
            nextBitsBoundary, nextBitsCount,
            nextDecodedBoundary, nextDecodedCount,
            nextBitsBoundarySize, nextDecodedBoundarySize] ↔
        CompactBinaryNatStreamStateCoreGraph tokenTable width tokenCount
          (compactBinaryNatStreamStateRowCoordinatesOf
            nextStart nextFinish nextBitsFinish nextDecodedFinish
            nextBitsBoundary nextBitsCount
            nextDecodedBoundary nextDecodedCount)
          { bitsBoundarySize := nextBitsBoundarySize
            decodedBoundarySize := nextDecodedBoundarySize } := by
    simpa only [compactBinaryNatStreamStateCoreFormulaEnvironment] using
      compactBinaryNatStreamStateCoreGraphDef_spec
        tokenTable width tokenCount
        nextStart nextFinish nextBitsFinish nextDecodedFinish
        nextBitsBoundary nextBitsCount
        nextDecodedBoundary nextDecodedCount
        nextBitsBoundarySize nextDecodedBoundarySize
  simp [compactBinaryNatStreamStepStateGraphDef,
    CompactBinaryNatStreamStepStateGraph,
    compactBinaryNatStreamStateRowCoordinatesOf,
    compactBinaryNatStreamRowCoordinatesOf,
    compactBinaryNatStreamStepWitnessCoordinatesOf,
    hcurrentEnv, hnextEnv, hstepEnv, hcurrentSpec, hnextSpec]

theorem compactBinaryNatStreamStepStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamStepStateGraphDef.val := by
  simp [compactBinaryNatStreamStepStateGraphDef]

#print axioms compactBinaryNatStreamStepStateGraphDef_spec
#print axioms compactBinaryNatStreamStepStateGraphDef_sigmaZero

end FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula
