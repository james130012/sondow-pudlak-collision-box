import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepRows

/-!
# Handwritten bounded formula for one binary-natural stream step

All branch-specific data are explicit free witness coordinates.  The local
graph is therefore Delta-zero; an outer Sigma-one formula may quantify these
witnesses once while retaining their proved bit-size guards.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBoolListPackedValue
open FoundationCompactNumericListedDirectBoolListDropRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListReverseRows
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectBinaryNatDecodeFailure
open FoundationCompactNumericListedDirectCompletedStatusReverseRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows

structure CompactBinaryNatStreamStepWitnessCoordinates where
  branch : Nat
  payload : Nat
  digitCount : Nat
  token : Nat
  consumed : Nat
  sourceOutputStart : Nat
  sourceOutputBoundary : Nat
  sourceOutputBoundarySize : Nat
  targetOutputStart : Nat
  targetOutputBoundary : Nat
  targetOutputBoundarySize : Nat
  outputCount : Nat

def CompactBinaryNatStreamDoneGraphRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates)
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) : Prop :=
  witness.branch = 0 ∧
    CompactAdditiveBoolListDropRows
      tokenTable width tokenCount
        current.bitsBoundary current.bitsCount
        next.bitsBoundary next.bitsCount 0 ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.decodedBoundary current.decodedCount
        next.decodedBoundary next.decodedCount ∧
    ((CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount current.decodedFinish current.finish ∧
      CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount next.decodedFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsWithSize
        tokenTable width tokenCount
          current.decodedFinish current.finish
          next.decodedFinish next.finish
          witness.sourceOutputStart witness.sourceOutputBoundary
          witness.sourceOutputBoundarySize
          witness.targetOutputStart witness.targetOutputBoundary
          witness.targetOutputBoundarySize witness.outputCount)

def CompactBinaryNatStreamEmptyGraphRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates)
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) : Prop :=
  witness.branch = 1 ∧
    current.bitsCount = 0 ∧
    next.bitsCount = 0 ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.decodedFinish current.finish ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.decodedBoundary current.decodedCount
        next.decodedBoundary next.decodedCount ∧
    CompactBinaryNatCompletedOutputReverseRowsWithSize
      tokenTable width tokenCount next.decodedFinish next.finish
        current.decodedBoundary current.decodedCount
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize

def CompactBinaryNatStreamDecodeFailureGraphRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates)
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) : Prop :=
  witness.branch = 2 ∧
    0 < current.bitsCount ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.decodedFinish current.finish ∧
    CompactAdditiveBoolListDecodeFailureRows
      tokenTable width tokenCount current.bitsBoundary current.bitsCount
        witness.payload ∧
    CompactAdditiveBoolListDropRows
      tokenTable width tokenCount
        current.bitsBoundary current.bitsCount
        next.bitsBoundary next.bitsCount 0 ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.decodedBoundary current.decodedCount
        next.decodedBoundary next.decodedCount ∧
    CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount next.decodedFinish next.finish

def CompactBinaryNatStreamDecodeSuccessGraphRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates)
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) : Prop :=
  witness.branch = 3 ∧
    0 < current.bitsCount ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.decodedFinish current.finish ∧
    CompactAdditiveBoolListDecodeSuccessRows
      tokenTable width tokenCount
        current.bitsBoundary current.bitsCount
        next.bitsBoundary next.bitsCount
        witness.payload witness.digitCount witness.token witness.consumed ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        current.decodedBoundary current.decodedCount
        next.decodedBoundary next.decodedCount witness.token ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount next.decodedFinish next.finish

def CompactBinaryNatStreamStepGraphRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates)
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) : Prop :=
  CompactBinaryNatStreamDoneGraphRows
      tokenTable width tokenCount current next witness ∨
    CompactBinaryNatStreamEmptyGraphRows
      tokenTable width tokenCount current next witness ∨
    CompactBinaryNatStreamDecodeFailureGraphRows
      tokenTable width tokenCount current next witness ∨
    CompactBinaryNatStreamDecodeSuccessGraphRows
      tokenTable width tokenCount current next witness

def compactBinaryNatStreamDoneGraphRowsDef : 𝚺₀.Semisentence 31 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    branch = 0 ∧
    !(compactAdditiveBoolListDropRowsDef)
      tokenTable width tokenCount
        currentBitsBoundary currentBitsCount
        nextBitsBoundary nextBitsCount 0 ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentDecodedBoundary currentDecodedCount
        nextDecodedBoundary nextDecodedCount ∧
    ((!(compactBinaryNatFailedStatusSliceDef)
        tokenTable width tokenCount currentDecodedFinish currentFinish ∧
      !(compactBinaryNatFailedStatusSliceDef)
        tokenTable width tokenCount nextDecodedFinish nextFinish) ∨
      (!(compactBinaryNatCompletedStatusPrefixDef)
          tokenTable width tokenCount currentDecodedFinish sourceOutputStart ∧
       !(compactAdditiveStructuredListLayoutDef)
          tokenTable width tokenCount sourceOutputStart outputCount
            currentFinish sourceOutputBoundary ∧
       !(compactBinaryNatCompletedStatusPrefixDef)
          tokenTable width tokenCount nextDecodedFinish targetOutputStart ∧
       !(compactAdditiveStructuredListLayoutDef)
          tokenTable width tokenCount targetOutputStart outputCount
            nextFinish targetOutputBoundary ∧
       !(compactAdditiveNatListSameRowsDef)
          tokenTable width tokenCount sourceOutputBoundary outputCount
            targetOutputBoundary outputCount ∧
       !(compactNatSizeDef)
          sourceOutputBoundarySize sourceOutputBoundary ∧
       sourceOutputBoundarySize ≤ (outputCount + 1) * tokenCount ∧
       !(compactNatSizeDef)
          targetOutputBoundarySize targetOutputBoundary ∧
       targetOutputBoundarySize ≤ (outputCount + 1) * tokenCount))”

def compactBinaryNatStreamEmptyGraphRowsDef : 𝚺₀.Semisentence 31 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    branch = 1 ∧
    currentBitsCount = 0 ∧
    nextBitsCount = 0 ∧
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentDecodedFinish currentFinish ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentDecodedBoundary currentDecodedCount
        nextDecodedBoundary nextDecodedCount ∧
    !(compactBinaryNatCompletedStatusPrefixDef)
      tokenTable width tokenCount nextDecodedFinish targetOutputStart ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount targetOutputStart currentDecodedCount
        nextFinish targetOutputBoundary ∧
    !(compactAdditiveNatListReverseRowsDef)
      tokenTable width tokenCount
        currentDecodedBoundary currentDecodedCount
        targetOutputBoundary currentDecodedCount ∧
    !(compactNatSizeDef)
      targetOutputBoundarySize targetOutputBoundary ∧
    targetOutputBoundarySize ≤
      (currentDecodedCount + 1) * tokenCount”

def compactBinaryNatStreamDecodeFailureGraphRowsDef :
    𝚺₀.Semisentence 31 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    branch = 2 ∧
    0 < currentBitsCount ∧
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentDecodedFinish currentFinish ∧
    !(compactAdditiveBoolListPackedValueDef)
      tokenTable width tokenCount
        currentBitsBoundary currentBitsCount payload ∧
    !(compactBinaryNatNoDecodeShapeDef) payload currentBitsCount ∧
    !(compactAdditiveBoolListDropRowsDef)
      tokenTable width tokenCount
        currentBitsBoundary currentBitsCount
        nextBitsBoundary nextBitsCount 0 ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentDecodedBoundary currentDecodedCount
        nextDecodedBoundary nextDecodedCount ∧
    !(compactBinaryNatFailedStatusSliceDef)
      tokenTable width tokenCount nextDecodedFinish nextFinish”

def compactBinaryNatStreamDecodeSuccessGraphRowsDef :
    𝚺₀.Semisentence 31 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    branch = 3 ∧
    0 < currentBitsCount ∧
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentDecodedFinish currentFinish ∧
    !(compactAdditiveBoolListDecodeSuccessRowsDef)
      tokenTable width tokenCount
        currentBitsBoundary currentBitsCount
        nextBitsBoundary nextBitsCount
        payload digitCount token consumed ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        currentDecodedBoundary currentDecodedCount
        nextDecodedBoundary nextDecodedCount token ∧
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount nextDecodedFinish nextFinish”

def compactBinaryNatStreamStepGraphRowsDef : 𝚺₀.Semisentence 31 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    !(compactBinaryNatStreamDoneGraphRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount ∨
    !(compactBinaryNatStreamEmptyGraphRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount ∨
    !(compactBinaryNatStreamDecodeFailureGraphRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount ∨
    !(compactBinaryNatStreamDecodeSuccessGraphRowsDef)
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

def compactBinaryNatStreamRowCoordinatesOf
    (start finish bitsFinish decodedFinish bitsBoundary bitsCount
      decodedBoundary decodedCount : Nat) :
    CompactBinaryNatStreamRowCoordinates where
  start := start
  finish := finish
  bitsFinish := bitsFinish
  decodedFinish := decodedFinish
  bitsBoundary := bitsBoundary
  bitsCount := bitsCount
  decodedBoundary := decodedBoundary
  decodedCount := decodedCount

def compactBinaryNatStreamStepWitnessCoordinatesOf
    (branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : CompactBinaryNatStreamStepWitnessCoordinates where
  branch := branch
  payload := payload
  digitCount := digitCount
  token := token
  consumed := consumed
  sourceOutputStart := sourceOutputStart
  sourceOutputBoundary := sourceOutputBoundary
  sourceOutputBoundarySize := sourceOutputBoundarySize
  targetOutputStart := targetOutputStart
  targetOutputBoundary := targetOutputBoundary
  targetOutputBoundarySize := targetOutputBoundarySize
  outputCount := outputCount

private abbrev streamStepFormulaEnvironment
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : Fin 31 → Nat :=
  ![tokenTable, width, tokenCount,
    currentStart, currentFinish, currentBitsFinish, currentDecodedFinish,
    currentBitsBoundary, currentBitsCount,
    currentDecodedBoundary, currentDecodedCount,
    nextStart, nextFinish, nextBitsFinish, nextDecodedFinish,
    nextBitsBoundary, nextBitsCount, nextDecodedBoundary, nextDecodedCount,
    branch, payload, digitCount, token, consumed,
    sourceOutputStart, sourceOutputBoundary, sourceOutputBoundarySize,
    targetOutputStart, targetOutputBoundary, targetOutputBoundarySize,
    outputCount]

@[simp] theorem compactBinaryNatStreamDoneGraphRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamDoneGraphRowsDef.val.Evalb
        (streamStepFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactBinaryNatStreamDoneGraphRows tokenTable width tokenCount
        (compactBinaryNatStreamRowCoordinatesOf
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount)
        (compactBinaryNatStreamRowCoordinatesOf
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount)
        (compactBinaryNatStreamStepWitnessCoordinatesOf
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  let env := streamStepFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentBitsFinish currentDecodedFinish
    currentBitsBoundary currentBitsCount
    currentDecodedBoundary currentDecodedCount
    nextStart nextFinish nextBitsFinish nextDecodedFinish
    nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
    branch payload digitCount token consumed
    sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
    outputCount
  change compactBinaryNatStreamDoneGraphRowsDef.val.Evalb env ↔ _
  have hdropEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #7, #8, #15, #16,
          ↑(0 : Nat)]) =
        ![tokenTable, width, tokenCount,
          currentBitsBoundary, currentBitsCount,
          nextBitsBoundary, nextBitsCount, 0] := by
    funext index
    fin_cases index <;> rfl
  have hdecodedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #9, #10, #17, #18]) =
        ![tokenTable, width, tokenCount,
          currentDecodedBoundary, currentDecodedCount,
          nextDecodedBoundary, nextDecodedCount] := by
    funext index
    fin_cases index <;> rfl
  have hcurrentFailedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          currentDecodedFinish, currentFinish] := by
    funext index
    fin_cases index <;> rfl
  have hnextFailedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount,
          nextDecodedFinish, nextFinish] := by
    funext index
    fin_cases index <;> rfl
  have hsourcePrefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #6, #24]) =
        ![tokenTable, width, tokenCount,
          currentDecodedFinish, sourceOutputStart] := by
    funext index
    fin_cases index <;> rfl
  have hsourceLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #24, #30, #4, #25]) =
        ![tokenTable, width, tokenCount, sourceOutputStart, outputCount,
          currentFinish, sourceOutputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htargetPrefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #14, #27]) =
        ![tokenTable, width, tokenCount,
          nextDecodedFinish, targetOutputStart] := by
    funext index
    fin_cases index <;> rfl
  have htargetLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #27, #30, #12,
          #28]) =
        ![tokenTable, width, tokenCount, targetOutputStart, outputCount,
          nextFinish, targetOutputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have houtputRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #25, #30, #28,
          #30]) =
        ![tokenTable, width, tokenCount,
          sourceOutputBoundary, outputCount,
          targetOutputBoundary, outputCount] := by
    funext index
    fin_cases index <;> rfl
  simp [compactBinaryNatStreamDoneGraphRowsDef,
    compactBinaryNatStreamRowCoordinatesOf,
    compactBinaryNatStreamStepWitnessCoordinatesOf,
    CompactBinaryNatStreamDoneGraphRows,
    CompactBinaryNatCompletedStatusSameRowsWithSize,
    CompactBinaryNatCompletedStatusSameRows,
    hdropEnv, hdecodedEnv, hcurrentFailedEnv, hnextFailedEnv,
    hsourcePrefixEnv, hsourceLayoutEnv,
    htargetPrefixEnv, htargetLayoutEnv, houtputRowsEnv]
  tauto

@[simp] theorem compactBinaryNatStreamEmptyGraphRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamEmptyGraphRowsDef.val.Evalb
        (streamStepFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactBinaryNatStreamEmptyGraphRows tokenTable width tokenCount
        (compactBinaryNatStreamRowCoordinatesOf
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount)
        (compactBinaryNatStreamRowCoordinatesOf
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount)
        (compactBinaryNatStreamStepWitnessCoordinatesOf
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  let env := streamStepFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentBitsFinish currentDecodedFinish
    currentBitsBoundary currentBitsCount
    currentDecodedBoundary currentDecodedCount
    nextStart nextFinish nextBitsFinish nextDecodedFinish
    nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
    branch payload digitCount token consumed
    sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
    outputCount
  change compactBinaryNatStreamEmptyGraphRowsDef.val.Evalb env ↔ _
  have hcurrentRunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          currentDecodedFinish, currentFinish] := by
    funext index
    fin_cases index <;> rfl
  have hdecodedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #9, #10, #17, #18]) =
        ![tokenTable, width, tokenCount,
          currentDecodedBoundary, currentDecodedCount,
          nextDecodedBoundary, nextDecodedCount] := by
    funext index
    fin_cases index <;> rfl
  have htargetPrefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #14, #27]) =
        ![tokenTable, width, tokenCount,
          nextDecodedFinish, targetOutputStart] := by
    funext index
    fin_cases index <;> rfl
  have htargetLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #27, #10, #12,
          #28]) =
        ![tokenTable, width, tokenCount,
          targetOutputStart, currentDecodedCount,
          nextFinish, targetOutputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hreverseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #9, #10, #28,
          #10]) =
        ![tokenTable, width, tokenCount,
          currentDecodedBoundary, currentDecodedCount,
          targetOutputBoundary, currentDecodedCount] := by
    funext index
    fin_cases index <;> rfl
  simp [compactBinaryNatStreamEmptyGraphRowsDef,
    compactBinaryNatStreamRowCoordinatesOf,
    compactBinaryNatStreamStepWitnessCoordinatesOf,
    CompactBinaryNatStreamEmptyGraphRows,
    CompactBinaryNatCompletedOutputReverseRowsWithSize,
    CompactBinaryNatCompletedOutputReverseRows,
    hcurrentRunningEnv, hdecodedEnv, htargetPrefixEnv,
    htargetLayoutEnv, hreverseEnv]
  tauto

@[simp] theorem compactBinaryNatStreamDecodeFailureGraphRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamDecodeFailureGraphRowsDef.val.Evalb
        (streamStepFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactBinaryNatStreamDecodeFailureGraphRows
        tokenTable width tokenCount
        (compactBinaryNatStreamRowCoordinatesOf
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount)
        (compactBinaryNatStreamRowCoordinatesOf
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount)
        (compactBinaryNatStreamStepWitnessCoordinatesOf
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  let env := streamStepFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentBitsFinish currentDecodedFinish
    currentBitsBoundary currentBitsCount
    currentDecodedBoundary currentDecodedCount
    nextStart nextFinish nextBitsFinish nextDecodedFinish
    nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
    branch payload digitCount token consumed
    sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
    outputCount
  change compactBinaryNatStreamDecodeFailureGraphRowsDef.val.Evalb env ↔ _
  have hcurrentRunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          currentDecodedFinish, currentFinish] := by
    funext index
    fin_cases index <;> rfl
  have hpackedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #7, #8, #20]) =
        ![tokenTable, width, tokenCount,
          currentBitsBoundary, currentBitsCount, payload] := by
    funext index
    fin_cases index <;> rfl
  have hdropEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #7, #8, #15, #16,
          ↑(0 : Nat)]) =
        ![tokenTable, width, tokenCount,
          currentBitsBoundary, currentBitsCount,
          nextBitsBoundary, nextBitsCount, 0] := by
    funext index
    fin_cases index <;> rfl
  have hdecodedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #9, #10, #17, #18]) =
        ![tokenTable, width, tokenCount,
          currentDecodedBoundary, currentDecodedCount,
          nextDecodedBoundary, nextDecodedCount] := by
    funext index
    fin_cases index <;> rfl
  have hnextFailedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount,
          nextDecodedFinish, nextFinish] := by
    funext index
    fin_cases index <;> rfl
  simp [compactBinaryNatStreamDecodeFailureGraphRowsDef,
    compactBinaryNatStreamRowCoordinatesOf,
    compactBinaryNatStreamStepWitnessCoordinatesOf,
    CompactBinaryNatStreamDecodeFailureGraphRows,
    CompactAdditiveBoolListDecodeFailureRows,
    hcurrentRunningEnv, hpackedEnv, hdropEnv,
    hdecodedEnv, hnextFailedEnv]
  tauto

@[simp] theorem compactBinaryNatStreamDecodeSuccessGraphRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamDecodeSuccessGraphRowsDef.val.Evalb
        (streamStepFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactBinaryNatStreamDecodeSuccessGraphRows
        tokenTable width tokenCount
        (compactBinaryNatStreamRowCoordinatesOf
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount)
        (compactBinaryNatStreamRowCoordinatesOf
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount)
        (compactBinaryNatStreamStepWitnessCoordinatesOf
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  let env := streamStepFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentBitsFinish currentDecodedFinish
    currentBitsBoundary currentBitsCount
    currentDecodedBoundary currentDecodedCount
    nextStart nextFinish nextBitsFinish nextDecodedFinish
    nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
    branch payload digitCount token consumed
    sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
    outputCount
  change compactBinaryNatStreamDecodeSuccessGraphRowsDef.val.Evalb env ↔ _
  have hcurrentRunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          currentDecodedFinish, currentFinish] := by
    funext index
    fin_cases index <;> rfl
  have hdecodeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #7, #8, #15, #16,
          #20, #21, #22, #23]) =
        ![tokenTable, width, tokenCount,
          currentBitsBoundary, currentBitsCount,
          nextBitsBoundary, nextBitsCount,
          payload, digitCount, token, consumed] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #9, #10, #17, #18,
          #22]) =
        ![tokenTable, width, tokenCount,
          currentDecodedBoundary, currentDecodedCount,
          nextDecodedBoundary, nextDecodedCount, token] := by
    funext index
    fin_cases index <;> rfl
  have hnextRunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount,
          nextDecodedFinish, nextFinish] := by
    funext index
    fin_cases index <;> rfl
  simp [compactBinaryNatStreamDecodeSuccessGraphRowsDef,
    compactBinaryNatStreamRowCoordinatesOf,
    compactBinaryNatStreamStepWitnessCoordinatesOf,
    CompactBinaryNatStreamDecodeSuccessGraphRows,
    hcurrentRunningEnv, hdecodeEnv, hconsEnv, hnextRunningEnv]
  tauto

@[simp] theorem compactBinaryNatStreamStepGraphRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamStepGraphRowsDef.val.Evalb
        (streamStepFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactBinaryNatStreamStepGraphRows tokenTable width tokenCount
        (compactBinaryNatStreamRowCoordinatesOf
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount)
        (compactBinaryNatStreamRowCoordinatesOf
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount)
        (compactBinaryNatStreamStepWitnessCoordinatesOf
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  let env := streamStepFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentBitsFinish currentDecodedFinish
    currentBitsBoundary currentBitsCount
    currentDecodedBoundary currentDecodedCount
    nextStart nextFinish nextBitsFinish nextDecodedFinish
    nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
    branch payload digitCount token consumed
    sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
    outputCount
  change compactBinaryNatStreamStepGraphRowsDef.val.Evalb env ↔ _
  have hidentityEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18, #19,
          #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30]) =
        env := by
    funext index
    fin_cases index <;> rfl
  simp [compactBinaryNatStreamStepGraphRowsDef,
    hidentityEnv, env,
    compactBinaryNatStreamRowCoordinatesOf,
    compactBinaryNatStreamStepWitnessCoordinatesOf,
    CompactBinaryNatStreamStepGraphRows]

theorem compactBinaryNatStreamDoneGraphRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamDoneGraphRowsDef.val := by
  simp [compactBinaryNatStreamDoneGraphRowsDef]

theorem compactBinaryNatStreamEmptyGraphRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamEmptyGraphRowsDef.val := by
  simp [compactBinaryNatStreamEmptyGraphRowsDef]

theorem compactBinaryNatStreamDecodeFailureGraphRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamDecodeFailureGraphRowsDef.val := by
  simp [compactBinaryNatStreamDecodeFailureGraphRowsDef]

theorem compactBinaryNatStreamDecodeSuccessGraphRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamDecodeSuccessGraphRowsDef.val := by
  simp [compactBinaryNatStreamDecodeSuccessGraphRowsDef]

theorem compactBinaryNatStreamStepGraphRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamStepGraphRowsDef.val := by
  simp [compactBinaryNatStreamStepGraphRowsDef]

theorem exists_stepGraphRows_iff_stepRows
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : FoundationCompactBinaryNatStreamMachine.BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactBinaryNatStreamStepGraphRows
          tokenTable width tokenCount
            currentCoordinates nextCoordinates witness) ↔
      CompactBinaryNatStreamStepRows
        tokenTable width tokenCount currentCoordinates nextCoordinates := by
  constructor
  · rintro ⟨witness, hdone | hempty | hfailure | hsuccess⟩
    · left
      rcases hdone.2.2.2 with hfailed | hcompleted
      · exact ⟨hdone.2.1, hdone.2.2.1, Or.inl hfailed⟩
      · exact ⟨hdone.2.1, hdone.2.2.1, Or.inr
          ⟨witness.sourceOutputStart, witness.sourceOutputBoundary,
            witness.targetOutputStart, witness.targetOutputBoundary,
            witness.outputCount, hcompleted.1⟩⟩
    · right; left
      exact ⟨hempty.2.1, hempty.2.2.1, hempty.2.2.2.1,
        hempty.2.2.2.2.1,
        witness.targetOutputStart, witness.targetOutputBoundary,
        hempty.2.2.2.2.2.1⟩
    · right; right; left
      exact ⟨hfailure.2.1, hfailure.2.2.1,
        ⟨witness.payload, hfailure.2.2.2.1⟩,
        hfailure.2.2.2.2.1, hfailure.2.2.2.2.2.1,
        hfailure.2.2.2.2.2.2⟩
    · right; right; right
      exact ⟨hsuccess.2.1, hsuccess.2.2.1, witness.token,
        ⟨witness.payload, witness.digitCount, witness.consumed,
          hsuccess.2.2.2.1⟩,
        hsuccess.2.2.2.2.1, hsuccess.2.2.2.2.2⟩
  · intro hstep
    rcases hstep with hdone | hempty | hfailure | hsuccess
    · rcases hdone with ⟨hbits, hdecoded, hstatus⟩
      rcases hstatus with hfailed | hcompleted
      · let witness : CompactBinaryNatStreamStepWitnessCoordinates :=
          { branch := 0
            payload := 0
            digitCount := 0
            token := 0
            consumed := 0
            sourceOutputStart := 0
            sourceOutputBoundary := 0
            sourceOutputBoundarySize := 0
            targetOutputStart := 0
            targetOutputBoundary := 0
            targetOutputBoundarySize := 0
            outputCount := 0 }
        exact ⟨witness, Or.inl ⟨rfl, hbits, hdecoded, Or.inl hfailed⟩⟩
      · have hsemantic :=
          (completedStatusSameRows_iff
            hcurrent.statusLayout hnext.statusLayout).mp hcompleted
        rcases (completedStatusSameRowsWithSize_iff
            hcurrent.statusLayout hnext.statusLayout).mpr hsemantic with
          ⟨sourceOutputStart, sourceOutputBoundary,
            sourceOutputBoundarySize, targetOutputStart,
            targetOutputBoundary, targetOutputBoundarySize,
            outputCount, hstrong⟩
        let witness : CompactBinaryNatStreamStepWitnessCoordinates :=
          { branch := 0
            payload := 0
            digitCount := 0
            token := 0
            consumed := 0
            sourceOutputStart := sourceOutputStart
            sourceOutputBoundary := sourceOutputBoundary
            sourceOutputBoundarySize := sourceOutputBoundarySize
            targetOutputStart := targetOutputStart
            targetOutputBoundary := targetOutputBoundary
            targetOutputBoundarySize := targetOutputBoundarySize
            outputCount := outputCount }
        exact ⟨witness, Or.inl ⟨rfl, hbits, hdecoded, Or.inr hstrong⟩⟩
    · rcases hempty with
        ⟨hcurrentCount, hnextCount, hcurrentRunning,
          hdecoded, hcompleted⟩
      have hcompleted' :
          ∃ outputStart outputBoundary,
            CompactBinaryNatCompletedOutputReverseRows
              tokenTable width tokenCount
                nextCoordinates.decodedFinish nextCoordinates.finish
                currentCoordinates.decodedBoundary current.2.1.length
                outputStart outputBoundary := by
        simpa only [CompactBinaryNatCompletedOutputReverseRowsExists,
          hcurrent.decodedCount_eq] using hcompleted
      have hsemantic :=
        (completedOutputReverseRows_iff
          hcurrent.decodedRows hnext.statusLayout).mp hcompleted'
      rcases (completedOutputReverseRowsWithSize_iff
          hcurrent.decodedRows hnext.statusLayout).mpr hsemantic with
        ⟨targetOutputStart, targetOutputBoundary,
          targetOutputBoundarySize, hstrong⟩
      have hstrong' : CompactBinaryNatCompletedOutputReverseRowsWithSize
          tokenTable width tokenCount
            nextCoordinates.decodedFinish nextCoordinates.finish
            currentCoordinates.decodedBoundary
            currentCoordinates.decodedCount
            targetOutputStart targetOutputBoundary
            targetOutputBoundarySize := by
        simpa only [hcurrent.decodedCount_eq] using hstrong
      let witness : CompactBinaryNatStreamStepWitnessCoordinates :=
        { branch := 1
          payload := 0
          digitCount := 0
          token := 0
          consumed := 0
          sourceOutputStart := 0
          sourceOutputBoundary := 0
          sourceOutputBoundarySize := 0
          targetOutputStart := targetOutputStart
          targetOutputBoundary := targetOutputBoundary
          targetOutputBoundarySize := targetOutputBoundarySize
          outputCount := currentCoordinates.decodedCount }
      exact ⟨witness, Or.inr (Or.inl
        ⟨rfl, hcurrentCount, hnextCount,
          hcurrentRunning, hdecoded, hstrong'⟩)⟩
    · rcases hfailure with
        ⟨hpositive, hcurrentRunning, hdecodeExists,
          hbits, hdecoded, hnextFailed⟩
      rcases hdecodeExists with ⟨payload, hdecode⟩
      let witness : CompactBinaryNatStreamStepWitnessCoordinates :=
        { branch := 2
          payload := payload
          digitCount := 0
          token := 0
          consumed := 0
          sourceOutputStart := 0
          sourceOutputBoundary := 0
          sourceOutputBoundarySize := 0
          targetOutputStart := 0
          targetOutputBoundary := 0
          targetOutputBoundarySize := 0
          outputCount := 0 }
      exact ⟨witness, Or.inr (Or.inr (Or.inl
        ⟨rfl, hpositive, hcurrentRunning, hdecode,
          hbits, hdecoded, hnextFailed⟩))⟩
    · rcases hsuccess with
        ⟨hpositive, hcurrentRunning, token, hdecodeExists,
          hcons, hnextRunning⟩
      rcases hdecodeExists with
        ⟨payload, digitCount, consumed, hdecode⟩
      let witness : CompactBinaryNatStreamStepWitnessCoordinates :=
        { branch := 3
          payload := payload
          digitCount := digitCount
          token := token
          consumed := consumed
          sourceOutputStart := 0
          sourceOutputBoundary := 0
          sourceOutputBoundarySize := 0
          targetOutputStart := 0
          targetOutputBoundary := 0
          targetOutputBoundarySize := 0
          outputCount := 0 }
      exact ⟨witness, Or.inr (Or.inr (Or.inr
        ⟨rfl, hpositive, hcurrentRunning, hdecode,
          hcons, hnextRunning⟩))⟩

theorem exists_stepGraphRows_iff_step
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : FoundationCompactBinaryNatStreamMachine.BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactBinaryNatStreamStepGraphRows
          tokenTable width tokenCount
            currentCoordinates nextCoordinates witness) ↔
      next = FoundationCompactBinaryNatStreamMachine.binaryNatStreamStep
        current := by
  rw [exists_stepGraphRows_iff_stepRows hcurrent hnext]
  exact compactBinaryNatStreamStepRows_iff_step hcurrent hnext

#print axioms compactBinaryNatStreamDoneGraphRowsDef_spec
#print axioms compactBinaryNatStreamEmptyGraphRowsDef_spec
#print axioms compactBinaryNatStreamDecodeFailureGraphRowsDef_spec
#print axioms compactBinaryNatStreamDecodeSuccessGraphRowsDef_spec
#print axioms compactBinaryNatStreamStepGraphRowsDef_spec
#print axioms compactBinaryNatStreamStepGraphRowsDef_sigmaZero
#print axioms exists_stepGraphRows_iff_stepRows
#print axioms exists_stepGraphRows_iff_step

end FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
