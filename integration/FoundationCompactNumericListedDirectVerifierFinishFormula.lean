import integration.FoundationCompactNumericListedDirectTokenSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

/-!
# Bounded formula for the verifier finish branch

The finish branch is entered only by a running state with an empty task stack.
It preserves the complete running payload.  A valid singleton child-result
stack supplies the final Boolean; every other payload shape finishes false.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierFinishFormula

open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

def CompactNumericVerifierFinishRows
    (tokenTable width tokenCount
      currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag
      nextStart nextValuesFinish
      nextProofCount nextCertificateCount nextTaskCount nextValueCount
      nextStatusTag nextStatusBool : Nat) : Prop :=
  currentStatusTag = 0 ∧
    currentTaskCount = 0 ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      currentStart currentValuesFinish nextStart nextValuesFinish ∧
    nextProofCount = currentProofCount ∧
    nextCertificateCount = currentCertificateCount ∧
    nextTaskCount = currentTaskCount ∧
    nextValueCount = currentValueCount ∧
    nextStatusTag = 1 ∧
    ((currentProofCount = 0 ∧
        currentCertificateCount = 0 ∧
        currentTaskCount = 0 ∧
        currentValueCount = 1 ∧
        CompactNumericChildResultBoundedRowWithBool
          tokenTable width tokenCount currentValueBoundary
          currentValueValueBound 0 nextStatusBool) ∨
      ((currentProofCount ≠ 0 ∨
          currentCertificateCount ≠ 0 ∨
          currentTaskCount ≠ 0 ∨
          currentValueCount ≠ 1) ∧
        nextStatusBool = 0))

def compactNumericVerifierFinishRowsDef :
    𝚺₀.Semisentence 20 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag
      nextStart nextValuesFinish
      nextProofCount nextCertificateCount nextTaskCount nextValueCount
      nextStatusTag nextStatusBool.
    currentStatusTag = 0 ∧
    currentTaskCount = 0 ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        currentStart currentValuesFinish nextStart nextValuesFinish ∧
    nextProofCount = currentProofCount ∧
    nextCertificateCount = currentCertificateCount ∧
    nextTaskCount = currentTaskCount ∧
    nextValueCount = currentValueCount ∧
    nextStatusTag = 1 ∧
    ((currentProofCount = 0 ∧
      currentCertificateCount = 0 ∧
      currentTaskCount = 0 ∧
      currentValueCount = 1 ∧
      !(compactNumericChildResultBoundedRowWithBoolDef)
        tokenTable width tokenCount currentValueBoundary
          currentValueValueBound 0 nextStatusBool) ∨
     ((currentProofCount ≠ 0 ∨
        currentCertificateCount ≠ 0 ∨
        currentTaskCount ≠ 0 ∨
        currentValueCount ≠ 1) ∧
      nextStatusBool = 0))”

@[simp] theorem compactNumericVerifierFinishRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag
      nextStart nextValuesFinish
      nextProofCount nextCertificateCount nextTaskCount nextValueCount
      nextStatusTag nextStatusBool : Nat) :
    compactNumericVerifierFinishRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          currentStart, currentValuesFinish,
          currentProofCount, currentCertificateCount, currentTaskCount,
          currentValueCount, currentValueBoundary, currentValueValueBound,
          currentStatusTag,
          nextStart, nextValuesFinish,
          nextProofCount, nextCertificateCount, nextTaskCount, nextValueCount,
          nextStatusTag, nextStatusBool] ↔
      CompactNumericVerifierFinishRows tokenTable width tokenCount
        currentStart currentValuesFinish
        currentProofCount currentCertificateCount currentTaskCount
        currentValueCount currentValueBoundary currentValueValueBound
        currentStatusTag
        nextStart nextValuesFinish
        nextProofCount nextCertificateCount nextTaskCount nextValueCount
        nextStatusTag nextStatusBool := by
  have heqEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            currentStart, currentValuesFinish,
            currentProofCount, currentCertificateCount, currentTaskCount,
            currentValueCount, currentValueBoundary, currentValueValueBound,
            currentStatusTag,
            nextStart, nextValuesFinish,
            nextProofCount, nextCertificateCount, nextTaskCount, nextValueCount,
            nextStatusTag, nextStatusBool]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2,
          #3, #4, #12, #13]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentValuesFinish, nextStart, nextValuesFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hchildEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            currentStart, currentValuesFinish,
            currentProofCount, currentCertificateCount, currentTaskCount,
            currentValueCount, currentValueBoundary, currentValueValueBound,
            currentStatusTag,
            nextStart, nextValuesFinish,
            nextProofCount, nextCertificateCount, nextTaskCount, nextValueCount,
            nextStatusTag, nextStatusBool]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2,
          #9, #10, (‘0’ : Semiterm ℒₒᵣ Empty 20), #19]) =
        ![tokenTable, width, tokenCount,
          currentValueBoundary, currentValueValueBound, 0, nextStatusBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierFinishRowsDef,
    CompactNumericVerifierFinishRows, heqEnv, hchildEnv]

theorem compactNumericVerifierFinishRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierFinishRowsDef.val := by
  simp [compactNumericVerifierFinishRowsDef]

#print axioms compactNumericVerifierFinishRowsDef_spec
#print axioms compactNumericVerifierFinishRowsDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierFinishFormula
