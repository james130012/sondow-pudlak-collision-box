import integration.FoundationCompactNumericListedDirectTracePackedStreamStateLayouts

/-!
# Exact four-branch normal form of one binary-natural stream step

This semantic decomposition fixes the cases that the subsequent handwritten
bounded arithmetic graph must represent, including noncanonical decoder input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepCases

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNatStreamMachine

def BinaryNatStreamStepDoneCase
    (current next : BinaryNatStreamState) : Prop :=
  ∃ result, current.2.2 = some result ∧ next = current

def BinaryNatStreamStepEmptyCase
    (current next : BinaryNatStreamState) : Prop :=
  current.2.2 = none ∧ current.1 = [] ∧
    next = ([], current.2.1, some (some current.2.1.reverse))

def BinaryNatStreamStepDecodeFailureCase
    (current next : BinaryNatStreamState) : Prop :=
  current.2.2 = none ∧ current.1 ≠ [] ∧
    decodeBinaryNat current.1 = none ∧
    next = (current.1, current.2.1, some none)

def BinaryNatStreamStepDecodeSuccessCase
    (current next : BinaryNatStreamState) : Prop :=
  ∃ token suffix,
    current.2.2 = none ∧ current.1 ≠ [] ∧
      decodeBinaryNat current.1 = some (token, suffix) ∧
      next = (suffix, token :: current.2.1, none)

def BinaryNatStreamStepCases
    (current next : BinaryNatStreamState) : Prop :=
  BinaryNatStreamStepDoneCase current next ∨
    BinaryNatStreamStepEmptyCase current next ∨
    BinaryNatStreamStepDecodeFailureCase current next ∨
    BinaryNatStreamStepDecodeSuccessCase current next

theorem binaryNatStreamStepCases_iff
    (current next : BinaryNatStreamState) :
    BinaryNatStreamStepCases current next ↔
      next = binaryNatStreamStep current := by
  rcases current with ⟨bits, decoded, status⟩
  cases status with
  | some result =>
      simp [BinaryNatStreamStepCases, BinaryNatStreamStepDoneCase,
        BinaryNatStreamStepEmptyCase,
        BinaryNatStreamStepDecodeFailureCase,
        BinaryNatStreamStepDecodeSuccessCase,
        binaryNatStreamStep]
  | none =>
      cases bits with
      | nil =>
          simp [BinaryNatStreamStepCases, BinaryNatStreamStepDoneCase,
            BinaryNatStreamStepEmptyCase,
            BinaryNatStreamStepDecodeFailureCase,
            BinaryNatStreamStepDecodeSuccessCase,
            binaryNatStreamStep, binaryNatStreamRunningStep]
      | cons bit bits =>
          cases hdecode : decodeBinaryNat (bit :: bits) with
          | none =>
              simp [BinaryNatStreamStepCases,
                BinaryNatStreamStepDoneCase,
                BinaryNatStreamStepEmptyCase,
                BinaryNatStreamStepDecodeFailureCase,
                BinaryNatStreamStepDecodeSuccessCase,
                binaryNatStreamStep, binaryNatStreamRunningStep,
                hdecode]
          | some result =>
              rcases result with ⟨token, suffix⟩
              simp [BinaryNatStreamStepCases,
                BinaryNatStreamStepDoneCase,
                BinaryNatStreamStepEmptyCase,
                BinaryNatStreamStepDecodeFailureCase,
                BinaryNatStreamStepDecodeSuccessCase,
                binaryNatStreamStep, binaryNatStreamRunningStep,
                hdecode]

theorem binaryNatStreamStepCases_exhaustive
    (current : BinaryNatStreamState) :
    BinaryNatStreamStepCases current (binaryNatStreamStep current) :=
  (binaryNatStreamStepCases_iff current
    (binaryNatStreamStep current)).2 rfl

#print axioms binaryNatStreamStepCases_iff
#print axioms binaryNatStreamStepCases_exhaustive

end FoundationCompactNumericListedDirectBinaryNatStreamStepCases
