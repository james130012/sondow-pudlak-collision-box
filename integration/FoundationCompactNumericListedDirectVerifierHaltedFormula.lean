import integration.FoundationCompactNumericListedDirectTokenSliceEquality

/-!
# Bounded formula for the halted verifier branch

An already halted verifier state has option tag `1` and is copied byte for
byte to the next row.  The complete state slice, rather than selected fields,
is preserved.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierHaltedFormula

open FoundationCompactNumericListedDirectTokenSliceEquality

def CompactNumericVerifierHaltedRows
    (tokenTable width tokenCount
      currentStart currentFinish currentStatusTag
      nextStart nextFinish : Nat) : Prop :=
  currentStatusTag = 1 ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      currentStart currentFinish nextStart nextFinish

def compactNumericVerifierHaltedRowsDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentStatusTag nextStart nextFinish.
    currentStatusTag = 1 ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        currentStart currentFinish nextStart nextFinish”

@[simp] theorem compactNumericVerifierHaltedRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentStatusTag
      nextStart nextFinish : Nat) :
    compactNumericVerifierHaltedRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          currentStart, currentFinish, currentStatusTag,
          nextStart, nextFinish] ↔
      CompactNumericVerifierHaltedRows tokenTable width tokenCount
        currentStart currentFinish currentStatusTag
        nextStart nextFinish := by
  have heqEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            currentStart, currentFinish, currentStatusTag,
            nextStart, nextFinish]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 8), #1, #2, #3, #4, #6, #7]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentFinish, nextStart, nextFinish] := by
    funext index
    fin_cases index <;> rfl
  simp [compactNumericVerifierHaltedRowsDef,
    CompactNumericVerifierHaltedRows, heqEnv]

theorem compactNumericVerifierHaltedRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierHaltedRowsDef.val := by
  simp [compactNumericVerifierHaltedRowsDef]

#print axioms compactNumericVerifierHaltedRowsDef_spec
#print axioms compactNumericVerifierHaltedRowsDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierHaltedFormula
