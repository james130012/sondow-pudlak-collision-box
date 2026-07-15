import integration.FoundationCompactNumericListedDirectVerifierParseStateFrameRows
import integration.FoundationCompactNumericListedDirectVerifierTaskListDropRows
import integration.FoundationCompactNumericListedDirectChildResultListPushDropRows

/-!
# Exact stack changes for successful leaf parsing

A successful leaf node removes the parse-task head, preserves the remaining
task stack, and pushes exactly one checked child result.  The relation also
locks both row-graph bounds to the current state's bounds and keeps the next
state running.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierLeafParseStackRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskListDropRows
open FoundationCompactNumericListedDirectChildResultListPushDropRows

def CompactNumericVerifierLeafParseStackRows
    (tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag : Nat) : Prop :=
  nextTaskTableWidth = currentTaskTableWidth ∧
    nextTaskValueBound = currentTaskValueBound ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    nextStatusTag = 0 ∧
    CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      currentTaskTableWidth currentTaskValueBound 1 ∧
    CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentValueTableWidth currentValueValueBound 0 resultBool

def compactNumericVerifierLeafParseStackRowsDef :
    𝚺₀.Semisentence 23 := .mkSigma
  “tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag.
    nextTaskTableWidth = currentTaskTableWidth ∧
    nextTaskValueBound = currentTaskValueBound ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    nextStatusTag = 0 ∧
    !(compactNumericVerifierTaskListDropRowsDef)
      tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      currentTaskTableWidth currentTaskValueBound 1 ∧
    !(compactNumericChildResultListPushDropRowsDef)
      tokenTable width tokenCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentValueTableWidth currentValueValueBound 0 resultBool”

@[simp] theorem compactNumericVerifierLeafParseStackRowsDef_spec
    (tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag : Nat) :
    compactNumericVerifierLeafParseStackRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceTaskBoundary, sourceTaskCount,
          targetTaskBoundary, targetTaskCount,
          sourceValueBoundary, sourceValueCount,
          targetValueBoundary, targetValueCount,
          gammaBoundary, gammaCount,
          currentTaskTableWidth, currentTaskValueBound,
          currentValueTableWidth, currentValueValueBound,
          nextTaskTableWidth, nextTaskValueBound,
          nextValueTableWidth, nextValueValueBound,
          resultBool, nextStatusTag] ↔
      CompactNumericVerifierLeafParseStackRows
        tokenTable width tokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        gammaBoundary gammaCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        resultBool nextStatusTag := by
  let env : Fin 23 → Nat :=
    ![tokenTable, width, tokenCount,
      sourceTaskBoundary, sourceTaskCount,
      targetTaskBoundary, targetTaskCount,
      sourceValueBoundary, sourceValueCount,
      targetValueBoundary, targetValueCount,
      gammaBoundary, gammaCount,
      currentTaskTableWidth, currentTaskValueBound,
      currentValueTableWidth, currentValueValueBound,
      nextTaskTableWidth, nextTaskValueBound,
      nextValueTableWidth, nextValueValueBound,
      resultBool, nextStatusTag]
  change compactNumericVerifierLeafParseStackRowsDef.val.Evalb env ↔ _
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2,
          #3, #4, #5, #6, #13, #14, ‘1’]) =
        ![tokenTable, width, tokenCount,
          sourceTaskBoundary, sourceTaskCount,
          targetTaskBoundary, targetTaskCount,
          currentTaskTableWidth, currentTaskValueBound, 1] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hvalueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2,
          #7, #8, #9, #10, #11, #12, #15, #16, ‘0’, #21]) =
        ![tokenTable, width, tokenCount,
          sourceValueBoundary, sourceValueCount,
          targetValueBoundary, targetValueCount,
          gammaBoundary, gammaCount,
          currentValueTableWidth, currentValueValueBound, 0, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierLeafParseStackRowsDef,
    CompactNumericVerifierLeafParseStackRows,
    htaskEnv, hvalueEnv]
  simp [env]

theorem compactNumericVerifierLeafParseStackRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierLeafParseStackRowsDef.val := by
  simp [compactNumericVerifierLeafParseStackRowsDef]

theorem CompactNumericVerifierLeafParseStackRows.sound
    {tokenTable width tokenCount
      sourceTaskBoundary targetTaskBoundary
      sourceValueBoundary targetValueBoundary gammaBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound nextStatusTag : Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {Gamma : List (List Nat)} {result : Bool}
    (hrows : CompactNumericVerifierLeafParseStackRows
      tokenTable width tokenCount
      sourceTaskBoundary sourceTasks.length
      targetTaskBoundary targetTasks.length
      sourceValueBoundary sourceValues.length
      targetValueBoundary targetValues.length
      gammaBoundary Gamma.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      (compactAdditiveBoolTag result) nextStatusTag)
    (hsourceTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceTaskBoundary sourceTasks)
    (htargetTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetTaskBoundary targetTasks)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetValueBoundary targetValues)
    (hGammaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma) :
    targetTasks = sourceTasks.drop 1 ∧
      targetValues = (Gamma, result) :: sourceValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  rcases hrows with
    ⟨htaskWidth, htaskBound, hvalueWidth, hvalueBound,
      hstatus, htaskDrop, hvaluePush⟩
  have htasks := htaskDrop.eq_drop_of_rows
    hsourceTaskRows htargetTaskRows
  have hvalues := hvaluePush.eq_push_drop_of_rows
    hsourceValueRows htargetValueRows hGammaRows
  exact ⟨by simpa using htasks, by simpa using hvalues,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩

#print axioms compactNumericVerifierLeafParseStackRowsDef_spec
#print axioms compactNumericVerifierLeafParseStackRowsDef_sigmaZero
#print axioms CompactNumericVerifierLeafParseStackRows.sound

end FoundationCompactNumericListedDirectVerifierLeafParseStackRows
