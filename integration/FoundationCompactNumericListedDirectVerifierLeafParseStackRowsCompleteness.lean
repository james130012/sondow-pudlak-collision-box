import integration.FoundationCompactNumericListedDirectVerifierLeafParseStackRows

/-!
# Converse construction for successful leaf parse stacks

Typed source and target task/result rows, sharing their canonical row-graph
bounds, realize the exact stack transition of a successful leaf parse.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierLeafParseStackRowsCompleteness

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
open FoundationCompactNumericListedDirectVerifierLeafParseStackRows

theorem CompactNumericVerifierLeafParseStackRows.of_rows
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
        gammaBoundary Gamma)
    (hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceTaskBoundary sourceTasks.length
        currentTaskTableWidth currentTaskValueBound)
    (htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetTaskBoundary targetTasks.length
        currentTaskTableWidth currentTaskValueBound)
    (hsourceValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceValueBoundary sourceValues.length
        currentValueTableWidth currentValueValueBound)
    (htargetValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetValueBoundary targetValues.length
        currentValueTableWidth currentValueValueBound)
    (htaskTableWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskValueBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueTableWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueValueBound : nextValueValueBound = currentValueValueBound)
    (hsourceTaskNonempty : 1 ≤ sourceTasks.length)
    (htasks : targetTasks = sourceTasks.drop 1)
    (hvalues : targetValues = (Gamma, result) :: sourceValues)
    (hstatus : nextStatusTag = 0) :
    CompactNumericVerifierLeafParseStackRows
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
      (compactAdditiveBoolTag result) nextStatusTag := by
  refine ⟨htaskTableWidth, htaskValueBound, hvalueTableWidth,
    hvalueValueBound, hstatus, ?_, ?_⟩
  · exact (compactNumericVerifierTaskListDropRows_iff_drop_of_rows
      hsourceTaskRows htargetTaskRows hsourceTaskGraph htargetTaskGraph).mpr
        ⟨hsourceTaskNonempty, htasks⟩
  · exact (compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
      hsourceValueRows htargetValueRows hGammaRows
        hsourceValueGraph htargetValueGraph).mpr
        ⟨by simp, by simpa using hvalues⟩

theorem compactNumericVerifierLeafParseStackRows_iff_of_rows
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
        gammaBoundary Gamma)
    (hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceTaskBoundary sourceTasks.length
        currentTaskTableWidth currentTaskValueBound)
    (htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetTaskBoundary targetTasks.length
        currentTaskTableWidth currentTaskValueBound)
    (hsourceValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceValueBoundary sourceValues.length
        currentValueTableWidth currentValueValueBound)
    (htargetValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetValueBoundary targetValues.length
        currentValueTableWidth currentValueValueBound) :
    CompactNumericVerifierLeafParseStackRows
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
        (compactAdditiveBoolTag result) nextStatusTag ↔
      1 ≤ sourceTasks.length ∧
        targetTasks = sourceTasks.drop 1 ∧
        targetValues = (Gamma, result) :: sourceValues ∧
        nextTaskTableWidth = currentTaskTableWidth ∧
        nextTaskValueBound = currentTaskValueBound ∧
        nextValueTableWidth = currentValueTableWidth ∧
        nextValueValueBound = currentValueValueBound ∧
        nextStatusTag = 0 := by
  constructor
  · intro hrows
    have hsourceTaskNonempty : 1 ≤ sourceTasks.length :=
      hrows.2.2.2.2.2.1.1
    rcases hrows.sound hsourceTaskRows htargetTaskRows
        hsourceValueRows htargetValueRows hGammaRows with
      ⟨htasks, hvalues, htaskTableWidth, htaskValueBound,
        hvalueTableWidth, hvalueValueBound, hstatus⟩
    exact ⟨hsourceTaskNonempty, htasks, hvalues,
      htaskTableWidth, htaskValueBound,
      hvalueTableWidth, hvalueValueBound, hstatus⟩
  · rintro ⟨hsourceTaskNonempty, htasks, hvalues,
      htaskTableWidth, htaskValueBound,
      hvalueTableWidth, hvalueValueBound, hstatus⟩
    exact CompactNumericVerifierLeafParseStackRows.of_rows
      hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
      hGammaRows hsourceTaskGraph htargetTaskGraph
      hsourceValueGraph htargetValueGraph
      htaskTableWidth htaskValueBound hvalueTableWidth hvalueValueBound
      hsourceTaskNonempty htasks hvalues hstatus

#print axioms CompactNumericVerifierLeafParseStackRows.of_rows
#print axioms compactNumericVerifierLeafParseStackRows_iff_of_rows

end FoundationCompactNumericListedDirectVerifierLeafParseStackRowsCompleteness
