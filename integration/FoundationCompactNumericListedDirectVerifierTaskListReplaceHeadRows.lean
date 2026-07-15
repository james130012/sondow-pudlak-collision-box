import integration.FoundationCompactNumericListedDirectVerifierTaskListDropRows

/-!
# Direct verifier-task rows for replacing one head by a short prefix

A parse step removes its parse-task head and may prepend zero, two, or three
new tasks.  This bounded relation identifies every remaining target row with
the corresponding source row after that replacement.  Prefix contents are
checked separately by explicit indexed task rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskListReplaceHeadRows

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskListDropRows

def CompactNumericVerifierTaskListReplaceHeadRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      valueBound prefixCount : Nat) : Prop :=
  1 ≤ sourceCount ∧
    sourceCount + prefixCount = targetCount + 1 ∧
    ∀ index < sourceCount,
      1 + index < sourceCount →
        CompactNumericVerifierTaskBoundedRowsEq
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (1 + index) (prefixCount + index)

def compactNumericVerifierTaskListReplaceHeadRowsDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      valueBound prefixCount.
    1 ≤ sourceCount ∧
    sourceCount + prefixCount = targetCount + 1 ∧
    ∀ index < sourceCount,
      1 + index < sourceCount →
        !(compactNumericVerifierTaskBoundedRowsEqDef)
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (1 + index) (prefixCount + index)”

@[simp] theorem compactNumericVerifierTaskListReplaceHeadRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      valueBound prefixCount : Nat) :
    compactNumericVerifierTaskListReplaceHeadRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          valueBound, prefixCount] ↔
      CompactNumericVerifierTaskListReplaceHeadRows
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        valueBound prefixCount := by
  have hrow (index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![index, tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                valueBound, prefixCount]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 10), #2, #3, #4, #6,
              #8, ‘(1 + #0)’, ‘(#9 + #0)’])
          Empty.elim) compactNumericVerifierTaskBoundedRowsEqDef.val ↔
        CompactNumericVerifierTaskBoundedRowsEq
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (1 + index) (prefixCount + index) := by
    have henv :
        (Semiterm.val
            ![index, tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              valueBound, prefixCount]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 10), #2, #3, #4, #6,
            #8, ‘(1 + #0)’, ‘(#9 + #0)’]) =
          ![tokenTable, width, tokenCount,
            sourceBoundary, targetBoundary, valueBound,
            1 + index, prefixCount + index] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericVerifierTaskBoundedRowsEqDef_spec
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound (1 + index) (prefixCount + index)
  simp [compactNumericVerifierTaskListReplaceHeadRowsDef,
    CompactNumericVerifierTaskListReplaceHeadRows, hrow]

theorem compactNumericVerifierTaskListReplaceHeadRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskListReplaceHeadRowsDef.val := by
  simp [compactNumericVerifierTaskListReplaceHeadRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.verifierTaskReplaceHeadRows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound prefixCount : Nat}
    {source target : List CompactNumericVerifierTask}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (hsourceNonempty : 1 ≤ source.length)
    (hprefix : prefixCount ≤ target.length)
    (htail : target.drop prefixCount = source.drop 1) :
    CompactNumericVerifierTaskListReplaceHeadRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      valueBound prefixCount := by
  have hcount : source.length + prefixCount = target.length + 1 := by
    have htargetDropLength := congrArg List.length htail
    simp only [List.length_drop] at htargetDropLength
    omega
  refine ⟨hsourceNonempty, hcount, ?_⟩
  intro index hindex hremaining
  have htargetIndex : prefixCount + index < target.length := by omega
  have hsourceIndex : 1 + index < source.length := hremaining
  have htargetDropIndex : index < (target.drop prefixCount).length := by
    simp only [List.length_drop]
    omega
  have hsourceDropIndex : index < (source.drop 1).length := by
    simp only [List.length_drop]
    omega
  have hvalueDrop := congrArg
    (fun values : List CompactNumericVerifierTask => values.getI index) htail
  rw [List.getI_eq_getElem _ htargetDropIndex] at hvalueDrop
  rw [List.getI_eq_getElem _ hsourceDropIndex] at hvalueDrop
  have hvalue : target.getI (prefixCount + index) =
      source.getI (1 + index) := by
    rw [List.getI_eq_getElem _ htargetIndex]
    rw [List.getI_eq_getElem _ hsourceIndex]
    simpa [Nat.add_comm] using hvalueDrop
  exact CompactNumericVerifierTaskBoundedRowsEq.of_value_eq
    hsourceGraph htargetGraph hsourceIndex htargetIndex
      hsourceRows htargetRows hvalue

theorem CompactNumericVerifierTaskListReplaceHeadRows.eq_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound prefixCount : Nat}
    {source target : List CompactNumericVerifierTask}
    (hreplace : CompactNumericVerifierTaskListReplaceHeadRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      valueBound prefixCount)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    target.drop prefixCount = source.drop 1 := by
  have hsourceNonempty := hreplace.1
  have hcount := hreplace.2.1
  have hrows := hreplace.2.2
  have hprefix : prefixCount ≤ target.length := by omega
  apply List.ext_getElem
  · simp only [List.length_drop]
    omega
  · intro index htargetDropIndex hsourceDropIndex
    have hsourceIndex : 1 + index < source.length := by
      simp only [List.length_drop] at hsourceDropIndex
      omega
    have htargetIndex : prefixCount + index < target.length := by
      simp only [List.length_drop] at htargetDropIndex
      omega
    have hvalue := (hrows index (by omega) hsourceIndex).value_eq
      hsourceIndex htargetIndex hsourceRows htargetRows
    rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
    rw [List.getI_eq_getElem _ htargetIndex] at hvalue
    simpa [Nat.add_comm] using hvalue

theorem compactNumericVerifierTaskListReplaceHeadRows_iff_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound prefixCount : Nat}
    {source target : List CompactNumericVerifierTask}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound) :
    CompactNumericVerifierTaskListReplaceHeadRows
        tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length
        valueBound prefixCount ↔
      1 ≤ source.length ∧ prefixCount ≤ target.length ∧
        target.drop prefixCount = source.drop 1 := by
  constructor
  · intro hreplace
    have hprefix : prefixCount ≤ target.length := by
      have hsourceNonempty := hreplace.1
      have hcount := hreplace.2.1
      omega
    exact ⟨hreplace.1, hprefix,
      hreplace.eq_drop_of_rows hsourceRows htargetRows⟩
  · rintro ⟨hsourceNonempty, hprefix, htail⟩
    exact
      CompactAdditiveStructuredListElementRowLayouts.verifierTaskReplaceHeadRows
        hsourceRows htargetRows hsourceGraph htargetGraph
          hsourceNonempty hprefix htail

#print axioms compactNumericVerifierTaskListReplaceHeadRowsDef_spec
#print axioms compactNumericVerifierTaskListReplaceHeadRowsDef_sigmaZero
#print axioms
  CompactAdditiveStructuredListElementRowLayouts.verifierTaskReplaceHeadRows
#print axioms CompactNumericVerifierTaskListReplaceHeadRows.eq_drop_of_rows
#print axioms compactNumericVerifierTaskListReplaceHeadRows_iff_drop_of_rows

end FoundationCompactNumericListedDirectVerifierTaskListReplaceHeadRows
