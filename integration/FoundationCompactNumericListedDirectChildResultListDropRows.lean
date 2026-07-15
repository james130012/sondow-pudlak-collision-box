import integration.FoundationCompactNumericListedDirectChildResultBoundedRowsEquality

/-!
# Direct row graph for dropping a child-result-list prefix

The target list begins at a certified source index.  Every target child result
is directly equal to the corresponding shifted source result, with all parser
coordinates bounded by the common value bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectChildResultListDropRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedRowsEquality

def CompactNumericChildResultListDropRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      _tableWidth valueBound consumed : Nat) : Prop :=
  consumed ≤ sourceCount ∧
    sourceCount = consumed + targetCount ∧
    ∀ index < targetCount,
      CompactNumericChildResultBoundedRowsEq
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (consumed + index) index

def compactNumericChildResultListDropRowsDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound consumed.
    consumed ≤ sourceCount ∧
    sourceCount = consumed + targetCount ∧
    ∀ index < targetCount,
      !(compactNumericChildResultBoundedRowsEqDef)
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (consumed + index) index”

@[simp] theorem compactNumericChildResultListDropRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound consumed : Nat) :
    compactNumericChildResultListDropRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, consumed] ↔
      CompactNumericChildResultListDropRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount
          tableWidth valueBound consumed := by
  have hrow (index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![index, tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                tableWidth, valueBound, consumed]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 11), #2, #3, #4, #6,
              #9, ‘(#10 + #0)’, #0])
          Empty.elim) compactNumericChildResultBoundedRowsEqDef.val ↔
        CompactNumericChildResultBoundedRowsEq
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (consumed + index) index := by
    have henv :
        (Semiterm.val
            ![index, tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              tableWidth, valueBound, consumed]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 11), #2, #3, #4, #6,
            #9, ‘(#10 + #0)’, #0]) =
          ![tokenTable, width, tokenCount,
            sourceBoundary, targetBoundary, valueBound,
            consumed + index, index] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultBoundedRowsEqDef_spec
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound (consumed + index) index
  simp [compactNumericChildResultListDropRowsDef,
    CompactNumericChildResultListDropRows, hrow]

theorem compactNumericChildResultListDropRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultListDropRowsDef.val := by
  simp [compactNumericChildResultListDropRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.childResultDropRows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound consumed : Nat}
    {source target : List CompactNumericChildResult}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (hconsumed : consumed ≤ source.length)
    (hdrop : target = source.drop consumed) :
    CompactNumericChildResultListDropRows
      tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length
        tableWidth valueBound consumed := by
  have hcount : source.length = consumed + target.length := by
    rw [hdrop, List.length_drop]
    omega
  refine ⟨hconsumed, hcount, ?_⟩
  intro index hindex
  have hsourceIndex : consumed + index < source.length := by omega
  have hdropIndex : index < (source.drop consumed).length := by
    simpa [hdrop] using hindex
  have hvalue : target.getI index = source.getI (consumed + index) := by
    rw [hdrop]
    rw [List.getI_eq_getElem _ hdropIndex]
    rw [List.getI_eq_getElem _ hsourceIndex]
    simp
  exact CompactNumericChildResultBoundedRowsEq.of_value_eq
    hsourceGraph htargetGraph rfl rfl
      hsourceIndex hindex hsourceRows htargetRows hvalue

theorem CompactNumericChildResultListDropRows.eq_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound consumed : Nat}
    {source target : List CompactNumericChildResult}
    (hdropRows : CompactNumericChildResultListDropRows
      tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length
        tableWidth valueBound consumed)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    target = source.drop consumed := by
  have hconsumed := hdropRows.1
  have hcount := hdropRows.2.1
  have hrowPairs := hdropRows.2.2
  apply List.ext_getElem
  · rw [List.length_drop]
    omega
  · intro index htargetIndex hdropIndex
    have hsourceIndex : consumed + index < source.length := by omega
    have hvalue := (hrowPairs index htargetIndex).value_eq
      hsourceIndex htargetIndex hsourceRows htargetRows
    rw [List.getI_eq_getElem _ htargetIndex] at hvalue
    rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
    simpa using hvalue

theorem compactNumericChildResultListDropRows_iff_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound consumed : Nat}
    {source target : List CompactNumericChildResult}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound) :
    CompactNumericChildResultListDropRows
        tokenTable width tokenCount
          sourceBoundary source.length targetBoundary target.length
          tableWidth valueBound consumed ↔
      consumed ≤ source.length ∧ target = source.drop consumed := by
  constructor
  · intro hdropRows
    exact ⟨hdropRows.1,
      hdropRows.eq_drop_of_rows hsourceRows htargetRows⟩
  · rintro ⟨hconsumed, hdrop⟩
    exact CompactAdditiveStructuredListElementRowLayouts.childResultDropRows
      hsourceRows htargetRows hsourceGraph htargetGraph hconsumed hdrop

#print axioms compactNumericChildResultListDropRowsDef_spec
#print axioms compactNumericChildResultListDropRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.childResultDropRows
#print axioms CompactNumericChildResultListDropRows.eq_drop_of_rows
#print axioms compactNumericChildResultListDropRows_iff_drop_of_rows

end FoundationCompactNumericListedDirectChildResultListDropRows
