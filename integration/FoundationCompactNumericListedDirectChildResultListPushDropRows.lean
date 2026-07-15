import integration.FoundationCompactNumericListedDirectChildResultBoundedHeadEquality

/-!
# Direct child-result stack push after dropping a prefix

The target head is a prescribed checked context and Boolean.  Every later
target row equals the corresponding source row after `consumed` source rows.
The relation is exactly `target = head :: source.drop consumed` under the real
child-result row graphs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectChildResultListPushDropRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedRowsEquality
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality

def CompactNumericChildResultListPushDropRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      expectedGammaBoundary expectedGammaCount
      _tableWidth valueBound consumed expectedBool : Nat) : Prop :=
  consumed ≤ sourceCount ∧
    sourceCount + 1 = consumed + targetCount ∧
    1 ≤ targetCount ∧
    CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount targetBoundary
        expectedGammaBoundary expectedGammaCount valueBound 0 expectedBool ∧
    ∀ index < sourceCount,
      consumed + index < sourceCount →
        CompactNumericChildResultBoundedRowsEq
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (consumed + index) (index + 1)

def compactNumericChildResultListPushDropRowsDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      expectedGammaBoundary expectedGammaCount
      tableWidth valueBound consumed expectedBool.
    consumed ≤ sourceCount ∧
    sourceCount + 1 = consumed + targetCount ∧
    1 ≤ targetCount ∧
    !(compactNumericChildResultBoundedHeadEqDef)
      tokenTable width tokenCount targetBoundary
        expectedGammaBoundary expectedGammaCount valueBound 0 expectedBool ∧
    ∀ index < sourceCount,
      consumed + index < sourceCount →
        !(compactNumericChildResultBoundedRowsEqDef)
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (consumed + index) (index + 1)”

@[simp] theorem compactNumericChildResultListPushDropRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      expectedGammaBoundary expectedGammaCount
      tableWidth valueBound consumed expectedBool : Nat) :
    compactNumericChildResultListPushDropRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          expectedGammaBoundary, expectedGammaCount,
          tableWidth, valueBound, consumed, expectedBool] ↔
      CompactNumericChildResultListPushDropRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount
          expectedGammaBoundary expectedGammaCount
          tableWidth valueBound consumed expectedBool := by
  have hhead :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                expectedGammaBoundary, expectedGammaCount,
                tableWidth, valueBound, consumed, expectedBool]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #5,
              #7, #8, #10, ‘0’, #12])
          Empty.elim) compactNumericChildResultBoundedHeadEqDef.val ↔
        CompactNumericChildResultBoundedHeadEq
          tokenTable width tokenCount targetBoundary
            expectedGammaBoundary expectedGammaCount valueBound
            0 expectedBool := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              expectedGammaBoundary, expectedGammaCount,
              tableWidth, valueBound, consumed, expectedBool]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #5,
            #7, #8, #10, ‘0’, #12]) =
          ![tokenTable, width, tokenCount, targetBoundary,
            expectedGammaBoundary, expectedGammaCount, valueBound,
            0, expectedBool] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultBoundedHeadEqDef_spec
      tokenTable width tokenCount targetBoundary
      expectedGammaBoundary expectedGammaCount valueBound 0 expectedBool
  have hrow (index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![index, tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                expectedGammaBoundary, expectedGammaCount,
                tableWidth, valueBound, consumed, expectedBool]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 14), #2, #3, #4, #6,
              #11, ‘(#12 + #0)’, ‘(#0 + 1)’])
          Empty.elim) compactNumericChildResultBoundedRowsEqDef.val ↔
        CompactNumericChildResultBoundedRowsEq
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (consumed + index) (index + 1) := by
    have henv :
        (Semiterm.val
            ![index, tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              expectedGammaBoundary, expectedGammaCount,
              tableWidth, valueBound, consumed, expectedBool]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 14), #2, #3, #4, #6,
            #11, ‘(#12 + #0)’, ‘(#0 + 1)’]) =
          ![tokenTable, width, tokenCount,
            sourceBoundary, targetBoundary, valueBound,
            consumed + index, index + 1] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultBoundedRowsEqDef_spec
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound (consumed + index) (index + 1)
  simp [compactNumericChildResultListPushDropRowsDef,
    CompactNumericChildResultListPushDropRows, hhead, hrow]

theorem compactNumericChildResultListPushDropRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultListPushDropRowsDef.val := by
  simp [compactNumericChildResultListPushDropRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      expectedGammaBoundary tableWidth valueBound consumed : Nat}
    {expectedGamma : List (List Nat)} {expectedResult : Bool}
    {source target : List CompactNumericChildResult}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hexpectedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedGammaBoundary expectedGamma)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (hconsumed : consumed ≤ source.length)
    (hpush : target =
      (expectedGamma, expectedResult) :: source.drop consumed) :
    CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length
        expectedGammaBoundary expectedGamma.length
        tableWidth valueBound consumed
        (compactAdditiveBoolTag expectedResult) := by
  have hcount : source.length + 1 = consumed + target.length := by
    rw [hpush]
    simp [List.length_drop]
    omega
  have htargetNonempty : 1 ≤ target.length := by
    rw [hpush]
    simp
  have htargetZero : 0 < target.length := by omega
  have hheadValue :
      target.getI 0 = (expectedGamma, expectedResult) := by
    rw [hpush]
    simp
  have hhead := CompactNumericChildResultBoundedHeadEq.of_value_eq
    htargetGraph htargetZero hexpectedRows htargetRows hheadValue
  refine ⟨hconsumed, hcount, htargetNonempty, hhead, ?_⟩
  intro index hindex hremaining
  have htargetIndex : index + 1 < target.length := by omega
  have hdropIndex : index < (source.drop consumed).length := by
    rw [List.length_drop]
    omega
  have hvalue :
      target.getI (index + 1) = source.getI (consumed + index) := by
    rw [hpush, List.getI_cons_succ]
    rw [List.getI_eq_getElem _ hdropIndex]
    rw [List.getI_eq_getElem _ hremaining]
    simp
  exact CompactNumericChildResultBoundedRowsEq.of_value_eq
    hsourceGraph htargetGraph rfl rfl
      hremaining htargetIndex hsourceRows htargetRows hvalue

theorem CompactNumericChildResultListPushDropRows.eq_push_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      expectedGammaBoundary tableWidth valueBound consumed : Nat}
    {expectedGamma : List (List Nat)} {expectedResult : Bool}
    {source target : List CompactNumericChildResult}
    (hpushRows : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length
        expectedGammaBoundary expectedGamma.length
        tableWidth valueBound consumed
        (compactAdditiveBoolTag expectedResult))
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hexpectedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedGammaBoundary expectedGamma) :
    target = (expectedGamma, expectedResult) :: source.drop consumed := by
  have hconsumed := hpushRows.1
  have hcount := hpushRows.2.1
  have htargetNonempty := hpushRows.2.2.1
  have hhead := hpushRows.2.2.2.1
  have htailRows := hpushRows.2.2.2.2
  apply List.ext_getElem
  · simp [List.length_drop]
    omega
  · intro index htargetIndex hconsIndex
    cases index with
    | zero =>
        have hvalue := hhead.value_eq
          (by omega) hexpectedRows htargetRows
        rw [List.getI_eq_getElem _ htargetIndex] at hvalue
        simpa using hvalue
    | succ index =>
        have hsourceIndex : consumed + index < source.length := by omega
        have hvalue :=
          (htailRows index (by omega) hsourceIndex).value_eq
            hsourceIndex htargetIndex hsourceRows htargetRows
        rw [List.getI_eq_getElem _ htargetIndex] at hvalue
        rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
        simpa using hvalue

theorem compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      expectedGammaBoundary tableWidth valueBound consumed : Nat}
    {expectedGamma : List (List Nat)} {expectedResult : Bool}
    {source target : List CompactNumericChildResult}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hexpectedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedGammaBoundary expectedGamma)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound) :
    CompactNumericChildResultListPushDropRows
        tokenTable width tokenCount
          sourceBoundary source.length targetBoundary target.length
          expectedGammaBoundary expectedGamma.length
          tableWidth valueBound consumed
          (compactAdditiveBoolTag expectedResult) ↔
      consumed ≤ source.length ∧
        target = (expectedGamma, expectedResult) :: source.drop consumed := by
  constructor
  · intro hpushRows
    exact ⟨hpushRows.1,
      hpushRows.eq_push_drop_of_rows
        hsourceRows htargetRows hexpectedRows⟩
  · rintro ⟨hconsumed, hpush⟩
    exact CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hexpectedRows
        hsourceGraph htargetGraph hconsumed hpush

#print axioms compactNumericChildResultListPushDropRowsDef_spec
#print axioms compactNumericChildResultListPushDropRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
#print axioms CompactNumericChildResultListPushDropRows.eq_push_drop_of_rows
#print axioms compactNumericChildResultListPushDropRows_iff_push_drop_of_rows

end FoundationCompactNumericListedDirectChildResultListPushDropRows
