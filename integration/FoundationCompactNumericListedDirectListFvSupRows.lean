import integration.FoundationCompactNumericFormulaFvSup
import integration.FoundationCompactNumericListedDirectNatListAtRows

/-!
# Direct bounded free-variable supremum over natural-list rows

The graph characterizes `listFvSup values` without accepting the result as an
external certificate.  Every listed index plus one is bounded by `maximum`,
and a nonempty list contains an index that attains `maximum`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectListFvSupRows

open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListAtRows

def CompactAdditiveNatListFvSupRows
    (tokenTable width tokenCount boundaryTable count maximum : Nat) : Prop :=
  (forall index, index < count ->
    exists value, value <= maximum /\
      CompactAdditiveNatListAtRows
        tokenTable width tokenCount boundaryTable count index value /\
      value + 1 <= maximum) /\
  ((count = 0 /\ maximum = 0) \/
    exists index, index <= count /\ index < count /\
      exists value, value <= maximum /\
        CompactAdditiveNatListAtRows
          tokenTable width tokenCount boundaryTable count index value /\
        value + 1 = maximum)

def compactAdditiveNatListFvSupRowsDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount boundaryTable count maximum.
    (∀ index < count,
      ∃ value <⁺ maximum,
        !(compactAdditiveNatListAtRowsDef)
          tokenTable width tokenCount boundaryTable count index value ∧
        value + 1 ≤ maximum) ∧
    ((count = 0 ∧ maximum = 0) ∨
      ∃ index <⁺ count,
        index < count ∧
        ∃ value <⁺ maximum,
          !(compactAdditiveNatListAtRowsDef)
            tokenTable width tokenCount boundaryTable count index value ∧
          value + 1 = maximum)”

@[simp] theorem compactAdditiveNatListFvSupRowsDef_spec
    (tokenTable width tokenCount boundaryTable count maximum : Nat) :
    compactAdditiveNatListFvSupRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, boundaryTable, count, maximum] ↔
      CompactAdditiveNatListFvSupRows
        tokenTable width tokenCount boundaryTable count maximum := by
  have hatRows (value index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![value, index, tokenTable, width, tokenCount,
                boundaryTable, count, maximum]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 8), #3, #4, #5, #6, #1, #0])
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows
          tokenTable width tokenCount boundaryTable count index value := by
    have henv :
        (Semiterm.val
            ![value, index, tokenTable, width, tokenCount,
              boundaryTable, count, maximum]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 8), #3, #4, #5, #6, #1, #0]) =
          ![tokenTable, width, tokenCount,
            boundaryTable, count, index, value] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveNatListAtRowsDef_spec
      tokenTable width tokenCount boundaryTable count index value
  simp [compactAdditiveNatListFvSupRowsDef,
    CompactAdditiveNatListFvSupRows, hatRows]

theorem compactAdditiveNatListFvSupRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListFvSupRowsDef.val := by
  simp [compactAdditiveNatListFvSupRowsDef]

private theorem listFvSup_le_of_forall_mem
    {values : List Nat} {bound : Nat}
    (hbound : forall value, value ∈ values -> value + 1 <= bound) :
    listFvSup values <= bound := by
  induction values with
  | nil => simp [listFvSup]
  | cons value values ih =>
      simp only [listFvSup]
      apply max_le
      · exact hbound value (by simp)
      · apply ih
        intro tailValue htailValue
        exact hbound tailValue (List.mem_cons_of_mem value htailValue)

theorem compactAdditiveNatListFvSupRows_iff
    {tokenTable width tokenCount boundaryTable : Nat}
    {values : List Nat}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        boundaryTable values)
    (maximum : Nat) :
    CompactAdditiveNatListFvSupRows
        tokenTable width tokenCount boundaryTable values.length maximum ↔
      maximum = listFvSup values := by
  constructor
  · rintro ⟨hall, hempty | hattained⟩
    · rcases hempty with ⟨hlength, hmaximum⟩
      have hvalues : values = [] := by simpa using hlength
      subst values
      simpa [listFvSup] using hmaximum
    · rcases hattained with
        ⟨index, _hindexBound, hindex,
          value, _hvalueBound, hatRows, hvalueMaximum⟩
      have hatValue :=
        (compactAdditiveNatListAtRows_iff_getI
          hrows index value).mp hatRows
      have hallValues :
          forall candidate, candidate ∈ values -> candidate + 1 <= maximum := by
        intro candidate hcandidate
        obtain ⟨candidateIndex, hcandidateIndex, hcandidateValue⟩ :=
          List.mem_iff_getElem.mp hcandidate
        rcases hall candidateIndex hcandidateIndex with
          ⟨rowValue, _hrowValueBound, hrowValue, hrowMaximum⟩
        have hrowGet :=
          (compactAdditiveNatListAtRows_iff_getI
            hrows candidateIndex rowValue).mp hrowValue
        rw [List.getI_eq_getElem values hcandidateIndex,
          hcandidateValue] at hrowGet
        simpa [hrowGet] using hrowMaximum
      have hsupLe : listFvSup values <= maximum :=
        listFvSup_le_of_forall_mem hallValues
      have hvalueMem : value ∈ values := by
        rw [← hatValue.2, List.getI_eq_getElem values hatValue.1]
        exact List.getElem_mem hatValue.1
      have hvalueLt : value < listFvSup values :=
        mem_lt_listFvSup hvalueMem
      omega
  · intro hmaximum
    have hall : forall index, index < values.length ->
        exists value, value <= maximum /\
          CompactAdditiveNatListAtRows tokenTable width tokenCount
            boundaryTable values.length index value /\
          value + 1 <= maximum := by
      intro index hindex
      let value := values.getI index
      have hvalueMem : value ∈ values := by
        dsimp [value]
        rw [List.getI_eq_getElem values hindex]
        exact List.getElem_mem hindex
      have hvalueLt : value < listFvSup values :=
        mem_lt_listFvSup hvalueMem
      have hatRows : CompactAdditiveNatListAtRows
          tokenTable width tokenCount boundaryTable values.length index value :=
        (compactAdditiveNatListAtRows_iff_getI
          hrows index value).mpr ⟨hindex, rfl⟩
      refine ⟨value, ?_, hatRows, ?_⟩
      · omega
      · omega
    refine ⟨hall, ?_⟩
    by_cases hvalues : values = []
    · subst values
      left
      simpa [listFvSup] using hmaximum
    · right
      have hsupPos : 0 < listFvSup values := by
        cases values with
        | nil => contradiction
        | cons value values =>
            simp only [listFvSup]
            exact lt_of_lt_of_le (Nat.zero_lt_succ value)
              (le_max_left _ _)
      have hpredMem : listFvSup values - 1 ∈ values :=
        pred_mem_of_listFvSup_pos values hsupPos
      obtain ⟨index, hindex, hindexValue⟩ :=
        List.mem_iff_getElem.mp hpredMem
      let value := values.getI index
      have hvalue : value = listFvSup values - 1 := by
        dsimp [value]
        rw [List.getI_eq_getElem values hindex, hindexValue]
      have hatRows : CompactAdditiveNatListAtRows
          tokenTable width tokenCount boundaryTable values.length index value :=
        (compactAdditiveNatListAtRows_iff_getI
          hrows index value).mpr ⟨hindex, rfl⟩
      refine ⟨index, Nat.le_of_lt hindex, hindex,
        value, ?_, hatRows, ?_⟩
      · omega
      · omega

#print axioms compactAdditiveNatListFvSupRowsDef_spec
#print axioms compactAdditiveNatListFvSupRowsDef_sigmaZero
#print axioms compactAdditiveNatListFvSupRows_iff

end FoundationCompactNumericListedDirectListFvSupRows
