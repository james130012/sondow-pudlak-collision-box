import integration.FoundationCompactNumericListedDirectNatListListRowsRealization

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListWitnessRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierValueRealization

def CompactAdditiveNatListListWitnessRows
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) : Prop :=
  CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount boundaryTable count ∧
    boundarySize = Nat.size boundaryTable ∧
    boundarySize ≤ (count + 1) * tokenCount

def compactAdditiveNatListListWitnessRowsDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount start count finish boundaryTable boundarySize.
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount start count finish boundaryTable ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount boundaryTable count ∧
    !(compactNatSizeDef) boundarySize boundaryTable ∧
    boundarySize ≤ (count + 1) * tokenCount”

@[simp] theorem compactAdditiveNatListListWitnessRowsDef_spec
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) :
    compactAdditiveNatListListWitnessRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, start, count, finish,
          boundaryTable, boundarySize] ↔
      CompactAdditiveNatListListWitnessRows
        tokenTable width tokenCount start count finish boundaryTable
          boundarySize := by
  let env : Fin 8 → Nat :=
    ![tokenTable, width, tokenCount, start, count, finish,
      boundaryTable, boundarySize]
  change compactAdditiveNatListListWitnessRowsDef.val.Evalb env ↔ _
  have hlayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 8), #1, #2, #3, #4, #5, #6]) =
      ![tokenTable, width, tokenCount, start, count, finish,
        boundaryTable] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 8), #1, #2, #6, #4]) =
      ![tokenTable, width, tokenCount, boundaryTable, count] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactAdditiveNatListListWitnessRowsDef,
    CompactAdditiveNatListListWitnessRows, hlayoutEnv, hrowsEnv, env]

theorem compactAdditiveNatListListWitnessRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListListWitnessRowsDef.val := by
  simp [compactAdditiveNatListListWitnessRowsDef]

theorem CompactAdditiveNatListListWitnessRows.realize
    {tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat}
    (hrows : CompactAdditiveNatListListWitnessRows
      tokenTable width tokenCount start count finish boundaryTable
        boundarySize) :
    ∃ values : List (List Nat),
      values.length = count ∧
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount start finish values ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          boundaryTable values := by
  rcases hrows with ⟨hlayout, hwellFormed, hsizeEq, hsize⟩
  classical
  have hexists (index : Nat) (hindex : index < count) :
      ∃ value : List Nat,
      ∃ left, left ≤ tokenCount ∧
      ∃ right, right ≤ tokenCount ∧
        CompactFixedWidthEntry boundaryTable tokenCount index left ∧
        CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
        CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount left right value := by
    rcases hwellFormed index hindex with
      ⟨left, hleft, right, hright, innerCount, _hinnerCount,
        hleftEntry, hrightEntry, hslice⟩
    rcases CompactAdditiveNatListSlice.realizeDirectLayout hslice hright with
      ⟨value, _hvalueLength, hvalue⟩
    exact ⟨value, left, hleft, right, hright,
      hleftEntry, hrightEntry, hvalue⟩
  let valueAt (index : Fin count) : List Nat :=
    Classical.choose (hexists index index.isLt)
  let values : List (List Nat) := List.ofFn valueAt
  have hlength : values.length = count := by
    simp [values]
  have hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        boundaryTable values := by
    intro index hindex
    have hcount : index < count := by
      simpa [hlength] using hindex
    have hspec := Classical.choose_spec (hexists index hcount)
    rcases hspec with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, hvalue⟩
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    have hget : values.getI index = valueAt ⟨index, hcount⟩ := by
      rw [List.getI_eq_getElem _
        (by simpa [hlength] using hcount)]
      simp [values]
    rw [hget]
    exact hvalue
  refine ⟨values, hlength, ⟨boundaryTable, ?_, hvalueRows, ?_⟩,
    hvalueRows⟩
  · simpa only [hlength] using hlayout
  · rw [hlength, ← hsizeEq]
    exact hsize

theorem CompactAdditiveNatListListDirectLayout.exists_witnessRows
    {tokenTable width tokenCount start finish : Nat}
    {values : List (List Nat)}
    (hlayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount start finish values) :
    ∃ boundaryTable boundarySize,
      CompactAdditiveNatListListWitnessRows
        tokenTable width tokenCount start values.length finish boundaryTable
          boundarySize := by
  rcases hlayout with ⟨boundaryTable, hstructure, hvalueRows, hsize⟩
  refine ⟨boundaryTable, Nat.size boundaryTable,
    hstructure, ?_, rfl, hsize⟩
  exact CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
    hvalueRows

#print axioms compactAdditiveNatListListWitnessRowsDef_spec
#print axioms compactAdditiveNatListListWitnessRowsDef_sigmaZero
#print axioms CompactAdditiveNatListListWitnessRows.realize
#print axioms CompactAdditiveNatListListDirectLayout.exists_witnessRows

end FoundationCompactNumericListedDirectNatListListWitnessRows
