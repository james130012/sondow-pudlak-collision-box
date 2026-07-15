import integration.FoundationCompactNumericListedDirectAtomicListRowRealization
import integration.FoundationCompactNumericListedDirectVerifierValueLayouts

/-!
# Self-contained rows for one flat natural-number list

The bounded graph exposes the structured-list boundary table, proves that
every element occupies one token, and records the exact boundary-code size.
It therefore realizes a typed natural-number list without receiving that list
as an external parameter.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListWitnessRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts

def CompactAdditiveNatListWitnessRows
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) : Prop :=
  CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable ∧
    CompactAdditiveUnitBoundaryRows tokenCount count boundaryTable ∧
    boundarySize = Nat.size boundaryTable ∧
    boundarySize ≤ (count + 1) * tokenCount

def compactAdditiveNatListWitnessRowsDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount start count finish boundaryTable boundarySize.
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount start count finish boundaryTable ∧
    !(compactAdditiveUnitBoundaryRowsDef)
      tokenCount count boundaryTable ∧
    !(compactNatSizeDef) boundarySize boundaryTable ∧
    boundarySize ≤ (count + 1) * tokenCount”

@[simp] theorem compactAdditiveNatListWitnessRowsDef_spec
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) :
    compactAdditiveNatListWitnessRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, start, count, finish,
          boundaryTable, boundarySize] ↔
      CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount start count finish boundaryTable
          boundarySize := by
  let env : Fin 8 → Nat :=
    ![tokenTable, width, tokenCount, start, count, finish,
      boundaryTable, boundarySize]
  change compactAdditiveNatListWitnessRowsDef.val.Evalb env ↔ _
  have hlayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 8), #1, #2, #3, #4, #5, #6]) =
      ![tokenTable, width, tokenCount, start, count, finish,
        boundaryTable] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactAdditiveNatListWitnessRowsDef,
    CompactAdditiveNatListWitnessRows, hlayoutEnv, env]

theorem compactAdditiveNatListWitnessRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListWitnessRowsDef.val := by
  simp [compactAdditiveNatListWitnessRowsDef]

theorem CompactAdditiveNatListWitnessRows.realize
    {tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat}
    (hrows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount start count finish boundaryTable
        boundarySize) :
    ∃ values : List Nat,
      values.length = count ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount start finish values ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
          boundaryTable values := by
  rcases hrows with ⟨hlayout, hunit, hsizeEq, hsize⟩
  let values := compactAdditiveNatListRowValues
    tokenTable width tokenCount boundaryTable count
  have hlength : values.length = count := by
    simp [values]
  have hvalueRows :
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
          boundaryTable values := by
    exact CompactAdditiveUnitBoundaryRows.realizedNatRows hunit
  refine ⟨values, hlength, ⟨boundaryTable, ?_, hvalueRows, ?_⟩,
    hvalueRows⟩
  · simpa only [hlength] using hlayout
  · rw [hlength, ← hsizeEq]
    exact hsize

theorem CompactAdditiveNatListDirectLayout.exists_witnessRows
    {tokenTable width tokenCount start finish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish values) :
    ∃ boundaryTable boundarySize,
      CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount start values.length finish boundaryTable
          boundarySize := by
  rcases hlayout with
    ⟨boundaryTable, hstructure, hvalueRows, hsize⟩
  refine ⟨boundaryTable, Nat.size boundaryTable,
    hstructure, ?_, rfl, hsize⟩
  exact
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      hvalueRows

#print axioms compactAdditiveNatListWitnessRowsDef_spec
#print axioms compactAdditiveNatListWitnessRowsDef_sigmaZero
#print axioms CompactAdditiveNatListWitnessRows.realize
#print axioms CompactAdditiveNatListDirectLayout.exists_witnessRows

end FoundationCompactNumericListedDirectNatListWitnessRows
