import integration.FoundationCompactNumericListedDirectVerifierValueLayouts
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization

/-!
# Bounded row formula for lists of natural-number lists

For every row in an outer structured list, the formula reads its two cursors,
reads the inner list count, and checks the exact additive `List Nat` slice.
All witnesses are bounded by the common token count.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListRowsFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts

def CompactAdditiveNatListListRowsWellFormed
    (tokenTable width tokenCount boundaryTable count : Nat) : Prop :=
  ∀ index < count,
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
    ∃ innerCount, innerCount ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      CompactAdditiveNatListSlice
        tokenTable width tokenCount left innerCount right

def compactAdditiveNatListListRowsWellFormedDef :
    𝚺₀.Semisentence 5 := .mkSigma
  “tokenTable width tokenCount boundaryTable count.
    ∀ index < count,
      ∃ left <⁺ tokenCount,
        ∃ right <⁺ tokenCount,
          ∃ innerCount <⁺ tokenCount,
            !(compactFixedWidthEntryDef)
              boundaryTable tokenCount index left ∧
            !(compactFixedWidthEntryDef)
              boundaryTable tokenCount (index + 1) right ∧
            !(compactAdditiveNatListSliceDef)
              tokenTable width tokenCount left innerCount right”

@[simp] theorem compactAdditiveNatListListRowsWellFormedDef_spec
    (tokenTable width tokenCount boundaryTable count : Nat) :
    compactAdditiveNatListListRowsWellFormedDef.val.Evalb
        ![tokenTable, width, tokenCount, boundaryTable, count] ↔
      CompactAdditiveNatListListRowsWellFormed
        tokenTable width tokenCount boundaryTable count := by
  have hslice (innerCount right left index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![innerCount, right, left, index, tokenTable, width,
                tokenCount, boundaryTable, count]
              Empty.elim ∘
            ![(#4 : Semiterm ℒₒᵣ Empty 9), #5, #6, #2, #0, #1])
          Empty.elim)
        compactAdditiveNatListSliceDef.val ↔
      CompactAdditiveNatListSlice
        tokenTable width tokenCount left innerCount right := by
    have henv :
        (Semiterm.val
            ![innerCount, right, left, index, tokenTable, width,
              tokenCount, boundaryTable, count]
            Empty.elim ∘
          ![(#4 : Semiterm ℒₒᵣ Empty 9), #5, #6, #2, #0, #1]) =
          ![tokenTable, width, tokenCount, left, innerCount, right] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  simp [compactAdditiveNatListListRowsWellFormedDef,
    CompactAdditiveNatListListRowsWellFormed, hslice]

theorem compactAdditiveNatListListRowsWellFormedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListListRowsWellFormedDef.val := by
  simp [compactAdditiveNatListListRowsWellFormedDef]

theorem CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
    {tokenTable width tokenCount boundaryTable : Nat}
    {values : List (List Nat)}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      boundaryTable values) :
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount boundaryTable values.length := by
  intro index hindex
  rcases hrows index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  have hslice := CompactAdditiveNatListDirectLayout.toSlice hlayout
  have hinnerCount : (values.getI index).length ≤ tokenCount := by
    rcases hslice with
      ⟨bodyStart, _hbodyStart, hheader, _hfinish⟩
    exact Nat.le_trans (Nat.le_add_left _ _)
      hheader.2
  exact ⟨left, hleft, right, hright,
    (values.getI index).length, hinnerCount,
    hleftEntry, hrightEntry, hslice⟩

#print axioms compactAdditiveNatListListRowsWellFormedDef_spec
#print axioms compactAdditiveNatListListRowsWellFormedDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed

end FoundationCompactNumericListedDirectNatListListRowsFormula
