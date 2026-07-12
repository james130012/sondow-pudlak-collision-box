import integration.FoundationCompactNumericListedDirectTraceComponentTableau

/-!
# Direct bounded layouts for additive codec constructors

These formulas expose the fixed token grammar of `Bool`, `Option`, products,
and structured lists.  The payload relation for an option and the element
relation for a list are deliberately left to the concrete component formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAdditiveTypeLayouts

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph

/-- A Boolean is one token, exactly `0` or `1`. -/
def CompactAdditiveBoolSlice
    (tokenTable width tokenCount start value finish : Nat) : Prop :=
  CompactAdditiveTokenCell
      tokenTable width tokenCount start value finish ∧
    (value = 0 ∨ value = 1)

def compactAdditiveBoolSliceDef : 𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount start value finish.
    !(compactAdditiveTokenCellDef)
      tokenTable width tokenCount start value finish ∧
    (value = 0 ∨ value = 1)”

@[simp] theorem compactAdditiveBoolSliceDef_spec
    (tokenTable width tokenCount start value finish : Nat) :
    compactAdditiveBoolSliceDef.val.Evalb
        ![tokenTable, width, tokenCount, start, value, finish] ↔
      CompactAdditiveBoolSlice
        tokenTable width tokenCount start value finish := by
  simp [compactAdditiveBoolSliceDef, compactAdditiveTokenCellDef,
    CompactAdditiveBoolSlice, CompactAdditiveTokenCell]

theorem compactAdditiveBoolSliceDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBoolSliceDef.val := by
  simp [compactAdditiveBoolSliceDef]

theorem CompactAdditiveBoolSlice.exists_bool
    {tokenTable width tokenCount start value finish : Nat}
    (hvalid : CompactAdditiveBoolSlice
      tokenTable width tokenCount start value finish) :
    ∃ decoded : Bool, value = if decoded then 1 else 0 := by
  rcases hvalid.2 with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-- The `0` option tag has no payload.  The `1` tag is followed by one
nonempty payload slice whose concrete grammar is supplied separately. -/
def CompactAdditiveOptionLayout
    (tokenTable width tokenCount start tag payloadStart finish : Nat) : Prop :=
  CompactAdditiveTokenCell
      tokenTable width tokenCount start tag payloadStart ∧
    ((tag = 0 ∧ finish = payloadStart) ∨
      (tag = 1 ∧ payloadStart < finish ∧ finish ≤ tokenCount))

def compactAdditiveOptionLayoutDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount start tag payloadStart finish.
    !(compactAdditiveTokenCellDef)
      tokenTable width tokenCount start tag payloadStart ∧
    ((tag = 0 ∧ finish = payloadStart) ∨
      (tag = 1 ∧ payloadStart < finish ∧ finish ≤ tokenCount))”

@[simp] theorem compactAdditiveOptionLayoutDef_spec
    (tokenTable width tokenCount start tag payloadStart finish : Nat) :
    compactAdditiveOptionLayoutDef.val.Evalb
        ![tokenTable, width, tokenCount, start, tag, payloadStart, finish] ↔
      CompactAdditiveOptionLayout
        tokenTable width tokenCount start tag payloadStart finish := by
  simp [compactAdditiveOptionLayoutDef, compactAdditiveTokenCellDef,
    CompactAdditiveOptionLayout, CompactAdditiveTokenCell]

theorem compactAdditiveOptionLayoutDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveOptionLayoutDef.val := by
  simp [compactAdditiveOptionLayoutDef]

theorem CompactAdditiveOptionLayout.tag_cases
    {tokenTable width tokenCount start tag payloadStart finish : Nat}
    (hvalid : CompactAdditiveOptionLayout
      tokenTable width tokenCount start tag payloadStart finish) :
    (tag = 0 ∧ finish = payloadStart) ∨
      (tag = 1 ∧ payloadStart < finish ∧ finish ≤ tokenCount) :=
  hvalid.2

/-- Both components of an additive product are nonempty and concatenate at
the displayed middle cursor. -/
def CompactAdditiveProductSplit
    (tokenCount start middle finish : Nat) : Prop :=
  start < middle ∧ middle < finish ∧ finish ≤ tokenCount

def compactAdditiveProductSplitDef : 𝚺₀.Semisentence 4 := .mkSigma
  “tokenCount start middle finish.
    start < middle ∧ middle < finish ∧ finish ≤ tokenCount”

@[simp] theorem compactAdditiveProductSplitDef_spec
    (tokenCount start middle finish : Nat) :
    compactAdditiveProductSplitDef.val.Evalb
        ![tokenCount, start, middle, finish] ↔
      CompactAdditiveProductSplit tokenCount start middle finish := by
  simp [compactAdditiveProductSplitDef, CompactAdditiveProductSplit]

theorem compactAdditiveProductSplitDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveProductSplitDef.val := by
  simp [compactAdditiveProductSplitDef]

theorem compactAdditiveProductSplit_of_lengths
    (tokenCount start leftLength rightLength : Nat)
    (hleft : 0 < leftLength) (hright : 0 < rightLength)
    (hfinish : start + leftLength + rightLength ≤ tokenCount) :
    CompactAdditiveProductSplit tokenCount start
      (start + leftLength) (start + leftLength + rightLength) := by
  simp only [CompactAdditiveProductSplit]
  omega

/-- A structured list consists of its count header followed by `count`
nonempty element slices recorded in a direct boundary table. -/
def CompactAdditiveStructuredListLayout
    (tokenTable width tokenCount start count finish
      elementBoundaryTable : Nat) : Prop :=
  ∃ bodyStart, bodyStart ≤ tokenCount ∧
    CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart ∧
    CompactAdditiveBoundaryTable
      tokenCount count bodyStart finish elementBoundaryTable

def compactAdditiveStructuredListLayoutDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount start count finish elementBoundaryTable.
    ∃ bodyStart <⁺ tokenCount,
      !(compactAdditiveListHeaderDef)
        tokenTable width tokenCount start count bodyStart ∧
      !(compactAdditiveBoundaryTableDef)
        tokenCount count bodyStart finish elementBoundaryTable”

@[simp] theorem compactAdditiveStructuredListLayoutDef_spec
    (tokenTable width tokenCount start count finish
      elementBoundaryTable : Nat) :
    compactAdditiveStructuredListLayoutDef.val.Evalb
        ![tokenTable, width, tokenCount, start, count, finish,
          elementBoundaryTable] ↔
      CompactAdditiveStructuredListLayout
        tokenTable width tokenCount start count finish
        elementBoundaryTable := by
  simp [compactAdditiveStructuredListLayoutDef,
    CompactAdditiveStructuredListLayout]
  constructor
  · rintro ⟨bodyStart, hbodyStart, hheaderEval, hboundaryEval⟩
    have hheaderEnv :
        (Semiterm.val
            ![bodyStart, tokenTable, width, tokenCount, start, count,
              finish, elementBoundaryTable]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 8), #2, #3, #4, #5, #0]) =
          ![tokenTable, width, tokenCount, start, count, bodyStart] := by
      funext index
      fin_cases index <;> rfl
    have hboundaryEnv :
        (Semiterm.val
            ![bodyStart, tokenTable, width, tokenCount, start, count,
              finish, elementBoundaryTable]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 8), #5, #0, #6, #7]) =
          ![tokenCount, count, bodyStart, finish,
            elementBoundaryTable] := by
      funext index
      fin_cases index <;> rfl
    rw [hheaderEnv] at hheaderEval
    rw [hboundaryEnv] at hboundaryEval
    exact ⟨bodyStart, hbodyStart,
      (compactAdditiveListHeaderDef_spec
        tokenTable width tokenCount start count bodyStart).mp hheaderEval,
      (compactAdditiveBoundaryTableDef_spec
        tokenCount count bodyStart finish elementBoundaryTable).mp
          hboundaryEval⟩
  · rintro ⟨bodyStart, hbodyStart, hheader, hboundaries⟩
    refine ⟨bodyStart, hbodyStart, ?_, ?_⟩
    · have hheaderEval :=
        (compactAdditiveListHeaderDef_spec
          tokenTable width tokenCount start count bodyStart).mpr hheader
      have hheaderEnv :
          (Semiterm.val
              ![bodyStart, tokenTable, width, tokenCount, start, count,
                finish, elementBoundaryTable]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 8), #2, #3, #4, #5, #0]) =
            ![tokenTable, width, tokenCount, start, count, bodyStart] := by
        funext index
        fin_cases index <;> rfl
      rwa [hheaderEnv]
    · have hboundaryEval :=
        (compactAdditiveBoundaryTableDef_spec
          tokenCount count bodyStart finish elementBoundaryTable).mpr
            hboundaries
      have hboundaryEnv :
          (Semiterm.val
              ![bodyStart, tokenTable, width, tokenCount, start, count,
                finish, elementBoundaryTable]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 8), #5, #0, #6, #7]) =
            ![tokenCount, count, bodyStart, finish,
              elementBoundaryTable] := by
        funext index
        fin_cases index <;> rfl
      rwa [hboundaryEnv]

theorem compactAdditiveStructuredListLayoutDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveStructuredListLayoutDef.val := by
  simp [compactAdditiveStructuredListLayoutDef]

theorem CompactAdditiveListHeader.structuredLayout
    {tokenTable width tokenCount start count bodyStart finish
      elementBoundaryTable : Nat}
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart)
    (hboundaries : CompactAdditiveBoundaryTable
      tokenCount count bodyStart finish elementBoundaryTable) :
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish
      elementBoundaryTable := by
  exact ⟨bodyStart,
    (Nat.le_add_right bodyStart count).trans hheader.2,
    hheader, hboundaries⟩

#print axioms compactAdditiveBoolSliceDef_spec
#print axioms compactAdditiveBoolSliceDef_sigmaZero
#print axioms CompactAdditiveBoolSlice.exists_bool
#print axioms compactAdditiveOptionLayoutDef_spec
#print axioms compactAdditiveOptionLayoutDef_sigmaZero
#print axioms CompactAdditiveOptionLayout.tag_cases
#print axioms compactAdditiveProductSplitDef_spec
#print axioms compactAdditiveProductSplitDef_sigmaZero
#print axioms compactAdditiveProductSplit_of_lengths
#print axioms compactAdditiveStructuredListLayoutDef_spec
#print axioms compactAdditiveStructuredListLayoutDef_sigmaZero
#print axioms CompactAdditiveListHeader.structuredLayout

end FoundationCompactNumericListedDirectAdditiveTypeLayouts
