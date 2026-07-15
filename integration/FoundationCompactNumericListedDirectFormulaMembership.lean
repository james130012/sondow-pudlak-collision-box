import integration.FoundationCompactNumericListedDirectNatListSliceEquality
import integration.FoundationCompactNumericListedDirectNatListListRowsFormula

/-!
# Bounded membership in a directly encoded formula list

A formula is a natural-number token list.  A context is a structured list of
such token lists.  Membership is witnessed by one bounded row index and exact
fixed-width equality between the formula slice and that row.  The relation is
Delta-zero and is equivalent to ordinary typed list membership under the
checked direct layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaMembership

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectNatListSliceEquality

def CompactAdditiveFormulaMemberRows
    (tokenTable width tokenCount contextBoundary contextCount
      formulaStart formulaFinish : Nat) : Prop :=
  exists index, index < contextCount ∧
    exists candidateStart, candidateStart <= tokenCount ∧
    exists candidateFinish, candidateFinish <= tokenCount ∧
      CompactFixedWidthEntry contextBoundary tokenCount
        index candidateStart ∧
      CompactFixedWidthEntry contextBoundary tokenCount
        (index + 1) candidateFinish ∧
      CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
        formulaStart formulaFinish candidateStart candidateFinish

def compactAdditiveFormulaMemberRowsDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount contextBoundary contextCount
      formulaStart formulaFinish.
    ∃ index < contextCount,
      ∃ candidateStart <⁺ tokenCount,
        ∃ candidateFinish <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            contextBoundary tokenCount index candidateStart ∧
          !(compactFixedWidthEntryDef)
            contextBoundary tokenCount (index + 1) candidateFinish ∧
          !(compactFixedWidthTokenSlicesEqDef)
            tokenTable width tokenCount
              formulaStart formulaFinish candidateStart candidateFinish”

@[simp] theorem compactAdditiveFormulaMemberRowsDef_spec
    (tokenTable width tokenCount contextBoundary contextCount
      formulaStart formulaFinish : Nat) :
    compactAdditiveFormulaMemberRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, contextBoundary, contextCount,
          formulaStart, formulaFinish] ↔
      CompactAdditiveFormulaMemberRows tokenTable width tokenCount
        contextBoundary contextCount formulaStart formulaFinish := by
  have hslices (candidateFinish candidateStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![candidateFinish, candidateStart, index,
                tokenTable, width, tokenCount, contextBoundary,
                contextCount, formulaStart, formulaFinish]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 10), #4, #5,
              #8, #9, #1, #0])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          formulaStart formulaFinish candidateStart candidateFinish := by
    have henv :
        (Semiterm.val
            ![candidateFinish, candidateStart, index,
              tokenTable, width, tokenCount, contextBoundary,
              contextCount, formulaStart, formulaFinish]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 10), #4, #5,
            #8, #9, #1, #0]) =
          ![tokenTable, width, tokenCount,
            formulaStart, formulaFinish,
            candidateStart, candidateFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount formulaStart formulaFinish
        candidateStart candidateFinish
  simp [compactAdditiveFormulaMemberRowsDef,
    CompactAdditiveFormulaMemberRows, hslices]

theorem compactAdditiveFormulaMemberRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFormulaMemberRowsDef.val := by
  simp [compactAdditiveFormulaMemberRowsDef]

theorem compactAdditiveFormulaMemberRows_iff_mem
    {tokenTable width tokenCount contextBoundary
      formulaStart formulaFinish : Nat}
    {context : List (List Nat)} {formula : List Nat}
    (hcontext : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        contextBoundary context)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount formulaStart formulaFinish formula) :
    CompactAdditiveFormulaMemberRows tokenTable width tokenCount
        contextBoundary context.length formulaStart formulaFinish ↔
      formula ∈ context := by
  constructor
  · rintro ⟨index, hindex, candidateStart, _hcandidateStart,
      candidateFinish, _hcandidateFinish,
      hstartEntry, hfinishEntry, hslices⟩
    rcases hcontext index hindex with
      ⟨rowStart, _hrowStart, rowFinish, _hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hstart : candidateStart = rowStart :=
      (CompactFixedWidthEntry.value_eq_tableValue hstartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowStartEntry).symm
    have hfinish : candidateFinish = rowFinish :=
      (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowFinishEntry).symm
    subst candidateStart
    subst candidateFinish
    have hvalue : context.getI index = formula :=
      CompactFixedWidthTokenSlicesEq.natListValues_eq
        hslices hformula hrowLayout
    rw [← hvalue, List.getI_eq_getElem context hindex]
    exact List.getElem_mem hindex
  · intro hmember
    obtain ⟨index, hindex, hvalue⟩ :=
      List.mem_iff_getElem.mp hmember
    rcases hcontext index hindex with
      ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have htyped : formula = context.getI index := by
      rw [List.getI_eq_getElem context hindex]
      exact hvalue.symm
    have hslices :=
      CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hformula hrowLayout htyped
    exact ⟨index, hindex, rowStart, hrowStart,
      rowFinish, hrowFinish, hrowStartEntry, hrowFinishEntry, hslices⟩

#print axioms compactAdditiveFormulaMemberRowsDef_spec
#print axioms compactAdditiveFormulaMemberRowsDef_sigmaZero
#print axioms compactAdditiveFormulaMemberRows_iff_mem

end FoundationCompactNumericListedDirectFormulaMembership
