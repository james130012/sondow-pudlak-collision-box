import integration.FoundationCompactNumericListedDirectFormulaConstructorSlices

/-!
# Direct set equality against a formula-cons context

Rule checks compare a stored child conclusion with `head :: Gamma`, but that
expected context is not itself stored in the verifier state.  This file gives
a direct Delta-zero characterization: every stored child formula belongs to
the cons context, while the head and every tail formula belong to the child
context.  No auxiliary encoded context is postulated.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaSetEqCons

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectFormulaMembership
open FoundationCompactNumericListedDirectFormulaSetChecks

def CompactAdditiveFormulaSubsetConsRows
    (tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish
      tailBoundary tailCount : Nat) : Prop :=
  forall index, index < actualCount ->
    exists formulaStart, formulaStart <= tokenCount ∧
    exists formulaFinish, formulaFinish <= tokenCount ∧
      CompactFixedWidthEntry actualBoundary tokenCount index formulaStart ∧
      CompactFixedWidthEntry actualBoundary tokenCount
        (index + 1) formulaFinish ∧
      (CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          formulaStart formulaFinish headStart headFinish ∨
        CompactAdditiveFormulaMemberRows tokenTable width tokenCount
          tailBoundary tailCount formulaStart formulaFinish)

def CompactAdditiveFormulaSetEqConsRows
    (tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish
      tailBoundary tailCount : Nat) : Prop :=
  CompactAdditiveFormulaSubsetConsRows tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish tailBoundary tailCount ∧
    CompactAdditiveFormulaMemberRows tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish ∧
    CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
      tailBoundary tailCount actualBoundary actualCount

def compactAdditiveFormulaSubsetConsRowsDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish
      tailBoundary tailCount.
    ∀ index < actualCount,
      ∃ formulaStart <⁺ tokenCount,
        ∃ formulaFinish <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            actualBoundary tokenCount index formulaStart ∧
          !(compactFixedWidthEntryDef)
            actualBoundary tokenCount (index + 1) formulaFinish ∧
          (!(compactFixedWidthTokenSlicesEqDef)
              tokenTable width tokenCount
                formulaStart formulaFinish headStart headFinish ∨
            !(compactAdditiveFormulaMemberRowsDef)
              tokenTable width tokenCount
                tailBoundary tailCount formulaStart formulaFinish)”

def compactAdditiveFormulaSetEqConsRowsDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish
      tailBoundary tailCount.
    !(compactAdditiveFormulaSubsetConsRowsDef)
      tokenTable width tokenCount
        actualBoundary actualCount headStart headFinish
        tailBoundary tailCount ∧
    !(compactAdditiveFormulaMemberRowsDef)
      tokenTable width tokenCount
        actualBoundary actualCount headStart headFinish ∧
    !(compactAdditiveFormulaSubsetRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount actualBoundary actualCount”

@[simp] theorem compactAdditiveFormulaSubsetConsRowsDef_spec
    (tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish
      tailBoundary tailCount : Nat) :
    compactAdditiveFormulaSubsetConsRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          actualBoundary, actualCount, headStart, headFinish,
          tailBoundary, tailCount] ↔
      CompactAdditiveFormulaSubsetConsRows tokenTable width tokenCount
        actualBoundary actualCount headStart headFinish
        tailBoundary tailCount := by
  have hslices (formulaFinish formulaStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaFinish, formulaStart, index,
                tokenTable, width, tokenCount,
                actualBoundary, actualCount, headStart, headFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 12), #4, #5,
              #1, #0, #8, #9])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          formulaStart formulaFinish headStart headFinish := by
    have henv :
        (Semiterm.val
            ![formulaFinish, formulaStart, index,
              tokenTable, width, tokenCount,
              actualBoundary, actualCount, headStart, headFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 12), #4, #5,
            #1, #0, #8, #9]) =
          ![tokenTable, width, tokenCount,
            formulaStart, formulaFinish, headStart, headFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        formulaStart formulaFinish headStart headFinish
  have hmember (formulaFinish formulaStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaFinish, formulaStart, index,
                tokenTable, width, tokenCount,
                actualBoundary, actualCount, headStart, headFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 12), #4, #5,
              #10, #11, #1, #0])
          Empty.elim) compactAdditiveFormulaMemberRowsDef.val ↔
        CompactAdditiveFormulaMemberRows tokenTable width tokenCount
          tailBoundary tailCount formulaStart formulaFinish := by
    have henv :
        (Semiterm.val
            ![formulaFinish, formulaStart, index,
              tokenTable, width, tokenCount,
              actualBoundary, actualCount, headStart, headFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 12), #4, #5,
            #10, #11, #1, #0]) =
          ![tokenTable, width, tokenCount,
            tailBoundary, tailCount, formulaStart, formulaFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaMemberRowsDef_spec
      tokenTable width tokenCount tailBoundary tailCount
        formulaStart formulaFinish
  simp [compactAdditiveFormulaSubsetConsRowsDef,
    CompactAdditiveFormulaSubsetConsRows, hslices, hmember]

@[simp] theorem compactAdditiveFormulaSetEqConsRowsDef_spec
    (tokenTable width tokenCount
      actualBoundary actualCount headStart headFinish
      tailBoundary tailCount : Nat) :
    compactAdditiveFormulaSetEqConsRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          actualBoundary, actualCount, headStart, headFinish,
          tailBoundary, tailCount] ↔
      CompactAdditiveFormulaSetEqConsRows tokenTable width tokenCount
        actualBoundary actualCount headStart headFinish
        tailBoundary tailCount := by
  have hsubsetCons :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                actualBoundary, actualCount, headStart, headFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2,
              #3, #4, #5, #6, #7, #8])
          Empty.elim) compactAdditiveFormulaSubsetConsRowsDef.val ↔
        CompactAdditiveFormulaSubsetConsRows tokenTable width tokenCount
          actualBoundary actualCount headStart headFinish
          tailBoundary tailCount := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              actualBoundary, actualCount, headStart, headFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2,
            #3, #4, #5, #6, #7, #8]) =
          ![tokenTable, width, tokenCount,
            actualBoundary, actualCount, headStart, headFinish,
            tailBoundary, tailCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaSubsetConsRowsDef_spec
      tokenTable width tokenCount
        actualBoundary actualCount headStart headFinish
        tailBoundary tailCount
  have hheadMember :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                actualBoundary, actualCount, headStart, headFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2,
              #3, #4, #5, #6])
          Empty.elim) compactAdditiveFormulaMemberRowsDef.val ↔
        CompactAdditiveFormulaMemberRows tokenTable width tokenCount
          actualBoundary actualCount headStart headFinish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              actualBoundary, actualCount, headStart, headFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2,
            #3, #4, #5, #6]) =
          ![tokenTable, width, tokenCount,
            actualBoundary, actualCount, headStart, headFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaMemberRowsDef_spec
      tokenTable width tokenCount actualBoundary actualCount
        headStart headFinish
  have htailSubset :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                actualBoundary, actualCount, headStart, headFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2,
              #7, #8, #3, #4])
          Empty.elim) compactAdditiveFormulaSubsetRowsDef.val ↔
        CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
          tailBoundary tailCount actualBoundary actualCount := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              actualBoundary, actualCount, headStart, headFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2,
            #7, #8, #3, #4]) =
          ![tokenTable, width, tokenCount,
            tailBoundary, tailCount, actualBoundary, actualCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaSubsetRowsDef_spec
      tokenTable width tokenCount tailBoundary tailCount
        actualBoundary actualCount
  simp [compactAdditiveFormulaSetEqConsRowsDef,
    CompactAdditiveFormulaSetEqConsRows,
    hsubsetCons, hheadMember, htailSubset]

theorem compactAdditiveFormulaSubsetConsRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFormulaSubsetConsRowsDef.val := by
  simp [compactAdditiveFormulaSubsetConsRowsDef]

theorem compactAdditiveFormulaSetEqConsRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFormulaSetEqConsRowsDef.val := by
  simp [compactAdditiveFormulaSetEqConsRowsDef]

theorem compactAdditiveFormulaSubsetConsRows_iff
    {tokenTable width tokenCount actualBoundary
      headStart headFinish tailBoundary : Nat}
    {actual tail : List (List Nat)} {head : List Nat}
    (hactual : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        actualBoundary actual)
    (hhead : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      headStart headFinish head)
    (htail : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        tailBoundary tail) :
    CompactAdditiveFormulaSubsetConsRows tokenTable width tokenCount
        actualBoundary actual.length headStart headFinish
        tailBoundary tail.length ↔
      forall formula, formula ∈ actual -> formula ∈ head :: tail := by
  constructor
  · intro hsubset formula hformula
    obtain ⟨index, hindex, hvalue⟩ :=
      List.mem_iff_getElem.mp hformula
    rcases hsubset index hindex with
      ⟨formulaStart, _hformulaStart,
        formulaFinish, _hformulaFinish,
        hstartEntry, hfinishEntry, hcase⟩
    rcases hactual index hindex with
      ⟨rowStart, _hrowStart, rowFinish, _hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hstart : formulaStart = rowStart :=
      (CompactFixedWidthEntry.value_eq_tableValue hstartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowStartEntry).symm
    have hfinish : formulaFinish = rowFinish :=
      (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowFinishEntry).symm
    subst formulaStart
    subst formulaFinish
    rcases hcase with hslices | hmember
    · have heq := CompactFixedWidthTokenSlicesEq.natListValues_eq
        hslices hrowLayout hhead
      have hformulaEq : formula = head := by
        rw [List.getI_eq_getElem actual hindex, hvalue] at heq
        exact heq.symm
      simp [hformulaEq]
    · have htailMember : actual.getI index ∈ tail :=
        (compactAdditiveFormulaMemberRows_iff_mem
          htail hrowLayout).mp hmember
      rw [List.getI_eq_getElem actual hindex, hvalue] at htailMember
      simp [htailMember]
  · intro hsubset index hindex
    rcases hactual index hindex with
      ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hactualMember : actual.getI index ∈ actual := by
      rw [List.getI_eq_getElem actual hindex]
      exact List.getElem_mem hindex
    have hconsMember := hsubset (actual.getI index) hactualMember
    simp only [List.mem_cons] at hconsMember
    rcases hconsMember with hheadEq | htailMember
    · have hslices := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hrowLayout hhead hheadEq
      exact ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, Or.inl hslices⟩
    · have hmember : CompactAdditiveFormulaMemberRows
          tokenTable width tokenCount tailBoundary tail.length
            rowStart rowFinish :=
        (compactAdditiveFormulaMemberRows_iff_mem
          htail hrowLayout).mpr htailMember
      exact ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, Or.inr hmember⟩

theorem compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
    {tokenTable width tokenCount actualBoundary
      headStart headFinish tailBoundary : Nat}
    {actual tail : List (List Nat)} {head : List Nat}
    (hactual : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        actualBoundary actual)
    (hhead : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      headStart headFinish head)
    (htail : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        tailBoundary tail) :
    CompactAdditiveFormulaSetEqConsRows tokenTable width tokenCount
        actualBoundary actual.length headStart headFinish
        tailBoundary tail.length ↔
      tokenFormulaSetEq actual (head :: tail) = true := by
  simp only [CompactAdditiveFormulaSetEqConsRows,
    tokenFormulaSetEq, Bool.and_eq_true, tokenFormulaSubset,
    tokenFormulaMem_eq_true_iff, tokenFormulaSubset_eq_true_iff]
  exact and_congr
    (compactAdditiveFormulaSubsetConsRows_iff hactual hhead htail)
    (and_congr
      (compactAdditiveFormulaMemberRows_iff_mem hactual hhead)
      (compactAdditiveFormulaSubsetRows_iff htail hactual))

#print axioms compactAdditiveFormulaSubsetConsRowsDef_spec
#print axioms compactAdditiveFormulaSetEqConsRowsDef_spec
#print axioms compactAdditiveFormulaSubsetConsRowsDef_sigmaZero
#print axioms compactAdditiveFormulaSetEqConsRowsDef_sigmaZero
#print axioms compactAdditiveFormulaSubsetConsRows_iff
#print axioms compactAdditiveFormulaSetEqConsRows_iff_tokenCheck

end FoundationCompactNumericListedDirectFormulaSetEqCons
