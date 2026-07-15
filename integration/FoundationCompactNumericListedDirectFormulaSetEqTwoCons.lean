import integration.FoundationCompactNumericListedDirectWkRuleCheck

/-!
# Direct set equality against a two-formula prefix

This is the stored-free characterization of
`actual = first :: second :: tail` up to the checker's set equality.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaSetEqTwoCons

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

def CompactAdditiveFormulaSubsetTwoConsRows
    (tokenTable width tokenCount
      actualBoundary actualCount
      firstStart firstFinish secondStart secondFinish
      tailBoundary tailCount : Nat) : Prop :=
  forall index, index < actualCount ->
    exists formulaStart, formulaStart <= tokenCount ∧
    exists formulaFinish, formulaFinish <= tokenCount ∧
      CompactFixedWidthEntry actualBoundary tokenCount index formulaStart ∧
      CompactFixedWidthEntry actualBoundary tokenCount
        (index + 1) formulaFinish ∧
      (CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          formulaStart formulaFinish firstStart firstFinish ∨
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          formulaStart formulaFinish secondStart secondFinish ∨
        CompactAdditiveFormulaMemberRows tokenTable width tokenCount
          tailBoundary tailCount formulaStart formulaFinish)

def CompactAdditiveFormulaSetEqTwoConsRows
    (tokenTable width tokenCount
      actualBoundary actualCount
      firstStart firstFinish secondStart secondFinish
      tailBoundary tailCount : Nat) : Prop :=
  CompactAdditiveFormulaSubsetTwoConsRows tokenTable width tokenCount
      actualBoundary actualCount
      firstStart firstFinish secondStart secondFinish
      tailBoundary tailCount ∧
    CompactAdditiveFormulaMemberRows tokenTable width tokenCount
      actualBoundary actualCount firstStart firstFinish ∧
    CompactAdditiveFormulaMemberRows tokenTable width tokenCount
      actualBoundary actualCount secondStart secondFinish ∧
    CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
      tailBoundary tailCount actualBoundary actualCount

def compactAdditiveFormulaSubsetTwoConsRowsDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount
      actualBoundary actualCount
      firstStart firstFinish secondStart secondFinish
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
                formulaStart formulaFinish firstStart firstFinish ∨
            !(compactFixedWidthTokenSlicesEqDef)
              tokenTable width tokenCount
                formulaStart formulaFinish secondStart secondFinish ∨
            !(compactAdditiveFormulaMemberRowsDef)
              tokenTable width tokenCount
                tailBoundary tailCount formulaStart formulaFinish)”

def compactAdditiveFormulaSetEqTwoConsRowsDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount
      actualBoundary actualCount
      firstStart firstFinish secondStart secondFinish
      tailBoundary tailCount.
    !(compactAdditiveFormulaSubsetTwoConsRowsDef)
      tokenTable width tokenCount
        actualBoundary actualCount
        firstStart firstFinish secondStart secondFinish
        tailBoundary tailCount ∧
    !(compactAdditiveFormulaMemberRowsDef)
      tokenTable width tokenCount
        actualBoundary actualCount firstStart firstFinish ∧
    !(compactAdditiveFormulaMemberRowsDef)
      tokenTable width tokenCount
        actualBoundary actualCount secondStart secondFinish ∧
    !(compactAdditiveFormulaSubsetRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount actualBoundary actualCount”

@[simp] theorem compactAdditiveFormulaSubsetTwoConsRowsDef_spec
    (tokenTable width tokenCount
      actualBoundary actualCount
      firstStart firstFinish secondStart secondFinish
      tailBoundary tailCount : Nat) :
    compactAdditiveFormulaSubsetTwoConsRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          actualBoundary, actualCount,
          firstStart, firstFinish, secondStart, secondFinish,
          tailBoundary, tailCount] ↔
      CompactAdditiveFormulaSubsetTwoConsRows tokenTable width tokenCount
        actualBoundary actualCount
        firstStart firstFinish secondStart secondFinish
        tailBoundary tailCount := by
  have hfirst (formulaFinish formulaStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaFinish, formulaStart, index,
                tokenTable, width, tokenCount,
                actualBoundary, actualCount,
                firstStart, firstFinish, secondStart, secondFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 14), #4, #5,
              #1, #0, #8, #9])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          formulaStart formulaFinish firstStart firstFinish := by
    have henv :
        (Semiterm.val
            ![formulaFinish, formulaStart, index,
              tokenTable, width, tokenCount,
              actualBoundary, actualCount,
              firstStart, firstFinish, secondStart, secondFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 14), #4, #5,
            #1, #0, #8, #9]) =
          ![tokenTable, width, tokenCount,
            formulaStart, formulaFinish, firstStart, firstFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        formulaStart formulaFinish firstStart firstFinish
  have hsecond (formulaFinish formulaStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaFinish, formulaStart, index,
                tokenTable, width, tokenCount,
                actualBoundary, actualCount,
                firstStart, firstFinish, secondStart, secondFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 14), #4, #5,
              #1, #0, #10, #11])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          formulaStart formulaFinish secondStart secondFinish := by
    have henv :
        (Semiterm.val
            ![formulaFinish, formulaStart, index,
              tokenTable, width, tokenCount,
              actualBoundary, actualCount,
              firstStart, firstFinish, secondStart, secondFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 14), #4, #5,
            #1, #0, #10, #11]) =
          ![tokenTable, width, tokenCount,
            formulaStart, formulaFinish, secondStart, secondFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        formulaStart formulaFinish secondStart secondFinish
  have hmember (formulaFinish formulaStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaFinish, formulaStart, index,
                tokenTable, width, tokenCount,
                actualBoundary, actualCount,
                firstStart, firstFinish, secondStart, secondFinish,
                tailBoundary, tailCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 14), #4, #5,
              #12, #13, #1, #0])
          Empty.elim) compactAdditiveFormulaMemberRowsDef.val ↔
        CompactAdditiveFormulaMemberRows tokenTable width tokenCount
          tailBoundary tailCount formulaStart formulaFinish := by
    have henv :
        (Semiterm.val
            ![formulaFinish, formulaStart, index,
              tokenTable, width, tokenCount,
              actualBoundary, actualCount,
              firstStart, firstFinish, secondStart, secondFinish,
              tailBoundary, tailCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 14), #4, #5,
            #12, #13, #1, #0]) =
          ![tokenTable, width, tokenCount,
            tailBoundary, tailCount, formulaStart, formulaFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaMemberRowsDef_spec
      tokenTable width tokenCount tailBoundary tailCount
        formulaStart formulaFinish
  simp [compactAdditiveFormulaSubsetTwoConsRowsDef,
    CompactAdditiveFormulaSubsetTwoConsRows, hfirst, hsecond, hmember]

@[simp] theorem compactAdditiveFormulaSetEqTwoConsRowsDef_spec
    (tokenTable width tokenCount
      actualBoundary actualCount
      firstStart firstFinish secondStart secondFinish
      tailBoundary tailCount : Nat) :
    compactAdditiveFormulaSetEqTwoConsRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          actualBoundary, actualCount,
          firstStart, firstFinish, secondStart, secondFinish,
          tailBoundary, tailCount] ↔
      CompactAdditiveFormulaSetEqTwoConsRows tokenTable width tokenCount
        actualBoundary actualCount
        firstStart firstFinish secondStart secondFinish
        tailBoundary tailCount := by
  let env : Fin 11 → Nat :=
    ![tokenTable, width, tokenCount,
      actualBoundary, actualCount,
      firstStart, firstFinish, secondStart, secondFinish,
      tailBoundary, tailCount]
  change compactAdditiveFormulaSetEqTwoConsRowsDef.val.Evalb env ↔ _
  have hsubsetEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10]) =
        ![tokenTable, width, tokenCount,
          actualBoundary, actualCount,
          firstStart, firstFinish, secondStart, secondFinish,
          tailBoundary, tailCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2,
          #3, #4, #5, #6]) =
        ![tokenTable, width, tokenCount,
          actualBoundary, actualCount, firstStart, firstFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsecondEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2,
          #3, #4, #7, #8]) =
        ![tokenTable, width, tokenCount,
          actualBoundary, actualCount, secondStart, secondFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2,
          #9, #10, #3, #4]) =
        ![tokenTable, width, tokenCount,
          tailBoundary, tailCount, actualBoundary, actualCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactAdditiveFormulaSetEqTwoConsRowsDef,
    CompactAdditiveFormulaSetEqTwoConsRows,
    hsubsetEnv, hfirstEnv, hsecondEnv, htailEnv]

theorem compactAdditiveFormulaSubsetTwoConsRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFormulaSubsetTwoConsRowsDef.val := by
  simp [compactAdditiveFormulaSubsetTwoConsRowsDef]

theorem compactAdditiveFormulaSetEqTwoConsRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFormulaSetEqTwoConsRowsDef.val := by
  simp [compactAdditiveFormulaSetEqTwoConsRowsDef]

theorem compactAdditiveFormulaSubsetTwoConsRows_iff
    {tokenTable width tokenCount actualBoundary
      firstStart firstFinish secondStart secondFinish tailBoundary : Nat}
    {actual tail : List (List Nat)} {first second : List Nat}
    (hactual : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        actualBoundary actual)
    (hfirst : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      firstStart firstFinish first)
    (hsecond : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      secondStart secondFinish second)
    (htail : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        tailBoundary tail) :
    CompactAdditiveFormulaSubsetTwoConsRows tokenTable width tokenCount
        actualBoundary actual.length
        firstStart firstFinish secondStart secondFinish
        tailBoundary tail.length ↔
      forall formula, formula ∈ actual ->
        formula ∈ first :: second :: tail := by
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
    rcases hcase with hfirstSlices | hsecondSlices | hmember
    · have heq := CompactFixedWidthTokenSlicesEq.natListValues_eq
        hfirstSlices hrowLayout hfirst
      have hformulaEq : formula = first := by
        rw [List.getI_eq_getElem actual hindex, hvalue] at heq
        exact heq.symm
      simp [hformulaEq]
    · have heq := CompactFixedWidthTokenSlicesEq.natListValues_eq
        hsecondSlices hrowLayout hsecond
      have hformulaEq : formula = second := by
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
    have hprefixed := hsubset (actual.getI index) hactualMember
    simp only [List.mem_cons] at hprefixed
    rcases hprefixed with hfirstEq | hsecondEq | htailMember
    · have hslices := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hrowLayout hfirst hfirstEq
      exact ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, Or.inl hslices⟩
    · have hslices := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hrowLayout hsecond hsecondEq
      exact ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, Or.inr (Or.inl hslices)⟩
    · have hmember : CompactAdditiveFormulaMemberRows
          tokenTable width tokenCount tailBoundary tail.length
            rowStart rowFinish :=
        (compactAdditiveFormulaMemberRows_iff_mem
          htail hrowLayout).mpr htailMember
      exact ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, Or.inr (Or.inr hmember)⟩

theorem compactAdditiveFormulaSetEqTwoConsRows_iff_tokenCheck
    {tokenTable width tokenCount actualBoundary
      firstStart firstFinish secondStart secondFinish tailBoundary : Nat}
    {actual tail : List (List Nat)} {first second : List Nat}
    (hactual : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        actualBoundary actual)
    (hfirst : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      firstStart firstFinish first)
    (hsecond : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      secondStart secondFinish second)
    (htail : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        tailBoundary tail) :
    CompactAdditiveFormulaSetEqTwoConsRows tokenTable width tokenCount
        actualBoundary actual.length
        firstStart firstFinish secondStart secondFinish
        tailBoundary tail.length ↔
      tokenFormulaSetEq actual (first :: second :: tail) = true := by
  simp only [CompactAdditiveFormulaSetEqTwoConsRows,
    tokenFormulaSetEq, Bool.and_eq_true, tokenFormulaSubset,
    tokenFormulaMem_eq_true_iff, tokenFormulaSubset_eq_true_iff]
  exact and_congr
    (compactAdditiveFormulaSubsetTwoConsRows_iff
      hactual hfirst hsecond htail)
    (and_congr
      (compactAdditiveFormulaMemberRows_iff_mem hactual hfirst)
      (and_congr
        (compactAdditiveFormulaMemberRows_iff_mem hactual hsecond)
        (compactAdditiveFormulaSubsetRows_iff htail hactual)))

#print axioms compactAdditiveFormulaSubsetTwoConsRowsDef_spec
#print axioms compactAdditiveFormulaSetEqTwoConsRowsDef_spec
#print axioms compactAdditiveFormulaSubsetTwoConsRowsDef_sigmaZero
#print axioms compactAdditiveFormulaSetEqTwoConsRowsDef_sigmaZero
#print axioms compactAdditiveFormulaSubsetTwoConsRows_iff
#print axioms compactAdditiveFormulaSetEqTwoConsRows_iff_tokenCheck

end FoundationCompactNumericListedDirectFormulaSetEqTwoCons
