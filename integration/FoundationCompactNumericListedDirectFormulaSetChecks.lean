import integration.FoundationCompactNumericListedDirectFormulaMembership

/-!
# Bounded subset and set equality for directly encoded formula lists

Subset is a bounded universal scan of the left context whose body invokes the
checked formula-membership graph on the right context.  Set equality is the
two subset directions.  Under direct typed row layouts these relations are
exactly the Boolean checks used by the public verifier.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaSetChecks

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaMembership

def CompactAdditiveFormulaSubsetRows
    (tokenTable width tokenCount
      leftBoundary leftCount rightBoundary rightCount : Nat) : Prop :=
  forall index, index < leftCount ->
    exists formulaStart, formulaStart <= tokenCount ∧
    exists formulaFinish, formulaFinish <= tokenCount ∧
      CompactFixedWidthEntry leftBoundary tokenCount index formulaStart ∧
      CompactFixedWidthEntry leftBoundary tokenCount
        (index + 1) formulaFinish ∧
      CompactAdditiveFormulaMemberRows tokenTable width tokenCount
        rightBoundary rightCount formulaStart formulaFinish

def compactAdditiveFormulaSubsetRowsDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      leftBoundary leftCount rightBoundary rightCount.
    ∀ index < leftCount,
      ∃ formulaStart <⁺ tokenCount,
        ∃ formulaFinish <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            leftBoundary tokenCount index formulaStart ∧
          !(compactFixedWidthEntryDef)
            leftBoundary tokenCount (index + 1) formulaFinish ∧
          !(compactAdditiveFormulaMemberRowsDef)
            tokenTable width tokenCount
              rightBoundary rightCount formulaStart formulaFinish”

@[simp] theorem compactAdditiveFormulaSubsetRowsDef_spec
    (tokenTable width tokenCount
      leftBoundary leftCount rightBoundary rightCount : Nat) :
    compactAdditiveFormulaSubsetRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          leftBoundary, leftCount, rightBoundary, rightCount] ↔
      CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
        leftBoundary leftCount rightBoundary rightCount := by
  have hmember (formulaFinish formulaStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaFinish, formulaStart, index,
                tokenTable, width, tokenCount,
                leftBoundary, leftCount, rightBoundary, rightCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 10), #4, #5,
              #8, #9, #1, #0])
          Empty.elim) compactAdditiveFormulaMemberRowsDef.val ↔
        CompactAdditiveFormulaMemberRows tokenTable width tokenCount
          rightBoundary rightCount formulaStart formulaFinish := by
    have henv :
        (Semiterm.val
            ![formulaFinish, formulaStart, index,
              tokenTable, width, tokenCount,
              leftBoundary, leftCount, rightBoundary, rightCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 10), #4, #5,
            #8, #9, #1, #0]) =
          ![tokenTable, width, tokenCount,
            rightBoundary, rightCount, formulaStart, formulaFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaMemberRowsDef_spec
      tokenTable width tokenCount rightBoundary rightCount
        formulaStart formulaFinish
  simp [compactAdditiveFormulaSubsetRowsDef,
    CompactAdditiveFormulaSubsetRows, hmember]

theorem compactAdditiveFormulaSubsetRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFormulaSubsetRowsDef.val := by
  simp [compactAdditiveFormulaSubsetRowsDef]

def CompactAdditiveFormulaSetEqRows
    (tokenTable width tokenCount
      leftBoundary leftCount rightBoundary rightCount : Nat) : Prop :=
  CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
      leftBoundary leftCount rightBoundary rightCount ∧
    CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
      rightBoundary rightCount leftBoundary leftCount

def compactAdditiveFormulaSetEqRowsDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      leftBoundary leftCount rightBoundary rightCount.
    !(compactAdditiveFormulaSubsetRowsDef)
      tokenTable width tokenCount
        leftBoundary leftCount rightBoundary rightCount ∧
    !(compactAdditiveFormulaSubsetRowsDef)
      tokenTable width tokenCount
        rightBoundary rightCount leftBoundary leftCount”

@[simp] theorem compactAdditiveFormulaSetEqRowsDef_spec
    (tokenTable width tokenCount
      leftBoundary leftCount rightBoundary rightCount : Nat) :
    compactAdditiveFormulaSetEqRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          leftBoundary, leftCount, rightBoundary, rightCount] ↔
      CompactAdditiveFormulaSetEqRows tokenTable width tokenCount
        leftBoundary leftCount rightBoundary rightCount := by
  have hforward :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                leftBoundary, leftCount, rightBoundary, rightCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 7), #1, #2,
              #3, #4, #5, #6])
          Empty.elim) compactAdditiveFormulaSubsetRowsDef.val ↔
        CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
          leftBoundary leftCount rightBoundary rightCount := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              leftBoundary, leftCount, rightBoundary, rightCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 7), #1, #2,
            #3, #4, #5, #6]) =
          ![tokenTable, width, tokenCount,
            leftBoundary, leftCount, rightBoundary, rightCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaSubsetRowsDef_spec
      tokenTable width tokenCount leftBoundary leftCount
        rightBoundary rightCount
  have hreverse :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                leftBoundary, leftCount, rightBoundary, rightCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 7), #1, #2,
              #5, #6, #3, #4])
          Empty.elim) compactAdditiveFormulaSubsetRowsDef.val ↔
        CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
          rightBoundary rightCount leftBoundary leftCount := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              leftBoundary, leftCount, rightBoundary, rightCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 7), #1, #2,
            #5, #6, #3, #4]) =
          ![tokenTable, width, tokenCount,
            rightBoundary, rightCount, leftBoundary, leftCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveFormulaSubsetRowsDef_spec
      tokenTable width tokenCount rightBoundary rightCount
        leftBoundary leftCount
  simp [compactAdditiveFormulaSetEqRowsDef,
    CompactAdditiveFormulaSetEqRows, hforward, hreverse]

theorem compactAdditiveFormulaSetEqRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveFormulaSetEqRowsDef.val := by
  simp [compactAdditiveFormulaSetEqRowsDef]

theorem compactAdditiveFormulaSubsetRows_iff
    {tokenTable width tokenCount leftBoundary rightBoundary : Nat}
    {left right : List (List Nat)}
    (hleft : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftBoundary left)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightBoundary right) :
    CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
        leftBoundary left.length rightBoundary right.length ↔
      forall formula, formula ∈ left -> formula ∈ right := by
  constructor
  · intro hsubset formula hformula
    obtain ⟨index, hindex, hvalue⟩ :=
      List.mem_iff_getElem.mp hformula
    rcases hsubset index hindex with
      ⟨formulaStart, _hformulaStart,
        formulaFinish, _hformulaFinish,
        hstartEntry, hfinishEntry, hmember⟩
    rcases hleft index hindex with
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
    have hrowMember : left.getI index ∈ right :=
      (compactAdditiveFormulaMemberRows_iff_mem
        hright hrowLayout).mp hmember
    rw [List.getI_eq_getElem left hindex, hvalue] at hrowMember
    exact hrowMember
  · intro hsubset index hindex
    rcases hleft index hindex with
      ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hleftMember : left.getI index ∈ left := by
      rw [List.getI_eq_getElem left hindex]
      exact List.getElem_mem hindex
    have hrightMember : left.getI index ∈ right :=
      hsubset (left.getI index) hleftMember
    have hmember : CompactAdditiveFormulaMemberRows
        tokenTable width tokenCount rightBoundary right.length
          rowStart rowFinish :=
      (compactAdditiveFormulaMemberRows_iff_mem
        hright hrowLayout).mpr hrightMember
    exact ⟨rowStart, hrowStart, rowFinish, hrowFinish,
      hrowStartEntry, hrowFinishEntry, hmember⟩

theorem compactAdditiveFormulaSubsetRows_iff_tokenCheck
    {tokenTable width tokenCount leftBoundary rightBoundary : Nat}
    {left right : List (List Nat)}
    (hleft : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftBoundary left)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightBoundary right) :
    CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
        leftBoundary left.length rightBoundary right.length ↔
      tokenFormulaSubset left right = true := by
  rw [compactAdditiveFormulaSubsetRows_iff hleft hright,
    tokenFormulaSubset_eq_true_iff]

theorem compactAdditiveFormulaSetEqRows_iff_tokenCheck
    {tokenTable width tokenCount leftBoundary rightBoundary : Nat}
    {left right : List (List Nat)}
    (hleft : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftBoundary left)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightBoundary right) :
    CompactAdditiveFormulaSetEqRows tokenTable width tokenCount
        leftBoundary left.length rightBoundary right.length ↔
      tokenFormulaSetEq left right = true := by
  simp only [CompactAdditiveFormulaSetEqRows, tokenFormulaSetEq,
    Bool.and_eq_true]
  exact and_congr
    (compactAdditiveFormulaSubsetRows_iff_tokenCheck hleft hright)
    (compactAdditiveFormulaSubsetRows_iff_tokenCheck hright hleft)

#print axioms compactAdditiveFormulaSubsetRowsDef_spec
#print axioms compactAdditiveFormulaSubsetRowsDef_sigmaZero
#print axioms compactAdditiveFormulaSetEqRowsDef_spec
#print axioms compactAdditiveFormulaSetEqRowsDef_sigmaZero
#print axioms compactAdditiveFormulaSubsetRows_iff_tokenCheck
#print axioms compactAdditiveFormulaSetEqRows_iff_tokenCheck

end FoundationCompactNumericListedDirectFormulaSetChecks
