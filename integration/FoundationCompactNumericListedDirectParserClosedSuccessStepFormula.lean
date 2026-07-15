import integration.FoundationCompactNumericListedDirectParserClosedSuccessBridge
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormula

/-!
# Bounded step formula for successful closed-formula parsing

The ordinary syntax-step formula already opens every executable branch.  A
successful closed-formula trace needs one additional local condition: whenever
the same row is a term-task row, either fewer than two tokens remain or its
term tag is not the rejected free-variable tag `1`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedSuccessStepFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneRows
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserEmptyRows
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserClosedSuccessBridge

theorem CompactUnifiedParserSyntaxTermRows.safe_of_guard
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current : CompactUnifiedParserState}
    {witness : CompactSyntaxTermTaskWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hterm : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount currentCoordinates nextCoordinates
        binderArity witness)
    (hguard : currentCoordinates.tokensCount ≤ 1 ∨ witness.tag ≠ 1) :
    CompactClosedSyntaxStepSafe current := by
  intro _status _actualBinder _actualRepeat _actualTail _tasks
  rcases hguard with hshort | htagNotOne
  · exact Or.inl (by
      simpa only [hcurrent.tokensCount_eq] using hshort)
  · rcases hterm with ⟨_running, _uncons, hbranch⟩
    rcases hbranch with hshort | henough
    · exact Or.inl (by
        simpa only [hcurrent.tokensCount_eq] using hshort.1)
    · apply Or.inr
      rcases henough with ⟨_length, htagRows, _argumentRows, _control⟩
      have htagAt :=
        (compactAdditiveNatListAtRows_iff_getI
          hcurrent.tokensRows 0 witness.tag).mp (by
            simpa only [hcurrent.tokensCount_eq] using htagRows)
      have htagToken : compactTokenAt 0 current.1 = witness.tag :=
        (compactTokenAt_eq_getI 0 current.1).trans htagAt.2
      intro hactual
      exact htagNotOne (htagToken.symm.trans hactual)

theorem CompactUnifiedParserSyntaxTermRows.guard_of_safe
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current : CompactUnifiedParserState}
    {witness : CompactSyntaxTermTaskWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hterm : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount currentCoordinates nextCoordinates
        binderArity witness)
    (hsafe : CompactClosedSyntaxStepSafe current) :
    currentCoordinates.tokensCount ≤ 1 ∨ witness.tag ≠ 1 := by
  by_cases hshortCoordinates : currentCoordinates.tokensCount ≤ 1
  · exact Or.inl hshortCoordinates
  · apply Or.inr
    intro hwitnessTag
    rcases hterm with ⟨hcurrentRunning, huncons, hbranch⟩
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    rcases huncons.realizes hcurrent.tasksCount_eq hcurrent.tasksRows with
      ⟨tail, _tailRows, _tailCount, hcurrentTasks⟩
    rcases hsafe hcurrentStatus binderArity 0 tail hcurrentTasks with
      hshort | htagNotOne
    · have : currentCoordinates.tokensCount ≤ 1 := by
        simpa only [hcurrent.tokensCount_eq] using hshort
      exact hshortCoordinates this
    · rcases hbranch with hshort | henough
      · exact hshortCoordinates hshort.1
      · rcases henough with ⟨_length, htagRows, _argumentRows, _control⟩
        have htagAt :=
          (compactAdditiveNatListAtRows_iff_getI
            hcurrent.tokensRows 0 witness.tag).mp (by
              simpa only [hcurrent.tokensCount_eq] using htagRows)
        have htagToken : compactTokenAt 0 current.1 = witness.tag :=
          (compactTokenAt_eq_getI 0 current.1).trans htagAt.2
        exact htagNotOne (htagToken.trans hwitnessTag)

def CompactUnifiedParserClosedSuccessStepRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Prop :=
  CompactUnifiedParserSyntaxStepRows
      tokenTable width tokenCount current next witness ∧
    (CompactUnifiedParserSyntaxTermRows
        tokenTable width tokenCount current next witness.slot0 witness.term →
      current.tokensCount ≤ 1 ∨ witness.slot4 ≠ 1)

def compactUnifiedParserClosedSuccessStepRowsDef :
    𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6.
    !(compactUnifiedParserSyntaxStepRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∧
    (!(compactUnifiedParserSyntaxTermRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 →
        currentTokensCount ≤ 1 ∨ slot4 ≠ 1)”

@[simp] theorem compactUnifiedParserClosedSuccessStepRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    compactUnifiedParserClosedSuccessStepRowsDef.val.Evalb
        (compactUnifiedParserSyntaxStepFormulaEnvironment
          tokenTable width tokenCount current next witness) ↔
      CompactUnifiedParserClosedSuccessStepRows
        tokenTable width tokenCount current next witness := by
  let env := compactUnifiedParserSyntaxStepFormulaEnvironment
    tokenTable width tokenCount current next witness
  change compactUnifiedParserClosedSuccessStepRowsDef.val.Evalb env ↔ _
  have hidentity :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25]) = env := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepSpec : compactUnifiedParserSyntaxStepRowsDef.val.Evalb env ↔
      CompactUnifiedParserSyntaxStepRows
        tokenTable width tokenCount current next witness := by
    simpa [env] using compactUnifiedParserSyntaxStepRowsDef_spec
      tokenTable width tokenCount current next witness
  have htermSpec : compactUnifiedParserSyntaxTermRowsDef.val.Evalb env ↔
      CompactUnifiedParserSyntaxTermRows
        tokenTable width tokenCount current next witness.slot0 witness.term := by
    have htermIdentity : env =
        compactUnifiedParserSyntaxTermFormulaEnvironment
          tokenTable width tokenCount current next witness.slot0 witness.term := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [htermIdentity]
    exact compactUnifiedParserSyntaxTermRowsDef_spec
      tokenTable width tokenCount current next witness.slot0 witness.term
  have hcurrentCount : env 8 = current.tokensCount := rfl
  have hslot4 : env 23 = witness.slot4 := rfl
  simp [compactUnifiedParserClosedSuccessStepRowsDef,
    CompactUnifiedParserClosedSuccessStepRows,
    hidentity, hstepSpec, htermSpec, hcurrentCount, hslot4]

theorem compactUnifiedParserClosedSuccessStepRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserClosedSuccessStepRowsDef.val := by
  simp [compactUnifiedParserClosedSuccessStepRowsDef]

theorem compactUnifiedParserClosedSuccessStepRows_sound
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    {witness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hrows : CompactUnifiedParserClosedSuccessStepRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness) :
    next = compactClosedSyntaxParserStep current := by
  have hordinary : next = compactSyntaxParserStep current :=
    compactUnifiedParserSyntaxStepRows_sound hcurrent hnext
      ⟨witness, hrows.1⟩
  have hsafe : CompactClosedSyntaxStepSafe current := by
    rcases hrows.1 with hdone | hempty | hrepeat | hterm | hformula | hinvalid
    · rcases (exists_compactUnifiedParserDoneGraphRows_iff hcurrent hnext).mp
        ⟨witness.done, hdone⟩ with ⟨result, hstatus, _next⟩
      intro hnone
      rw [hstatus] at hnone
      contradiction
    · rcases (exists_compactUnifiedParserEmptyGraphRows_iff hcurrent hnext).mp
        ⟨witness.empty, hempty⟩ with ⟨_status, htasks, _next⟩
      intro _ binderArity repeatCount tail hhead
      rw [htasks] at hhead
      contradiction
    · rcases (compactUnifiedParserSyntaxRepeatRows_iff hcurrent hnext).mp
        ⟨witness.repeat, hrepeat⟩ with
          ⟨_status, tail, htasks, _next⟩
      intro _ binderArity repeatCount actualTail hhead
      have hcontra := hhead.symm.trans htasks
      simp at hcontra
    · exact CompactUnifiedParserSyntaxTermRows.safe_of_guard
        hcurrent hterm (hrows.2 hterm)
    · rcases (compactUnifiedParserSyntaxFormulaRows_iff hcurrent hnext).mp
        ⟨witness.formula, hformula⟩ with
          ⟨_status, tail, htasks, _next⟩
      intro _ binderArity repeatCount actualTail hhead
      have hcontra := hhead.symm.trans htasks
      simp at hcontra
    · rcases (compactUnifiedParserSyntaxInvalidRows_iff hcurrent hnext).mp
        ⟨witness.invalid, hinvalid⟩ with
          ⟨_status, kind, binderArity, repeatCount, tail,
            htasks, hkindZero, _hkindOne, _hkindTwo, _next⟩
      intro _ actualBinder actualRepeat actualTail hhead
      have hkinds := hhead.symm.trans htasks
      have hfirst := (List.cons.inj hkinds).1
      have hkind : kind = 0 := (congrArg Prod.fst hfirst).symm
      exact (hkindZero hkind).elim
  exact hordinary.trans
    (compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
      current hsafe).symm

theorem compactUnifiedParserClosedSuccessStepRows_complete
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1)
    (hsafe : CompactClosedSyntaxStepSafe current)
    (hstep : next = compactClosedSyntaxParserStep current) :
    ∃ witness, CompactUnifiedParserClosedSuccessStepRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness := by
  have hordinary : next = compactSyntaxParserStep current :=
    hstep.trans
      (compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
        current hsafe)
  rcases compactUnifiedParserSyntaxStepRows_complete
      hcurrent hnext hwell hordinary with ⟨witness, hrows⟩
  refine ⟨witness, hrows, ?_⟩
  intro hterm
  exact CompactUnifiedParserSyntaxTermRows.guard_of_safe
    hcurrent hterm hsafe

theorem exists_compactUnifiedParserClosedSuccessStepFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1)
    (hsafe : CompactClosedSyntaxStepSafe current) :
    (∃ witness,
        compactUnifiedParserClosedSuccessStepRowsDef.val.Evalb
          (compactUnifiedParserSyntaxStepFormulaEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              witness)) ↔
      next = compactClosedSyntaxParserStep current := by
  simp only [compactUnifiedParserClosedSuccessStepRowsDef_spec]
  exact ⟨fun ⟨witness, hrows⟩ =>
      compactUnifiedParserClosedSuccessStepRows_sound
        hcurrent hnext hrows,
    compactUnifiedParserClosedSuccessStepRows_complete
      hcurrent hnext hwell hsafe⟩

#print axioms CompactUnifiedParserSyntaxTermRows.safe_of_guard
#print axioms CompactUnifiedParserSyntaxTermRows.guard_of_safe
#print axioms compactUnifiedParserClosedSuccessStepRowsDef_spec
#print axioms compactUnifiedParserClosedSuccessStepRowsDef_sigmaZero
#print axioms compactUnifiedParserClosedSuccessStepRows_sound
#print axioms compactUnifiedParserClosedSuccessStepRows_complete
#print axioms exists_compactUnifiedParserClosedSuccessStepFormula_iff

end FoundationCompactNumericListedDirectParserClosedSuccessStepFormula
