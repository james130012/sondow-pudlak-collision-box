import integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph

/-!
# Canonical completeness for every public verifier combine step

The public executable transition is split by its real task tag and source
stack shape.  Every successful rule and the exact failure result then receives
the concrete fixed 93-column graph constructed in the canonical token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph

def CompactNumericVerifierCanonicalCombineStateGraph
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult) : Prop :=
  ∃ target nextStatus backTokens,
    compactNumericCombineState task
        ((proofTokens, certificateTokens), (tasks, source)) =
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus) ∧
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens task tasks source target
        nextStatus backTokens

theorem CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10)
    (htransition : compactNumericCombineTransition task source = none) :
    CompactNumericVerifierCanonicalCombineStateGraph
      proofTokens certificateTokens task tasks source := by
  refine ⟨source, some false, [], ?_,
    CompactNumericVerifierCanonicalCombineGraph.exists_of_failure
      proofTokens certificateTokens task tasks source htaskNe htransition⟩
  simp [compactNumericCombineState, htransition]

theorem CompactNumericVerifierCanonicalCombineStateGraph.exists_of_public_step
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10) :
    CompactNumericVerifierCanonicalCombineStateGraph
      proofTokens certificateTokens task tasks source := by
  rcases task with
    ⟨tag, ⟨Gamma,
      ⟨firstFormula, ⟨secondFormula, ⟨witness, suffix⟩⟩⟩⟩⟩
  by_cases htag3 : tag = 3
  · subst tag
    cases source with
    | nil =>
        apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
          proofTokens certificateTokens
          (3, (Gamma,
            (firstFormula, (secondFormula, (witness, suffix)))))
          tasks [] (by simp)
        simp [compactNumericCombineTransition]
    | cons right rest =>
        rcases right with ⟨rightConclusion, rightValid⟩
        cases rest with
        | nil =>
            apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
              proofTokens certificateTokens
              (3, (Gamma,
                (firstFormula, (secondFormula, (witness, suffix)))))
              tasks [(rightConclusion, rightValid)] (by simp)
            simp [compactNumericCombineTransition]
        | cons left tail =>
            rcases left with ⟨leftConclusion, leftValid⟩
            let target : List CompactNumericChildResult :=
              (Gamma, compactAndRuleCheck
                (Gamma, firstFormula, secondFormula,
                  (leftConclusion, leftValid),
                  rightConclusion, rightValid)) :: tail
            refine ⟨target, none, [], ?_, ?_⟩
            · simp [compactNumericCombineState,
                compactNumericCombineTransition, target]
            · simpa only [target] using
                CompactNumericVerifierCanonicalCombineGraph.exists_of_and
                  proofTokens certificateTokens Gamma firstFormula
                  secondFormula witness suffix tasks rightConclusion
                  leftConclusion rightValid leftValid tail
  by_cases htag4 : tag = 4
  · subst tag
    cases source with
    | nil =>
        apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
          proofTokens certificateTokens
          (4, (Gamma,
            (firstFormula, (secondFormula, (witness, suffix)))))
          tasks [] (by simp)
        simp [compactNumericCombineTransition]
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactOrRuleCheck
            (Gamma, firstFormula, secondFormula,
              rightConclusion, rightValid)) :: tail
        refine ⟨target, none, [], ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa only [target] using
            CompactNumericVerifierCanonicalCombineGraph.exists_of_or
              proofTokens certificateTokens Gamma firstFormula
              secondFormula witness suffix tasks rightConclusion
              rightValid tail
  by_cases htag5 : tag = 5
  · subst tag
    cases source with
    | nil =>
        apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
          proofTokens certificateTokens
          (5, (Gamma,
            (firstFormula, (secondFormula, (witness, suffix)))))
          tasks [] (by simp)
        simp [compactNumericCombineTransition]
    | cons premise tail =>
        rcases premise with ⟨premise, premiseValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactAllRuleCheck
            (Gamma, firstFormula, premise, premiseValid)) :: tail
        refine ⟨target, none,
          compactNumericAllCombineAuxiliaryTokens Gamma firstFormula,
          ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa only [target] using
            CompactNumericVerifierCanonicalCombineGraph.exists_of_all
              proofTokens certificateTokens Gamma firstFormula
              secondFormula witness suffix tasks premise premiseValid tail
  by_cases htag6 : tag = 6
  · subst tag
    cases source with
    | nil =>
        apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
          proofTokens certificateTokens
          (6, (Gamma,
            (firstFormula, (secondFormula, (witness, suffix)))))
          tasks [] (by simp)
        simp [compactNumericCombineTransition]
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactExsRuleCheck
            (Gamma, firstFormula, witness,
              rightConclusion, rightValid)) :: tail
        refine ⟨target, none,
          compactNumericExsCombineAuxiliaryTokens firstFormula witness,
          ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa only [target] using
            CompactNumericVerifierCanonicalCombineGraph.exists_of_exs
              proofTokens certificateTokens Gamma firstFormula
              secondFormula witness suffix tasks rightConclusion
              rightValid tail
  by_cases htag7 : tag = 7
  · subst tag
    cases source with
    | nil =>
        apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
          proofTokens certificateTokens
          (7, (Gamma,
            (firstFormula, (secondFormula, (witness, suffix)))))
          tasks [] (by simp)
        simp [compactNumericCombineTransition]
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactWkRuleCheck
            (Gamma, rightConclusion, rightValid)) :: tail
        refine ⟨target, none, [], ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa only [target] using
            CompactNumericVerifierCanonicalCombineGraph.exists_of_wk
              proofTokens certificateTokens Gamma firstFormula
              secondFormula witness suffix tasks rightConclusion
              rightValid tail
  by_cases htag8 : tag = 8
  · subst tag
    cases source with
    | nil =>
        apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
          proofTokens certificateTokens
          (8, (Gamma,
            (firstFormula, (secondFormula, (witness, suffix)))))
          tasks [] (by simp)
        simp [compactNumericCombineTransition]
    | cons premise tail =>
        rcases premise with ⟨premise, premiseValid⟩
        let target : List CompactNumericChildResult :=
          (Gamma, compactShiftRuleCheck
            (Gamma, premise, premiseValid)) :: tail
        refine ⟨target, none,
          compactNumericShiftCombineAuxiliaryTokens premise, ?_, ?_⟩
        · simp [compactNumericCombineState,
            compactNumericCombineTransition, target]
        · simpa only [target] using
            CompactNumericVerifierCanonicalCombineGraph.exists_of_shift
              proofTokens certificateTokens Gamma firstFormula
              secondFormula witness suffix tasks premise premiseValid tail
  by_cases htag9 : tag = 9
  · subst tag
    cases source with
    | nil =>
        apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
          proofTokens certificateTokens
          (9, (Gamma,
            (firstFormula, (secondFormula, (witness, suffix)))))
          tasks [] (by simp)
        simp [compactNumericCombineTransition]
    | cons right rest =>
        rcases right with ⟨rightConclusion, rightValid⟩
        cases rest with
        | nil =>
            apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
              proofTokens certificateTokens
              (9, (Gamma,
                (firstFormula, (secondFormula, (witness, suffix)))))
              tasks [(rightConclusion, rightValid)] (by simp)
            simp [compactNumericCombineTransition]
        | cons left tail =>
            rcases left with ⟨leftConclusion, leftValid⟩
            let target : List CompactNumericChildResult :=
              (Gamma, compactCutRuleCheck
                (Gamma, firstFormula, (leftConclusion, leftValid),
                  rightConclusion, rightValid)) :: tail
            refine ⟨target, none,
              compactNumericCutCombineAuxiliaryTokens firstFormula,
              ?_, ?_⟩
            · simp [compactNumericCombineState,
                compactNumericCombineTransition, target]
            · simpa only [target] using
                CompactNumericVerifierCanonicalCombineGraph.exists_of_cut
                  proofTokens certificateTokens Gamma firstFormula
                  secondFormula witness suffix tasks rightConclusion
                  leftConclusion rightValid leftValid tail
  apply CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
    proofTokens certificateTokens
    (tag, (Gamma,
      (firstFormula, (secondFormula, (witness, suffix)))))
    tasks source (by simpa using htaskNe)
  simp [compactNumericCombineTransition, htag3, htag4, htag5,
    htag6, htag7, htag8, htag9]

#print axioms
  CompactNumericVerifierCanonicalCombineStateGraph.of_transition_none
#print axioms
  CompactNumericVerifierCanonicalCombineStateGraph.exists_of_public_step

end FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness
