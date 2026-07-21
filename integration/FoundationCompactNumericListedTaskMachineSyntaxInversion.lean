import integration.FoundationCompactNumericListedTaskMachine
import integration.FoundationCompactProofTokenMachineInversion
import integration.FoundationCompactCertificateTokenMachineInversion
import integration.FoundationCompactNumericListedProofNodeTypedInversion
import integration.FoundationCompactNumericListedCertificateNodeTypedInversion
import integration.FoundationCompactNumericListedDirectNodeTransitionCases

/-!
# Syntax inversion for the synchronized listed-proof task machine

The verifier stack contains parse tasks and postorder combine tasks.  Erasing
the combine tasks yields exactly the pending recursive tasks of the public
proof and structural-certificate parsers.  This file records that erasure and
the typed syntax invariant used by the reverse `P_direct` endpoint.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedTaskMachineSyntaxInversion

open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactProofTokenMachineInversion
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedProofNodeTypedInversion
open FoundationCompactNumericListedCertificateNodeTypedInversion
open FoundationCompactNumericListedDirectNodeTransitionCases

def compactNumericVerifierPendingProofTasks :
    List CompactNumericVerifierTask -> List CompactProofParserTask
  | [] => []
  | task :: tasks =>
      if task.1 = 10 then
        compactProofTask :: compactNumericVerifierPendingProofTasks tasks
      else
        compactNumericVerifierPendingProofTasks tasks

def compactNumericVerifierPendingCertificateTasks :
    List CompactNumericVerifierTask -> List CompactCertificateTask
  | [] => []
  | task :: tasks =>
      if task.1 = 10 then
        compactStructuralCertificateTask ::
          compactNumericVerifierPendingCertificateTasks tasks
      else
        compactNumericVerifierPendingCertificateTasks tasks

@[simp] theorem compactNumericVerifierPendingProofTasks_nil :
    compactNumericVerifierPendingProofTasks [] = [] := rfl

@[simp] theorem compactNumericVerifierPendingCertificateTasks_nil :
    compactNumericVerifierPendingCertificateTasks [] = [] := rfl

@[simp] theorem compactNumericVerifierPendingProofTasks_parse
    (tasks : List CompactNumericVerifierTask) :
    compactNumericVerifierPendingProofTasks
        (compactNumericParseTask :: tasks) =
      compactProofTask :: compactNumericVerifierPendingProofTasks tasks := by
  simp [compactNumericVerifierPendingProofTasks, compactNumericParseTask]

@[simp] theorem compactNumericVerifierPendingCertificateTasks_parse
    (tasks : List CompactNumericVerifierTask) :
    compactNumericVerifierPendingCertificateTasks
        (compactNumericParseTask :: tasks) =
      compactStructuralCertificateTask ::
        compactNumericVerifierPendingCertificateTasks tasks := by
  simp [compactNumericVerifierPendingCertificateTasks,
    compactNumericParseTask]

@[simp] theorem compactNumericVerifierPendingProofTasks_nonparse
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (htag : task.1 ≠ 10) :
    compactNumericVerifierPendingProofTasks (task :: tasks) =
      compactNumericVerifierPendingProofTasks tasks := by
  simp [compactNumericVerifierPendingProofTasks, htag]

@[simp] theorem compactNumericVerifierPendingCertificateTasks_nonparse
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (htag : task.1 ≠ 10) :
    compactNumericVerifierPendingCertificateTasks (task :: tasks) =
      compactNumericVerifierPendingCertificateTasks tasks := by
  simp [compactNumericVerifierPendingCertificateTasks, htag]

def CompactNumericVerifierSyntaxRealizes
    (payload : CompactNumericRunningPayload) : Prop :=
  CompactProofTasksRealize
      (compactNumericVerifierPendingProofTasks payload.2.1)
      payload.1.1 [] /\
    CompactCertificateTasksRealize
      (compactNumericVerifierPendingCertificateTasks payload.2.1)
      payload.1.2 []

def CompactNumericVerifierAcceptedStatusGuard
    (state : CompactNumericVerifierState) : Prop :=
  state.2 = some true ->
    state.1.1.1 = [] /\
      state.1.1.2 = [] /\
      state.1.2.1 = [] /\
      state.1.2.2.length = 1

theorem compactNumericVerifierAcceptedStatusGuard_initial
    (proofTokens certificateTokens : List Nat) :
    CompactNumericVerifierAcceptedStatusGuard
      (compactNumericVerifierInitialState proofTokens certificateTokens) := by
  simp [CompactNumericVerifierAcceptedStatusGuard,
    compactNumericVerifierInitialState]

theorem compactNumericVerifierAcceptedStatusGuard_step
    {state : CompactNumericVerifierState}
    (hguard : CompactNumericVerifierAcceptedStatusGuard state) :
    CompactNumericVerifierAcceptedStatusGuard
      (compactNumericVerifierStep state) := by
  rcases state with ⟨payload, status⟩
  rcases payload with ⟨streams, tasksAndValues⟩
  rcases streams with ⟨proofTokens, certificateTokens⟩
  rcases tasksAndValues with ⟨tasks, values⟩
  cases status with
  | some result =>
      cases result with
      | false =>
          simp [CompactNumericVerifierAcceptedStatusGuard,
            compactNumericVerifierStep]
      | true =>
          simpa [CompactNumericVerifierAcceptedStatusGuard,
            compactNumericVerifierStep] using hguard
  | none =>
      cases tasks with
      | nil =>
          simp only [compactNumericVerifierStep,
            compactNumericRunningStep]
          unfold compactNumericFinishState
          by_cases hfinish : proofTokens = [] ∧ certificateTokens = [] ∧
              values.length = 1
          · simp [hfinish, CompactNumericVerifierAcceptedStatusGuard]
          · simp [hfinish, CompactNumericVerifierAcceptedStatusGuard]
      | cons task restTasks =>
          by_cases hparse : task.1 = 10
          · simp only [compactNumericVerifierStep,
              compactNumericRunningStep, hparse, if_pos]
            unfold compactNumericParseState
            cases compactNumericParsePayload
                ((proofTokens, certificateTokens), (restTasks, values)) <;>
              simp [CompactNumericVerifierAcceptedStatusGuard]
          · simp only [compactNumericVerifierStep,
              compactNumericRunningStep, hparse, if_neg]
            unfold compactNumericCombineState
            cases compactNumericCombineTransition task values <;>
              simp [CompactNumericVerifierAcceptedStatusGuard]

theorem compactNumericVerifierAcceptedStatusGuard_iterate
    (steps : Nat) {state : CompactNumericVerifierState}
    (hguard : CompactNumericVerifierAcceptedStatusGuard state) :
    CompactNumericVerifierAcceptedStatusGuard
      ((compactNumericVerifierStep^[steps]) state) := by
  induction steps generalizing state with
  | zero => exact hguard
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih (compactNumericVerifierAcceptedStatusGuard_step hguard)

def CompactNumericVerifierParseSyntaxBackward : Prop :=
  forall (proofTokens certificateTokens : List Nat)
      (restTasks : List CompactNumericVerifierTask)
      (values : List
        FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
      (nextPayload : CompactNumericRunningPayload),
    compactNumericParsePayload
        ((proofTokens, certificateTokens), (restTasks, values)) =
          some nextPayload ->
      CompactNumericVerifierSyntaxRealizes nextPayload ->
      CompactNumericVerifierSyntaxRealizes
        ((proofTokens, certificateTokens),
          (compactNumericParseTask :: restTasks, values))

private theorem compactNumericVerifierSyntaxRealizes_leaf_backward
    (tree : ListedCheckedPAProofTree)
    (certificate :
      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (nextValues : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (hnext : CompactNumericVerifierSyntaxRealizes
      ((proofSuffix, certificateSuffix),
        (restTasks, nextValues))) :
    CompactNumericVerifierSyntaxRealizes
      ((compactListedProofTokens tree ++ proofSuffix,
        compactStructuralCertificateTokens certificate ++ certificateSuffix),
        (compactNumericParseTask :: restTasks, values)) := by
  rcases hnext with ⟨hproof, hcertificate⟩
  constructor
  · simp only [compactNumericVerifierPendingProofTasks_parse]
    exact CompactProofTasksRealize.proof tree hproof
  · simp only [compactNumericVerifierPendingCertificateTasks_parse]
    exact CompactCertificateTasksRealize.structural certificate hcertificate

private theorem compactNumericVerifierSyntaxRealizes_unary_backward
    (proofPrefix certificatePrefix : List Nat)
    (wrapProof : ListedCheckedPAProofTree -> ListedCheckedPAProofTree)
    (wrapCertificate :
      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate ->
        FoundationCompactPAAxiomCertificate.StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (combineTask : CompactNumericVerifierTask)
    (restTasks : List CompactNumericVerifierTask)
    (values nextValues : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (hcombineTag : combineTask.1 ≠ 10)
    (hproofTokens : forall premise,
      compactListedProofTokens (wrapProof premise) =
        proofPrefix ++ compactListedProofTokens premise)
    (hcertificateTokens : forall premiseCertificate,
      compactStructuralCertificateTokens
          (wrapCertificate premiseCertificate) =
        certificatePrefix ++
          compactStructuralCertificateTokens premiseCertificate)
    (hnext : CompactNumericVerifierSyntaxRealizes
      ((proofSuffix, certificateSuffix),
        (compactNumericParseTask :: combineTask :: restTasks,
          nextValues))) :
    CompactNumericVerifierSyntaxRealizes
      ((proofPrefix ++ proofSuffix,
        certificatePrefix ++ certificateSuffix),
        (compactNumericParseTask :: restTasks, values)) := by
  rcases hnext with ⟨hproof, hcertificate⟩
  simp only [compactNumericVerifierPendingProofTasks_parse,
    compactNumericVerifierPendingProofTasks_nonparse
      combineTask restTasks hcombineTag] at hproof
  simp only [compactNumericVerifierPendingCertificateTasks_parse,
    compactNumericVerifierPendingCertificateTasks_nonparse
      combineTask restTasks hcombineTag] at hcertificate
  cases hproof with
  | proof premise hproofRest =>
      cases hcertificate with
      | structural premiseCertificate hcertificateRest =>
          constructor
          · simp only [compactNumericVerifierPendingProofTasks_parse]
            simpa only [compactProofTask, hproofTokens premise,
              List.append_assoc] using
              CompactProofTasksRealize.proof
                (wrapProof premise) hproofRest
          · simp only [compactNumericVerifierPendingCertificateTasks_parse]
            simpa only [compactStructuralCertificateTask,
              hcertificateTokens premiseCertificate,
              List.append_assoc] using
              CompactCertificateTasksRealize.structural
                (wrapCertificate premiseCertificate) hcertificateRest

private theorem compactNumericVerifierSyntaxRealizes_binary_backward
    (proofPrefix certificatePrefix : List Nat)
    (wrapProof : ListedCheckedPAProofTree -> ListedCheckedPAProofTree ->
      ListedCheckedPAProofTree)
    (wrapCertificate :
      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate ->
        FoundationCompactPAAxiomCertificate.StructuralValidityCertificate ->
          FoundationCompactPAAxiomCertificate.StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (combineTask : CompactNumericVerifierTask)
    (restTasks : List CompactNumericVerifierTask)
    (values nextValues : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (hcombineTag : combineTask.1 ≠ 10)
    (hproofTokens : forall left right,
      compactListedProofTokens (wrapProof left right) =
        proofPrefix ++ compactListedProofTokens left ++
          compactListedProofTokens right)
    (hcertificateTokens : forall leftCertificate rightCertificate,
      compactStructuralCertificateTokens
          (wrapCertificate leftCertificate rightCertificate) =
        certificatePrefix ++
          compactStructuralCertificateTokens leftCertificate ++
          compactStructuralCertificateTokens rightCertificate)
    (hnext : CompactNumericVerifierSyntaxRealizes
      ((proofSuffix, certificateSuffix),
        (compactNumericParseTask :: compactNumericParseTask ::
          combineTask :: restTasks, nextValues))) :
    CompactNumericVerifierSyntaxRealizes
      ((proofPrefix ++ proofSuffix,
        certificatePrefix ++ certificateSuffix),
        (compactNumericParseTask :: restTasks, values)) := by
  rcases hnext with ⟨hproof, hcertificate⟩
  simp only [compactNumericVerifierPendingProofTasks_parse,
    compactNumericVerifierPendingProofTasks_nonparse
      combineTask restTasks hcombineTag] at hproof
  simp only [compactNumericVerifierPendingCertificateTasks_parse,
    compactNumericVerifierPendingCertificateTasks_nonparse
      combineTask restTasks hcombineTag] at hcertificate
  cases hproof with
  | proof left hproofAfterLeft =>
      cases hproofAfterLeft with
      | proof right hproofRest =>
          cases hcertificate with
          | structural leftCertificate hcertificateAfterLeft =>
              cases hcertificateAfterLeft with
              | structural rightCertificate hcertificateRest =>
                  constructor
                  · simp only [compactNumericVerifierPendingProofTasks_parse]
                    simpa only [compactProofTask,
                      hproofTokens left right,
                      List.append_assoc] using
                      CompactProofTasksRealize.proof
                        (wrapProof left right) hproofRest
                  · simp only [
                      compactNumericVerifierPendingCertificateTasks_parse]
                    simpa only [compactStructuralCertificateTask,
                      hcertificateTokens leftCertificate rightCertificate,
                      List.append_assoc] using
                      CompactCertificateTasksRealize.structural
                        (wrapCertificate leftCertificate rightCertificate)
                        hcertificateRest

theorem compactNumericVerifierParseSyntaxBackward :
    CompactNumericVerifierParseSyntaxBackward := by
  intro proofTokens certificateTokens restTasks values nextPayload
    hparse hnextSyntax
  cases hproof :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        proofTokens with
  | none =>
      simp [compactNumericParsePayload, hproof] at hparse
  | some proofRoot =>
      cases hcertificate :
          FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
            certificateTokens with
      | none =>
          simp [compactNumericParsePayload, hproof, hcertificate] at hparse
      | some certificateRoot =>
          have hproofTyped :=
            (compactListedProofNodeFieldsParser_eq_some_iff_typed
              proofTokens proofRoot).mp hproof
          have hcertificateTyped :=
            (compactStructuralCertificateNodeParser_eq_some_iff_typed
              certificateTokens certificateRoot).mp hcertificate
          have htransition : compactNumericNodeTransition proofRoot
              certificateRoot restTasks values = some nextPayload := by
            simpa [compactNumericParsePayload, hproof, hcertificate]
              using hparse
          have houtput :=
            (compactNumericNodeTransition_eq_some_iff_outputCase
              proofRoot certificateRoot restTasks values nextPayload).mp
              htransition
          rcases houtput with hclosed | haxm | hverum | hand | hor | hall |
            hexs | hwk | hshift | hcut
          · rcases hclosed with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case closed Gamma formula proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case leaf certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                simpa [compactListedProofTokens,
                  compactStructuralCertificateTokens, List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_leaf_backward
                    (ListedCheckedPAProofTree.closed Gamma formula)
                    FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.leaf
                    proofSuffix certificateSuffix restTasks values _ hnextSyntax
          · rcases haxm with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case axm Gamma sentence proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case pa certificate certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                simpa [compactListedProofTokens,
                  compactStructuralCertificateTokens, List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_leaf_backward
                    (ListedCheckedPAProofTree.axm Gamma sentence)
                    (FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.axiomCert
                      certificate)
                    proofSuffix certificateSuffix restTasks values _ hnextSyntax
          · rcases hverum with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case verum Gamma proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case leaf certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                simpa [compactListedProofTokens,
                  compactStructuralCertificateTokens, List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_leaf_backward
                    (ListedCheckedPAProofTree.verum Gamma)
                    FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.leaf
                    proofSuffix certificateSuffix restTasks values _ hnextSyntax
          · rcases hand with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case andNode Gamma leftFormula rightFormula proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case binary certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                let fields :=
                  (arithmeticPropositionTokenValues Gamma,
                    (compactArithmeticFormulaTokens leftFormula,
                      (compactArithmeticFormulaTokens rightFormula,
                        (([] : List Nat), proofSuffix))))
                have hnextSyntax' : CompactNumericVerifierSyntaxRealizes
                    ((proofSuffix, certificateSuffix),
                      (compactNumericParseTask :: compactNumericParseTask ::
                        compactNumericCombineTask 3 fields :: restTasks,
                        values)) := by
                  simpa [fields,
                    FoundationCompactNumericListedNodeFields.compactNumericNodeFieldsSuffix]
                    using hnextSyntax
                simpa [List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_binary_backward
                    (3 :: compactSequentListTokens Gamma ++
                      compactArithmeticFormulaTokens leftFormula ++
                      compactArithmeticFormulaTokens rightFormula)
                    [3]
                    (fun left right => ListedCheckedPAProofTree.and Gamma
                      leftFormula rightFormula left right)
                    (fun leftCertificate rightCertificate =>
                      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.binary
                        leftCertificate rightCertificate)
                    proofSuffix certificateSuffix
                    (compactNumericCombineTask 3 fields)
                    restTasks values values
                    (by simp [compactNumericCombineTask])
                    (by
                      intro left right
                      simp [compactListedProofTokens, List.append_assoc])
                    (by
                      intro leftCertificate rightCertificate
                      simp [compactStructuralCertificateTokens,
                        List.append_assoc])
                    hnextSyntax'
          · rcases hor with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case orNode Gamma leftFormula rightFormula proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case unary certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                let fields :=
                  (arithmeticPropositionTokenValues Gamma,
                    (compactArithmeticFormulaTokens leftFormula,
                      (compactArithmeticFormulaTokens rightFormula,
                        (([] : List Nat), proofSuffix))))
                have hnextSyntax' : CompactNumericVerifierSyntaxRealizes
                    ((proofSuffix, certificateSuffix),
                      (compactNumericParseTask ::
                        compactNumericCombineTask 4 fields :: restTasks,
                        values)) := by
                  simpa [fields,
                    FoundationCompactNumericListedNodeFields.compactNumericNodeFieldsSuffix]
                    using hnextSyntax
                simpa [List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_unary_backward
                    (4 :: compactSequentListTokens Gamma ++
                      compactArithmeticFormulaTokens leftFormula ++
                      compactArithmeticFormulaTokens rightFormula)
                    [2]
                    (fun premise => ListedCheckedPAProofTree.or Gamma
                      leftFormula rightFormula premise)
                    (fun premiseCertificate =>
                      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.unary
                        premiseCertificate)
                    proofSuffix certificateSuffix
                    (compactNumericCombineTask 4 fields)
                    restTasks values values
                    (by simp [compactNumericCombineTask])
                    (by
                      intro premise
                      simp [compactListedProofTokens, List.append_assoc])
                    (by
                      intro premiseCertificate
                      simp [compactStructuralCertificateTokens,
                        List.append_assoc])
                    hnextSyntax'
          · rcases hall with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case allNode Gamma formula proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case unary certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                let fields :=
                  (arithmeticPropositionTokenValues Gamma,
                    (compactArithmeticFormulaTokens formula,
                      (([] : List Nat), (([] : List Nat), proofSuffix))))
                have hnextSyntax' : CompactNumericVerifierSyntaxRealizes
                    ((proofSuffix, certificateSuffix),
                      (compactNumericParseTask ::
                        compactNumericCombineTask 5 fields :: restTasks,
                        values)) := by
                  simpa [fields,
                    FoundationCompactNumericListedNodeFields.compactNumericNodeFieldsSuffix]
                    using hnextSyntax
                simpa [List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_unary_backward
                    (5 :: compactSequentListTokens Gamma ++
                      compactArithmeticFormulaTokens formula)
                    [2]
                    (fun premise => ListedCheckedPAProofTree.all Gamma
                      formula premise)
                    (fun premiseCertificate =>
                      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.unary
                        premiseCertificate)
                    proofSuffix certificateSuffix
                    (compactNumericCombineTask 5 fields)
                    restTasks values values
                    (by simp [compactNumericCombineTask])
                    (by
                      intro premise
                      simp [compactListedProofTokens, List.append_assoc])
                    (by
                      intro premiseCertificate
                      simp [compactStructuralCertificateTokens,
                        List.append_assoc])
                    hnextSyntax'
          · rcases hexs with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case exsNode Gamma formula witness proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case unary certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                let fields :=
                  (arithmeticPropositionTokenValues Gamma,
                    (compactArithmeticFormulaTokens formula,
                      (([] : List Nat),
                        (compactArithmeticTermTokens witness, proofSuffix))))
                have hnextSyntax' : CompactNumericVerifierSyntaxRealizes
                    ((proofSuffix, certificateSuffix),
                      (compactNumericParseTask ::
                        compactNumericCombineTask 6 fields :: restTasks,
                        values)) := by
                  simpa [fields,
                    FoundationCompactNumericListedNodeFields.compactNumericNodeFieldsSuffix]
                    using hnextSyntax
                simpa [List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_unary_backward
                    (6 :: compactSequentListTokens Gamma ++
                      compactArithmeticFormulaTokens formula ++
                      compactArithmeticTermTokens witness)
                    [2]
                    (fun premise => ListedCheckedPAProofTree.exs Gamma
                      formula witness premise)
                    (fun premiseCertificate =>
                      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.unary
                        premiseCertificate)
                    proofSuffix certificateSuffix
                    (compactNumericCombineTask 6 fields)
                    restTasks values values
                    (by simp [compactNumericCombineTask])
                    (by
                      intro premise
                      simp [compactListedProofTokens, List.append_assoc])
                    (by
                      intro premiseCertificate
                      simp [compactStructuralCertificateTokens,
                        List.append_assoc])
                    hnextSyntax'
          · rcases hwk with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case wkNode Gamma proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case unary certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                let fields :=
                  (arithmeticPropositionTokenValues Gamma,
                    (([] : List Nat),
                      (([] : List Nat), (([] : List Nat), proofSuffix))))
                have hnextSyntax' : CompactNumericVerifierSyntaxRealizes
                    ((proofSuffix, certificateSuffix),
                      (compactNumericParseTask ::
                        compactNumericCombineTask 7 fields :: restTasks,
                        values)) := by
                  simpa [fields,
                    FoundationCompactNumericListedNodeFields.compactNumericNodeFieldsSuffix]
                    using hnextSyntax
                simpa [List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_unary_backward
                    (7 :: compactSequentListTokens Gamma)
                    [2]
                    (fun premise => ListedCheckedPAProofTree.wk Gamma premise)
                    (fun premiseCertificate =>
                      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.unary
                        premiseCertificate)
                    proofSuffix certificateSuffix
                    (compactNumericCombineTask 7 fields)
                    restTasks values values
                    (by simp [compactNumericCombineTask])
                    (by
                      intro premise
                      simp [compactListedProofTokens, List.append_assoc])
                    (by
                      intro premiseCertificate
                      simp [compactStructuralCertificateTokens,
                        List.append_assoc])
                    hnextSyntax'
          · rcases hshift with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case shiftNode Gamma proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case unary certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                let fields :=
                  (arithmeticPropositionTokenValues Gamma,
                    (([] : List Nat),
                      (([] : List Nat), (([] : List Nat), proofSuffix))))
                have hnextSyntax' : CompactNumericVerifierSyntaxRealizes
                    ((proofSuffix, certificateSuffix),
                      (compactNumericParseTask ::
                        compactNumericCombineTask 8 fields :: restTasks,
                        values)) := by
                  simpa [fields,
                    FoundationCompactNumericListedNodeFields.compactNumericNodeFieldsSuffix]
                    using hnextSyntax
                simpa [List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_unary_backward
                    (8 :: compactSequentListTokens Gamma)
                    [2]
                    (fun premise =>
                      ListedCheckedPAProofTree.shift Gamma premise)
                    (fun premiseCertificate =>
                      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.unary
                        premiseCertificate)
                    proofSuffix certificateSuffix
                    (compactNumericCombineTask 8 fields)
                    restTasks values values
                    (by simp [compactNumericCombineTask])
                    (by
                      intro premise
                      simp [compactListedProofTokens, List.append_assoc])
                    (by
                      intro premiseCertificate
                      simp [compactStructuralCertificateTokens,
                        List.append_assoc])
                    hnextSyntax'
          · rcases hcut with ⟨hproofTag, hcertificateTag, hnextPayload⟩
            cases hproofTyped <;> simp at hproofTag
            case cutNode Gamma formula proofSuffix =>
              cases hcertificateTyped <;> simp at hcertificateTag
              case binary certificateSuffix =>
                rw [← hnextPayload] at hnextSyntax
                let fields :=
                  (arithmeticPropositionTokenValues Gamma,
                    (compactArithmeticFormulaTokens formula,
                      (([] : List Nat), (([] : List Nat), proofSuffix))))
                have hnextSyntax' : CompactNumericVerifierSyntaxRealizes
                    ((proofSuffix, certificateSuffix),
                      (compactNumericParseTask :: compactNumericParseTask ::
                        compactNumericCombineTask 9 fields :: restTasks,
                        values)) := by
                  simpa [fields,
                    FoundationCompactNumericListedNodeFields.compactNumericNodeFieldsSuffix]
                    using hnextSyntax
                simpa [List.append_assoc] using
                  compactNumericVerifierSyntaxRealizes_binary_backward
                    (9 :: compactSequentListTokens Gamma ++
                      compactArithmeticFormulaTokens formula)
                    [3]
                    (fun left right => ListedCheckedPAProofTree.cut Gamma
                      formula left right)
                    (fun leftCertificate rightCertificate =>
                      FoundationCompactPAAxiomCertificate.StructuralValidityCertificate.binary
                        leftCertificate rightCertificate)
                    proofSuffix certificateSuffix
                    (compactNumericCombineTask 9 fields)
                    restTasks values values
                    (by simp [compactNumericCombineTask])
                    (by
                      intro left right
                      simp [compactListedProofTokens, List.append_assoc])
                    (by
                      intro leftCertificate rightCertificate
                      simp [compactStructuralCertificateTokens,
                        List.append_assoc])
                    hnextSyntax'

theorem compactNumericVerifierSyntaxRealizes_finished
    (values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult) :
    CompactNumericVerifierSyntaxRealizes (([], []), ([], values)) := by
  exact ⟨CompactProofTasksRealize.nil [],
    CompactCertificateTasksRealize.nil []⟩

theorem compactNumericVerifierSyntaxRealizes_of_acceptedIterate
    (hparseBackward : CompactNumericVerifierParseSyntaxBackward)
    (steps : Nat) (state : CompactNumericVerifierState)
    (hguard : CompactNumericVerifierAcceptedStatusGuard state)
    (haccepted :
      ((compactNumericVerifierStep^[steps]) state).2 = some true) :
    CompactNumericVerifierSyntaxRealizes state.1 := by
  induction steps generalizing state with
  | zero =>
      have hfinish := hguard haccepted
      rcases state with
        ⟨⟨⟨proofTokens, certificateTokens⟩, ⟨tasks, values⟩⟩,
          status⟩
      simp only at hfinish
      rcases hfinish with
        ⟨hproof, hcertificate, htasks, _hvalueLength⟩
      subst proofTokens
      subst certificateTokens
      subst tasks
      exact compactNumericVerifierSyntaxRealizes_finished values
  | succ remaining ih =>
      have hnextAccepted :
          ((compactNumericVerifierStep^[remaining])
            (compactNumericVerifierStep state)).2 = some true := by
        simpa only [Function.iterate_succ_apply] using haccepted
      have hnextSyntax := ih
        (compactNumericVerifierStep state)
        (compactNumericVerifierAcceptedStatusGuard_step hguard)
        hnextAccepted
      rcases state with
        ⟨⟨⟨proofTokens, certificateTokens⟩, ⟨tasks, values⟩⟩,
          status⟩
      cases status with
      | some result =>
          simpa [compactNumericVerifierStep] using hnextSyntax
      | none =>
          cases tasks with
          | nil =>
              have hfinishPayload :
                  (compactNumericFinishState
                    ((proofTokens, certificateTokens), ([], values))).1 =
                    ((proofTokens, certificateTokens), ([], values)) := by
                unfold compactNumericFinishState
                split <;> rfl
              simpa only [compactNumericVerifierStep,
                Option.isSome_none, Bool.false_eq_true, if_false,
                compactNumericRunningStep, hfinishPayload]
                using hnextSyntax
          | cons task restTasks =>
              by_cases hparseTask : task.1 = 10
              · cases hparsePayload : compactNumericParsePayload
                    ((proofTokens, certificateTokens),
                      (restTasks, values)) with
                | none =>
                    have hhalted := compactNumericVerifierStep_iterate_halted
                      remaining
                      ((proofTokens, certificateTokens), (restTasks, values))
                      false
                    have hnextState : compactNumericVerifierStep
                        ((((proofTokens, certificateTokens),
                          (task :: restTasks, values)),
                            none)) =
                        (((proofTokens, certificateTokens),
                          (restTasks, values)), some false) := by
                      simp [compactNumericVerifierStep,
                        compactNumericRunningStep, hparseTask,
                        compactNumericParseState, hparsePayload]
                    rw [hnextState, hhalted] at hnextAccepted
                    simp at hnextAccepted
                | some nextPayload =>
                    have hnextSyntax' :
                        CompactNumericVerifierSyntaxRealizes nextPayload := by
                      simpa [compactNumericVerifierStep,
                        compactNumericRunningStep, hparseTask,
                        compactNumericParseState, hparsePayload]
                        using hnextSyntax
                    have hstandard := hparseBackward proofTokens certificateTokens
                      restTasks values nextPayload hparsePayload hnextSyntax'
                    simpa [CompactNumericVerifierSyntaxRealizes,
                      compactNumericVerifierPendingProofTasks,
                      compactNumericVerifierPendingCertificateTasks,
                      compactNumericParseTask, hparseTask] using hstandard
              · unfold compactNumericVerifierStep at hnextSyntax
                simp only [Option.isSome_none, Bool.false_eq_true,
                  if_false, compactNumericRunningStep, hparseTask,
                  if_neg] at hnextSyntax
                unfold compactNumericCombineState at hnextSyntax
                cases hcombine : compactNumericCombineTransition task values <;>
                  simp [hcombine, CompactNumericVerifierSyntaxRealizes,
                    compactNumericVerifierPendingProofTasks,
                    compactNumericVerifierPendingCertificateTasks,
                    hparseTask] at hnextSyntax ⊢ <;>
                  exact hnextSyntax

theorem CompactNumericVerifierSyntaxRealizes.initial_exists
    {proofTokens certificateTokens : List Nat}
    (hsyntax : CompactNumericVerifierSyntaxRealizes
      ((proofTokens, certificateTokens), ([compactNumericParseTask], []))) :
    exists tree : ListedCheckedPAProofTree,
      exists certificate :
          FoundationCompactPAAxiomCertificate.StructuralValidityCertificate,
        proofTokens = compactListedProofTokens tree /\
          certificateTokens =
            compactStructuralCertificateTokens certificate := by
  rcases hsyntax with ⟨hproof, hcertificate⟩
  simp only [compactNumericVerifierPendingProofTasks_parse,
    compactNumericVerifierPendingProofTasks_nil] at hproof
  simp only [compactNumericVerifierPendingCertificateTasks_parse,
    compactNumericVerifierPendingCertificateTasks_nil] at hcertificate
  cases hproof with
  | proof tree proofRest =>
      cases proofRest with
      | nil =>
          cases hcertificate with
          | structural certificate certificateRest =>
              cases certificateRest with
              | nil =>
                  exact ⟨tree, certificate, by simp, by simp⟩

theorem compactNumericVerifierResult_true_exists_canonical
    (proofTokens certificateTokens : List Nat)
    (hresult :
      compactNumericVerifierResult proofTokens certificateTokens = true) :
    exists tree : ListedCheckedPAProofTree,
      exists certificate :
          FoundationCompactPAAxiomCertificate.StructuralValidityCertificate,
        proofTokens = compactListedProofTokens tree /\
          certificateTokens =
            compactStructuralCertificateTokens certificate /\
          listedCertificateValid tree certificate := by
  have haccepted :
      (compactNumericVerifierRun proofTokens certificateTokens).2 =
        some true := by
    unfold compactNumericVerifierResult at hresult
    cases hstatus :
        (compactNumericVerifierRun proofTokens certificateTokens).2 with
    | none => simp [hstatus] at hresult
    | some result =>
        cases result with
        | false => simp [hstatus] at hresult
        | true => rfl
  have hsyntax := compactNumericVerifierSyntaxRealizes_of_acceptedIterate
    compactNumericVerifierParseSyntaxBackward
    (compactNumericVerifierFuelBound proofTokens certificateTokens)
    (compactNumericVerifierInitialState proofTokens certificateTokens)
    (compactNumericVerifierAcceptedStatusGuard_initial
      proofTokens certificateTokens)
    (by simpa [compactNumericVerifierRun] using haccepted)
  have hinitial : CompactNumericVerifierSyntaxRealizes
      ((proofTokens, certificateTokens), ([compactNumericParseTask], [])) := by
    simpa [compactNumericVerifierInitialState] using hsyntax
  rcases CompactNumericVerifierSyntaxRealizes.initial_exists hinitial with
    ⟨tree, certificate, hproofTokens, hcertificateTokens⟩
  have hcanonicalResult :
      compactNumericVerifierResult
          (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate) = true := by
    simpa [← hproofTokens, ← hcertificateTokens] using hresult
  rw [compactNumericVerifierResult_canonical] at hcanonicalResult
  have hvalid :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).mp
      hcanonicalResult
  exact ⟨tree, certificate, hproofTokens, hcertificateTokens, hvalid⟩

#print axioms
  CompactNumericVerifierSyntaxRealizes.initial_exists
#print axioms compactNumericVerifierParseSyntaxBackward
#print axioms compactNumericVerifierAcceptedStatusGuard_step
#print axioms compactNumericVerifierAcceptedStatusGuard_iterate
#print axioms compactNumericVerifierSyntaxRealizes_of_acceptedIterate
#print axioms compactNumericVerifierResult_true_exists_canonical

end FoundationCompactNumericListedTaskMachineSyntaxInversion
