import integration.FoundationCompactNumericListedTaskMachine

/-!
# Exact public cases for the listed node transition

The transition can fail only when the proof-node and certificate-node tags do
not match.  Leaf rule checks return a Boolean child result inside `some`; they
do not add another failure branch.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNodeTransitionCases

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine

def CompactNumericNodeTransitionTagMatch
    (proofTag certificateTag : Nat) : Prop :=
  (proofTag = 0 ∧ certificateTag = 0) ∨
    (proofTag = 1 ∧ certificateTag = 1) ∨
    (proofTag = 2 ∧ certificateTag = 0) ∨
    (proofTag = 3 ∧ certificateTag = 3) ∨
    (proofTag = 4 ∧ certificateTag = 2) ∨
    (proofTag = 5 ∧ certificateTag = 2) ∨
    (proofTag = 6 ∧ certificateTag = 2) ∨
    (proofTag = 7 ∧ certificateTag = 2) ∨
    (proofTag = 8 ∧ certificateTag = 2) ∨
    (proofTag = 9 ∧ certificateTag = 3)

def compactNumericNodeTransitionTagMatchDef :
    𝚺₀.Semisentence 2 := .mkSigma
  “proofTag certificateTag.
    (proofTag = 0 ∧ certificateTag = 0) ∨
    (proofTag = 1 ∧ certificateTag = 1) ∨
    (proofTag = 2 ∧ certificateTag = 0) ∨
    (proofTag = 3 ∧ certificateTag = 3) ∨
    (proofTag = 4 ∧ certificateTag = 2) ∨
    (proofTag = 5 ∧ certificateTag = 2) ∨
    (proofTag = 6 ∧ certificateTag = 2) ∨
    (proofTag = 7 ∧ certificateTag = 2) ∨
    (proofTag = 8 ∧ certificateTag = 2) ∨
    (proofTag = 9 ∧ certificateTag = 3)”

@[simp] theorem compactNumericNodeTransitionTagMatchDef_spec
    (proofTag certificateTag : Nat) :
    compactNumericNodeTransitionTagMatchDef.val.Evalb
        ![proofTag, certificateTag] ↔
      CompactNumericNodeTransitionTagMatch proofTag certificateTag := by
  simp [compactNumericNodeTransitionTagMatchDef,
    CompactNumericNodeTransitionTagMatch] <;> aesop

theorem compactNumericNodeTransitionTagMatchDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericNodeTransitionTagMatchDef.val := by
  simp [compactNumericNodeTransitionTagMatchDef]

def CompactNumericNodeTransitionOutputCase
    (proofNode : Nat × CompactNumericNodeFields)
    (certificateNode : CompactNumericCertificateNode)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (output : CompactNumericRunningPayload) : Prop :=
  let fields := proofNode.2
  let proofSuffix := compactNumericNodeFieldsSuffix fields
  let certificateSuffix := certificateNode.2.2
  let Gamma := fields.1
  let firstFormula := fields.2.1
  let axiomTokens := certificateNode.2.1
  (proofNode.1 = 0 ∧ certificateNode.1 = 0 ∧
    ((proofSuffix, certificateSuffix),
      (restTasks,
        (Gamma, compactClosedRuleCheck (Gamma, firstFormula)) :: values)) =
      output) ∨
  (proofNode.1 = 1 ∧ certificateNode.1 = 1 ∧
    ((proofSuffix, certificateSuffix),
      (restTasks,
        (Gamma, compactAxmRuleCheck
          (Gamma, (firstFormula, axiomTokens))) :: values)) = output) ∨
  (proofNode.1 = 2 ∧ certificateNode.1 = 0 ∧
    ((proofSuffix, certificateSuffix),
      (restTasks, (Gamma, compactVerumRuleCheck Gamma) :: values)) = output) ∨
  (proofNode.1 = 3 ∧ certificateNode.1 = 3 ∧
    ((proofSuffix, certificateSuffix),
      (compactNumericParseTask :: compactNumericParseTask ::
        compactNumericCombineTask 3 fields :: restTasks, values)) = output) ∨
  (proofNode.1 = 4 ∧ certificateNode.1 = 2 ∧
    ((proofSuffix, certificateSuffix),
      (compactNumericParseTask ::
        compactNumericCombineTask 4 fields :: restTasks, values)) = output) ∨
  (proofNode.1 = 5 ∧ certificateNode.1 = 2 ∧
    ((proofSuffix, certificateSuffix),
      (compactNumericParseTask ::
        compactNumericCombineTask 5 fields :: restTasks, values)) = output) ∨
  (proofNode.1 = 6 ∧ certificateNode.1 = 2 ∧
    ((proofSuffix, certificateSuffix),
      (compactNumericParseTask ::
        compactNumericCombineTask 6 fields :: restTasks, values)) = output) ∨
  (proofNode.1 = 7 ∧ certificateNode.1 = 2 ∧
    ((proofSuffix, certificateSuffix),
      (compactNumericParseTask ::
        compactNumericCombineTask 7 fields :: restTasks, values)) = output) ∨
  (proofNode.1 = 8 ∧ certificateNode.1 = 2 ∧
    ((proofSuffix, certificateSuffix),
      (compactNumericParseTask ::
        compactNumericCombineTask 8 fields :: restTasks, values)) = output) ∨
  (proofNode.1 = 9 ∧ certificateNode.1 = 3 ∧
    ((proofSuffix, certificateSuffix),
      (compactNumericParseTask :: compactNumericParseTask ::
        compactNumericCombineTask 9 fields :: restTasks, values)) = output)

theorem compactNumericNodeTransition_eq_some_iff_outputCase
    (proofNode : Nat × CompactNumericNodeFields)
    (certificateNode : CompactNumericCertificateNode)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (output : CompactNumericRunningPayload) :
    compactNumericNodeTransition proofNode certificateNode restTasks values =
        some output ↔
      CompactNumericNodeTransitionOutputCase
        proofNode certificateNode restTasks values output := by
  rcases proofNode with ⟨proofTag, fields⟩
  rcases certificateNode with ⟨certificateTag, certificatePayload⟩
  by_cases h0 : proofTag = 0
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase]
  by_cases h1 : proofTag = 1
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase, h0]
  by_cases h2 : proofTag = 2
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase, h0, h1]
  by_cases h3 : proofTag = 3
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase, h0, h1, h2]
  by_cases h4 : proofTag = 4
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase, h0, h1, h2, h3]
  by_cases h5 : proofTag = 5
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase, h0, h1, h2, h3, h4]
  by_cases h6 : proofTag = 6
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase, h0, h1, h2, h3, h4, h5]
  by_cases h7 : proofTag = 7
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase,
      h0, h1, h2, h3, h4, h5, h6]
  by_cases h8 : proofTag = 8
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase,
      h0, h1, h2, h3, h4, h5, h6, h7]
  by_cases h9 : proofTag = 9
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionOutputCase,
      h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp [compactNumericNodeTransition,
    CompactNumericNodeTransitionOutputCase,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem compactNumericNodeTransition_eq_none_iff_not_tagMatch
    (proofNode : Nat × CompactNumericNodeFields)
    (certificateNode : CompactNumericCertificateNode)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    compactNumericNodeTransition proofNode certificateNode restTasks values =
        none ↔
      ¬ CompactNumericNodeTransitionTagMatch
        proofNode.1 certificateNode.1 := by
  rcases proofNode with ⟨proofTag, fields⟩
  rcases certificateNode with ⟨certificateTag, certificatePayload⟩
  simp only
  by_cases h0 : proofTag = 0
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch]
  by_cases h1 : proofTag = 1
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch, h0]
  by_cases h2 : proofTag = 2
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch, h0, h1]
  by_cases h3 : proofTag = 3
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch, h0, h1, h2]
  by_cases h4 : proofTag = 4
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch, h0, h1, h2, h3]
  by_cases h5 : proofTag = 5
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch, h0, h1, h2, h3, h4]
  by_cases h6 : proofTag = 6
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch, h0, h1, h2, h3, h4, h5]
  by_cases h7 : proofTag = 7
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch,
      h0, h1, h2, h3, h4, h5, h6]
  by_cases h8 : proofTag = 8
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch,
      h0, h1, h2, h3, h4, h5, h6, h7]
  by_cases h9 : proofTag = 9
  · subst proofTag
    simp [compactNumericNodeTransition,
      CompactNumericNodeTransitionTagMatch,
      h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp [compactNumericNodeTransition,
    CompactNumericNodeTransitionTagMatch,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem compactNumericNodeTransition_exists_iff_tagMatch
    (proofNode : Nat × CompactNumericNodeFields)
    (certificateNode : CompactNumericCertificateNode)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    (∃ output,
      compactNumericNodeTransition proofNode certificateNode
        restTasks values = some output) ↔
      CompactNumericNodeTransitionTagMatch
        proofNode.1 certificateNode.1 := by
  constructor
  · rintro ⟨output, houtput⟩
    by_contra hmatch
    have hnone : compactNumericNodeTransition proofNode certificateNode
        restTasks values = none :=
      (compactNumericNodeTransition_eq_none_iff_not_tagMatch
        proofNode certificateNode restTasks values).2 hmatch
    rw [houtput] at hnone
    simp at hnone
  · intro hmatch
    cases htransition : compactNumericNodeTransition proofNode
        certificateNode restTasks values with
    | none =>
        have hnotMatch :=
          (compactNumericNodeTransition_eq_none_iff_not_tagMatch
            proofNode certificateNode restTasks values).1 htransition
        exact False.elim (hnotMatch hmatch)
    | some output =>
        exact ⟨output, rfl⟩

#print axioms compactNumericNodeTransition_eq_none_iff_not_tagMatch
#print axioms compactNumericNodeTransition_exists_iff_tagMatch
#print axioms compactNumericNodeTransitionTagMatchDef_spec
#print axioms compactNumericNodeTransitionTagMatchDef_sigmaZero
#print axioms compactNumericNodeTransition_eq_some_iff_outputCase

end FoundationCompactNumericListedDirectNodeTransitionCases
