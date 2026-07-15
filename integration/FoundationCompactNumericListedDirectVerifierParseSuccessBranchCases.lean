import integration.FoundationCompactNumericListedDirectVerifierStepCases
import integration.FoundationCompactNumericListedDirectNodeTransitionCases

/-!
# Public branch cases for successful verifier parsing

A successful payload parse exposes both parser results and the actual node
transition.  Its proof-node tag is then classified from the ten successful
output cases of that transition.
-/

namespace FoundationCompactNumericListedDirectVerifierParseSuccessBranchCases

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectNodeTransitionCases

theorem compactNumericParsePayload_eq_some_with_exact_tag_cases
    (payload parsed : CompactNumericRunningPayload)
    (hparse : compactNumericParsePayload payload = some parsed) :
    ∃ proofNode certificateNode,
      compactListedProofNodeFieldsParser payload.1.1 = some proofNode ∧
      compactStructuralCertificateNodeParser payload.1.2 =
        some certificateNode ∧
      compactNumericNodeTransition proofNode certificateNode
        payload.2.1 payload.2.2 = some parsed ∧
      (proofNode.1 = 0 ∨ proofNode.1 = 1 ∨ proofNode.1 = 2 ∨
        proofNode.1 = 3 ∨ proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
        proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 ∨
        proofNode.1 = 9) := by
  rcases (compactNumericParsePayload_eq_some_iff payload parsed).1 hparse with
    ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
      htransition⟩
  have houtput :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode payload.2.1 payload.2.2 parsed).1 htransition
  simp only [CompactNumericNodeTransitionOutputCase] at houtput
  have htag : proofNode.1 = 0 ∨ proofNode.1 = 1 ∨ proofNode.1 = 2 ∨
      proofNode.1 = 3 ∨ proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
      proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 ∨
      proofNode.1 = 9 := by
    rcases houtput with hzero | hone | htwo | hthree | hfour | hfive |
      hsix | hseven | height | hnine
    · exact Or.inl hzero.1
    · exact Or.inr (Or.inl hone.1)
    · exact Or.inr (Or.inr (Or.inl htwo.1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hthree.1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfour.1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfive.1)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hsix.1))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl hseven.1)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl height.1))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr hnine.1))))))))
  exact ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
    htransition, htag⟩

theorem compactNumericParsePayload_eq_some_with_grouped_tag_cases
    (payload parsed : CompactNumericRunningPayload)
    (hparse : compactNumericParsePayload payload = some parsed) :
    ∃ proofNode certificateNode,
      compactListedProofNodeFieldsParser payload.1.1 = some proofNode ∧
      compactStructuralCertificateNodeParser payload.1.2 =
        some certificateNode ∧
      compactNumericNodeTransition proofNode certificateNode
        payload.2.1 payload.2.2 = some parsed ∧
      (proofNode.1 = 0 ∨ proofNode.1 = 1 ∨ proofNode.1 = 2 ∨
        (proofNode.1 = 3 ∨ proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
          proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 ∨
          proofNode.1 = 9)) := by
  rcases compactNumericParsePayload_eq_some_with_exact_tag_cases
      payload parsed hparse with
    ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
      htransition, htag⟩
  exact ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
    htransition, htag⟩

#print axioms compactNumericParsePayload_eq_some_with_exact_tag_cases
#print axioms compactNumericParsePayload_eq_some_with_grouped_tag_cases

end FoundationCompactNumericListedDirectVerifierParseSuccessBranchCases
