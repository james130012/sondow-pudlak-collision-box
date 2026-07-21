import integration.FoundationCompactNumericListedDirectVerifierCanonicalNonLeafRowsGlobalBound

/-!
# Exact canonical root steps for non-leaf nodes

Each theorem identifies the public verifier step from a canonical non-leaf
root state with the corresponding scheduled child start state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCanonicalNonLeafExactSteps

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine

theorem compactNumericVerifierCanonicalAnd_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let tree : ListedCheckedPAProofTree :=
      .and Gamma leftFormula rightFormula left right
    let structuralCertificate : StructuralValidityCertificate :=
      .binary leftCertificate rightCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let scheduledChildStart : CompactNumericVerifierState :=
      (((compactListedProofTokens left ++ compactListedProofTokens right ++
            proofSuffix,
          compactStructuralCertificateTokens leftCertificate ++
            compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask 3 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStep currentState = scheduledChildStart := by
  simp [compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition, List.append_assoc]

theorem compactNumericVerifierCanonicalOr_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let tree : ListedCheckedPAProofTree :=
      .or Gamma leftFormula rightFormula premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let scheduledChildStart : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 4 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStep currentState = scheduledChildStart := by
  simp [compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition]

theorem compactNumericVerifierCanonicalAll_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let tree : ListedCheckedPAProofTree := .all Gamma formula premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let scheduledChildStart : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 5 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStep currentState = scheduledChildStart := by
  simp [compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition]

theorem compactNumericVerifierCanonicalExs_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let tree : ListedCheckedPAProofTree :=
      .exs Gamma formula witness premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let scheduledChildStart : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 6 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStep currentState = scheduledChildStart := by
  simp [compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition]

theorem compactNumericVerifierCanonicalWk_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let tree : ListedCheckedPAProofTree := .wk Gamma premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let scheduledChildStart : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 7 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStep currentState = scheduledChildStart := by
  simp [compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition]

theorem compactNumericVerifierCanonicalShift_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let tree : ListedCheckedPAProofTree := .shift Gamma premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let scheduledChildStart : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 8 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStep currentState = scheduledChildStart := by
  simp [compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition]

theorem compactNumericVerifierCanonicalCut_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let tree : ListedCheckedPAProofTree := .cut Gamma formula left right
    let structuralCertificate : StructuralValidityCertificate :=
      .binary leftCertificate rightCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let scheduledChildStart : CompactNumericVerifierState :=
      (((compactListedProofTokens left ++ compactListedProofTokens right ++
            proofSuffix,
          compactStructuralCertificateTokens leftCertificate ++
            compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask 9 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStep currentState = scheduledChildStart := by
  simp [compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition, List.append_assoc]

#print axioms compactNumericVerifierCanonicalAnd_step
#print axioms compactNumericVerifierCanonicalOr_step
#print axioms compactNumericVerifierCanonicalAll_step
#print axioms compactNumericVerifierCanonicalExs_step
#print axioms compactNumericVerifierCanonicalWk_step
#print axioms compactNumericVerifierCanonicalShift_step
#print axioms compactNumericVerifierCanonicalCut_step

end FoundationCompactNumericListedDirectVerifierCanonicalNonLeafExactSteps
