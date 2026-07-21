import integration.FoundationCompactNumericListedTaskMachine
import integration.FoundationCompactListedCertificateVerifier
import integration.FoundationCompactNumericListedRuleChecks
import integration.FoundationCompactNumericListedDirectTrace

/-!
# Exact PA-leaf offsets in the listed verifier execution

An occurrence records the machine-step offset of a PA axiom leaf relative to
the parse step of the enclosing proof tree.  The offsets follow the real
depth-first scheduler used by `compactNumericTreeTaskSteps`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedPAAxiomLeafOccurrence

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace

def compactNumericTreeTaskStartState
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    CompactNumericVerifierState :=
  (((compactListedProofTokens tree ++ proofSuffix,
      compactStructuralCertificateTokens certificate ++ certificateSuffix),
    (compactNumericParseTask :: restTasks, values)), none)

inductive ListedPAAxiomLeafAt :
    ListedCheckedPAProofTree -> StructuralValidityCertificate -> Nat ->
      List LO.FirstOrder.ArithmeticProposition ->
      LO.FirstOrder.ArithmeticSentence -> PAAxiomCertificate -> Prop
  | here (Gamma sentence paCertificate) :
      ListedPAAxiomLeafAt (.axm Gamma sentence) (.axiomCert paCertificate)
        0 Gamma sentence paCertificate
  | andLeft {Gamma leftFormula rightFormula left right
      leftCertificate rightCertificate offset leafGamma leafSentence
      leafCertificate}
      (occurrence : ListedPAAxiomLeafAt left leftCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate) (1 + offset)
        leafGamma leafSentence leafCertificate
  | andRight {Gamma leftFormula rightFormula left right
      leftCertificate rightCertificate offset leafGamma leafSentence
      leafCertificate}
      (occurrence : ListedPAAxiomLeafAt right rightCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate)
        (1 + compactNumericTreeTaskSteps left leftCertificate + offset)
        leafGamma leafSentence leafCertificate
  | orPremise {Gamma leftFormula rightFormula premise premiseCertificate
      offset leafGamma leafSentence leafCertificate}
      (occurrence : ListedPAAxiomLeafAt premise premiseCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate) (1 + offset)
        leafGamma leafSentence leafCertificate
  | allPremise {Gamma formula premise premiseCertificate offset leafGamma
      leafSentence leafCertificate}
      (occurrence : ListedPAAxiomLeafAt premise premiseCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt (.all Gamma formula premise)
        (.unary premiseCertificate) (1 + offset)
        leafGamma leafSentence leafCertificate
  | exsPremise {Gamma formula witness premise premiseCertificate offset
      leafGamma leafSentence leafCertificate}
      (occurrence : ListedPAAxiomLeafAt premise premiseCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt (.exs Gamma formula witness premise)
        (.unary premiseCertificate) (1 + offset)
        leafGamma leafSentence leafCertificate
  | wkPremise {Gamma premise premiseCertificate offset leafGamma leafSentence
      leafCertificate}
      (occurrence : ListedPAAxiomLeafAt premise premiseCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt (.wk Gamma premise) (.unary premiseCertificate)
        (1 + offset) leafGamma leafSentence leafCertificate
  | shiftPremise {Gamma premise premiseCertificate offset leafGamma
      leafSentence leafCertificate}
      (occurrence : ListedPAAxiomLeafAt premise premiseCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt (.shift Gamma premise) (.unary premiseCertificate)
        (1 + offset) leafGamma leafSentence leafCertificate
  | cutLeft {Gamma formula left right leftCertificate rightCertificate offset
      leafGamma leafSentence leafCertificate}
      (occurrence : ListedPAAxiomLeafAt left leftCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate) (1 + offset)
        leafGamma leafSentence leafCertificate
  | cutRight {Gamma formula left right leftCertificate rightCertificate offset
      leafGamma leafSentence leafCertificate}
      (occurrence : ListedPAAxiomLeafAt right rightCertificate offset
        leafGamma leafSentence leafCertificate) :
      ListedPAAxiomLeafAt (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate)
        (1 + compactNumericTreeTaskSteps left leftCertificate + offset)
        leafGamma leafSentence leafCertificate

theorem ListedPAAxiomLeafAt.localValid
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    {offset : Nat}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    {sentence : LO.FirstOrder.ArithmeticSentence}
    {paCertificate : PAAxiomCertificate}
    (occurrence : ListedPAAxiomLeafAt tree certificate offset
      Gamma sentence paCertificate)
    (hvalid : listedCertificateValid tree certificate) :
    listedCertificateValid (.axm Gamma sentence)
      (.axiomCert paCertificate) := by
  induction occurrence with
  | here => exact hvalid
  | andLeft occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2.2.2.1
  | andRight occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2.2.2.2
  | orPremise occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2.2
  | allPremise occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2.2
  | exsPremise occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2.2
  | wkPremise occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2
  | shiftPremise occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2
  | cutLeft occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2.2.1
  | cutRight occurrence inductionHypothesis =>
      exact inductionHypothesis hvalid.2.2.2

theorem ListedPAAxiomLeafAt.compactAxmRuleCheck_eq_true
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    {offset : Nat}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    {sentence : LO.FirstOrder.ArithmeticSentence}
    {paCertificate : PAAxiomCertificate}
    (occurrence : ListedPAAxiomLeafAt tree certificate offset
      Gamma sentence paCertificate)
    (hvalid : listedCertificateValid tree certificate) :
    compactAxmRuleCheck
      (arithmeticPropositionTokenValues Gamma,
        (compactSentenceTokens sentence,
          compactPAAxiomCertificateTokens paCertificate)) = true := by
  have hlocal := occurrence.localValid hvalid
  have htrace :
      (listedCertificateValidTrace (.axm Gamma sentence)
        (.axiomCert paCertificate)).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff
      (.axm Gamma sentence) (.axiomCert paCertificate)).2 hlocal
  exact (compactAxmRuleCheck_canonical Gamma sentence paCertificate).trans
    htrace

theorem ListedPAAxiomLeafAt.offset_lt_taskSteps
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    {offset : Nat}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    {sentence : LO.FirstOrder.ArithmeticSentence}
    {paCertificate : PAAxiomCertificate}
    (occurrence : ListedPAAxiomLeafAt tree certificate offset
      Gamma sentence paCertificate) :
    offset < compactNumericTreeTaskSteps tree certificate := by
  induction occurrence with
  | here => simp [compactNumericTreeTaskSteps]
  | andLeft occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | andRight occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | orPremise occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | allPremise occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | exsPremise occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | wkPremise occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | shiftPremise occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | cutLeft occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega
  | cutRight occurrence inductionHypothesis =>
      simp only [compactNumericTreeTaskSteps]
      omega

theorem compactNumericTreeCertificateShapeMatches_eq_true_of_valid
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate) :
    compactNumericTreeCertificateShapeMatches tree certificate = true := by
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  cases hshape : compactNumericTreeCertificateShapeMatches tree certificate with
  | false =>
      have hfalse :=
        listedCertificateValidTrace_result_false_of_shape_mismatch
          tree certificate hshape
      rw [htrace] at hfalse
      contradiction
  | true => rfl

theorem ListedPAAxiomLeafAt.exists_stateAt_eq_leafStart
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    {offset : Nat}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    {sentence : LO.FirstOrder.ArithmeticSentence}
    {paCertificate : PAAxiomCertificate}
    (occurrence : ListedPAAxiomLeafAt tree certificate offset
      Gamma sentence paCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    exists leafProofSuffix leafCertificateSuffix
        leafRestTasks leafValues,
      compactNumericVerifierStateAt
          (compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values) offset =
        compactNumericTreeTaskStartState (.axm Gamma sentence)
          (.axiomCert paCertificate) leafProofSuffix
          leafCertificateSuffix leafRestTasks leafValues := by
  induction occurrence generalizing proofSuffix certificateSuffix restTasks
      values with
  | here =>
      exact ⟨proofSuffix, certificateSuffix, restTasks, values, by
        simp [compactNumericVerifierStateAt]⟩
  | @andLeft rootGamma leftFormula rightFormula left right leftCertificate
      rightCertificate childOffset leafGamma leafSentence leafCertificate
      occurrence inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.and rootGamma leftFormula rightFormula left right) proofSuffix).2
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState
                (.and rootGamma leftFormula rightFormula left right)
                (.binary leftCertificate rightCertificate)
                proofSuffix certificateSuffix restTasks values) =
            compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 3 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
          List.append_assoc]
      rcases inductionHypothesis hvalid.2.2.2.1
          (compactListedProofTokens right ++ proofSuffix)
          (compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix)
          (compactNumericParseTask ::
            compactNumericCombineTask 3 fields :: restTasks) values with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans hnode hleaf
  | @andRight rootGamma leftFormula rightFormula left right leftCertificate
      rightCertificate childOffset leafGamma leafSentence leafCertificate
      occurrence inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.and rootGamma leftFormula rightFormula left right) proofSuffix).2
      let leftResult : CompactNumericChildResult :=
        (arithmeticPropositionTokenValues left.conclusionList,
          (listedCertificateValidTrace left leftCertificate).1)
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState
                (.and rootGamma leftFormula rightFormula left right)
                (.binary leftCertificate rightCertificate)
                proofSuffix certificateSuffix restTasks values) =
            compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 3 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
          List.append_assoc]
      have hleftShape :=
        compactNumericTreeCertificateShapeMatches_eq_true_of_valid
          left leftCertificate hvalid.2.2.2.1
      have hleftRaw := compactNumericTreeTask_execute_of_shape
        left leftCertificate
        (compactListedProofTokens right ++ proofSuffix)
        (compactStructuralCertificateTokens rightCertificate ++
          certificateSuffix)
        (compactNumericParseTask ::
          compactNumericCombineTask 3 fields :: restTasks) values hleftShape
      have hleft :
          (compactNumericVerifierStep^[
              compactNumericTreeTaskSteps left leftCertificate])
              (compactNumericTreeTaskStartState left leftCertificate
                (compactListedProofTokens right ++ proofSuffix)
                (compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix)
                (compactNumericParseTask ::
                  compactNumericCombineTask 3 fields :: restTasks) values) =
            compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 3 fields :: restTasks)
              (leftResult :: values) := by
        simpa [compactNumericTreeTaskStartState,
          compactNumericTreeTaskSuccessState, leftResult] using hleftRaw
      rcases inductionHypothesis hvalid.2.2.2.2 proofSuffix
          certificateSuffix (compactNumericCombineTask 3 fields :: restTasks)
          (leftResult :: values) with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans
        (compactNumericVerifier_iterate_trans hnode hleft) hleaf
  | @orPremise rootGamma leftFormula rightFormula premise premiseCertificate
      childOffset leafGamma leafSentence leafCertificate occurrence
      inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.or rootGamma leftFormula rightFormula premise) proofSuffix).2
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState
                (.or rootGamma leftFormula rightFormula premise)
                (.unary premiseCertificate) proofSuffix certificateSuffix
                restTasks values) =
            compactNumericTreeTaskStartState premise premiseCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 4 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
      rcases inductionHypothesis hvalid.2.2 proofSuffix certificateSuffix
          (compactNumericCombineTask 4 fields :: restTasks) values with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans hnode hleaf
  | @allPremise rootGamma formula premise premiseCertificate childOffset
      leafGamma leafSentence leafCertificate occurrence inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.all rootGamma formula premise) proofSuffix).2
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState
                (.all rootGamma formula premise)
                (.unary premiseCertificate) proofSuffix certificateSuffix
                restTasks values) =
            compactNumericTreeTaskStartState premise premiseCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 5 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
      rcases inductionHypothesis hvalid.2.2 proofSuffix certificateSuffix
          (compactNumericCombineTask 5 fields :: restTasks) values with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans hnode hleaf
  | @exsPremise rootGamma formula witness premise premiseCertificate
      childOffset leafGamma leafSentence leafCertificate occurrence
      inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.exs rootGamma formula witness premise) proofSuffix).2
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState
                (.exs rootGamma formula witness premise)
                (.unary premiseCertificate) proofSuffix certificateSuffix
                restTasks values) =
            compactNumericTreeTaskStartState premise premiseCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 6 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
      rcases inductionHypothesis hvalid.2.2 proofSuffix certificateSuffix
          (compactNumericCombineTask 6 fields :: restTasks) values with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans hnode hleaf
  | @wkPremise rootGamma premise premiseCertificate childOffset leafGamma
      leafSentence leafCertificate occurrence inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.wk rootGamma premise) proofSuffix).2
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState (.wk rootGamma premise)
                (.unary premiseCertificate) proofSuffix certificateSuffix
                restTasks values) =
            compactNumericTreeTaskStartState premise premiseCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 7 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
      rcases inductionHypothesis hvalid.2 proofSuffix certificateSuffix
          (compactNumericCombineTask 7 fields :: restTasks) values with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans hnode hleaf
  | @shiftPremise rootGamma premise premiseCertificate childOffset leafGamma
      leafSentence leafCertificate occurrence inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.shift rootGamma premise) proofSuffix).2
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState (.shift rootGamma premise)
                (.unary premiseCertificate) proofSuffix certificateSuffix
                restTasks values) =
            compactNumericTreeTaskStartState premise premiseCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 8 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
      rcases inductionHypothesis hvalid.2 proofSuffix certificateSuffix
          (compactNumericCombineTask 8 fields :: restTasks) values with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans hnode hleaf
  | @cutLeft rootGamma formula left right leftCertificate rightCertificate
      childOffset leafGamma leafSentence leafCertificate occurrence
      inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.cut rootGamma formula left right) proofSuffix).2
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState
                (.cut rootGamma formula left right)
                (.binary leftCertificate rightCertificate)
                proofSuffix certificateSuffix restTasks values) =
            compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 9 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
          List.append_assoc]
      rcases inductionHypothesis hvalid.2.2.1
          (compactListedProofTokens right ++ proofSuffix)
          (compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix)
          (compactNumericParseTask ::
            compactNumericCombineTask 9 fields :: restTasks) values with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans hnode hleaf
  | @cutRight rootGamma formula left right leftCertificate rightCertificate
      childOffset leafGamma leafSentence leafCertificate occurrence
      inductionHypothesis =>
      let fields := (compactListedProofNodeExpectedFields
        (.cut rootGamma formula left right) proofSuffix).2
      let leftResult : CompactNumericChildResult :=
        (arithmeticPropositionTokenValues left.conclusionList,
          (listedCertificateValidTrace left leftCertificate).1)
      have hnode :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskStartState
                (.cut rootGamma formula left right)
                (.binary leftCertificate rightCertificate)
                proofSuffix certificateSuffix restTasks values) =
            compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 9 fields :: restTasks) values := by
        simp [compactNumericTreeTaskStartState, Function.iterate_one, fields,
          compactListedProofNodeExpectedFields,
          compactStructuralCertificateNodeExpected,
          compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
          List.append_assoc]
      have hleftShape :=
        compactNumericTreeCertificateShapeMatches_eq_true_of_valid
          left leftCertificate hvalid.2.2.1
      have hleftRaw := compactNumericTreeTask_execute_of_shape
        left leftCertificate
        (compactListedProofTokens right ++ proofSuffix)
        (compactStructuralCertificateTokens rightCertificate ++
          certificateSuffix)
        (compactNumericParseTask ::
          compactNumericCombineTask 9 fields :: restTasks) values hleftShape
      have hleft :
          (compactNumericVerifierStep^[
              compactNumericTreeTaskSteps left leftCertificate])
              (compactNumericTreeTaskStartState left leftCertificate
                (compactListedProofTokens right ++ proofSuffix)
                (compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix)
                (compactNumericParseTask ::
                  compactNumericCombineTask 9 fields :: restTasks) values) =
            compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 9 fields :: restTasks)
              (leftResult :: values) := by
        simpa [compactNumericTreeTaskStartState,
          compactNumericTreeTaskSuccessState, leftResult] using hleftRaw
      rcases inductionHypothesis hvalid.2.2.2 proofSuffix certificateSuffix
          (compactNumericCombineTask 9 fields :: restTasks)
          (leftResult :: values) with
        ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks, leafValues,
          hleaf⟩
      refine ⟨leafProofSuffix, leafCertificateSuffix, leafRestTasks,
        leafValues, ?_⟩
      unfold compactNumericVerifierStateAt at hleaf ⊢
      exact compactNumericVerifier_iterate_trans
        (compactNumericVerifier_iterate_trans hnode hleft) hleaf

#print axioms ListedPAAxiomLeafAt.localValid
#print axioms ListedPAAxiomLeafAt.compactAxmRuleCheck_eq_true
#print axioms ListedPAAxiomLeafAt.offset_lt_taskSteps
#print axioms compactNumericTreeCertificateShapeMatches_eq_true_of_valid
#print axioms ListedPAAxiomLeafAt.exists_stateAt_eq_leafStart

end FoundationCompactNumericListedPAAxiomLeafOccurrence
