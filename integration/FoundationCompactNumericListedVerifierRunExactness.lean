import integration.FoundationCompactNumericListedTaskMachine

/-!
# Exact final state of an accepted canonical verifier run
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedTaskMachine

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactListedProofDecoder
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedCertificateVerifier

theorem compactNumericVerifierRun_canonical_of_valid
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate) :
    compactNumericVerifierRun
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) =
      (compactNumericTreeFinalPayload tree certificate, some true) := by
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = true := by
    cases hshapeValue :
        compactNumericTreeCertificateShapeMatches tree certificate with
    | false =>
        have hfalse :=
          listedCertificateValidTrace_result_false_of_shape_mismatch
            tree certificate hshapeValue
        rw [htrace] at hfalse
        contradiction
    | true => rfl
  have htask := compactNumericTreeTask_execute_of_shape tree certificate
    [] [] [] [] hshape
  have htask' :
      (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps tree certificate])
        (compactNumericVerifierInitialState
          (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate)) =
      compactNumericTreeTaskSuccessState tree certificate [] [] [] [] := by
    simpa [compactNumericVerifierInitialState] using htask
  have hfinish :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState tree certificate [] [] [] []) =
        (compactNumericTreeFinalPayload tree certificate,
          some (listedCertificateValidTrace tree certificate).1) := by
    simpa only [Function.iterate_one] using
      compactNumericVerifierStep_finish_canonical tree certificate
  have hused := compactNumericVerifier_iterate_trans htask' hfinish
  have hfuel := compactNumericTreeTaskSteps_add_one_le_fuel tree certificate
  obtain ⟨extra, hfuelEq⟩ := exists_add_of_le hfuel
  have hrun :
      (compactNumericVerifierStep^[
        compactNumericVerifierFuelBound
          (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate)])
        (compactNumericVerifierInitialState
          (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate)) =
      (compactNumericTreeFinalPayload tree certificate,
        some (listedCertificateValidTrace tree certificate).1) := by
    rw [hfuelEq]
    exact compactNumericVerifier_iterate_trans hused
      (compactNumericVerifierStep_iterate_halted extra
        (compactNumericTreeFinalPayload tree certificate)
        (listedCertificateValidTrace tree certificate).1)
  unfold compactNumericVerifierRun
  simpa only [htrace] using hrun

#print axioms compactNumericVerifierRun_canonical_of_valid

end FoundationCompactNumericListedTaskMachine
