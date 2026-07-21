import integration.FoundationCompactNumericListedTaskMachine

/-!
# Exact canonical combine transitions and verifier steps

Each canonical non-leaf rule exposes both the underlying combine-state
transition and the enclosing public verifier step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCanonicalCombineExactSteps

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine

theorem compactNumericVerifierCanonicalAnd_combine_transition
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.and Gamma leftFormula rightFormula left right) proofSuffix).2
    let leftResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues left.conclusionList,
        (listedCertificateValidTrace left leftCertificate).1)
    let task := compactNumericCombineTask 3 fields
    let payload : CompactNumericRunningPayload :=
      ((proofSuffix, certificateSuffix),
        (restTasks,
          (arithmeticPropositionTokenValues right.conclusionList,
            (listedCertificateValidTrace right rightCertificate).1) ::
          leftResult :: values))
    let targetState : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate)
        proofSuffix certificateSuffix restTasks values
    compactNumericCombineState task payload = targetState := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericCombineTask, compactNumericCombineState,
    compactNumericCombineTransition,
    compactListedProofNodeExpectedFields]
  constructor
  · rfl
  · exact compactAndRuleCheck_canonical Gamma leftFormula rightFormula
      left right leftCertificate rightCertificate

theorem compactNumericVerifierCanonicalAnd_combine_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.and Gamma leftFormula rightFormula left right) proofSuffix).2
    let leftResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues left.conclusionList,
        (listedCertificateValidTrace left leftCertificate).1)
    let beforeCombine : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState right rightCertificate
        proofSuffix certificateSuffix
        (compactNumericCombineTask 3 fields :: restTasks)
        (leftResult :: values)
    compactNumericVerifierStep beforeCombine =
      compactNumericTreeTaskSuccessState
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate)
        proofSuffix certificateSuffix restTasks values := by
  simpa [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericTreeTaskSuccessState, compactNumericCombineTask] using
    compactNumericVerifierCanonicalAnd_combine_transition Gamma
      leftFormula rightFormula left right leftCertificate rightCertificate
      proofSuffix certificateSuffix restTasks values

theorem compactNumericVerifierCanonicalOr_combine_transition
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.or Gamma leftFormula rightFormula premise) proofSuffix).2
    let task := compactNumericCombineTask 4 fields
    let payload : CompactNumericRunningPayload :=
      ((proofSuffix, certificateSuffix),
        (restTasks,
          (arithmeticPropositionTokenValues premise.conclusionList,
            (listedCertificateValidTrace premise premiseCertificate).1) ::
          values))
    let targetState : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState
        (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values
    compactNumericCombineState task payload = targetState := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericCombineTask, compactNumericCombineState,
    compactNumericCombineTransition,
    compactListedProofNodeExpectedFields]
  constructor
  · rfl
  · exact compactOrRuleCheck_canonical Gamma leftFormula rightFormula
      premise premiseCertificate

theorem compactNumericVerifierCanonicalOr_combine_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.or Gamma leftFormula rightFormula premise) proofSuffix).2
    let beforeCombine : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState premise premiseCertificate
        proofSuffix certificateSuffix
        (compactNumericCombineTask 4 fields :: restTasks) values
    compactNumericVerifierStep beforeCombine =
      compactNumericTreeTaskSuccessState
        (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  simpa [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericTreeTaskSuccessState, compactNumericCombineTask] using
    compactNumericVerifierCanonicalOr_combine_transition Gamma
      leftFormula rightFormula premise premiseCertificate proofSuffix
      certificateSuffix restTasks values

theorem compactNumericVerifierCanonicalAll_combine_transition
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.all Gamma formula premise) proofSuffix).2
    let task := compactNumericCombineTask 5 fields
    let payload : CompactNumericRunningPayload :=
      ((proofSuffix, certificateSuffix),
        (restTasks,
          (arithmeticPropositionTokenValues premise.conclusionList,
            (listedCertificateValidTrace premise premiseCertificate).1) ::
          values))
    let targetState : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState (.all Gamma formula premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values
    compactNumericCombineState task payload = targetState := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericCombineTask, compactNumericCombineState,
    compactNumericCombineTransition,
    compactListedProofNodeExpectedFields]
  constructor
  · rfl
  · exact compactAllRuleCheck_canonical Gamma formula premise
      premiseCertificate

theorem compactNumericVerifierCanonicalAll_combine_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.all Gamma formula premise) proofSuffix).2
    let beforeCombine : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState premise premiseCertificate
        proofSuffix certificateSuffix
        (compactNumericCombineTask 5 fields :: restTasks) values
    compactNumericVerifierStep beforeCombine =
      compactNumericTreeTaskSuccessState (.all Gamma formula premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  simpa [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericTreeTaskSuccessState, compactNumericCombineTask] using
    compactNumericVerifierCanonicalAll_combine_transition Gamma formula
      premise premiseCertificate proofSuffix certificateSuffix restTasks values

theorem compactNumericVerifierCanonicalExs_combine_transition
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.exs Gamma formula witness premise) proofSuffix).2
    let task := compactNumericCombineTask 6 fields
    let payload : CompactNumericRunningPayload :=
      ((proofSuffix, certificateSuffix),
        (restTasks,
          (arithmeticPropositionTokenValues premise.conclusionList,
            (listedCertificateValidTrace premise premiseCertificate).1) ::
          values))
    let targetState : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState
        (.exs Gamma formula witness premise) (.unary premiseCertificate)
        proofSuffix certificateSuffix restTasks values
    compactNumericCombineState task payload = targetState := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericCombineTask, compactNumericCombineState,
    compactNumericCombineTransition,
    compactListedProofNodeExpectedFields]
  constructor
  · rfl
  · exact compactExsRuleCheck_canonical Gamma formula witness premise
      premiseCertificate

theorem compactNumericVerifierCanonicalExs_combine_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.exs Gamma formula witness premise) proofSuffix).2
    let beforeCombine : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState premise premiseCertificate
        proofSuffix certificateSuffix
        (compactNumericCombineTask 6 fields :: restTasks) values
    compactNumericVerifierStep beforeCombine =
      compactNumericTreeTaskSuccessState
        (.exs Gamma formula witness premise) (.unary premiseCertificate)
        proofSuffix certificateSuffix restTasks values := by
  simpa [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericTreeTaskSuccessState, compactNumericCombineTask] using
    compactNumericVerifierCanonicalExs_combine_transition Gamma formula
      witness premise premiseCertificate proofSuffix certificateSuffix
      restTasks values

theorem compactNumericVerifierCanonicalWk_combine_transition
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.wk Gamma premise) proofSuffix).2
    let task := compactNumericCombineTask 7 fields
    let payload : CompactNumericRunningPayload :=
      ((proofSuffix, certificateSuffix),
        (restTasks,
          (arithmeticPropositionTokenValues premise.conclusionList,
            (listedCertificateValidTrace premise premiseCertificate).1) ::
          values))
    let targetState : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState (.wk Gamma premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values
    compactNumericCombineState task payload = targetState := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericCombineTask, compactNumericCombineState,
    compactNumericCombineTransition,
    compactListedProofNodeExpectedFields]
  constructor
  · rfl
  · exact compactWkRuleCheck_canonical Gamma premise premiseCertificate

theorem compactNumericVerifierCanonicalWk_combine_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.wk Gamma premise) proofSuffix).2
    let beforeCombine : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState premise premiseCertificate
        proofSuffix certificateSuffix
        (compactNumericCombineTask 7 fields :: restTasks) values
    compactNumericVerifierStep beforeCombine =
      compactNumericTreeTaskSuccessState (.wk Gamma premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  simpa [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericTreeTaskSuccessState, compactNumericCombineTask] using
    compactNumericVerifierCanonicalWk_combine_transition Gamma premise
      premiseCertificate proofSuffix certificateSuffix restTasks values

theorem compactNumericVerifierCanonicalShift_combine_transition
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.shift Gamma premise) proofSuffix).2
    let task := compactNumericCombineTask 8 fields
    let payload : CompactNumericRunningPayload :=
      ((proofSuffix, certificateSuffix),
        (restTasks,
          (arithmeticPropositionTokenValues premise.conclusionList,
            (listedCertificateValidTrace premise premiseCertificate).1) ::
          values))
    let targetState : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState (.shift Gamma premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values
    compactNumericCombineState task payload = targetState := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericCombineTask, compactNumericCombineState,
    compactNumericCombineTransition,
    compactListedProofNodeExpectedFields]
  constructor
  · rfl
  · exact compactShiftRuleCheck_canonical Gamma premise
      premiseCertificate

theorem compactNumericVerifierCanonicalShift_combine_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.shift Gamma premise) proofSuffix).2
    let beforeCombine : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState premise premiseCertificate
        proofSuffix certificateSuffix
        (compactNumericCombineTask 8 fields :: restTasks) values
    compactNumericVerifierStep beforeCombine =
      compactNumericTreeTaskSuccessState (.shift Gamma premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  simpa [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericTreeTaskSuccessState, compactNumericCombineTask] using
    compactNumericVerifierCanonicalShift_combine_transition Gamma premise
      premiseCertificate proofSuffix certificateSuffix restTasks values

theorem compactNumericVerifierCanonicalCut_combine_transition
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.cut Gamma formula left right) proofSuffix).2
    let leftResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues left.conclusionList,
        (listedCertificateValidTrace left leftCertificate).1)
    let task := compactNumericCombineTask 9 fields
    let payload : CompactNumericRunningPayload :=
      ((proofSuffix, certificateSuffix),
        (restTasks,
          (arithmeticPropositionTokenValues right.conclusionList,
            (listedCertificateValidTrace right rightCertificate).1) ::
          leftResult :: values))
    let targetState : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate)
        proofSuffix certificateSuffix restTasks values
    compactNumericCombineState task payload = targetState := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericCombineTask, compactNumericCombineState,
    compactNumericCombineTransition,
    compactListedProofNodeExpectedFields]
  constructor
  · rfl
  · exact compactCutRuleCheck_canonical Gamma formula left right
      leftCertificate rightCertificate

theorem compactNumericVerifierCanonicalCut_combine_step
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    let fields := (compactListedProofNodeExpectedFields
      (.cut Gamma formula left right) proofSuffix).2
    let leftResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues left.conclusionList,
        (listedCertificateValidTrace left leftCertificate).1)
    let beforeCombine : CompactNumericVerifierState :=
      compactNumericTreeTaskSuccessState right rightCertificate
        proofSuffix certificateSuffix
        (compactNumericCombineTask 9 fields :: restTasks)
        (leftResult :: values)
    compactNumericVerifierStep beforeCombine =
      compactNumericTreeTaskSuccessState (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate)
        proofSuffix certificateSuffix restTasks values := by
  simpa [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericTreeTaskSuccessState, compactNumericCombineTask] using
    compactNumericVerifierCanonicalCut_combine_transition Gamma formula
      left right leftCertificate rightCertificate proofSuffix
      certificateSuffix restTasks values

#print axioms compactNumericVerifierCanonicalAnd_combine_transition
#print axioms compactNumericVerifierCanonicalOr_combine_transition
#print axioms compactNumericVerifierCanonicalAll_combine_transition
#print axioms compactNumericVerifierCanonicalExs_combine_transition
#print axioms compactNumericVerifierCanonicalWk_combine_transition
#print axioms compactNumericVerifierCanonicalShift_combine_transition
#print axioms compactNumericVerifierCanonicalCut_combine_transition

#print axioms compactNumericVerifierCanonicalAnd_combine_step
#print axioms compactNumericVerifierCanonicalOr_combine_step
#print axioms compactNumericVerifierCanonicalAll_combine_step
#print axioms compactNumericVerifierCanonicalExs_combine_step
#print axioms compactNumericVerifierCanonicalWk_combine_step
#print axioms compactNumericVerifierCanonicalShift_combine_step
#print axioms compactNumericVerifierCanonicalCut_combine_step

end FoundationCompactNumericListedDirectVerifierCanonicalCombineExactSteps
