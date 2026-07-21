import integration.FoundationCompactNumericListedDirectVerifierAcceptedUnaryTaskRowsStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedBinaryTaskRowsStateTableControlBounds

/-!
# Structural closure of bounded rows for every accepted tree-task step

This is the single induction which exhausts all ten listed proof-tree
constructors and installs a globally bounded checked row at every real task
offset.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsStateTableControlBounds

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierCheckedRowExecutionSplicing
open FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierCanonicalNonLeafExactSteps
open FoundationCompactNumericListedDirectVerifierAcceptedUnaryTaskRowsStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedBinaryTaskRowsStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
open FoundationCompactNumericListedPAAxiomLeafOccurrence

private theorem childWeights_of_prefix
    {parentStart childStart : CompactNumericVerifierState}
    {prefixSteps childSteps totalSteps rowWeight : Nat}
    (hprefix :
      (compactNumericVerifierStep^[prefixSteps]) parentStart = childStart)
    (hparent : forall offset, offset <= totalSteps ->
      compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt parentStart offset) <= rowWeight)
    (hfit : prefixSteps + childSteps <= totalSteps) :
    forall offset, offset <= childSteps ->
      compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt childStart offset) <= rowWeight := by
  intro offset hoffset
  exact compactNumericVerifierStateAt_weight_le_of_prefix hprefix hparent
    (by omega)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierAcceptedTreeTaskCheckedStepRow_with_control
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid tree certificate)
    {rowWeight offset : Nat}
    (hweights : forall taskOffset,
      taskOffset <= compactNumericTreeTaskSteps tree certificate ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState tree certificate proofSuffix
              certificateSuffix restTasks values) taskOffset) <= rowWeight)
    (hoffset : offset < compactNumericTreeTaskSteps tree certificate) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState tree certificate proofSuffix
          certificateSuffix restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState tree certificate proofSuffix
          certificateSuffix restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  induction tree generalizing certificate proofSuffix certificateSuffix
      restTasks values offset with
  | closed Gamma formula =>
      cases certificate with
      | leaf =>
          have hoffsetZero : offset = 0 := by
            simp only [compactNumericTreeTaskSteps] at hoffset
            omega
          subst offset
          exact exists_compactNumericVerifierAcceptedClosedLeafRow_at_zero_with_control
            Gamma formula proofSuffix certificateSuffix restTasks values
            hvalid hweights
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          simp [listedCertificateValid] at hvalid
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | axm Gamma sentence =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          have hoffsetZero : offset = 0 := by
            simp only [compactNumericTreeTaskSteps] at hoffset
            omega
          subst offset
          exact
            exists_compactNumericVerifierAcceptedPAAxiomLeafRow_at_zero_with_control
              Gamma sentence paCertificate proofSuffix certificateSuffix
              restTasks values hvalid hweights
      | unary premiseCertificate =>
          simp [listedCertificateValid] at hvalid
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | verum Gamma =>
      cases certificate with
      | leaf =>
          have hoffsetZero : offset = 0 := by
            simp only [compactNumericTreeTaskSteps] at hoffset
            omega
          subst offset
          exact exists_compactNumericVerifierAcceptedVerumLeafRow_at_zero_with_control
            Gamma proofSuffix certificateSuffix restTasks values hvalid
            hweights
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          simp [listedCertificateValid] at hvalid
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          simp [listedCertificateValid] at hvalid
      | binary leftCertificate rightCertificate =>
          let tree : ListedCheckedPAProofTree :=
            .and Gamma leftFormula rightFormula left right
          let certificate : StructuralValidityCertificate :=
            .binary leftCertificate rightCertificate
          let fields :=
            (compactListedProofNodeExpectedFields tree proofSuffix).2
          let combineTask := compactNumericCombineTask 3 fields
          let parentStart := compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values
          let leftStart := compactNumericTreeTaskStartState left
            leftCertificate (compactListedProofTokens right ++ proofSuffix)
            (compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix)
            (compactNumericParseTask :: combineTask :: restTasks) values
          let leftResult : CompactNumericChildResult :=
            (arithmeticPropositionTokenValues left.conclusionList,
              (listedCertificateValidTrace left leftCertificate).1)
          let rightStart := compactNumericTreeTaskStartState right
            rightCertificate proofSuffix certificateSuffix
            (combineTask :: restTasks) (leftResult :: values)
          have hleftValid :
              listedCertificateValid left leftCertificate :=
            hvalid.2.2.2.1
          have hrightValid :
              listedCertificateValid right rightCertificate :=
            hvalid.2.2.2.2
          have hrootStep :
              compactNumericVerifierStep parentStart = leftStart := by
            simpa [parentStart, leftStart, tree, certificate, fields,
              combineTask, compactNumericTreeTaskStartState,
              List.append_assoc] using
              compactNumericVerifierCanonicalAnd_step Gamma leftFormula
                rightFormula left right leftCertificate rightCertificate
                proofSuffix certificateSuffix restTasks values
          have hrootPrefix :
              (compactNumericVerifierStep^[1]) parentStart = leftStart := by
            simpa only [Function.iterate_one] using hrootStep
          have hleftWeights : forall childOffset,
              childOffset <=
                  compactNumericTreeTaskSteps left leftCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt leftStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrootPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hleftShape :=
            compactNumericTreeCertificateShapeMatches_eq_true_of_valid
              left leftCertificate hleftValid
          have hleftRun := compactNumericTreeTask_execute_of_shape left
            leftCertificate (compactListedProofTokens right ++ proofSuffix)
            (compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix)
            (compactNumericParseTask :: combineTask :: restTasks) values
            hleftShape
          have hleftExecute :
              (compactNumericVerifierStep^[
                compactNumericTreeTaskSteps left leftCertificate])
                  leftStart = rightStart := by
            simpa [leftStart, rightStart, leftResult,
              compactNumericTreeTaskStartState,
              compactNumericTreeTaskSuccessState] using hleftRun
          have hrightPrefix := compactNumericVerifier_iterate_trans
            hrootPrefix hleftExecute
          have hrightWeights : forall childOffset,
              childOffset <=
                  compactNumericTreeTaskSteps right rightCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt rightStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrightPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hleftRows : forall childOffset,
              childOffset <
                  compactNumericTreeTaskSteps left leftCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt leftStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt leftStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ihLeft leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask :: combineTask :: restTasks) values
              hleftValid hleftWeights hchildOffset
          have hrightRows : forall childOffset,
              childOffset <
                  compactNumericTreeTaskSteps right rightCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt rightStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt rightStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ihRight rightCertificate proofSuffix certificateSuffix
              (combineTask :: restTasks) (leftResult :: values) hrightValid
              hrightWeights hchildOffset
          exact exists_compactNumericVerifierAcceptedAndTaskRow_at_offset_with_control
            Gamma leftFormula rightFormula left right leftCertificate
            rightCertificate proofSuffix certificateSuffix restTasks values
            hvalid hweights (by simpa [tree, fields, combineTask] using
              hleftRows) (by simpa [tree, fields, combineTask, leftResult]
              using hrightRows) hoffset
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          let tree : ListedCheckedPAProofTree :=
            .or Gamma leftFormula rightFormula premise
          let certificate : StructuralValidityCertificate :=
            .unary premiseCertificate
          let fields :=
            (compactListedProofNodeExpectedFields tree proofSuffix).2
          let parentStart := compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values
          let childStart := compactNumericTreeTaskStartState premise
            premiseCertificate proofSuffix certificateSuffix
            (compactNumericCombineTask 4 fields :: restTasks) values
          have hchildValid :
              listedCertificateValid premise premiseCertificate :=
            hvalid.2.2
          have hrootStep :
              compactNumericVerifierStep parentStart = childStart := by
            simpa [parentStart, childStart, tree, certificate, fields,
              compactNumericTreeTaskStartState] using
              compactNumericVerifierCanonicalOr_step Gamma leftFormula
                rightFormula premise premiseCertificate proofSuffix
                certificateSuffix restTasks values
          have hrootPrefix :
              (compactNumericVerifierStep^[1]) parentStart = childStart := by
            simpa only [Function.iterate_one] using hrootStep
          have hchildWeights : forall childOffset,
              childOffset <= compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt childStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrootPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hchildRows : forall childOffset,
              childOffset < compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt childStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt childStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ih premiseCertificate proofSuffix certificateSuffix
              (compactNumericCombineTask 4 fields :: restTasks) values
              hchildValid hchildWeights hchildOffset
          exact exists_compactNumericVerifierAcceptedOrTaskRow_at_offset_with_control
            Gamma leftFormula rightFormula premise premiseCertificate
            proofSuffix certificateSuffix restTasks values hvalid hweights
            (by simpa [tree, fields, childStart] using hchildRows) hoffset
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | all Gamma formula premise ih =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          let tree : ListedCheckedPAProofTree := .all Gamma formula premise
          let certificate : StructuralValidityCertificate :=
            .unary premiseCertificate
          let fields :=
            (compactListedProofNodeExpectedFields tree proofSuffix).2
          let parentStart := compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values
          let childStart := compactNumericTreeTaskStartState premise
            premiseCertificate proofSuffix certificateSuffix
            (compactNumericCombineTask 5 fields :: restTasks) values
          have hchildValid :
              listedCertificateValid premise premiseCertificate :=
            hvalid.2.2
          have hrootStep :
              compactNumericVerifierStep parentStart = childStart := by
            simpa [parentStart, childStart, tree, certificate, fields,
              compactNumericTreeTaskStartState] using
              compactNumericVerifierCanonicalAll_step Gamma formula premise
                premiseCertificate proofSuffix certificateSuffix restTasks
                values
          have hrootPrefix :
              (compactNumericVerifierStep^[1]) parentStart = childStart := by
            simpa only [Function.iterate_one] using hrootStep
          have hchildWeights : forall childOffset,
              childOffset <= compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt childStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrootPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hchildRows : forall childOffset,
              childOffset < compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt childStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt childStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ih premiseCertificate proofSuffix certificateSuffix
              (compactNumericCombineTask 5 fields :: restTasks) values
              hchildValid hchildWeights hchildOffset
          exact exists_compactNumericVerifierAcceptedAllTaskRow_at_offset_with_control
            Gamma formula premise premiseCertificate proofSuffix
            certificateSuffix restTasks values hvalid hweights
            (by simpa [tree, fields, childStart] using hchildRows) hoffset
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          let tree : ListedCheckedPAProofTree :=
            .exs Gamma formula witness premise
          let certificate : StructuralValidityCertificate :=
            .unary premiseCertificate
          let fields :=
            (compactListedProofNodeExpectedFields tree proofSuffix).2
          let parentStart := compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values
          let childStart := compactNumericTreeTaskStartState premise
            premiseCertificate proofSuffix certificateSuffix
            (compactNumericCombineTask 6 fields :: restTasks) values
          have hchildValid :
              listedCertificateValid premise premiseCertificate :=
            hvalid.2.2
          have hrootStep :
              compactNumericVerifierStep parentStart = childStart := by
            simpa [parentStart, childStart, tree, certificate, fields,
              compactNumericTreeTaskStartState] using
              compactNumericVerifierCanonicalExs_step Gamma formula witness
                premise premiseCertificate proofSuffix certificateSuffix
                restTasks values
          have hrootPrefix :
              (compactNumericVerifierStep^[1]) parentStart = childStart := by
            simpa only [Function.iterate_one] using hrootStep
          have hchildWeights : forall childOffset,
              childOffset <= compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt childStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrootPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hchildRows : forall childOffset,
              childOffset < compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt childStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt childStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ih premiseCertificate proofSuffix certificateSuffix
              (compactNumericCombineTask 6 fields :: restTasks) values
              hchildValid hchildWeights hchildOffset
          exact exists_compactNumericVerifierAcceptedExsTaskRow_at_offset_with_control
            Gamma formula witness premise premiseCertificate proofSuffix
            certificateSuffix restTasks values hvalid hweights
            (by simpa [tree, fields, childStart] using hchildRows) hoffset
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | wk Gamma premise ih =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          let tree : ListedCheckedPAProofTree := .wk Gamma premise
          let certificate : StructuralValidityCertificate :=
            .unary premiseCertificate
          let fields :=
            (compactListedProofNodeExpectedFields tree proofSuffix).2
          let parentStart := compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values
          let childStart := compactNumericTreeTaskStartState premise
            premiseCertificate proofSuffix certificateSuffix
            (compactNumericCombineTask 7 fields :: restTasks) values
          have hchildValid :
              listedCertificateValid premise premiseCertificate := hvalid.2
          have hrootStep :
              compactNumericVerifierStep parentStart = childStart := by
            simpa [parentStart, childStart, tree, certificate, fields,
              compactNumericTreeTaskStartState] using
              compactNumericVerifierCanonicalWk_step Gamma premise
                premiseCertificate proofSuffix certificateSuffix restTasks
                values
          have hrootPrefix :
              (compactNumericVerifierStep^[1]) parentStart = childStart := by
            simpa only [Function.iterate_one] using hrootStep
          have hchildWeights : forall childOffset,
              childOffset <= compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt childStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrootPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hchildRows : forall childOffset,
              childOffset < compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt childStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt childStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ih premiseCertificate proofSuffix certificateSuffix
              (compactNumericCombineTask 7 fields :: restTasks) values
              hchildValid hchildWeights hchildOffset
          exact exists_compactNumericVerifierAcceptedWkTaskRow_at_offset_with_control
            Gamma premise premiseCertificate proofSuffix certificateSuffix
            restTasks values hvalid hweights
            (by simpa [tree, fields, childStart] using hchildRows) hoffset
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | shift Gamma premise ih =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          let tree : ListedCheckedPAProofTree := .shift Gamma premise
          let certificate : StructuralValidityCertificate :=
            .unary premiseCertificate
          let fields :=
            (compactListedProofNodeExpectedFields tree proofSuffix).2
          let parentStart := compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values
          let childStart := compactNumericTreeTaskStartState premise
            premiseCertificate proofSuffix certificateSuffix
            (compactNumericCombineTask 8 fields :: restTasks) values
          have hchildValid :
              listedCertificateValid premise premiseCertificate := hvalid.2
          have hrootStep :
              compactNumericVerifierStep parentStart = childStart := by
            simpa [parentStart, childStart, tree, certificate, fields,
              compactNumericTreeTaskStartState] using
              compactNumericVerifierCanonicalShift_step Gamma premise
                premiseCertificate proofSuffix certificateSuffix restTasks
                values
          have hrootPrefix :
              (compactNumericVerifierStep^[1]) parentStart = childStart := by
            simpa only [Function.iterate_one] using hrootStep
          have hchildWeights : forall childOffset,
              childOffset <= compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt childStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrootPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hchildRows : forall childOffset,
              childOffset < compactNumericTreeTaskSteps premise
                  premiseCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt childStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt childStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ih premiseCertificate proofSuffix certificateSuffix
              (compactNumericCombineTask 8 fields :: restTasks) values
              hchildValid hchildWeights hchildOffset
          exact exists_compactNumericVerifierAcceptedShiftTaskRow_at_offset_with_control
            Gamma premise premiseCertificate proofSuffix certificateSuffix
            restTasks values hvalid hweights
            (by simpa [tree, fields, childStart] using hchildRows) hoffset
      | binary leftCertificate rightCertificate =>
          simp [listedCertificateValid] at hvalid
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simp [listedCertificateValid] at hvalid
      | axiomCert paCertificate =>
          simp [listedCertificateValid] at hvalid
      | unary premiseCertificate =>
          simp [listedCertificateValid] at hvalid
      | binary leftCertificate rightCertificate =>
          let tree : ListedCheckedPAProofTree :=
            .cut Gamma formula left right
          let certificate : StructuralValidityCertificate :=
            .binary leftCertificate rightCertificate
          let fields :=
            (compactListedProofNodeExpectedFields tree proofSuffix).2
          let combineTask := compactNumericCombineTask 9 fields
          let parentStart := compactNumericTreeTaskStartState tree certificate
            proofSuffix certificateSuffix restTasks values
          let leftStart := compactNumericTreeTaskStartState left
            leftCertificate (compactListedProofTokens right ++ proofSuffix)
            (compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix)
            (compactNumericParseTask :: combineTask :: restTasks) values
          let leftResult : CompactNumericChildResult :=
            (arithmeticPropositionTokenValues left.conclusionList,
              (listedCertificateValidTrace left leftCertificate).1)
          let rightStart := compactNumericTreeTaskStartState right
            rightCertificate proofSuffix certificateSuffix
            (combineTask :: restTasks) (leftResult :: values)
          have hleftValid :
              listedCertificateValid left leftCertificate :=
            hvalid.2.2.1
          have hrightValid :
              listedCertificateValid right rightCertificate :=
            hvalid.2.2.2
          have hrootStep :
              compactNumericVerifierStep parentStart = leftStart := by
            simpa [parentStart, leftStart, tree, certificate, fields,
              combineTask, compactNumericTreeTaskStartState,
              List.append_assoc] using
              compactNumericVerifierCanonicalCut_step Gamma formula left
                right leftCertificate rightCertificate proofSuffix
                certificateSuffix restTasks values
          have hrootPrefix :
              (compactNumericVerifierStep^[1]) parentStart = leftStart := by
            simpa only [Function.iterate_one] using hrootStep
          have hleftWeights : forall childOffset,
              childOffset <=
                  compactNumericTreeTaskSteps left leftCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt leftStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrootPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hleftShape :=
            compactNumericTreeCertificateShapeMatches_eq_true_of_valid
              left leftCertificate hleftValid
          have hleftRun := compactNumericTreeTask_execute_of_shape left
            leftCertificate (compactListedProofTokens right ++ proofSuffix)
            (compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix)
            (compactNumericParseTask :: combineTask :: restTasks) values
            hleftShape
          have hleftExecute :
              (compactNumericVerifierStep^[
                compactNumericTreeTaskSteps left leftCertificate])
                  leftStart = rightStart := by
            simpa [leftStart, rightStart, leftResult,
              compactNumericTreeTaskStartState,
              compactNumericTreeTaskSuccessState] using hleftRun
          have hrightPrefix := compactNumericVerifier_iterate_trans
            hrootPrefix hleftExecute
          have hrightWeights : forall childOffset,
              childOffset <=
                  compactNumericTreeTaskSteps right rightCertificate ->
                compactNumericVerifierStateWeight
                  (compactNumericVerifierStateAt rightStart childOffset) <=
                    rowWeight := by
            apply childWeights_of_prefix hrightPrefix hweights
            simp only [compactNumericTreeTaskSteps]
            omega
          have hleftRows : forall childOffset,
              childOffset <
                  compactNumericTreeTaskSteps left leftCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt leftStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt leftStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ihLeft leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask :: combineTask :: restTasks) values
              hleftValid hleftWeights hchildOffset
          have hrightRows : forall childOffset,
              childOffset <
                  compactNumericTreeTaskSteps right rightCertificate ->
                exists row : CompactNumericVerifierCheckedStepRow,
                  row.currentState = compactNumericVerifierStateAt rightStart
                    childOffset /\
                  row.nextState = compactNumericVerifierStateAt rightStart
                    (childOffset + 1) /\
                  CompactNumericVerifierAcceptedTreeControlledRowBound
                    rowWeight row := by
            intro childOffset hchildOffset
            exact ihRight rightCertificate proofSuffix certificateSuffix
              (combineTask :: restTasks) (leftResult :: values) hrightValid
              hrightWeights hchildOffset
          exact exists_compactNumericVerifierAcceptedCutTaskRow_at_offset_with_control Gamma
            formula left right leftCertificate rightCertificate proofSuffix
            certificateSuffix restTasks values hvalid hweights
            (by simpa [tree, fields, combineTask] using hleftRows)
            (by simpa [tree, fields, combineTask, leftResult] using
              hrightRows) hoffset

#print axioms childWeights_of_prefix
#print axioms
  exists_compactNumericVerifierAcceptedTreeTaskCheckedStepRow_with_control

end FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsStateTableControlBounds
