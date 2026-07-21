import integration.FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierTypedNonLeafStepPublicBounds

/-!
# Numeric state-table controls for typed non-leaf rows

The successful non-leaf parser row uses the exact canonical state-pair table.
This module retains its numeric table-loop controls for every real transition
output case.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedNonLeafStateTableControlBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierTypedNonLeafStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds

set_option maxRecDepth 4000 in
set_option maxHeartbeats 9000000 in
theorem
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_controlBounds
    (proofTokens certificateTokens nextProofTokens nextCertificateTokens : List Nat)
    (restTasks nextTasks : List CompactNumericVerifierTask)
    (values nextValues : List CompactNumericChildResult)
    (proofNode : CompactNumericVerifierTask)
    (certificateNode : CompactNumericCertificateNode)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
    (houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, nextValues)))
    {rowWeight : Nat} :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    let coordinateBound :=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        width tokens.length blockBound
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          (forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) /\
          CompactNumericVerifierParseSuccessParserControlBounds
            row.environment blockBound := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierNonLeafStepFormulaWitness_of_outputCase_with_sourcePublicBounds
        proofTokens certificateTokens nextProofTokens nextCertificateTokens
          restTasks nextTasks values nextValues proofNode certificateNode
          hproofParser hcertificateParser hproofTag houtputCase with
    ⟨witness, hwitness, hparserControls⟩
  exact
    exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls_and_property
      _ _ rowWeight _
      (fun environment =>
        CompactNumericVerifierParseSuccessParserControlBounds environment _)
      (by simpa only [compactNumericVerifierStateWeight] using hcurrent)
      (by simpa only [compactNumericVerifierStateWeight] using hnext)
      witness hwitness hparserControls

#print axioms
  exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_controlBounds

end FoundationCompactNumericListedDirectVerifierTypedNonLeafStateTableControlBounds
