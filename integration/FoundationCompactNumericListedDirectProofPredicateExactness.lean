import integration.FoundationCompactNumericListedDirectProofPredicate
import integration.FoundationCompactNumericListedTaskMachineSyntaxInversion

/-!
# Semantic exactness data recovered from the direct proof predicate

This file opens an arbitrary direct witness.  It recovers the exact public
proof stream, the exact formula stream, and the deterministic accepted final
state from the same arithmetic tables.  The remaining public-checker bridge is
therefore only the synchronized parser inversion, not a trace or conclusion
identity assumption.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofPredicateExactness

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactAdditiveTokenCodec
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedTaskMachineSyntaxInversion
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectInputTableau
open FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit
open FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix
open FoundationCompactNumericListedDirectVerifierAcceptedConclusionRow
open FoundationCompactNumericListedDirectProofPredicate

def CompactNumericListedDirectSemanticAcceptance
    (bound formulaCode : Nat) : Prop :=
  exists proofCode : Nat,
    exists proofTokens certificateTokens formulaTokens : List Nat,
      packedPayloadLength proofCode <= bound /\
        proofCode =
          compactAdditivePackedCode (proofTokens ++ certificateTokens) /\
        formulaCode = compactAdditivePackedCode formulaTokens /\
        let finalState := compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          (compactNumericVerifierFuelBound proofTokens certificateTokens)
        finalState.2 = some true /\
          finalState.1.2.2.length = 1 /\
          (finalState.1.2.2.getI 0).1.toFinset = {formulaTokens}

/-- Every direct arithmetic witness recovers one deterministic accepted local
run whose final singleton conclusion is the formula stream encoded by the
same public formula code. -/
theorem directProofPredicate_recovers_semanticAcceptance
    {bound formulaCode : Nat}
    (hdirect : CompactListedPADirectProofPredicate bound formulaCode) :
    CompactNumericListedDirectSemanticAcceptance bound formulaCode := by
  rcases hdirect with
    ⟨proofCode,
      inputTokenCount, inputTable, inputOffsetTable, inputWidth,
      sourceTable, sourceWidth, sourceTokenCount,
      proofStart, proofFinish, certificateStart, certificateFinish, split,
      traceWidth, traceTable, traceValueBound,
      formulaTokenCount, formulaTable, formulaOffsetTable, formulaWidth,
      hinputWidth, hpayload, hformula, hconclusion⟩
  rcases hpayload with ⟨hinput, hsplit, htrace⟩
  let initialEnvironment :=
    compactNumericVerifierStepWitnessTableFormulaEnvironment
      traceWidth traceTable 0
  have htraceForInitial := htrace
  rcases htraceForInitial with
    ⟨_htraceValueBound, _hfuelPositive, _hbounded, _hadjacent,
      hinitial, _lastRow, _hlastRow, _hlastNext, _hfinal⟩
  have hinitialEnvironment : CompactNumericVerifierInitialEnvironment
      initialEnvironment
      sourceTable sourceWidth sourceTokenCount proofStart proofFinish
      sourceTable sourceWidth sourceTokenCount
        certificateStart certificateFinish := by
    simpa only [initialEnvironment] using hinitial.canonical_environment
  rcases acceptedTraceTable_rebase_initialLists htrace with
    ⟨proofTokens, certificateTokens,
      hproofLayout, hcertificateLayout, hselfTrace⟩
  have hdecoded := hsplit.decodedTokens_eq hinput
    hinitialEnvironment.1 hinitialEnvironment.2.1
    hproofLayout hcertificateLayout
  have hcode : proofCode =
      compactAdditivePackedCode (proofTokens ++ certificateTokens) := by
    calc
      proofCode = compactAdditivePackedCode
          (compactCanonicalPackedTokenStreamTableauAtWidthTokens
            inputTokenCount inputTable inputWidth) :=
        hinput.code_eq_canonical
      _ = compactAdditivePackedCode
          (proofTokens ++ certificateTokens) := by rw [hdecoded]
  have hinputLength : inputTokenCount =
      proofTokens.length + certificateTokens.length := by
    have hlengths := congrArg List.length hdecoded
    simpa using hlengths
  have hfuel : 4 * (inputTokenCount + 1) + 8 =
      compactNumericVerifierFuelBound proofTokens certificateTokens := by
    simp only [compactNumericVerifierFuelBound]
    omega

  let formulaTokens :=
    compactCanonicalPackedTokenStreamTableauAtWidthTokens
      formulaTokenCount formulaTable formulaWidth
  have hformulaCode :
      formulaCode = compactAdditivePackedCode formulaTokens := by
    exact hformula.code_eq_canonical
  have hformulaLength : formulaTokens.length = formulaTokenCount := by
    simp [formulaTokens,
      compactCanonicalPackedTokenStreamTableauAtWidthTokens]
  have hformulaEntries : forall index, index < formulaTokens.length ->
      FoundationCompactNumericListedDirectArithmeticPrimitives.CompactFixedWidthEntry
        formulaTable formulaWidth index (formulaTokens.getI index) := by
    intro index hindex
    exact compactCanonicalPackedTokenStreamTableauAtWidth_entry
      formulaTokenCount formulaTable formulaWidth index (by omega)

  rcases acceptedTraceTable_exact_finalLayout
      hselfTrace hproofLayout hcertificateLayout with
    ⟨hstep, hactualLayout⟩
  have hlastRow :
      (4 * (inputTokenCount + 1) + 8) - 1 =
        compactNumericVerifierDirectLastRow inputTokenCount := by
    unfold compactNumericVerifierDirectLastRow
    omega
  rw [hlastRow] at hstep hactualLayout
  rcases CompactNumericVerifierAcceptedConclusionRow.realize_formulaSet
      hstep hconclusion hformulaLength hformulaEntries with
    ⟨realizedState, hrealizedLayout,
      hrealizedLength, hrealizedFormulaSet⟩
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        hactualLayout with
    ⟨_hactualFinish, hactualBound, _hactualEntries⟩
  have hslices : CompactFixedWidthTokenSlicesEq
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable
        (compactNumericVerifierDirectLastRow inputTokenCount) 0)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable
        (compactNumericVerifierDirectLastRow inputTokenCount) 1)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable
        (compactNumericVerifierDirectLastRow inputTokenCount) 2)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable
        (compactNumericVerifierDirectLastRow inputTokenCount) 24)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable
        (compactNumericVerifierDirectLastRow inputTokenCount) 25)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable
        (compactNumericVerifierDirectLastRow inputTokenCount) 24)
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable
        (compactNumericVerifierDirectLastRow inputTokenCount) 25) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hactualBound
  have hstateEq : realizedState =
      compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        (4 * (inputTokenCount + 1) + 8) :=
    FoundationCompactNumericListedDirectVerifierPayloadEquality.CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      hslices hactualLayout hrealizedLayout
  have haccepted :
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        (compactNumericVerifierFuelBound proofTokens certificateTokens)).2 =
          some true := by
    rw [← hfuel]
    exact acceptedTraceTable_sound
      hselfTrace hproofLayout hcertificateLayout
  have hactualLength :
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        (compactNumericVerifierFuelBound proofTokens certificateTokens)).1.2.2.length =
          1 := by
    rw [← hfuel, ← hstateEq]
    exact hrealizedLength
  have hactualFormulaSet :
      ((compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        (compactNumericVerifierFuelBound proofTokens certificateTokens)).1.2.2.getI
          0).1.toFinset = {formulaTokens} := by
    rw [← hfuel, ← hstateEq]
    exact hrealizedFormulaSet
  refine ⟨proofCode, proofTokens, certificateTokens, formulaTokens,
    ?_, hcode, hformulaCode, ?_⟩
  · rw [hinput.packedPayloadLength_eq]
    exact hinputWidth
  · exact ⟨haccepted, hactualLength, hactualFormulaSet⟩

/-- The direct two-variable predicate is pointwise identical to bounded public
checker acceptance.  The reverse implication uses syntax inversion of the
same numeric task machine; no parser or conclusion certificate is supplied as
an extra hypothesis. -/
theorem directProofPredicate_iff_exists_publicVerifier
    (bound formulaCode : Nat) :
    CompactListedPADirectProofPredicate bound formulaCode ↔
      exists proofCode : Nat,
        packedPayloadLength proofCode <= bound /\
          compactNumericListedPublicVerifier proofCode formulaCode = true := by
  constructor
  · intro hdirect
    rcases directProofPredicate_recovers_semanticAcceptance hdirect with
      ⟨proofCode, proofTokens, certificateTokens, formulaTokens,
        hbound, hproofCode, hformulaCode,
        haccepted, _hfinalLength, hfinalFormulaSet⟩
    have hresult :
        compactNumericVerifierResult proofTokens certificateTokens = true :=
      (stateAccepted_iff_verifierResult_true
        proofTokens certificateTokens).mp haccepted
    rcases compactNumericVerifierResult_true_exists_canonical
        proofTokens certificateTokens hresult with
      ⟨tree, certificate, hproofTokens, hcertificateTokens, hcertificate⟩
    have hrun := compactNumericVerifierRun_canonical_of_valid
      tree certificate hcertificate
    have hfinalState :
        compactNumericVerifierStateAt
            (compactNumericVerifierInitialState
              proofTokens certificateTokens)
            (compactNumericVerifierFuelBound
              proofTokens certificateTokens) =
          (compactNumericTreeFinalPayload tree certificate, some true) := by
      rw [hproofTokens, hcertificateTokens]
      simpa [compactNumericVerifierStateAt,
        compactNumericVerifierRun] using hrun
    rw [hfinalState] at hfinalFormulaSet
    have htokenSet :
        (arithmeticPropositionTokenValues tree.conclusionList).toFinset =
          {formulaTokens} := by
      simpa [compactNumericTreeFinalPayload] using hfinalFormulaSet
    have hformulaTokenMem :
        formulaTokens ∈
          arithmeticPropositionTokenValues tree.conclusionList := by
      have hfinsetMem : formulaTokens ∈
          (arithmeticPropositionTokenValues tree.conclusionList).toFinset := by
        rw [htokenSet]
        simp
      simpa using hfinsetMem
    rcases List.mem_map.mp hformulaTokenMem with
      ⟨formula, hformulaMem, hformulaTokens⟩
    have hformulaTokensCanonical :
        compactArithmeticFormulaTokens formula = formulaTokens := by
      simpa [arithmeticPropositionTokenValue] using hformulaTokens
    have hsingletonFormulaTokens :
        (arithmeticPropositionTokenValues [formula]).toFinset =
          {formulaTokens} := by
      simp [arithmeticPropositionTokenValues,
        arithmeticPropositionTokenValue, hformulaTokensCanonical]
    have htokenSetFormula :
        (arithmeticPropositionTokenValues tree.conclusionList).toFinset =
          (arithmeticPropositionTokenValues [formula]).toFinset := by
      exact htokenSet.trans hsingletonFormulaTokens.symm
    have hconclusion : tree.conclusionList.toFinset = {formula} := by
      have hraw :=
        (arithmeticPropositionTokenValues_toFinset_eq_iff
          tree.conclusionList [formula]).mp htokenSetFormula
      simpa using hraw
    have hformulaCodePublic :
        compactFormulaCode formula = formulaCode := by
      calc
        compactFormulaCode formula =
            compactAdditivePackedCode
              (compactArithmeticFormulaTokens formula) :=
          compactFormulaCode_eq_additivePackedCode formula
        _ = compactAdditivePackedCode formulaTokens := by
          rw [hformulaTokensCanonical]
        _ = formulaCode := hformulaCode.symm
    have hproofStream : compactPackedTokenStream proofCode =
        some (compactListedCertifiedTokens tree certificate) := by
      rw [hproofCode, compactPackedTokenStream_additivePackedCode,
        hproofTokens, hcertificateTokens]
      rfl
    have hproofDecode :
        decodeCompactPackedListedCertifiedPAProof proofCode =
          some (tree, certificate) :=
      (compactPackedTokenStream_eq_proofTokens_iff
        proofCode tree certificate).mp hproofStream
    have hpublic :
        compactNumericListedPublicVerifier proofCode formulaCode = true :=
      (compactNumericListedPublicVerifier_eq_true_iff
        proofCode formulaCode).2
        ⟨tree, certificate, formula, hproofDecode,
          hcertificate, hconclusion, hformulaCodePublic⟩
    exact ⟨proofCode, hbound, hpublic⟩
  · rintro ⟨proofCode, hbound, hpublic⟩
    exact directProofPredicate_of_public hbound hpublic

/-- Formula-level identity audit: the explicit two-variable Sigma-one formula
uses the public formula code, the public checker, and the full certified-token
payload measure appearing on the right-hand side. -/
theorem compactListedPADirectProofFormula_iff_exists_publicVerifier
    (bound formulaCode : Nat) :
    compactListedPADirectProofFormula.val.Evalb ![bound, formulaCode] ↔
      exists proofCode : Nat,
        packedPayloadLength proofCode <= bound /\
          compactNumericListedPublicVerifier proofCode formulaCode = true := by
  rw [compactListedPADirectProofFormula_spec]
  exact directProofPredicate_iff_exists_publicVerifier bound formulaCode

#print axioms directProofPredicate_recovers_semanticAcceptance
#print axioms directProofPredicate_iff_exists_publicVerifier
#print axioms compactListedPADirectProofFormula_iff_exists_publicVerifier

end FoundationCompactNumericListedDirectProofPredicateExactness
