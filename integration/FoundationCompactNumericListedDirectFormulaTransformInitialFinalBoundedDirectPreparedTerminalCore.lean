import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectInstalledSyntax
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTerminal
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Prepared valuation-context terminal proof -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignment
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectData
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTerminal

noncomputable def
    formulaTransformInitialFinalBoundedDirectPreparedTerminalBoundOfData
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (data : FormulaTransformInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    ExplicitDirectFormulaBound
      compactFormulaTransformInitialFinalBoundedDirectZeroValuation
      (compactFormulaTransformInitialFinalBoundedDirectInstalledFormula
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity
        data.witness)
      (compactFormulaTransformInitialFinalBoundedDirectTerminalPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound) := by
  let endpointBound :=
    formulaTransformInitialFinalBoundedDirectTerminalOfData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound data
  have hformula :
      compactFormulaTransformInitialFinalRowsClosedFormula tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
          expectedSuffixCount binderArity data.witness =
        compactFormulaTransformInitialFinalBoundedDirectInstalledFormula
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity
          data.witness :=
    (compactFormulaTransformInitialFinalBoundedDirectRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      data.witness).symm
  let atEmpty := CertifiedPAContextProof.cast hformula endpointBound.proof
  have hclosed :
      (compactFormulaTransformInitialFinalBoundedDirectInstalledFormula
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity
        data.witness).freeVariables = ∅ := by
    exact
      compactFormulaTransformInitialFinalBoundedDirectInstalledTerminal_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity data.witness
  let proof : CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformInitialFinalBoundedDirectInstalledFormula
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity
          data.witness).freeVariables
        compactFormulaTransformInitialFinalBoundedDirectZeroValuation)
      (compactFormulaTransformInitialFinalBoundedDirectInstalledFormula
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity
        data.witness) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) atEmpty
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ atEmpty).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (CertifiedPAContextProof.cast hformula
    endpointBound.proof).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact endpointBound.payloadLength_le

#print axioms
  formulaTransformInitialFinalBoundedDirectPreparedTerminalBoundOfData

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal
