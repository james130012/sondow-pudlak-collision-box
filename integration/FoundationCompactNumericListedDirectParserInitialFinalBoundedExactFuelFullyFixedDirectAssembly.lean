import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity23

/-! # Arity-twenty-three assembly for the fully fixed exact-fuel endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectAssembly

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity23
open FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity23
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFreeVariables
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectInstalledFreeVariables
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFixedCodeBounds
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBound
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

noncomputable def
    compactParserInitialFinalBoundedExactFuelFullyFixedClosedDirectBoundOfPrepared
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound : Nat)
    (prepared :
      CompactParserInitialFinalBoundedExactFuelFullyFixedPrepared tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound numericBound bitBound) :
    CompactParserInitialFinalBoundedExactFuelClosedDirectBound
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound)
      (compactParserInitialFinalBoundedExactFuelFullyFixedPayloadPolynomial
        tokenCount valueBound numericBound bitBound) := by
  let data := prepared.data
  let body := compactParserInitialFinalBoundedExactFuelDirectRawTerminal
    tokenTable width tokenCount stateBoundary stateCount inputBoundary
    inputCount expectedBoundary expectedCount taskKind taskBinderArity
    taskRepeatCount
  let values := compactParserInitialFinalBoundedDirectWitnessValues data.witness
  let bodyCodeBound :=
    compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
      numericBound bitBound
  let terminalResource :=
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
      tokenCount numericBound bitBound
  let installedFormula :=
    body ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate)
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound := by
    simpa only [body, bodyCodeBound] using prepared.bodyCode_le
  let terminalAtEmpty : CertifiedPAContextProof ∅ installedFormula := by
    simpa only [installedFormula, body, values, data] using prepared.terminal
  have hterminalClosed : installedFormula.freeVariables = ∅ := by
    simpa only [installedFormula, body, values, data] using
      (compactParserInitialFinalBoundedExactFuelDirectInstalledTerminal_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount data.witness)
  let terminal : CertifiedPAContextProof
      (valuationContext installedFormula.freeVariables
        compactParserInitialFinalBoundedExactFuelDirectZeroValuation)
      installedFormula :=
    CertifiedPAContextProof.castContext (by
      rw [hterminalClosed]
      simp [valuationContext]) terminalAtEmpty
  have hterminal : terminal.payloadLength <= terminalResource := by
    change (CertifiedPAContextProof.castContext _
      terminalAtEmpty).payloadLength <= _
    rw [CertifiedPAContextProof.castContext_payloadLength]
    simpa only [terminalAtEmpty, terminalResource, data, id_eq] using
      prepared.terminal_payloadLength_le
  have hcontext : formulaCodeSum
      (valuationContext body.freeVariables
        compactParserInitialFinalBoundedExactFuelDirectZeroValuation) <= 0 := by
    rw [
      compactParserInitialFinalBoundedExactFuelDirectRawTerminal_freeVariables_eq_empty]
    simp [valuationContext, formulaCodeSum]
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 23 body
  let witnessBound := compileExplicitBoundedWitnessDirectPublicBoundArity23
    0 valueBound bodyCodeBound body values data.values_le hbody hcontext
    terminalResource terminal hterminal
  have hformula : sourceFormula =
      compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound :=
    (compactParserInitialFinalBoundedExactFuelDirectClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound).symm
  let contextualProof := castValuationContextProof hformula witnessBound.proof
  have hclosed :
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound).freeVariables = ∅ :=
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound
  let proof : CertifiedPAContextProof ∅
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) contextualProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _
    contextualProof).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (castValuationContextProof hformula witnessBound.proof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  simpa only [
    compactParserInitialFinalBoundedExactFuelFullyFixedPayloadPolynomial,
    bodyCodeBound, terminalResource] using witnessBound.payloadLength_le

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectAssembly
