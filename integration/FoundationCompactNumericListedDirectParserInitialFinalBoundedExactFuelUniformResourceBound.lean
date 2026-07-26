import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompilerArity23

/-! # Uniform-resource bound for bounded exact-fuel parser endpoints -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelUniformResourceBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompilerArity23
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFreeVariables
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectInstalledFreeVariables
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFixedCodeBounds
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBound
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

def compactParserInitialFinalBoundedExactFuelUniformPayloadPolynomial
    (tokenCount uniformValueBound numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 23 0 uniformValueBound
    (compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
      numericBound bitBound)
    (compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
      tokenCount numericBound bitBound)

noncomputable def
    compactParserInitialFinalBoundedExactFuelUniformClosedDirectBoundOfBounded
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount formulaValueBound uniformValueBound numericBound bitBound :
      Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hbounded : CompactParserInitialFinalBounded tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount formulaValueBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hinputCount : inputCount <= numericBound)
    (hexpectedCount : expectedCount <= numericBound)
    (hvalueBoundSucc : formulaValueBound + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hinputBoundarySize : Nat.size inputBoundary <= bitBound)
    (hexpectedBoundarySize : Nat.size expectedBoundary <= bitBound)
    (htaskKindSize : Nat.size taskKind <= bitBound)
    (htaskBinderAritySize : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CompactParserInitialFinalBoundedExactFuelClosedDirectBound
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
        formulaValueBound)
      (compactParserInitialFinalBoundedExactFuelUniformPayloadPolynomial tokenCount
        uniformValueBound numericBound bitBound) := by
  let prepared :=
    compactParserInitialFinalBoundedExactFuelFullyFixedPreparedOfBounded
      tokenTable width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      formulaValueBound numericBound bitBound hbounded hwidth htokenCount
      hstateCount hinputCount hexpectedCount hvalueBoundSucc htokenTableSize
      hstateBoundarySize hinputBoundarySize hexpectedBoundarySize htaskKindSize
      htaskBinderAritySize htaskRepeatCountSize hnumericSize hbitPositive
  let body := compactParserInitialFinalBoundedExactFuelDirectRawTerminal
    tokenTable width tokenCount stateBoundary stateCount inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
  let values :=
    compactParserInitialFinalBoundedDirectWitnessValues prepared.data.witness
  let installedFormula :=
    body ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate)
  have hterminalClosed : installedFormula.freeVariables = ∅ := by
    simpa only [installedFormula, body, values, prepared] using
      (compactParserInitialFinalBoundedExactFuelDirectInstalledTerminal_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount prepared.data.witness)
  let terminal : CertifiedPAContextProof
      (valuationContext installedFormula.freeVariables
        compactParserInitialFinalBoundedExactFuelDirectZeroValuation)
      installedFormula :=
    CertifiedPAContextProof.castContext (by
      rw [hterminalClosed]
      simp [valuationContext]) prepared.terminal
  let terminalResource :=
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
      tokenCount numericBound bitBound
  have hterminal : terminal.payloadLength <= terminalResource := by
    change (CertifiedPAContextProof.castContext _ prepared.terminal).payloadLength
      <= _
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact prepared.terminal_payloadLength_le
  have hcontext : formulaCodeSum
      (valuationContext body.freeVariables
        compactParserInitialFinalBoundedExactFuelDirectZeroValuation) <= 0 := by
    rw [
      compactParserInitialFinalBoundedExactFuelDirectRawTerminal_freeVariables_eq_empty]
    simp [valuationContext, formulaCodeSum]
  let bodyCodeBound :=
    compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
      numericBound bitBound
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm formulaValueBound) 23 body
  let compilation :=
    compileExplicitBoundedWitnessDirectPublicWithUniformResource 0
      formulaValueBound uniformValueBound bodyCodeBound hformulaValue body values
      prepared.data.values_le prepared.bodyCode_le hcontext terminalResource
      terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithUniformResource_coordinates_arity23
      0 formulaValueBound uniformValueBound bodyCodeBound hformulaValue body values
      prepared.data.values_le prepared.bodyCode_le hcontext terminalResource
      terminal hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
        formulaValueBound :=
    (compactParserInitialFinalBoundedExactFuelDirectClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount formulaValueBound).symm
  let contextualProof := castValuationContextProof hformula rawProof
  have hclosed :
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
        formulaValueBound).freeVariables = ∅ :=
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount formulaValueBound
  let proof : CertifiedPAContextProof ∅
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
        formulaValueBound) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) contextualProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ contextualProof).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [compactParserInitialFinalBoundedExactFuelUniformPayloadPolynomial,
    prepared, body, values, installedFormula, terminal, terminalResource,
    bodyCodeBound, sourceFormula, compilation, rawProof, contextualProof, proof]
    using hcoordinates.2

#print axioms
  compactParserInitialFinalBoundedExactFuelUniformClosedDirectBoundOfBounded

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelUniformResourceBound
