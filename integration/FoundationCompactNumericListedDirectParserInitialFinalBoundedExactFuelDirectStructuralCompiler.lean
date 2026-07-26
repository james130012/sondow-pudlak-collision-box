import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectInstalledFreeVariables
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelUniformDirectBound
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectUniformEndpointBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity23

/-!
# Structural direct compiler for exact-fuel bounded parser endpoints

The exact composite fuel term is retained in the terminal formula.  The
audited public arity-23 compiler installs all bounded endpoint witnesses.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity23
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectUniformEndpointBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFullyFixedDirectBound
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelUniformDirectBound
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFreeVariables
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectInstalledFreeVariables

def compactParserInitialFinalBoundedExactFuelDirectZeroValuation :
    Nat -> Nat :=
  fun _ => 0

structure CompactParserInitialFinalBoundedExactFuelClosedDirectBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

noncomputable def
    compactParserInitialFinalBoundedExactFuelDirectStructuralPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) : Nat :=
  let fuel := compactParserSyntaxExactFuel inputCount
  let numericBound :=
    compactParserInitialFinalBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound
  let bitBound :=
    compactParserInitialFinalBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount valueBound
  let body :=
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
  let terminalResource :=
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
      stateCount inputCount tokenCount numericBound bitBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 23 0 valueBound
    (binaryFormulaCode body).length terminalResource

noncomputable def
    compactParserInitialFinalBoundedExactFuelClosedDirectBoundOfBounded
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat)
    (hbounded : CompactParserInitialFinalBounded tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount valueBound) :
    CompactParserInitialFinalBoundedExactFuelClosedDirectBound
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound)
      (compactParserInitialFinalBoundedExactFuelDirectStructuralPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound) := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let data := compactParserInitialFinalBoundedDirectDataOfBounded tokenTable
    width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
    valueBound hbounded
  let body :=
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
  let values :=
    compactParserInitialFinalBoundedDirectWitnessValues data.witness
  let numericBound :=
    compactParserInitialFinalBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound
  let bitBound :=
    compactParserInitialFinalBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount valueBound
  have hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      data.witness := by
    simpa only [numericBound] using
      parserInitialFinalRowsValueBound_of_bounded_data tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound data
  have hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount bitBound
      data.witness := by
    have hraw :=
      parserInitialFinalRowsSizeBound_of_valueBound tokenTable width tokenCount
        stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount numericBound data.witness hvalue
    simpa only [bitBound,
      compactParserInitialFinalBoundedDirectBitBound, numericBound] using hraw
  let endpointBound :=
    compactUnifiedParserInitialFinalRowsExactFuelUniformClosedDirectBoundOfGraph
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound data.witness data.graph hvalue
      hsize
      (by
        unfold bitBound
          compactParserInitialFinalBoundedDirectBitBound
          numericBound
        omega)
      (by
        unfold bitBound
          compactParserInitialFinalBoundedDirectBitBound
        omega)
  let installedFormula :=
    body ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate)
  have hterminalFormula :
      compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount data.witness =
        installedFormula :=
    (compactParserInitialFinalBoundedExactFuelDirectRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount data.witness).symm
  let terminalAtEmpty :=
    CertifiedPAContextProof.cast hterminalFormula endpointBound.proof
  have hterminalClosed : installedFormula.freeVariables = ∅ := by
    simpa only [installedFormula, body, values] using
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
      simp [valuationContext])
      terminalAtEmpty
  let terminalResource :=
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
      stateCount inputCount tokenCount numericBound bitBound
  have hterminal : terminal.payloadLength <= terminalResource := by
    change (CertifiedPAContextProof.castContext _
      terminalAtEmpty).payloadLength <= _
    rw [CertifiedPAContextProof.castContext_payloadLength]
    change (CertifiedPAContextProof.cast hterminalFormula
      endpointBound.proof).payloadLength <= _
    rw [CertifiedPAContextProof.cast_payloadLength]
    exact endpointBound.payloadLength_le
  have hcontext : formulaCodeSum
      (valuationContext body.freeVariables
        compactParserInitialFinalBoundedExactFuelDirectZeroValuation) <= 0 := by
    rw [
      compactParserInitialFinalBoundedExactFuelDirectRawTerminal_freeVariables_eq_empty]
    simp [valuationContext, formulaCodeSum]
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 23 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    0 valueBound (binaryFormulaCode body).length body values data.values_le
      (by rfl) hcontext terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity23
      0 valueBound (binaryFormulaCode body).length body values data.values_le
      (by rfl) hcontext terminalResource terminal hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound :=
    (compactParserInitialFinalBoundedExactFuelDirectClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound).symm
  let contextualProof := castValuationContextProof hformula rawProof
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
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactParserInitialFinalBoundedExactFuelDirectStructuralPayloadEnvelope,
    fuel, data, body, values, numericBound, bitBound, endpointBound,
    installedFormula, terminalAtEmpty, terminal, terminalResource,
    sourceFormula, compilation, rawProof, contextualProof, proof] using
      hcoordinates.2

#print axioms
  compactParserInitialFinalBoundedExactFuelClosedDirectBoundOfBounded

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
