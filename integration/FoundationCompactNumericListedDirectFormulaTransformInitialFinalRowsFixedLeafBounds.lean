import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

/-! # Fixed direct bounds for the seven formula-transform endpoint leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

def formulaTransformInitialFinalZeroValuation : Nat -> Nat := fun _ => 0

noncomputable def
    formulaTransformInitialFinalStateAtRowsClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (numericBound bitBound : Nat)
    (hgraph : CompactFormulaTransformStateAtRows tokenTable width tokenCount
      stateBoundary stateCount index coordinates sizeWitness)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hstateCountValue : stateCount <= numericBound)
    (hparserTokensCountValue :
      coordinates.parserTokensCount <= numericBound)
    (hparserTasksCountValue : coordinates.parserTasksCount <= numericBound)
    (houtputCountValue : coordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hparserTokensBoundarySize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTasksBoundarySize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (houtputBoundarySize :
      Nat.size coordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactFormulaTransformStateAtRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index coordinates sizeWitness)
      (compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (shortBinaryNumeralTerm index) numericBound bitBound) := by
  let indexTerm : ValuationTerm := shortBinaryNumeralTerm index
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    rw [show indexTerm.freeVariables = ∅ by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty index]
    simp
  have hgraphAtTerm : CompactFormulaTransformStateAtRows tokenTable width
      tokenCount stateBoundary stateCount
      (termValue formulaTransformInitialFinalZeroValuation indexTerm)
      coordinates sizeWitness := by
    simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using hgraph
  let bound :=
    compactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
      formulaTransformInitialFinalZeroValuation tokenTable width tokenCount
      stateBoundary stateCount indexTerm coordinates sizeWitness numericBound
      bitBound hindexVariables hgraphAtTerm (Nat.zero_le numericBound)
      hwidthValue htokenCountValue hstateCountValue hparserTokensCountValue
      hparserTasksCountValue houtputCountValue htokenTableSize
      hstateBoundarySize hparserTokensBoundarySize hparserTasksBoundarySize
      houtputBoundarySize hnumericSize hnumericBit
  have hformula :
      compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
          tokenCount stateBoundary stateCount indexTerm coordinates
            sizeWitness =
        compactFormulaTransformStateAtRowsClosedFormula tokenTable width
          tokenCount stateBoundary stateCount index coordinates sizeWitness := by
    rfl
  let contextualProof := castValuationContextProof hformula bound.proof
  have hclosed :=
    compactFormulaTransformStateAtRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount stateBoundary stateCount index coordinates
      sizeWitness
  let proof : CertifiedPAContextProof ∅
      (compactFormulaTransformStateAtRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index coordinates sizeWitness) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) contextualProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ contextualProof).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (castValuationContextProof hformula bound.proof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  simpa only [indexTerm] using bound.payloadLength_le

noncomputable def
    formulaTransformInitialParserSourceClosedDirectBoundOfGraph
    (tokenTable width tokenCount inputBoundary inputCount binderArity
      numericBound bitBound : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates.parser inputBoundary inputCount 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hinputCountValue : inputCount <= numericBound)
    (htasksCountValue : coordinates.parserTasksCount <= numericBound)
    (htasksFinishValue : coordinates.parserTasksFinish <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hparserFinishSize : Nat.size coordinates.parserFinish <= bitBound)
    (hparserTokensFinishSize :
      Nat.size coordinates.parserTokensFinish <= bitBound)
    (hparserTasksFinishSize :
      Nat.size coordinates.parserTasksFinish <= bitBound)
    (hparserTokensBoundarySize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTokensCountSize :
      Nat.size coordinates.parserTokensCount <= bitBound)
    (hparserTasksBoundarySize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (hparserTasksCountSize :
      Nat.size coordinates.parserTasksCount <= bitBound)
    (hinputBoundarySize : Nat.size inputBoundary <= bitBound)
    (hinputCountSize : Nat.size inputCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates)
      (compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
        numericBound bitBound) := by
  let certificate :=
    compactFormulaTransformInitialParserSourcePublicCertificateOfGraph
      tokenTable width tokenCount inputBoundary inputCount binderArity
      coordinates hgraph
  have hresource :
      hybridFormulaStructuralPayloadBound certificate <=
        compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
          numericBound bitBound :=
    compactFormulaTransformInitialParserSourcePublicCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount inputBoundary inputCount binderArity
      numericBound bitBound coordinates hgraph hwidthValue htokenCountValue
      hinputCountValue htasksCountValue htasksFinishValue htokenTableSize
      hwidthSize htokenCountSize hstartSize hparserFinishSize
      hparserTokensFinishSize hparserTasksFinishSize
      hparserTokensBoundarySize hparserTokensCountSize
      hparserTasksBoundarySize hparserTasksCountSize hinputBoundarySize
      hinputCountSize hbinderAritySize hnumericSize
  have hclosed :=
    compactFormulaTransformInitialParserSourcePublicFormula_freeVariables_eq_empty
      tokenTable width tokenCount inputBoundary inputCount binderArity
      coordinates
  let proof : CertifiedPAContextProof ∅
      (compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) certificate.compile
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ certificate.compile).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact (compile_payloadLength_le_structuralPayloadBound certificate).trans
    hresource

def formulaTransformInitialOutputCountZeroTermCodeEnvelope
    (bitBound : Nat) : Nat :=
  max (binaryNumeralTermCodeEnvelope bitBound)
    (binaryTermCode (‘0’ : ValuationTerm)).length

def formulaTransformInitialOutputCountZeroPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (formulaTransformInitialOutputCountZeroTermCodeEnvelope bitBound)

private theorem termValue_arithmeticZero_initialFinalLeaf
    (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

noncomputable def formulaTransformInitialOutputCountZeroClosedDirectBound
    (outputCount numericBound bitBound : Nat)
    (hcount : outputCount = 0)
    (houtputCountSize : Nat.size outputCount <= bitBound) :
    ParserInitialFinalClosedDirectBound
      “!!(shortBinaryNumeralTerm outputCount) = 0”
      (formulaTransformInitialOutputCountZeroPayloadPolynomial numericBound
        bitBound) := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm outputCount
  let rightTerm : ValuationTerm := ‘0’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      formulaTransformInitialFinalZeroValuation Language.Eq.eq
      ![leftTerm, rightTerm] (by
        change termValue formulaTransformInitialFinalZeroValuation leftTerm =
          termValue formulaTransformInitialFinalZeroValuation rightTerm
        simpa only [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticZero_initialFinalLeaf] using hcount)
  let certificate :
      CheckedHybridValuationBoundedFormulaCertificate
        formulaTransformInitialFinalZeroValuation
        “!!(shortBinaryNumeralTerm outputCount) = 0” :=
    .cast (Semiformula.Operator.eq_def _ _).symm direct
  have hleftClosed : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty outputCount
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    simp [Semiterm.Operator.operator]
  have hleftCode : (binaryTermCode leftTerm).length <=
      formulaTransformInitialOutputCountZeroTermCodeEnvelope bitBound :=
    (binaryNumeralTerm_code_length_le_envelope outputCount bitBound
      houtputCountSize).trans (Nat.le_max_left _ _)
  have hrightCode : (binaryTermCode rightTerm).length <=
      formulaTransformInitialOutputCountZeroTermCodeEnvelope bitBound := by
    unfold formulaTransformInitialOutputCountZeroTermCodeEnvelope
    exact Nat.le_max_right _ _
  have hresource : hybridFormulaStructuralPayloadBound certificate <=
      formulaTransformInitialOutputCountZeroPayloadPolynomial numericBound
        bitBound := by
    have hfixed :=
      compilePositiveRelationPayloadResource_le_fixed_of_closed
        formulaTransformInitialFinalZeroValuation Language.Eq.eq leftTerm
        rightTerm numericBound
        (formulaTransformInitialOutputCountZeroTermCodeEnvelope bitBound)
        hleftClosed hrightClosed hleftCode hrightCode
    simpa only [certificate, direct, hybridFormulaStructuralPayloadBound,
      formulaTransformInitialOutputCountZeroPayloadPolynomial] using hfixed
  have hclosed :
      (“!!(shortBinaryNumeralTerm outputCount) = 0” : ValuationFormula
        ).freeVariables = ∅ := by
    change
      (Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm]).freeVariables = ∅
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    ext candidate
    simp [hleftClosed, hrightClosed]
  let proof : CertifiedPAContextProof ∅
      “!!(shortBinaryNumeralTerm outputCount) = 0” :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) certificate.compile
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ certificate.compile).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact (compile_payloadLength_le_structuralPayloadBound certificate).trans
    hresource

noncomputable def formulaTransformInitialFinalSameRowsClosedDirectBoundOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hsourceCountValue : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound) := by
  let certificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      hgraph
  have hresource : hybridFormulaStructuralPayloadBound certificate <=
      sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount hgraph).trans
    (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph hwidthValue htokenCountValue
      hsourceCountValue htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize)
  have hclosed :=
    compactAdditiveNatListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount
  let proof : CertifiedPAContextProof ∅
      (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) certificate.compile
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _ certificate.compile).payloadLength
      <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact (compile_payloadLength_le_structuralPayloadBound certificate).trans
    hresource

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBounds
