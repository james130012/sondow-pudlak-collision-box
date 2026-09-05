import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsHeavyBranchesFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactPAHybridFourRightDisjunctionClosedGeneralBounds

/-! # Fully fixed quiet-invalid branch of one transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietInvalidFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds
open FoundationCompactPAHybridFourRightDisjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsHeavyBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate

private abbrev quietInvalidZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

private abbrev QuietInvalidHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate quietInvalidZeroValuation
    formula

private theorem binaryFormulaCode_left_le_and_invalid
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_le_and_invalid
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_le_or_invalid
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def stepRowsQuietInvalidFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let parserPathResource := fourRightDisjunctionPathThreePayloadEnvelope
    syntaxResource
    (syntaxInvalidFullyFixedPayloadPolynomial tokenCount numericBound bitBound)
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  threeRightDisjunctionPathZeroPayloadEnvelope syntaxResource selectedResource

noncomputable def compactFormulaTransformStepRowsQuietInvalidFullyFixedCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hparser : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current.parser next.parser stepWitness.invalid)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next) :
    QuietInvalidHybridCertificate
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) :=
  .disjunctionLeft (.conjunction
    (.disjunctionRight (.disjunctionRight (.disjunctionRight
      (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.parser next.parser
        stepWitness.invalid hparser))))
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows))

theorem
    compactFormulaTransformStepRowsQuietInvalidFullyFixedCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current.parser next.parser stepWitness.invalid)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentOutputCount : current.outputCount <= numericBound)
    (hcurrentParserValue :
      CompactUnifiedParserStateCoordinateValueBound current.parser numericBound)
    (hnextParserValue :
      CompactUnifiedParserStateCoordinateValueBound next.parser numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentParserSize :
      CompactUnifiedParserStateCoordinateSizeBound current.parser bitBound)
    (hnextParserSize :
      CompactUnifiedParserStateCoordinateSizeBound next.parser bitBound)
    (hinvalidTailBoundarySize :
      Nat.size stepWitness.invalid.tailBoundary <= bitBound)
    (hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound)
    (hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsQuietInvalidFullyFixedCertificate
          tokenTable width tokenCount current next mode stepWitness
          consumedCount mappedHead witnessStart witnessFinish witnessCount
          hparser hrows) <=
      stepRowsQuietInvalidFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.slot1 stepWitness.repeat
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.invalid
  let parserFormula :=
    doneFormula ⋎ (emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
  let rowsFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.outputBoundary current.outputCount next.outputBoundary
    next.outputCount
  let quietFormula := parserFormula ⋏ rowsFormula
  let termFormula :=
    compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.term ⋏
      compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
        stepWitness.term.argument consumedCount witnessStart witnessFinish
        witnessCount
  let formulaFormula :=
    compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.formula ⋏
      compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.formula.tag consumedCount
        mappedHead
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let invalidResource := syntaxInvalidFullyFixedPayloadPolynomial tokenCount
    numericBound bitBound
  let parserPathResource := fourRightDisjunctionPathThreePayloadEnvelope
    syntaxResource invalidResource
  let rowsResource := sameRowsCompleteFullyFixedPayloadPolynomial numericBound
    bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource rowsResource
  let invalidCertificate :=
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parser next.parser
      stepWitness.invalid hparser
  let parserCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := doneFormula)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := emptyFormula)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := repeatFormula) invalidCertificate))
  let rowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      parserCertificate rowsCertificate
  have hinvalidResource :=
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.parser next.parser
      stepWitness.invalid numericBound bitBound hparser hwidth hwidthBit
      htokenCount hcurrentParserValue hnextParserValue htokenTableSize
      hcurrentParserSize hnextParserSize hinvalidTailBoundarySize hnumericSize
      hbitPositive
  have hrowsTransparent :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  have hrowsFixed :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount numericBound bitBound hrows hwidth
      htokenCount hcurrentOutputCount htokenTableSize
      hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    hrowsTransparent.trans hrowsFixed
  have hfullClosed := compactFormulaTransformStepRowsExplicitFormula_closed
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  have hfullCode :=
    compactFormulaTransformStepRowsExplicitFormula_code_length_le_fixed
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount bitBound
      hstepEnvironmentSize
  have hfullAlignment :
      compactFormulaTransformStepRowsExplicitFormula tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount =
        quietFormula ⋎ (termFormula ⋎ formulaFormula) := by
    rfl
  have hclosed :
      (quietFormula ⋎ (termFormula ⋎ formulaFormula)).freeVariables = ∅ := by
    rw [← hfullAlignment]
    exact hfullClosed
  have hcode :
      (binaryFormulaCode
        (quietFormula ⋎ (termFormula ⋎ formulaFormula))).length <=
        syntaxResource := by
    rw [← hfullAlignment]
    exact hfullCode
  have houterClosed := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hclosed)
  have hquietPartsClosed := Finset.union_eq_empty.mp (by
    simpa only [quietFormula,
      LO.FirstOrder.Semiformula.freeVariables_and] using houterClosed.1)
  have hquietCode :=
    (binaryFormulaCode_left_le_or_invalid quietFormula
      (termFormula ⋎ formulaFormula)).trans hcode
  have hparserCode :=
    (binaryFormulaCode_left_le_and_invalid parserFormula rowsFormula).trans
      hquietCode
  have hrowsCode :=
    (binaryFormulaCode_right_le_and_invalid parserFormula rowsFormula).trans
      hquietCode
  have hsyntaxPositive :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial_positive bitBound
  have hparserRaw1 := transparentHybridDisjunctionRightPayloadBound_le
    (left := repeatFormula) invalidCertificate invalidResource
    hinvalidResource
  let parserInner1 :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := repeatFormula) invalidCertificate
  have hparserRaw2 := transparentHybridDisjunctionRightPayloadBound_le
    (left := emptyFormula) parserInner1 _ hparserRaw1
  let parserInner2 :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := emptyFormula) parserInner1
  have hparserRaw3 := transparentHybridDisjunctionRightPayloadBound_le
    (left := doneFormula) parserInner2 _ hparserRaw2
  have hparserGeneral :=
    fourRightDisjunctionPathThreeTransparentEnvelope_le_closedGeneral
      quietInvalidZeroValuation doneFormula emptyFormula repeatFormula
      invalidFormula invalidResource syntaxResource hsyntaxPositive
      hquietPartsClosed.1 hparserCode
  have hparserResource :
      hybridFormulaStructuralPayloadBound parserCertificate <=
        parserPathResource := hparserRaw3.trans hparserGeneral
  have hselected :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource := by
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      parserCertificate rowsCertificate parserPathResource rowsResource
      syntaxResource hparserResource hrowsResource hsyntaxPositive
      hquietPartsClosed.1 hquietPartsClosed.2 hparserCode hrowsCode hquietCode
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termFormula ⋎ formulaFormula) selectedCertificate
    selectedResource hselected
  have hgeneral :=
    threeRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
      quietInvalidZeroValuation quietFormula termFormula formulaFormula
      selectedResource syntaxResource hsyntaxPositive hclosed hcode
  unfold compactFormulaTransformStepRowsQuietInvalidFullyFixedCertificate
    stepRowsQuietInvalidFixedPayloadPolynomial
  dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
    parserFormula, rowsFormula, quietFormula, termFormula, formulaFormula,
    syntaxResource, invalidResource, parserPathResource, rowsResource,
    selectedResource, invalidCertificate, parserInner1, parserInner2,
    parserCertificate, rowsCertificate, selectedCertificate]
  exact houter.trans hgeneral

#print axioms
  compactFormulaTransformStepRowsQuietInvalidFullyFixedCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietInvalidFullyFixedBounds
