import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAllBranchesFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAllBranchesFullyFixedBounds
import integration.FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fully fixed term and formula branches of one transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsHeavyBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermGraphFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsClosedGeneralBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAllBranchesFullyFixedBounds

private abbrev stepRowsFixedZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

private abbrev StepRowsHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate stepRowsFixedZeroValuation
    formula

private theorem binaryFormulaCode_left_le_and_step
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_le_and_step
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_le_or_step
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_le_or_step
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def stepRowsTermBranchFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource
    (syntaxTermGraphFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)
    (termRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound)
  threeRightDisjunctionPathOnePayloadEnvelope syntaxResource selectedResource

noncomputable def compactFormulaTransformStepRowsTermFullyFixedCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hparser : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current.parser next.parser stepWitness.slot0 stepWitness.term)
    (hrows : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode stepWitness.slot0 stepWitness.term.tag
      stepWitness.term.argument consumedCount witnessStart witnessFinish
      witnessCount) :
    StepRowsHybridCertificate
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) :=
  .disjunctionRight (.disjunctionLeft (.conjunction
    (syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount
      current.parser next.parser stepWitness.slot0 stepWitness.term hparser)
    (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode stepWitness.slot0
      stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
      witnessFinish witnessCount hrows)))

theorem
    compactFormulaTransformStepRowsTermFullyFixedCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current.parser next.parser stepWitness.slot0 stepWitness.term)
    (hrows : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode stepWitness.slot0 stepWitness.term.tag
      stepWitness.term.argument consumedCount witnessStart witnessFinish
      witnessCount)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (htermEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount coordinate) <= bitBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentOutputCount : current.outputCount <= numericBound)
    (hnextOutputCount : next.outputCount <= numericBound)
    (hwitnessCount : witnessCount <= numericBound)
    (hcurrentParserValue :
      CompactUnifiedParserStateCoordinateValueBound current.parser numericBound)
    (hnextParserValue :
      CompactUnifiedParserStateCoordinateValueBound next.parser numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentParserSize :
      CompactUnifiedParserStateCoordinateSizeBound current.parser bitBound)
    (hnextParserSize :
      CompactUnifiedParserStateCoordinateSizeBound next.parser bitBound)
    (hbinderSize : Nat.size stepWitness.slot0 <= bitBound)
    (htermWitnessSize :
      CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound
        stepWitness.term bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsTermFullyFixedCertificate tokenTable
          width tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount hparser hrows) <=
      stepRowsTermBranchFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  let quietFormula :=
    (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.done ⋎
      (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current.parser next.parser stepWitness.empty ⋎
        (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
            tokenCount current.parser next.parser stepWitness.slot0
            stepWitness.slot1 stepWitness.repeat ⋎
          compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
            tokenCount current.parser next.parser stepWitness.invalid))) ⋏
      compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        current.outputBoundary current.outputCount next.outputBoundary
        next.outputCount
  let parserFormula := compactUnifiedParserSyntaxTermClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.term
  let rowsFormula := compactFormulaTransformTermOutputRowsClosedFormula
    tokenTable width tokenCount current next mode stepWitness.slot0
    stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
    witnessFinish witnessCount
  let termFormula := parserFormula ⋏ rowsFormula
  let formulaFormula :=
    compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.formula ⋏
      compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.formula.tag consumedCount
        mappedHead
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let parserResource := syntaxTermGraphFullyFixedPayloadPolynomial tokenCount
    numericBound bitBound
  let rowsResource := termRowsAllBranchesFullyFixedPayloadPolynomial
    numericBound bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserResource rowsResource
  let parserCertificate := syntaxTermFullyFixedGraphCertificate tokenTable width
    tokenCount current.parser next.parser stepWitness.slot0 stepWitness.term
    hparser
  let rowsCertificate :=
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode stepWitness.slot0
      stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
      witnessFinish witnessCount hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      parserCertificate rowsCertificate
  have hparserResource :=
    syntaxTermFullyFixedGraphCertificate_structuralPayloadBound_le tokenTable
      width tokenCount current.parser next.parser stepWitness.slot0 numericBound
      bitBound stepWitness.term hparser hwidth htokenCount hcurrentParserValue
      hnextParserValue htokenTableSize hwidthSize htokenCountSize
      hcurrentParserSize hnextParserSize hbinderSize htermWitnessSize
      hnumericSize hbitPositive
  have hrowsResource :=
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next mode stepWitness.slot0
      stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
      witnessFinish witnessCount numericBound bitBound hrows
      htermEnvironmentSize hwidth htokenCount hcurrentOutputCount
      hnextOutputCount hwitnessCount hnumericSize
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
  have htailClosed := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using
      houterClosed.2)
  have htermPartsClosed := Finset.union_eq_empty.mp (by
    simpa only [termFormula,
      LO.FirstOrder.Semiformula.freeVariables_and] using
      htailClosed.1)
  have htailCode :=
    (binaryFormulaCode_right_le_or_step quietFormula
      (termFormula ⋎ formulaFormula)).trans hcode
  have htermCode :=
    (binaryFormulaCode_left_le_or_step termFormula formulaFormula).trans
      htailCode
  have hparserCode :=
    (binaryFormulaCode_left_le_and_step parserFormula rowsFormula).trans
      htermCode
  have hrowsCode :=
    (binaryFormulaCode_right_le_and_step parserFormula rowsFormula).trans
      htermCode
  have hsyntaxPositive :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial_positive bitBound
  have hselected :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource := by
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      parserCertificate rowsCertificate parserResource rowsResource
      syntaxResource hparserResource hrowsResource hsyntaxPositive
      htermPartsClosed.1 htermPartsClosed.2 hparserCode hrowsCode htermCode
  have hinner := transparentHybridDisjunctionLeftPayloadBound_le
    (right := formulaFormula) selectedCertificate selectedResource hselected
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := formulaFormula) selectedCertificate
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := quietFormula) innerCertificate _ hinner
  have hgeneral :=
    threeRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
      stepRowsFixedZeroValuation quietFormula termFormula formulaFormula
      selectedResource syntaxResource hsyntaxPositive hclosed hcode
  unfold compactFormulaTransformStepRowsTermFullyFixedCertificate
    stepRowsTermBranchFixedPayloadPolynomial
  dsimp only [quietFormula, parserFormula, rowsFormula, termFormula,
    formulaFormula, syntaxResource, parserResource, rowsResource,
    selectedResource, parserCertificate, rowsCertificate,
    selectedCertificate, innerCertificate]
  exact houter.trans hgeneral

def stepRowsFormulaBranchFixedPayloadPolynomial
    (currentOutputCount tokenCount numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource
    (cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
      bitBound)
    (outputRowsAllBranchesFullyFixedPayloadPolynomial currentOutputCount
      numericBound bitBound)
  threeRightDisjunctionPathTwoPayloadEnvelope syntaxResource selectedResource

noncomputable def compactFormulaTransformStepRowsFormulaFullyFixedCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hparser : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current.parser next.parser stepWitness.slot0 stepWitness.formula)
    (hrows : CompactFormulaTransformFormulaOutputRows tokenTable width
      tokenCount current next mode stepWitness.formula.tag consumedCount
      mappedHead) :
    StepRowsHybridCertificate
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) :=
  .disjunctionRight (.disjunctionRight (.conjunction
    (compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph tokenTable
      width tokenCount current.parser next.parser stepWitness.slot0
      stepWitness.formula hparser)
    (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode stepWitness.formula.tag
      consumedCount mappedHead hrows)))

theorem
    compactFormulaTransformStepRowsFormulaFullyFixedCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current.parser next.parser stepWitness.slot0 stepWitness.formula)
    (hrows : CompactFormulaTransformFormulaOutputRows tokenTable width
      tokenCount current next mode stepWitness.formula.tag consumedCount
      mappedHead)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (hformulaEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode stepWitness.formula.tag consumedCount
          mappedHead coordinate) <= bitBound)
    (hwidth : width <= numericBound)
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
    (htailBoundarySize :
      Nat.size stepWitness.formula.tailBoundary <= bitBound)
    (hbinderSize : Nat.size stepWitness.slot0 <= bitBound)
    (hrelationAritySize :
      Nat.size stepWitness.formula.relationArity <= bitBound)
    (hrelationCodeSize :
      Nat.size stepWitness.formula.relationCode <= bitBound)
    (htagSize : Nat.size stepWitness.formula.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsFormulaFullyFixedCertificate tokenTable
          width tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount hparser hrows) <=
      stepRowsFormulaBranchFixedPayloadPolynomial current.outputCount tokenCount
        numericBound bitBound := by
  let quietFormula :=
    (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.done ⋎
      (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current.parser next.parser stepWitness.empty ⋎
        (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
            tokenCount current.parser next.parser stepWitness.slot0
            stepWitness.slot1 stepWitness.repeat ⋎
          compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
            tokenCount current.parser next.parser stepWitness.invalid))) ⋏
      compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        current.outputBoundary current.outputCount next.outputBoundary
        next.outputCount
  let termFormula :=
    compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.term ⋏
      compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
        stepWitness.term.argument consumedCount witnessStart witnessFinish
        witnessCount
  let parserFormula := compactUnifiedParserSyntaxFormulaClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.formula
  let rowsFormula := compactFormulaTransformFormulaOutputRowsClosedFormula
    tokenTable width tokenCount current next mode stepWitness.formula.tag
    consumedCount mappedHead
  let formulaFormula := parserFormula ⋏ rowsFormula
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let parserResource := cleanParserSyntaxFormulaPartsPayloadPolynomial
    tokenCount numericBound bitBound
  let rowsResource := outputRowsAllBranchesFullyFixedPayloadPolynomial
    current.outputCount numericBound bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserResource rowsResource
  let parserCertificate :=
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph tokenTable
      width tokenCount current.parser next.parser stepWitness.slot0
      stepWitness.formula hparser
  let rowsCertificate :=
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode stepWitness.formula.tag
      consumedCount mappedHead hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      parserCertificate rowsCertificate
  have hparserResource :=
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.parser next.parser stepWitness.slot0
      numericBound bitBound stepWitness.formula hparser hwidth htokenCount
      hcurrentParserValue hnextParserValue htokenTableSize hcurrentParserSize
      hnextParserSize htailBoundarySize hbinderSize hrelationAritySize
      hrelationCodeSize htagSize hnumericSize hbitPositive
  have hrowsResource :=
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next mode stepWitness.formula.tag
      consumedCount mappedHead numericBound bitBound hrows
      hformulaEnvironmentSize hwidth htokenCount hcurrentOutputCount
      hnumericSize
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
  have htailClosed := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using
      houterClosed.2)
  have hformulaPartsClosed := Finset.union_eq_empty.mp (by
    simpa only [formulaFormula,
      LO.FirstOrder.Semiformula.freeVariables_and] using htailClosed.2)
  have htailCode :=
    (binaryFormulaCode_right_le_or_step quietFormula
      (termFormula ⋎ formulaFormula)).trans hcode
  have hformulaCode :=
    (binaryFormulaCode_right_le_or_step termFormula formulaFormula).trans
      htailCode
  have hparserCode :=
    (binaryFormulaCode_left_le_and_step parserFormula rowsFormula).trans
      hformulaCode
  have hrowsCode :=
    (binaryFormulaCode_right_le_and_step parserFormula rowsFormula).trans
      hformulaCode
  have hsyntaxPositive :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial_positive bitBound
  have hselected :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource := by
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      parserCertificate rowsCertificate parserResource rowsResource
      syntaxResource hparserResource hrowsResource hsyntaxPositive
      hformulaPartsClosed.1 hformulaPartsClosed.2 hparserCode hrowsCode
      hformulaCode
  have hinner := transparentHybridDisjunctionRightPayloadBound_le
    (left := termFormula) selectedCertificate selectedResource hselected
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termFormula) selectedCertificate
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := quietFormula) innerCertificate _ hinner
  have hgeneral :=
    threeRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral
      stepRowsFixedZeroValuation quietFormula termFormula formulaFormula
      selectedResource syntaxResource hsyntaxPositive hclosed hcode
  unfold compactFormulaTransformStepRowsFormulaFullyFixedCertificate
    stepRowsFormulaBranchFixedPayloadPolynomial
  dsimp only [quietFormula, termFormula, parserFormula, rowsFormula,
    formulaFormula, syntaxResource, parserResource, rowsResource,
    selectedResource, parserCertificate, rowsCertificate,
    selectedCertificate, innerCertificate]
  exact houter.trans hgeneral

#print axioms
  compactFormulaTransformStepRowsTermFullyFixedCertificate_structuralPayloadBound_le
#print axioms
  compactFormulaTransformStepRowsFormulaFullyFixedCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectFormulaTransformStepRowsHeavyBranchesFullyFixedBounds
