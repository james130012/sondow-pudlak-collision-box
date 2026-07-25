import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore

/-! # Fully fixed validity-choice certificate for a valid Term function code -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxTermTwoValidChoiceFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataGraph
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

noncomputable def syntaxTermTwoValidFixedChoiceCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument) :
    CheckedHybridValuationBoundedFormulaCertificate termZeroValuation
      ((compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.argument) ⋎
       (compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount)) :=
  CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph
        witness.argument witness.functionCode hvalid)
      (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity witness.argument hfunction))

theorem
    syntaxTermTwoValidFixedChoiceCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hfunctionCodeSize : Nat.size witness.functionCode <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermTwoValidFixedChoiceCertificate tokenTable width tokenCount
          current next binderArity witness hvalid hfunction) <=
      syntaxTermValidityChoiceFixedPayloadEnvelope
        (syntaxTermValidBranchFixedPayloadEnvelope tokenCount numericBound
          bitBound)
        bitBound := by
  let validFormula :=
    compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
      witness.functionCode
  let functionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.argument
  let invalidFormula :=
    compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
      witness.functionCode
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let validBranchFormula := validFormula ⋏ functionFormula
  let invalidBranchFormula := invalidFormula ⋏ failureFormula
  let syntaxResource := syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let validCertificate :=
    compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph
      witness.argument witness.functionCode hvalid
  let functionCertificate :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity witness.argument hfunction
  let validBranchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      validCertificate functionCertificate
  have hvalidResource :=
    compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      witness.argument witness.functionCode bitBound hvalid hargumentSize
      hfunctionCodeSize
  have hfunctionResource :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity witness.argument numericBound bitBound
      hfunction hwidth htokenCount hcurrentValue hnextValue htokenTableSize
      hcurrentSize hnextSize htailBoundarySize hbinderSize hargumentSize
      hnumericSize
  have hcode (formula : ValuationFormula)
      (hsub :
        (binaryFormulaCode formula).length <=
          (binaryFormulaCode
            (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable
              width tokenCount current next binderArity witness)).length) :
      (binaryFormulaCode formula).length <= syntaxResource := by
    dsimp only [syntaxResource]
    exact syntaxTermDecisionComponent_code_length_le_fixed tokenTable width
      tokenCount current next binderArity witness bitBound formula hsub hsize
  have hvalidCode : (binaryFormulaCode validFormula).length <= syntaxResource :=
    hcode validFormula (by
      dsimp only [validFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfunctionCode :
      (binaryFormulaCode functionFormula).length <= syntaxResource :=
    hcode functionFormula (by
      dsimp only [functionFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hvalidBranchCode :
      (binaryFormulaCode validBranchFormula).length <= syntaxResource :=
    hcode validBranchFormula (by
      dsimp only [validBranchFormula, validFormula, functionFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hinvalidBranchCode :
      (binaryFormulaCode invalidBranchFormula).length <= syntaxResource :=
    hcode invalidBranchFormula (by
      dsimp only [invalidBranchFormula, invalidFormula, failureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hchoiceCode :
      (binaryFormulaCode
        (validBranchFormula ⋎ invalidBranchFormula)).length <= syntaxResource :=
    hcode (validBranchFormula ⋎ invalidBranchFormula) (by
      dsimp only [validBranchFormula, invalidBranchFormula, validFormula,
        functionFormula, invalidFormula, failureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hvalidClosed : validFormula.freeVariables = ∅ := by
    dsimp only [validFormula]
    rw [compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment]
    exact
      compactAdditiveArithmeticFuncCodeValidExplicitFormula_freeVariables_eq_empty
        witness.argument witness.functionCode
  have hfunctionClosed : functionFormula.freeVariables = ∅ := by
    exact
      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity witness.argument
  have hinvalidClosed : invalidFormula.freeVariables = ∅ := by
    dsimp only [invalidFormula]
    rw [compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment]
    exact
      compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_freeVariables_eq_empty
        witness.argument witness.functionCode
  have hfailureClosed : failureFormula.freeVariables = ∅ :=
    syntaxTermFailureClosedFormula_freeVariables_eq_empty tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  have hvalidBranch :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral validCertificate
      functionCertificate
      (compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
        bitBound)
      (syntaxTermFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound)
      syntaxResource hvalidResource hfunctionResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hvalidClosed hfunctionClosed hvalidCode hfunctionCode hvalidBranchCode
  have hchoice :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      (right := invalidBranchFormula) validBranchCertificate
      (syntaxTermValidBranchFixedPayloadEnvelope tokenCount numericBound
        bitBound)
      syntaxResource (by
        simpa only [syntaxTermValidBranchFixedPayloadEnvelope] using
          hvalidBranch)
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hvalidClosed,
          hfunctionClosed]
        simp)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hinvalidClosed,
          hfailureClosed]
        simp)
      hvalidBranchCode hinvalidBranchCode hchoiceCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := invalidBranchFormula) validBranchCertificate) <= _
  simpa only [syntaxTermValidityChoiceFixedPayloadEnvelope] using hchoice

#print axioms
  syntaxTermTwoValidFixedChoiceCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermTwoValidChoiceFixedBounds
