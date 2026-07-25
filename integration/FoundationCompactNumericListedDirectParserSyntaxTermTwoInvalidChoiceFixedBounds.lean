import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore

/-! # Fully fixed validity-choice certificate for an invalid Term function code -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxTermTwoInvalidChoiceFixedBounds

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
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

noncomputable def syntaxTermTwoInvalidFixedChoiceCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
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
  CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left :=
      compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.argument)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph
        witness.argument witness.functionCode hinvalid)
      (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount hfailure))

theorem
    syntaxTermTwoInvalidFixedChoiceCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : witness.tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hfunctionCodeSize : Nat.size witness.functionCode <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermTwoInvalidFixedChoiceCertificate tokenTable width tokenCount
          current next binderArity witness hinvalid hfailure) <=
      syntaxTermValidityChoiceFixedPayloadEnvelope
        (syntaxTermInvalidBranchFixedPayloadEnvelope numericBound bitBound)
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
  let invalidCertificate :=
    compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph
      witness.argument witness.functionCode hinvalid
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let invalidBranchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      invalidCertificate failureCertificate
  have hinvalidResource :=
    compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      witness.argument witness.functionCode bitBound hinvalid hargumentSize
      hfunctionCodeSize
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount numericBound bitBound hfailure hwidth htokenCount
      htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
      hbitPositive
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
  have hvalidBranchCode :
      (binaryFormulaCode validBranchFormula).length <= syntaxResource :=
    hcode validBranchFormula (by
      dsimp only [validBranchFormula, validFormula, functionFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hinvalidCode :
      (binaryFormulaCode invalidFormula).length <= syntaxResource :=
    hcode invalidFormula (by
      dsimp only [invalidFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfailureCode :
      (binaryFormulaCode failureFormula).length <= syntaxResource :=
    hcode failureFormula (by
      dsimp only [failureFormula]
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
  have hinvalidBranch :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral invalidCertificate
      failureCertificate
      (compactAdditiveArithmeticFuncCodeInvalidFullyFixedPayloadPolynomial
        bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
      syntaxResource hinvalidResource hfailureResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hinvalidClosed hfailureClosed hinvalidCode hfailureCode
      hinvalidBranchCode
  have hchoice :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := validBranchFormula) invalidBranchCertificate
      (syntaxTermInvalidBranchFixedPayloadEnvelope numericBound bitBound)
      syntaxResource (by
        simpa only [syntaxTermInvalidBranchFixedPayloadEnvelope] using
          hinvalidBranch)
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
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := validBranchFormula) invalidBranchCertificate) <= _
  simpa only [syntaxTermValidityChoiceFixedPayloadEnvelope] using hchoice

#print axioms
  syntaxTermTwoInvalidFixedChoiceCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermTwoInvalidChoiceFixedBounds
