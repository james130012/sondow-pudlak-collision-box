import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendCapturedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-! # Fully fixed residual-witness certificate under term-output mode five -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsResidualExistsFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendCapturedFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

private abbrev residualRowsValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsResidualInstantiatedFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  2 * termRowsAtomicLeafFormulaCodePolynomial bitBound +
    appendTwoExactFullFormulaCodePolynomial bitBound +
    2 * (binaryNatCode 4).length

def termRowsResidualExistsSyntaxPolynomial (bitBound : Nat) : Nat :=
  termRowsOuterSyntaxPolynomial bitBound +
    termOutputFailureTermCodePolynomial bitBound +
    termRowsResidualInstantiatedFormulaCodePolynomial bitBound + 1

def termRowsResidualExistsFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsResidualExistsSyntaxPolynomial bitBound
  let bodyResource := hybridThreeConjunctionGeneralPayloadEnvelope
    syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound)
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound)
    (appendTwoFullyFixedPayloadPolynomial numericBound bitBound)
  hybridExistsWitnessGeneralPayloadEnvelope syntaxResource bodyResource

private theorem residualExists_body_code_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem
    compactFormulaTransformTermResidualExistsCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount residual numericBound bitBound : Nat)
    (hresidual : residual <= argument)
    (hequality : argument = witnessCount + residual)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 residual)
    (hresidualExistsClosed :
      (compactFormulaTransformTermResidualExistsFormula tokenTable width
        tokenCount current next argument witnessCount).freeVariables = ∅)
    (hresidualExistsCode :
      (binaryFormulaCode
        (compactFormulaTransformTermResidualExistsFormula tokenTable width
          tokenCount current next argument witnessCount)).length <=
        termRowsOuterSyntaxPolynomial bitBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentParserFinishSize : Nat.size current.parserFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hcurrentOutputCountSize : Nat.size current.outputCount <= bitBound)
    (hnextParserFinishSize : Nat.size next.parserFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound)
    (hnextOutputCountSize : Nat.size next.outputCount <= bitBound)
    (hargumentSize : Nat.size argument <= bitBound)
    (hwitnessCountSize : Nat.size witnessCount <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnextOutputCountBound : next.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermResidualExistsCertificate tokenTable width
          tokenCount current next argument witnessCount residual hresidual
          hequality hrows) <=
      termRowsResidualExistsFixedPayloadPolynomial numericBound bitBound := by
  let residualTerm := shortBinaryNumeralTerm residual
  let argumentTerm := shortBinaryNumeralTerm argument
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  let argumentSuccTerm := nativeAddTerm argumentTerm (‘1’ : ValuationTerm)
  let witnessResidualTerm := nativeAddTerm witnessCountTerm residualTerm
  let boundFormula := nativeLtFormula residualTerm argumentSuccTerm
  let equalityFormula := nativeEqFormula argumentTerm witnessResidualTerm
  let rowsFormula :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘1’ : ValuationTerm) residualTerm
  let instantiatedFormula := boundFormula ⋏ (equalityFormula ⋏ rowsFormula)
  let body := compactFormulaTransformTermResidualWitnessBody tokenTable width
    tokenCount current next argument witnessCount
  let existentialFormula : ValuationFormula := ∃⁰ body
  let syntaxResource := termRowsResidualExistsSyntaxPolynomial bitBound
  let boundResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let equalityResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let rowsResource := appendTwoFullyFixedPayloadPolynomial numericBound bitBound
  let bodyResource := hybridThreeConjunctionGeneralPayloadEnvelope
    syntaxResource boundResource equalityResource rowsResource
  have hresidualSize : Nat.size residual <= bitBound :=
    (Nat.size_le_size hresidual).trans hargumentSize
  have honeSize : Nat.size 1 <= bitBound := by simpa using hbitPositive
  have hresidualClosed : residualTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty residual
  have hargumentClosed : argumentTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty argument
  have hwitnessCountClosed : witnessCountTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty witnessCount
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have hargumentSuccClosed : argumentSuccTerm.freeVariables = ∅ := by
    dsimp only [argumentSuccTerm]
    rw [nativeAddTerm_freeVariables_failure, hargumentClosed, honeClosed]
    simp
  have hwitnessResidualClosed : witnessResidualTerm.freeVariables = ∅ := by
    simpa only [witnessResidualTerm, witnessCountTerm, residualTerm] using
      termRowsAddShortNumerals_closed witnessCount residual
  have hresidualTermCode : (binaryTermCode residualTerm).length <=
      termOutputFailureTermCodePolynomial bitBound := by
    simpa only [residualTerm] using
      termRowsShortNumeralCode_le residual bitBound hresidualSize
  have hargumentTermCode : (binaryTermCode argumentTerm).length <=
      termOutputFailureTermCodePolynomial bitBound := by
    simpa only [argumentTerm] using
      termRowsShortNumeralCode_le argument bitBound hargumentSize
  have hwitnessCountTermCode : (binaryTermCode witnessCountTerm).length <=
      termOutputFailureTermCodePolynomial bitBound := by
    simpa only [witnessCountTerm] using
      termRowsShortNumeralCode_le witnessCount bitBound hwitnessCountSize
  have honeTermCode : (binaryTermCode (‘1’ : ValuationTerm)).length <=
      termOutputFailureTermCodePolynomial bitBound :=
    termRowsLiteralCode_le (‘1’ : ValuationTerm) bitBound
      (Or.inr (Or.inl rfl))
  have hargumentSuccCode : (binaryTermCode argumentSuccTerm).length <=
      termOutputFailureTermCodePolynomial bitBound := by
    have hadd := paAddTerm_code_length_le argumentTerm (‘1’ : ValuationTerm)
    have hargumentNumeralCode : (binaryTermCode argumentTerm).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
      simpa only [argumentTerm] using
        binaryNumeralTerm_code_length_le_envelope argument bitBound
          hargumentSize
    change (binaryTermCode
      (paAddTerm argumentTerm (‘1’ : ValuationTerm))).length <= _
    unfold termOutputFailureTermCodePolynomial outputRowsAtomicTermCodePolynomial
    omega
  have hwitnessResidualCode :
      (binaryTermCode witnessResidualTerm).length <=
        termOutputFailureTermCodePolynomial bitBound := by
    simpa only [witnessResidualTerm, witnessCountTerm, residualTerm] using
      termRowsAddShortNumeralsCode_le witnessCount residual bitBound
        hwitnessCountSize hresidualSize
  have hboundClosed : boundFormula.freeVariables = ∅ := by
    dsimp only [boundFormula]
    unfold nativeLtFormula
    rw [LO.FirstOrder.Semiformula.Operator.lt_def]
    exact outputRowsBinaryRelation_closed Language.ORing.Rel.lt residualTerm
      argumentSuccTerm hresidualClosed hargumentSuccClosed
  have hequalityClosed : equalityFormula.freeVariables = ∅ := by
    dsimp only [equalityFormula]
    unfold nativeEqFormula
    rw [LO.FirstOrder.Semiformula.Operator.eq_def]
    exact outputRowsBinaryRelation_closed Language.Eq.eq argumentTerm
      witnessResidualTerm hargumentClosed hwitnessResidualClosed
  have hrowsClosed : rowsFormula.freeVariables = ∅ := by
    dsimp only [rowsFormula]
    exact compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_closed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘1’ : ValuationTerm) residualTerm honeClosed
      hresidualClosed
  have hinstantiatedClosed : instantiatedFormula.freeVariables = ∅ := by
    dsimp only [instantiatedFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and, hboundClosed,
      hequalityClosed, hrowsClosed]
    simp
  have hboundCode : (binaryFormulaCode boundFormula).length <=
      termRowsAtomicLeafFormulaCodePolynomial bitBound := by
    dsimp only [boundFormula]
    unfold nativeLtFormula
    rw [LO.FirstOrder.Semiformula.Operator.lt_def]
    exact outputRowsBinaryRelationCode_le Language.ORing.Rel.lt residualTerm
      argumentSuccTerm bitBound
      (by simpa [termOutputFailureTermCodePolynomial] using hresidualTermCode)
      (by simpa [termOutputFailureTermCodePolynomial] using hargumentSuccCode)
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      termRowsAtomicLeafFormulaCodePolynomial bitBound := by
    dsimp only [equalityFormula]
    unfold nativeEqFormula
    rw [LO.FirstOrder.Semiformula.Operator.eq_def]
    exact outputRowsBinaryRelationCode_le Language.Eq.eq argumentTerm
      witnessResidualTerm bitBound
      (by simpa [termOutputFailureTermCodePolynomial] using hargumentTermCode)
      (by simpa [termOutputFailureTermCodePolynomial] using
        hwitnessResidualCode)
  have hfirstAppendCode :
      (binaryTermCode (‘1’ : ValuationTerm)).length <=
        appendTwoExactTermCodePolynomial bitBound := by
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  have hsecondAppendCode : (binaryTermCode residualTerm).length <=
      appendTwoExactTermCodePolynomial bitBound := by
    simpa only [residualTerm] using
      appendTwoShortNumeralCode_le residual bitBound hresidualSize
  have hrowsCode : (binaryFormulaCode rowsFormula).length <=
      appendTwoExactFullFormulaCodePolynomial bitBound := by
    dsimp only [rowsFormula]
    exact
      compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_code_length_le_fixed
        tokenTable width tokenCount current.parserFinish current.finish
        current.outputCount next.parserFinish next.finish next.outputBoundary
        next.outputCount bitBound (‘1’ : ValuationTerm) residualTerm htableSize
        hwidthSize htokenCountSize hcurrentParserFinishSize hcurrentFinishSize
        hcurrentOutputCountSize hnextParserFinishSize hnextFinishSize
        hnextOutputBoundarySize hnextOutputCountSize hfirstAppendCode
        hsecondAppendCode
  have hinstantiatedCode :
      (binaryFormulaCode instantiatedFormula).length <=
        termRowsResidualInstantiatedFormulaCodePolynomial bitBound := by
    have htail := binaryFormulaCode_and_length_le_local equalityFormula
      rowsFormula
    have hfull := binaryFormulaCode_and_length_le_local boundFormula
      (equalityFormula ⋏ rowsFormula)
    dsimp only [instantiatedFormula]
    unfold termRowsResidualInstantiatedFormulaCodePolynomial
    omega
  have hboundValue : termValue residualRowsValuation residualTerm <
      termValue residualRowsValuation argumentSuccTerm := by
    simpa [residualTerm, argumentTerm, argumentSuccTerm, nativeAddTerm,
      termValue_shortBinaryNumeralTerm,
      FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.termValue_arithmeticAdd,
      FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.termValue_arithmeticOne]
      using (Nat.lt_succ_iff.mpr hresidual)
  have hequalityValue : termValue residualRowsValuation argumentTerm =
      termValue residualRowsValuation witnessResidualTerm := by
    simpa [argumentTerm, witnessCountTerm, residualTerm, witnessResidualTerm,
      nativeAddTerm, termValue_shortBinaryNumeralTerm,
      FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.termValue_arithmeticAdd]
      using hequality
  let boundCertificate := nativeLtCertificate residualTerm argumentSuccTerm
    hboundValue
  let equalityCertificate := nativeEqCertificate argumentTerm
    witnessResidualTerm hequalityValue
  let rowsCertificate :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 residual (‘1’ : ValuationTerm) residualTerm
      (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.termValue_arithmeticOne
        residualRowsValuation)
      (by simp [residualTerm, termValue_shortBinaryNumeralTerm]) hrows
  have hboundResource :
      hybridFormulaStructuralPayloadBound boundCertificate <= boundResource :=
    termRowsNativeLtCertificate_structuralPayloadBound_le_fixed residualTerm
      argumentSuccTerm hboundValue bitBound hresidualClosed
      hargumentSuccClosed hresidualTermCode hargumentSuccCode
  have hequalityResource :
      hybridFormulaStructuralPayloadBound equalityCertificate <=
        equalityResource :=
    termRowsNativeEqCertificate_structuralPayloadBound_le_fixed argumentTerm
      witnessResidualTerm hequalityValue bitBound hargumentClosed
      hwitnessResidualClosed hargumentTermCode hwitnessResidualCode
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 residual numericBound bitBound (‘1’ : ValuationTerm)
      residualTerm
      (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.termValue_arithmeticOne
        residualRowsValuation)
      (by simp [residualTerm, termValue_shortBinaryNumeralTerm]) honeClosed
      hresidualClosed hrows htableSize hwidthSize htokenCountSize
      hcurrentParserFinishSize hcurrentFinishSize hcurrentOutputCountSize
      hnextParserFinishSize hnextFinishSize hnextOutputBoundarySize
      hnextOutputCountSize honeSize hresidualSize hfirstAppendCode
      hsecondAppendCode hwidthBound htokenCountBound hnextOutputCountBound
      hnumericSize
  let equalityRowsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate rowsCertificate
  let canonicalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      boundCertificate equalityRowsCertificate
  have hequalityRowsRaw := transparentHybridConjunctionPayloadBound_le
    equalityCertificate rowsCertificate equalityResource rowsResource
    hequalityResource hrowsResource
  have hcanonicalRaw := transparentHybridConjunctionPayloadBound_le
    boundCertificate equalityRowsCertificate boundResource
    (transparentHybridConjunctionPayloadEnvelope residualRowsValuation
      equalityFormula rowsFormula equalityResource rowsResource)
    hboundResource hequalityRowsRaw
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold termRowsResidualExistsSyntaxPolynomial
    omega
  have hinstantiatedCodeLarge :
      (binaryFormulaCode instantiatedFormula).length <= syntaxResource :=
    hinstantiatedCode.trans (by
      dsimp only [syntaxResource]
      unfold termRowsResidualExistsSyntaxPolynomial
      omega)
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      residualRowsValuation boundFormula equalityFormula rowsFormula
      boundResource equalityResource rowsResource syntaxResource
      hsyntaxPositive hinstantiatedClosed hinstantiatedCodeLarge
  have hcanonical : hybridFormulaStructuralPayloadBound canonicalCertificate <=
      bodyResource := by
    exact hcanonicalRaw.trans hassembly
  let bodyCertificate : CheckedHybridValuationBoundedFormulaCertificate
      residualRowsValuation (body/[residualTerm]) :=
    .cast
      (compactFormulaTransformTermResidualWitnessBody_substitution_alignment
        tokenTable width tokenCount current next argument witnessCount
        residual).symm canonicalCertificate
  have hbodyCertificate :
      hybridFormulaStructuralPayloadBound bodyCertificate <= bodyResource := by
    change hybridFormulaStructuralPayloadBound canonicalCertificate <= _
    exact hcanonical
  have hbodyCode : (binaryFormulaCode body).length <= syntaxResource := by
    have hraw := residualExists_body_code_le body
    have houter : (binaryFormulaCode existentialFormula).length <=
        termRowsOuterSyntaxPolynomial bitBound := by
      simpa only [existentialFormula, body,
        compactFormulaTransformTermResidualExistsFormula] using
        hresidualExistsCode
    exact (hraw.trans houter).trans (by
      dsimp only [syntaxResource]
      unfold termRowsResidualExistsSyntaxPolynomial
      omega)
  have hwitnessCode : (binaryTermCode residualTerm).length <=
      syntaxResource := hresidualTermCode.trans (by
    dsimp only [syntaxResource]
    unfold termRowsResidualExistsSyntaxPolynomial
    omega)
  have hinstantiatedAlignment : body/[residualTerm] = instantiatedFormula := by
    simpa only [body, residualTerm, instantiatedFormula, boundFormula,
      equalityFormula, rowsFormula, argumentTerm, witnessCountTerm,
      argumentSuccTerm, witnessResidualTerm, nativeLtFormula,
      nativeAddTerm] using
      compactFormulaTransformTermResidualWitnessBody_substitution_alignment
        tokenTable width tokenCount current next argument witnessCount residual
  have hinstantiatedBodyCode :
      (binaryFormulaCode (body/[residualTerm])).length <= syntaxResource := by
    rw [hinstantiatedAlignment]
    exact hinstantiatedCodeLarge
  have hexistentialCode : (binaryFormulaCode existentialFormula).length <=
      syntaxResource := by
    have houter : (binaryFormulaCode existentialFormula).length <=
        termRowsOuterSyntaxPolynomial bitBound := by
      simpa only [existentialFormula, body,
        compactFormulaTransformTermResidualExistsFormula] using
        hresidualExistsCode
    exact houter.trans (by
      dsimp only [syntaxResource]
      unfold termRowsResidualExistsSyntaxPolynomial
      omega)
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext existentialFormula.freeVariables
            residualRowsValuation) <= syntaxResource := by
    have hclosed : existentialFormula.freeVariables = ∅ := by
      simpa only [existentialFormula, body,
        compactFormulaTransformTermResidualExistsFormula] using
        hresidualExistsClosed
    rw [hclosed]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hexistsRaw := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body residual bodyCertificate bodyResource hbodyCertificate
  have hexistsGeneral :=
    hybridExistsWitnessStructuralPayloadEnvelope_le_general
      residualRowsValuation body residual bodyResource syntaxResource
      hsyntaxPositive hcontext hbodyCode hwitnessCode hinstantiatedBodyCode
      hexistentialCode
  unfold compactFormulaTransformTermResidualExistsCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness body
        residual bodyCertificate) <= _
  simpa only [termRowsResidualExistsFixedPayloadPolynomial, syntaxResource,
    bodyResource, boundResource, equalityResource, rowsResource] using
      hexistsRaw.trans hexistsGeneral

#print axioms
  compactFormulaTransformTermResidualExistsCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsResidualExistsFullyFixedBounds
