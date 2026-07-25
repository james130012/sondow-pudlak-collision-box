import integration.FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-!
# Uniform direct compiler for a closed additive boundary table

The two endpoint inequalities and two endpoint table entries are compiled by
their checked atomic/fixed-width certificates.  The row condition uses the
uniform direct finite-universal compiler.  The five proofs are then assembled
under the empty PA context and cast back to the original closed predicate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveBoundaryTableDirectCompiler
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectFixedPolynomialBounds
open FoundationCompactSyntaxTransformationCodeBounds

private abbrev boundaryZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

theorem compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
    (tokenCount partCount start finish boundaryTable : Nat) :
    (compactAdditiveBoundaryTableClosedFormula tokenCount partCount start finish
      boundaryTable).freeVariables = ∅ := by
  unfold compactAdditiveBoundaryTableClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty partCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty start
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty finish
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable

theorem compactAdditiveBoundaryTableExplicitFormula_freeVariables_eq_empty
    (tokenCount partCount start finish boundaryTable : Nat) :
    (compactAdditiveBoundaryTableExplicitFormula tokenCount partCount start
      finish boundaryTable).freeVariables = ∅ := by
  rw [← compactAdditiveBoundaryTableClosedFormula_alignment]
  exact compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
    tokenCount partCount start finish boundaryTable

theorem compactAdditiveBoundaryTableUniversalFormula_freeVariables_eq_empty
    (tokenCount partCount boundaryTable : Nat) :
    ((compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm partCount)).freeVariables = ∅ := by
  unfold Semiformula.ballLT
  rw [LO.FirstOrder.Semiformula.ball_eq]
  rw [LO.FirstOrder.Semiformula.freeVariables_all]
  simp only [LO.FirstOrder.Semiformula.freeVariables_imp]
  rw [compactAdditiveBoundaryTableRowBody_freeVariables_eq_empty]
  simp
  exact bShift_freeVariables_eq_empty_of_empty _
    (shortBinaryNumeralTerm_freeVariables_eq_empty partCount)

def boundaryEndpointEntryInputTermCodeCeiling (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (unaryNumeralTerm 0)).length + 1

def boundaryEndpointEntryTermCodeCeiling (bitBound : Nat) : Nat :=
  16 * (boundaryEndpointEntryInputTermCodeCeiling bitBound +
    (binaryTermCode (&0 : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add +
    binaryFunctionTermCodeOverhead Language.Mul.mul + 1)

def boundaryEndpointEntryCoordinate
    (numericBound bitBound : Nat) : Nat :=
  numericBound + bitBound + boundaryEndpointEntryTermCodeCeiling bitBound + 1

def boundaryEndpointEntryScale (numericBound bitBound : Nat) : Nat :=
  fixedWidthOpenIndexAtomicUniformCoordinateCeiling
    (boundaryEndpointEntryCoordinate numericBound bitBound)

theorem boundaryEndpointAtomicCoordinateScale_le_fixed
    (table width value numericBound bitBound : Nat)
    (indexTerm : ValuationTerm)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue boundaryZeroValuation indexTerm <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue boundaryZeroValuation indexTerm) <=
      bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      boundaryEndpointEntryInputTermCodeCeiling bitBound) :
    fixedWidthOpenIndexAtomicCoordinateScale boundaryZeroValuation
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value) <=
      boundaryEndpointEntryScale numericBound bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate := boundaryEndpointEntryCoordinate numericBound bitBound
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope table bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hvalueCode : (binaryTermCode valueTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
  let inputCode := boundaryEndpointEntryInputTermCodeCeiling bitBound
  have hnumeralInput : numeralCode <= inputCode := by
    unfold inputCode boundaryEndpointEntryInputTermCodeCeiling
    omega
  have hproductCode : (binaryTermCode productTerm).length <=
      2 * inputCode + binaryFunctionTermCodeOverhead Language.Mul.mul := by
    have hraw := paMulTerm_code_length_le indexTerm widthTerm
    simpa only [productTerm, fixedWidthIndexWidthTerm] using
      hraw.trans (by omega)
  have hshiftedProductCode :
      (binaryTermCode (Rew.shift productTerm)).length <=
        2 * (2 * inputCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) :=
    (binaryTermCode_shift_length_le productTerm).trans
      (Nat.mul_le_mul_left 2 hproductCode)
  have hleftIndexCodeRaw := paAddTerm_code_length_le
    (Rew.shift productTerm) (&0 : ValuationTerm)
  have hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
        2 * (2 * inputCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) +
        (binaryTermCode (&0 : ValuationTerm)).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    unfold fixedWidthLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift productTerm) (&0 : ValuationTerm))).length <= _
    exact hleftIndexCodeRaw.trans (by omega)
  have hleftValueCode :
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <= 2 * numeralCode := by
    unfold fixedWidthLeftBitValueTerm
    exact (binaryTermCode_shift_length_le tableTerm).trans
      (Nat.mul_le_mul_left 2 htableCode)
  have hrightValueCode :
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <= 2 * numeralCode := by
    unfold fixedWidthRightBitValueTerm
    exact (binaryTermCode_shift_length_le valueTerm).trans
      (Nat.mul_le_mul_left 2 hvalueCode)
  have htermCeilings :
      numeralCode <= boundaryEndpointEntryTermCodeCeiling bitBound /\
      (binaryTermCode (&0 : ValuationTerm)).length <=
        boundaryEndpointEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
        boundaryEndpointEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
        boundaryEndpointEntryTermCodeCeiling bitBound /\
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
        boundaryEndpointEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
        boundaryEndpointEntryTermCodeCeiling bitBound := by
    unfold boundaryEndpointEntryTermCodeCeiling
    dsimp only [numeralCode, inputCode]
    constructor
    · omega
    constructor
    · omega
    constructor
    · exact hleftIndexCode.trans (by omega)
    constructor
    · exact hleftValueCode.trans (by omega)
    constructor
    · unfold fixedWidthRightBitIndexTerm
      omega
    · exact hrightValueCode.trans (by omega)
  apply fixedWidthOpenIndexAtomicCoordinateScale_le_uniformCeiling
    boundaryZeroValuation tableTerm widthTerm indexTerm valueTerm coordinate
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthValue.trans (by
        unfold coordinate boundaryEndpointEntryCoordinate
        omega)
  · exact hindexValue.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega)
  · change 0 <= coordinate
    exact Nat.zero_le _
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      htableSize.trans (by
        unfold coordinate boundaryEndpointEntryCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthSize.trans (by
        unfold coordinate boundaryEndpointEntryCoordinate
        omega)
  · exact hindexSize.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega)
  · simpa only [valueTerm, termValue_shortBinaryNumeralTerm] using
      hvalueSize.trans (by
        unfold coordinate boundaryEndpointEntryCoordinate
        omega)
  · exact htermCeilings.2.2.1.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega)
  · exact htermCeilings.2.2.2.1.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega)
  · exact htermCeilings.2.2.2.2.1.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega)
  · exact htermCeilings.2.2.2.2.2.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega)
  · exact htableCode.trans (htermCeilings.1.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega))
  · exact hwidthCode.trans (htermCeilings.1.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega))
  · exact hindexCode.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
        boundaryEndpointEntryTermCodeCeiling
      omega)
  · exact hvalueCode.trans (htermCeilings.1.trans (by
      unfold coordinate boundaryEndpointEntryCoordinate
      omega))

def compactAdditiveBoundaryTableUniformDirectPayloadEnvelope
    (tokenCount partCount start finish boundaryTable numericBound bitBound :
      Nat) : Nat :=
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount)
    (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm partCount)
  let startResource := boundaryClosedLeStructuralPayloadEnvelope
    boundaryZeroValuation start tokenCount
  let finishResource := boundaryClosedLeStructuralPayloadEnvelope
    boundaryZeroValuation finish tokenCount
  let scale := boundaryEndpointEntryScale numericBound bitBound
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let universalResource :=
    compactAdditiveBoundaryTableRowsUniformDirectUniversalResource tokenCount
      partCount boundaryTable numericBound bitBound
  let finishEntryUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
      finishEntryFormula universalFormula entryResource universalResource
  let startEntryTailResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
      startEntryFormula (finishEntryFormula ⋏ universalFormula) entryResource
      finishEntryUniversalResource
  let finishTailResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
      finishFormula
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula))
      finishResource startEntryTailResource
  transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
    startFormula
    (finishFormula ⋏
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula)))
    startResource finishTailResource

noncomputable def compileCompactAdditiveBoundaryTableUniformDirectClosedContext
    (tokenCount partCount start finish boundaryTable numericBound bitBound :
      Nat)
    (hstartBound : start <= tokenCount)
    (hfinishBound : finish <= tokenCount)
    (hstartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 start)
    (hfinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount partCount finish)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveBoundaryTableClosedFormula tokenCount partCount start
        finish boundaryTable) := by
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount)
    (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm partCount)
  let startCertificate := closedLeCertificate boundaryZeroValuation start
    tokenCount hstartBound
  let finishCertificate := closedLeCertificate boundaryZeroValuation finish
    tokenCount hfinishBound
  let startEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      boundaryZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm start) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm] using hstartEntry)
  let finishEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      boundaryZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm partCount)
      (shortBinaryNumeralTerm finish) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hfinishEntry)
  let universalRaw :=
    compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext
      tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
      hpartCount htableSize hnumericSize
  have huniversalContext : (∅ : Finset ValuationFormula) =
      valuationContext universalFormula.freeVariables boundaryZeroValuation := by
    rw [show universalFormula.freeVariables = ∅ by
      simpa only [universalFormula] using
        compactAdditiveBoundaryTableUniversalFormula_freeVariables_eq_empty
          tokenCount partCount boundaryTable]
    simp [valuationContext]
  let universalProof :=
    CertifiedPAContextProof.castContext huniversalContext universalRaw
  let finishEntryUniversal := compileDirectConjunction
    finishEntryCertificate.compile universalProof
  let startEntryTail := compileDirectConjunction
    startEntryCertificate.compile finishEntryUniversal
  let finishTail := compileDirectConjunction finishCertificate.compile
    startEntryTail
  let parts := compileDirectConjunction startCertificate.compile finishTail
  have hpartsFormula :
      (startFormula ⋏
        (finishFormula ⋏
          (startEntryFormula ⋏
            (finishEntryFormula ⋏ universalFormula)))) =
        compactAdditiveBoundaryTableExplicitFormula tokenCount partCount start
          finish boundaryTable := by
    rfl
  let explicitParts := CertifiedPAContextProof.cast hpartsFormula parts
  have hpartsContext :
      valuationContext
          (startFormula ⋏
            (finishFormula ⋏
              (startEntryFormula ⋏
                (finishEntryFormula ⋏ universalFormula)))).freeVariables
          boundaryZeroValuation =
        (∅ : Finset ValuationFormula) := by
    change valuationContext
      (compactAdditiveBoundaryTableExplicitFormula tokenCount partCount start
        finish boundaryTable).freeVariables boundaryZeroValuation = ∅
    rw [compactAdditiveBoundaryTableExplicitFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let closedParts :=
    CertifiedPAContextProof.castContext hpartsContext explicitParts
  exact CertifiedPAContextProof.cast
    (compactAdditiveBoundaryTableClosedFormula_alignment tokenCount partCount
      start finish boundaryTable).symm closedParts

theorem
    compileCompactAdditiveBoundaryTableUniformDirectClosedContext_payloadLength_le
    (tokenCount partCount start finish boundaryTable numericBound bitBound :
      Nat)
    (hstartBound : start <= tokenCount)
    (hfinishBound : finish <= tokenCount)
    (hstartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 start)
    (hfinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount partCount finish)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveBoundaryTableUniformDirectClosedContext tokenCount
      partCount start finish boundaryTable numericBound bitBound hstartBound
      hfinishBound hstartEntry hfinishEntry rows htokenCount hpartCount
      htableSize hnumericSize).payloadLength <=
      compactAdditiveBoundaryTableUniformDirectPayloadEnvelope tokenCount
        partCount start finish boundaryTable numericBound bitBound := by
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startIndexTerm := unaryNumeralTerm 0
  let finishIndexTerm := shortBinaryNumeralTerm partCount
  let startValueTerm := shortBinaryNumeralTerm start
  let finishValueTerm := shortBinaryNumeralTerm finish
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula tableTerm
    widthTerm startIndexTerm startValueTerm
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula tableTerm
    widthTerm finishIndexTerm finishValueTerm
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm partCount)
  let startCertificate := closedLeCertificate boundaryZeroValuation start
    tokenCount hstartBound
  let finishCertificate := closedLeCertificate boundaryZeroValuation finish
    tokenCount hfinishBound
  have hstartEntryAtTerms : CompactFixedWidthEntry
      (termValue boundaryZeroValuation tableTerm)
      (termValue boundaryZeroValuation widthTerm)
      (termValue boundaryZeroValuation startIndexTerm)
      (termValue boundaryZeroValuation startValueTerm) := by
    simpa only [tableTerm, widthTerm, startIndexTerm, startValueTerm,
      termValue_shortBinaryNumeralTerm, termValue_unaryNumeralTerm] using
      hstartEntry
  have hfinishEntryAtTerms : CompactFixedWidthEntry
      (termValue boundaryZeroValuation tableTerm)
      (termValue boundaryZeroValuation widthTerm)
      (termValue boundaryZeroValuation finishIndexTerm)
      (termValue boundaryZeroValuation finishValueTerm) := by
    simpa only [tableTerm, widthTerm, finishIndexTerm, finishValueTerm,
      termValue_shortBinaryNumeralTerm] using hfinishEntry
  let startEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      boundaryZeroValuation tableTerm widthTerm startIndexTerm startValueTerm
      hstartEntryAtTerms
  let finishEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      boundaryZeroValuation tableTerm widthTerm finishIndexTerm finishValueTerm
      hfinishEntryAtTerms
  let universalRaw :=
    compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext
      tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
      hpartCount htableSize hnumericSize
  have huniversalContext : (∅ : Finset ValuationFormula) =
      valuationContext universalFormula.freeVariables boundaryZeroValuation := by
    rw [show universalFormula.freeVariables = ∅ by
      simpa only [universalFormula] using
        compactAdditiveBoundaryTableUniversalFormula_freeVariables_eq_empty
          tokenCount partCount boundaryTable]
    simp [valuationContext]
  let universalProof :=
    CertifiedPAContextProof.castContext huniversalContext universalRaw
  let startResource := boundaryClosedLeStructuralPayloadEnvelope
    boundaryZeroValuation start tokenCount
  let finishResource := boundaryClosedLeStructuralPayloadEnvelope
    boundaryZeroValuation finish tokenCount
  let scale := boundaryEndpointEntryScale numericBound bitBound
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let universalResource :=
    compactAdditiveBoundaryTableRowsUniformDirectUniversalResource tokenCount
      partCount boundaryTable numericBound bitBound
  have hstart : startCertificate.compile.payloadLength <= startResource :=
    (compile_payloadLength_le_structuralPayloadBound startCertificate).trans
      (closedLeCertificate_structuralPayloadBound_le_transparent
        boundaryZeroValuation start tokenCount hstartBound)
  have hfinish : finishCertificate.compile.payloadLength <= finishResource :=
    (compile_payloadLength_le_structuralPayloadBound finishCertificate).trans
      (closedLeCertificate_structuralPayloadBound_le_transparent
        boundaryZeroValuation finish tokenCount hfinishBound)
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstartIndexEmpty : startIndexTerm.freeVariables = ∅ := by
    simp [startIndexTerm, unaryNumeralTerm,
      LO.FirstOrder.Semiterm.Operator.operator]
  have hfinishIndexEmpty : finishIndexTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty partCount
  have hstartIndex : startIndexTerm.freeVariables ⊆ {0} := by
    rw [hstartIndexEmpty]
    simp
  have hfinishIndex : finishIndexTerm.freeVariables ⊆ {0} := by
    rw [hfinishIndexEmpty]
    simp
  have hstartValue : startValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty start
  have hfinishValue : finishValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty finish
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hpartSize : Nat.size partCount <= bitBound :=
    (Nat.size_le_size hpartCount).trans hnumericSize
  have hstartSize : Nat.size start <= bitBound :=
    (Nat.size_le_size (hstartBound.trans htokenCount)).trans hnumericSize
  have hfinishSize : Nat.size finish <= bitBound :=
    (Nat.size_le_size (hfinishBound.trans htokenCount)).trans hnumericSize
  have hstartIndexValue :
      termValue boundaryZeroValuation startIndexTerm <= numericBound := by
    simp only [startIndexTerm, termValue_unaryNumeralTerm]
    exact Nat.zero_le _
  have hstartIndexSize :
      Nat.size (termValue boundaryZeroValuation startIndexTerm) <=
        bitBound := by
    simp only [startIndexTerm, termValue_unaryNumeralTerm, Nat.size_zero]
    exact Nat.zero_le _
  have hstartIndexCode : (binaryTermCode startIndexTerm).length <=
      boundaryEndpointEntryInputTermCodeCeiling bitBound := by
    unfold boundaryEndpointEntryInputTermCodeCeiling
    dsimp only [startIndexTerm]
    omega
  have hfinishIndexCode : (binaryTermCode finishIndexTerm).length <=
      boundaryEndpointEntryInputTermCodeCeiling bitBound := by
    have hraw := binaryNumeralTerm_code_length_le_envelope partCount bitBound
      hpartSize
    dsimp only [finishIndexTerm]
    exact hraw.trans (by
      unfold boundaryEndpointEntryInputTermCodeCeiling
      omega)
  have hfinishIndexValue :
      termValue boundaryZeroValuation finishIndexTerm <= numericBound := by
    simpa only [finishIndexTerm, termValue_shortBinaryNumeralTerm] using
      hpartCount
  have hfinishIndexSize :
      Nat.size (termValue boundaryZeroValuation finishIndexTerm) <=
        bitBound := by
    simpa only [finishIndexTerm, termValue_shortBinaryNumeralTerm] using
      hpartSize
  have hstartScale :
      fixedWidthOpenIndexAtomicCoordinateScale boundaryZeroValuation tableTerm
          widthTerm startIndexTerm startValueTerm <= scale := by
    simpa only [tableTerm, widthTerm, startValueTerm, scale] using
      (boundaryEndpointAtomicCoordinateScale_le_fixed boundaryTable tokenCount
        start numericBound bitBound startIndexTerm htokenCount
        hstartIndexValue htableSize htokenSize hstartIndexSize hstartSize
        hstartIndexCode)
  have hfinishScale :
      fixedWidthOpenIndexAtomicCoordinateScale boundaryZeroValuation tableTerm
          widthTerm finishIndexTerm finishValueTerm <= scale := by
    simpa only [tableTerm, widthTerm, finishValueTerm, scale] using
      (boundaryEndpointAtomicCoordinateScale_le_fixed boundaryTable tokenCount
        finish numericBound bitBound finishIndexTerm htokenCount
        hfinishIndexValue
        htableSize htokenSize hfinishIndexSize hfinishSize hfinishIndexCode)
  have hstartEntryOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      boundaryZeroValuation tableTerm widthTerm startIndexTerm startValueTerm
      htable hwidth hstartIndex hstartValue hstartEntryAtTerms
  have hstartEntryFixed :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      boundaryZeroValuation tableTerm widthTerm startIndexTerm startValueTerm
      scale hstartScale htable hwidth hstartIndex hstartValue
  have hstartEntryStructural := hstartEntryOpen.trans hstartEntryFixed
  have hstartEntry : startEntryCertificate.compile.payloadLength <=
      entryResource :=
    (compile_payloadLength_le_structuralPayloadBound
      startEntryCertificate).trans hstartEntryStructural
  have hfinishEntryOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      boundaryZeroValuation tableTerm widthTerm finishIndexTerm finishValueTerm
      htable hwidth hfinishIndex hfinishValue hfinishEntryAtTerms
  have hfinishEntryFixed :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      boundaryZeroValuation tableTerm widthTerm finishIndexTerm finishValueTerm
      scale hfinishScale htable hwidth hfinishIndex hfinishValue
  have hfinishEntryStructural := hfinishEntryOpen.trans hfinishEntryFixed
  have hfinishEntry : finishEntryCertificate.compile.payloadLength <=
      entryResource :=
    (compile_payloadLength_le_structuralPayloadBound
      finishEntryCertificate).trans hfinishEntryStructural
  have huniversalRaw : universalRaw.payloadLength <= universalResource :=
    compileCompactAdditiveBoundaryTableRowsUniformDirectUniversalContext_payloadLength_le
      tokenCount partCount boundaryTable numericBound bitBound rows htokenCount
      hpartCount htableSize hnumericSize
  have huniversal : universalProof.payloadLength <= universalResource := by
    dsimp only [universalProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact huniversalRaw
  let finishEntryUniversal := compileDirectConjunction
    finishEntryCertificate.compile universalProof
  let finishEntryUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
      finishEntryFormula universalFormula entryResource universalResource
  have hfinishEntryUniversal : finishEntryUniversal.payloadLength <=
      finishEntryUniversalResource :=
    compileDirectConjunction_payloadLength_le finishEntryCertificate.compile
      universalProof entryResource universalResource hfinishEntry huniversal
  let startEntryTail := compileDirectConjunction
    startEntryCertificate.compile finishEntryUniversal
  let startEntryTailResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
      startEntryFormula (finishEntryFormula ⋏ universalFormula) entryResource
      finishEntryUniversalResource
  have hstartEntryTail : startEntryTail.payloadLength <=
      startEntryTailResource :=
    compileDirectConjunction_payloadLength_le startEntryCertificate.compile
      finishEntryUniversal entryResource finishEntryUniversalResource
      hstartEntry hfinishEntryUniversal
  let finishTail := compileDirectConjunction finishCertificate.compile
    startEntryTail
  let finishTailResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
      finishFormula
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula))
      finishResource startEntryTailResource
  have hfinishTail : finishTail.payloadLength <= finishTailResource :=
    compileDirectConjunction_payloadLength_le finishCertificate.compile
      startEntryTail finishResource startEntryTailResource hfinish
      hstartEntryTail
  let parts := compileDirectConjunction startCertificate.compile finishTail
  have hparts : parts.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope boundaryZeroValuation
        startFormula
        (finishFormula ⋏
          (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula)))
        startResource finishTailResource :=
    compileDirectConjunction_payloadLength_le startCertificate.compile
      finishTail startResource finishTailResource hstart hfinishTail
  have hpartsFormula :
      (startFormula ⋏
        (finishFormula ⋏
          (startEntryFormula ⋏
            (finishEntryFormula ⋏ universalFormula)))) =
        compactAdditiveBoundaryTableExplicitFormula tokenCount partCount start
          finish boundaryTable := by
    rfl
  let explicitParts := CertifiedPAContextProof.cast hpartsFormula parts
  have hpartsContext :
      valuationContext
          (startFormula ⋏
            (finishFormula ⋏
              (startEntryFormula ⋏
                (finishEntryFormula ⋏ universalFormula)))).freeVariables
          boundaryZeroValuation =
        (∅ : Finset ValuationFormula) := by
    change valuationContext
      (compactAdditiveBoundaryTableExplicitFormula tokenCount partCount start
        finish boundaryTable).freeVariables boundaryZeroValuation = ∅
    rw [compactAdditiveBoundaryTableExplicitFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let closedParts :=
    CertifiedPAContextProof.castContext hpartsContext explicitParts
  unfold compileCompactAdditiveBoundaryTableUniformDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength,
    CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]
  simpa only [compactAdditiveBoundaryTableUniformDirectPayloadEnvelope,
    startFormula, finishFormula, tableTerm, widthTerm, startIndexTerm,
    finishIndexTerm, startValueTerm, finishValueTerm, startEntryFormula,
    finishEntryFormula, universalFormula, startCertificate,
    finishCertificate, startEntryCertificate, finishEntryCertificate,
    universalRaw, universalProof, startResource, finishResource, scale,
    entryResource, universalResource, finishEntryUniversal,
    finishEntryUniversalResource, startEntryTail, startEntryTailResource,
    finishTail, finishTailResource, parts, hpartsFormula, explicitParts,
    hpartsContext, closedParts] using hparts

#print axioms compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveBoundaryTableUniversalFormula_freeVariables_eq_empty
#print axioms
  compileCompactAdditiveBoundaryTableUniformDirectClosedContext
#print axioms
  compileCompactAdditiveBoundaryTableUniformDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler
