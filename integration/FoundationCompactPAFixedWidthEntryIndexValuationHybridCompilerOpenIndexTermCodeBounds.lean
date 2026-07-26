import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds

/-!
# Term-code bounds for the open-index fixed-width entry compiler

This file replaces the concrete syntax of the open index by one public upper
bound on its binary term-code length.  The represented table values remain
charged only through their bit lengths.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTermCodeBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationSuccinctFiniteConsistencyTarget

def fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
    (termCodeBound bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let rowIndexCode := (binaryTermCode (&0 : ValuationTerm)).length
  let productCode := termCodeBound + numeralCode +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let leftIndexCode := 2 * productCode + rowIndexCode +
    binaryFunctionTermCodeOverhead Language.Add.add
  numeralCode + termCodeBound + leftIndexCode + 2 * numeralCode +
    (binaryTermCode fixedWidthRightBitIndexTerm).length +
    2 * numeralCode + 1

def fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
    (termCodeBound numericBound bitBound : Nat) : Nat :=
  numericBound + bitBound +
    fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling termCodeBound
      bitBound + 1

def fixedWidthOpenIndexShortNumeralAtTermCodeBoundScale
    (termCodeBound numericBound bitBound : Nat) : Nat :=
  fixedWidthOpenIndexAtomicUniformCoordinateCeiling
    (fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate termCodeBound
      numericBound bitBound)

theorem
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_termCodeBound
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm) (termCodeBound numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hindex : indexTerm.freeVariables ⊆ {0}) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value) <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexShortNumeralAtTermCodeBoundScale termCodeBound
          numericBound bitBound) := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate :=
    fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate termCodeBound
      numericBound bitBound
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode := by
    exact binaryNumeralTerm_code_length_le_envelope table bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode := by
    exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hvalueCode : (binaryTermCode valueTerm).length <= numeralCode := by
    exact binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
  have hproductCode : (binaryTermCode productTerm).length <=
      (binaryTermCode indexTerm).length + numeralCode +
        binaryFunctionTermCodeOverhead Language.Mul.mul := by
    have hraw := paMulTerm_code_length_le indexTerm widthTerm
    simpa only [productTerm, fixedWidthIndexWidthTerm] using
      hraw.trans (by omega)
  have hleftIndexCodeRaw := paAddTerm_code_length_le
    (Rew.shift productTerm) (&0 : ValuationTerm)
  have hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
      2 * ((binaryTermCode indexTerm).length + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) +
        (binaryTermCode (&0 : ValuationTerm)).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    unfold fixedWidthLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift productTerm) (&0 : ValuationTerm))).length <= _
    exact hleftIndexCodeRaw.trans (by
      have hshiftedProductCode := binaryTermCode_shift_length_le productTerm
      omega)
  have hleftValueCode :
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthLeftBitValueTerm
    exact (binaryTermCode_shift_length_le tableTerm).trans
      (Nat.mul_le_mul_left 2 htableCode)
  have hrightValueCode :
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthRightBitValueTerm
    exact (binaryTermCode_shift_length_le valueTerm).trans
      (Nat.mul_le_mul_left 2 hvalueCode)
  have htermCodes :
      numeralCode <=
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
            termCodeBound bitBound /\
      (binaryTermCode indexTerm).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
            termCodeBound bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
            termCodeBound bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
            termCodeBound bitBound /\
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
            termCodeBound bitBound /\
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
            termCodeBound bitBound := by
    unfold fixedWidthOpenIndexShortNumeralAtTermCodeBoundCodeCeiling
    dsimp only [numeralCode]
    constructor
    · omega
    constructor
    · exact hindexCode.trans (by omega)
    constructor
    · exact hleftIndexCode.trans (by omega)
    constructor
    · exact hleftValueCode.trans (by omega)
    constructor
    · omega
    · exact hrightValueCode.trans (by omega)
  apply
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_uniformCeiling
      valuation tableTerm widthTerm indexTerm valueTerm coordinate
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthValue.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
        omega)
  · exact hindexValue.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · exact hvaluation.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      htableSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
        omega)
  · exact hindexSize.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · simpa only [valueTerm, termValue_shortBinaryNumeralTerm] using
      hvalueSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
        omega)
  · exact htermCodes.2.2.1.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · exact htermCodes.2.2.2.1.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · exact htermCodes.2.2.2.2.1.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · exact htermCodes.2.2.2.2.2.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · exact htableCode.trans (htermCodes.1.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega))
  · exact hwidthCode.trans (htermCodes.1.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega))
  · exact htermCodes.2.1.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega)
  · exact hvalueCode.trans (htermCodes.1.trans (by
      unfold coordinate
        fixedWidthOpenIndexShortNumeralAtTermCodeBoundCoordinate
      omega))
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty table
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · exact hindex
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value

theorem
    compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_termCodeBound
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm) (termCodeBound numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hentry)) <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexShortNumeralAtTermCodeBoundScale termCodeBound
          numericBound bitBound) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let hentryAtTerms : CompactFixedWidthEntry
      (termValue valuation tableTerm) (termValue valuation widthTerm)
      (termValue valuation indexTerm) (termValue valuation valueTerm) := by
    simpa only [tableTerm, widthTerm, valueTerm,
      termValue_shortBinaryNumeralTerm] using hentry
  have hopen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty table)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width) hindex
      (shortBinaryNumeralTerm_freeVariables_eq_empty value) hentryAtTerms
  have huniform :=
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_termCodeBound
      valuation table width value indexTerm termCodeBound numericBound bitBound
      hwidthValue hindexValue hvaluation htableSize hwidthSize hindexSize
      hvalueSize hindexCode hindex
  simpa only [tableTerm, widthTerm, valueTerm, hentryAtTerms] using
    hopen.trans huniform

#print axioms
  compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_termCodeBound
#print axioms
  compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_termCodeBound

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTermCodeBounds
