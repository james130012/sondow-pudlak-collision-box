import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Uniform entry ceiling for an arbitrary open index term

The table, width, and value inputs remain canonical short numerals.  The row
index may be any term with free variables contained in `{0}`, provided its
value, binary length, and code length are bounded.  This supports native
offset expressions without replacing them by extensionally equal numerals.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives

def fixedWidthOpenIndexShortNumeralAtTermCodeCeiling
    (bitBound indexCodeBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let productCode := indexCodeBound + numeralCode +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let leftIndexCode := 2 * productCode +
    (binaryTermCode (&0 : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add
  numeralCode + indexCodeBound + leftIndexCode + 2 * numeralCode +
    (binaryTermCode fixedWidthRightBitIndexTerm).length +
    2 * numeralCode + 1

def fixedWidthOpenIndexShortNumeralAtTermCoordinate
    (numericBound bitBound indexCodeBound : Nat) : Nat :=
  numericBound + bitBound +
    fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound indexCodeBound +
    1

theorem
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermStructuralPayloadPolynomial_le_uniform
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm)
    (numericBound bitBound indexCodeBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <= indexCodeBound)
    (hindex : indexTerm.freeVariables ⊆ {0}) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value) <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound
            bitBound indexCodeBound)) := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate := fixedWidthOpenIndexShortNumeralAtTermCoordinate
    numericBound bitBound indexCodeBound
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode := by
    exact binaryNumeralTerm_code_length_le_envelope table bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode := by
    exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hvalueCode : (binaryTermCode valueTerm).length <= numeralCode := by
    exact binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
  have hproductCode :
      (binaryTermCode productTerm).length <=
        indexCodeBound + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    have hraw := paMulTerm_code_length_le indexTerm widthTerm
    simpa only [productTerm, fixedWidthIndexWidthTerm] using
      hraw.trans (by omega)
  have hshiftedProductCode :
      (binaryTermCode (Rew.shift productTerm)).length <=
        2 * (indexCodeBound + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) :=
    (binaryTermCode_shift_length_le productTerm).trans
      (Nat.mul_le_mul_left 2 hproductCode)
  have hleftIndexCodeRaw := paAddTerm_code_length_le
    (Rew.shift productTerm) (&0 : ValuationTerm)
  have hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
      2 * (indexCodeBound + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) +
        (binaryTermCode (&0 : ValuationTerm)).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    unfold fixedWidthLeftBitIndexTerm
    simpa only [productTerm] using hleftIndexCodeRaw.trans (by omega)
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
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            indexCodeBound /\
      indexCodeBound <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            indexCodeBound /\
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            indexCodeBound /\
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            indexCodeBound /\
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            indexCodeBound /\
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            indexCodeBound := by
    unfold fixedWidthOpenIndexShortNumeralAtTermCodeCeiling
    dsimp only [numeralCode]
    constructor
    · omega
    constructor
    · omega
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
          fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · exact hindexValue.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · exact hvaluation.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      htableSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · exact hindexSize.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · simpa only [valueTerm, termValue_shortBinaryNumeralTerm] using
      hvalueSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · exact htermCodes.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · exact htermCodes.2.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
    exact htermCodes.2.2.2.2.1.trans (by omega)
  · exact htermCodes.2.2.2.2.2.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · exact htableCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))
  · exact hwidthCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))
  · exact hindexCode.trans (htermCodes.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))
  · exact hvalueCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty table
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · exact hindex
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value

theorem
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm)
    (numericBound bitBound indexCodeBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <= indexCodeBound)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value) :
    let resource :=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound
            bitBound indexCodeBound))
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value) <= resource ∧
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value))).length <= resource := by
  let resource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
        (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound
          bitBound indexCodeBound))
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hentry)
  have hresource :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm table)
            (shortBinaryNumeralTerm width) indexTerm
            (shortBinaryNumeralTerm value) <= resource := by
    dsimp only [resource]
    exact
      compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermStructuralPayloadPolynomial_le_uniform
        valuation table width value indexTerm numericBound bitBound
        indexCodeBound hwidthValue hindexValue hvaluation htableSize
        hwidthSize hindexSize hvalueSize hindexCode hindex
  have hopen :
      hybridFormulaStructuralPayloadBound certificate <=
        compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm table)
            (shortBinaryNumeralTerm width) indexTerm
            (shortBinaryNumeralTerm value) := by
    dsimp only [certificate]
    exact
      compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value)
          (shortBinaryNumeralTerm_freeVariables_eq_empty table)
          (shortBinaryNumeralTerm_freeVariables_eq_empty width) hindex
          (shortBinaryNumeralTerm_freeVariables_eq_empty value) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hentry)
  have hpayload : hybridFormulaStructuralPayloadBound certificate <=
      resource := hopen.trans hresource
  have hcodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  have hcode :
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value))).length <= resource := by
    simpa only [certificate] using hcodeRaw.trans hpayload
  exact ⟨hresource, hcode⟩

#print axioms
  compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermStructuralPayloadPolynomial_le_uniform
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform

end FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
