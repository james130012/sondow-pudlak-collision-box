import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds

/-!
# Uniform ceilings for the open-index fixed-width entry compiler

The fixed compiler is parameterized by one scalar containing every numeric and
syntactic coordinate used by an entry proof.  This file proves that the final
payload polynomial is monotone in that scalar and supplies a reusable ceiling
lemma for the raw coordinate sum.  These lemmas support coordinate-wise
bit-width bounds; they do not enumerate the represented value range.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds

open FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationSuccinctFiniteConsistencyTarget

/-- A common ceiling for the sixteen nonconstant summands in the open-index
coordinate scalar. -/
def fixedWidthOpenIndexAtomicUniformCoordinateCeiling (coordinate : Nat) : Nat :=
  17 * coordinate + 2

theorem fixedWidthOpenIndexAtomicCoordinateScale_le_uniformCeiling
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (coordinate : Nat)
    (hwidthValue : termValue valuation widthTerm <= coordinate)
    (hindexValue : termValue valuation indexTerm <= coordinate)
    (hvaluation : valuation 0 <= coordinate)
    (htableSize : Nat.size (termValue valuation tableTerm) <= coordinate)
    (hwidthSize : Nat.size (termValue valuation widthTerm) <= coordinate)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= coordinate)
    (hvalueSize : Nat.size (termValue valuation valueTerm) <= coordinate)
    (hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <= coordinate)
    (hleftValueCode :
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <= coordinate)
    (hrightIndexCode :
      (binaryTermCode fixedWidthRightBitIndexTerm).length <= coordinate)
    (hrightValueCode :
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <= coordinate)
    (htableCode : (binaryTermCode tableTerm).length <= coordinate)
    (hwidthCode : (binaryTermCode widthTerm).length <= coordinate)
    (hindexCode : (binaryTermCode indexTerm).length <= coordinate)
    (hvalueCode : (binaryTermCode valueTerm).length <= coordinate) :
    fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm <=
      fixedWidthOpenIndexAtomicUniformCoordinateCeiling coordinate := by
  unfold fixedWidthOpenIndexAtomicCoordinateScale
    fixedWidthOpenIndexPublicCoordinateScale
    fixedWidthOpenIndexAtomicUniformCoordinateCeiling
  omega

theorem
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_uniformCeiling
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (coordinate : Nat)
    (hwidthValue : termValue valuation widthTerm <= coordinate)
    (hindexValue : termValue valuation indexTerm <= coordinate)
    (hvaluation : valuation 0 <= coordinate)
    (htableSize : Nat.size (termValue valuation tableTerm) <= coordinate)
    (hwidthSize : Nat.size (termValue valuation widthTerm) <= coordinate)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= coordinate)
    (hvalueSize : Nat.size (termValue valuation valueTerm) <= coordinate)
    (hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <= coordinate)
    (hleftValueCode :
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <= coordinate)
    (hrightIndexCode :
      (binaryTermCode fixedWidthRightBitIndexTerm).length <= coordinate)
    (hrightValueCode :
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <= coordinate)
    (htableCode : (binaryTermCode tableTerm).length <= coordinate)
    (hwidthCode : (binaryTermCode widthTerm).length <= coordinate)
    (hindexCode : (binaryTermCode indexTerm).length <= coordinate)
    (hvalueCode : (binaryTermCode valueTerm).length <= coordinate)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling coordinate) := by
  apply
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm indexTerm valueTerm
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling coordinate)
  · exact fixedWidthOpenIndexAtomicCoordinateScale_le_uniformCeiling valuation
      tableTerm widthTerm indexTerm valueTerm coordinate hwidthValue hindexValue
      hvaluation htableSize hwidthSize hindexSize hvalueSize hleftIndexCode
      hleftValueCode hrightIndexCode hrightValueCode htableCode hwidthCode
      hindexCode hvalueCode
  · exact htable
  · exact hwidth
  · exact hindex
  · exact hvalue

/-- A proof-independent code ceiling for the standard open row index `&0` and
three short-binary numeral inputs. -/
def fixedWidthOpenIndexShortNumeralTermCodeCeiling (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let indexCode := (binaryTermCode (&0 : ValuationTerm)).length
  let productCode := indexCode + numeralCode +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let leftIndexCode := 2 * productCode + indexCode +
    binaryFunctionTermCodeOverhead Language.Add.add
  numeralCode + indexCode + leftIndexCode + 2 * numeralCode +
    (binaryTermCode fixedWidthRightBitIndexTerm).length +
    2 * numeralCode + 1

def fixedWidthOpenIndexShortNumeralCoordinate
    (numericBound bitBound : Nat) : Nat :=
  numericBound + bitBound +
    fixedWidthOpenIndexShortNumeralTermCodeCeiling bitBound + 1

theorem
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsStructuralPayloadPolynomial_le_uniform
    (valuation : Nat -> Nat) (table width value : Nat)
    (numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (valuation 0) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) (&0 : ValuationTerm)
          (shortBinaryNumeralTerm value) <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralCoordinate
            numericBound bitBound)) := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let indexTerm : ValuationTerm := &0
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate := fixedWidthOpenIndexShortNumeralCoordinate
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
  have hshiftedProductCode :
      (binaryTermCode (Rew.shift productTerm)).length <=
        2 * ((binaryTermCode indexTerm).length + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) :=
    (binaryTermCode_shift_length_le productTerm).trans
      (Nat.mul_le_mul_left 2 hproductCode)
  have hleftIndexCodeRaw := paAddTerm_code_length_le
    (Rew.shift productTerm) indexTerm
  have hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
      2 * ((binaryTermCode indexTerm).length + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) +
        (binaryTermCode indexTerm).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    unfold fixedWidthLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift productTerm) indexTerm)).length <= _
    exact hleftIndexCodeRaw.trans (by omega)
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
  dsimp only [indexTerm] at hleftIndexCode
  have htermCodes :
      numeralCode <= fixedWidthOpenIndexShortNumeralTermCodeCeiling bitBound /\
      (binaryTermCode indexTerm).length <=
        fixedWidthOpenIndexShortNumeralTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
        fixedWidthOpenIndexShortNumeralTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
        fixedWidthOpenIndexShortNumeralTermCodeCeiling bitBound /\
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
        fixedWidthOpenIndexShortNumeralTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
        fixedWidthOpenIndexShortNumeralTermCodeCeiling bitBound := by
    unfold fixedWidthOpenIndexShortNumeralTermCodeCeiling
    dsimp only [numeralCode, indexTerm]
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
        unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
        omega)
  · change valuation 0 <= coordinate
    exact hindexValue.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · exact hindexValue.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      htableSize.trans (by
        unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthSize.trans (by
        unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
        omega)
  · change Nat.size (valuation 0) <= coordinate
    exact hindexSize.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · simpa only [valueTerm, termValue_shortBinaryNumeralTerm] using
      hvalueSize.trans (by
        unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
        omega)
  · exact htermCodes.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · exact htermCodes.2.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · exact htermCodes.2.2.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · exact htermCodes.2.2.2.2.2.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · exact htableCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega))
  · exact hwidthCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega))
  · exact htermCodes.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega)
  · exact hvalueCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralCoordinate
      omega))
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty table
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · simp [indexTerm]
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value

theorem
    compactFixedWidthEntryAtValuationShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
    (valuation : Nat -> Nat) (table width value : Nat)
    (numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (valuation 0) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hentry : CompactFixedWidthEntry table width (valuation 0) value) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          (&0 : ValuationTerm) (shortBinaryNumeralTerm value) (by
            simpa only [termValue_shortBinaryNumeralTerm, termValue_fvar] using
              hentry)) <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralCoordinate
            numericBound bitBound)) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let indexTerm : ValuationTerm := &0
  let valueTerm := shortBinaryNumeralTerm value
  let hentryAtTerms : CompactFixedWidthEntry
      (termValue valuation tableTerm) (termValue valuation widthTerm)
      (termValue valuation indexTerm) (termValue valuation valueTerm) := by
    simpa only [tableTerm, widthTerm, indexTerm, valueTerm,
      termValue_shortBinaryNumeralTerm, termValue_fvar] using hentry
  have hopen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty table)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width) (by simp [indexTerm])
      (shortBinaryNumeralTerm_freeVariables_eq_empty value) hentryAtTerms
  have huniform :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsStructuralPayloadPolynomial_le_uniform
      valuation table width value numericBound bitBound hwidthValue hindexValue
      htableSize hwidthSize hindexSize hvalueSize
  simpa only [tableTerm, widthTerm, indexTerm, valueTerm, hentryAtTerms] using
    hopen.trans huniform

/-- A code ceiling for three short-binary numeral inputs and one fixed open
index term.  The index syntax is charged directly; no represented-value range
is enumerated. -/
def fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
    (indexTerm : ValuationTerm) (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let indexCode := (binaryTermCode indexTerm).length
  let rowIndexCode := (binaryTermCode (&0 : ValuationTerm)).length
  let productCode := indexCode + numeralCode +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let leftIndexCode := 2 * productCode + rowIndexCode +
    binaryFunctionTermCodeOverhead Language.Add.add
  numeralCode + indexCode + leftIndexCode + 2 * numeralCode +
    (binaryTermCode fixedWidthRightBitIndexTerm).length +
    2 * numeralCode + 1

def fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  numericBound + bitBound +
    fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling indexTerm bitBound + 1

theorem
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindex : indexTerm.freeVariables ⊆ {0}) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value) <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
            numericBound bitBound)) := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate := fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
    indexTerm numericBound bitBound
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
          fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
            indexTerm bitBound /\
      (binaryTermCode indexTerm).length <=
          fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
            indexTerm bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
            indexTerm bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
            indexTerm bitBound /\
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
          fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
            indexTerm bitBound /\
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
            indexTerm bitBound := by
    unfold fixedWidthOpenIndexShortNumeralAtIndexTermCodeCeiling
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
          fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        omega)
  · exact hindexValue.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · exact hvaluation.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      htableSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        omega)
  · exact hindexSize.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · simpa only [valueTerm, termValue_shortBinaryNumeralTerm] using
      hvalueSize.trans (by
        unfold coordinate
          fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        omega)
  · exact htermCodes.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · exact htermCodes.2.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · exact htermCodes.2.2.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · exact htermCodes.2.2.2.2.2.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · exact htableCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega))
  · exact hwidthCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega))
  · exact htermCodes.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega)
  · exact hvalueCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
      omega))
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty table
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · exact hindex
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value

theorem
    compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hentry)) <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
            numericBound bitBound)) := by
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
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
      valuation table width value indexTerm numericBound bitBound hwidthValue
      hindexValue hvaluation htableSize hwidthSize hindexSize hvalueSize hindex
  simpa only [tableTerm, widthTerm, valueTerm, hentryAtTerms] using
    hopen.trans huniform

theorem compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm indexTerm
      valueTerm).freeVariables ⊆ {0} := by
  intro candidate hcandidate
  unfold compactFixedWidthEntryAtValuationFormula at hcandidate
  have hsource := embeddedSubstitution_freeVariables_subset
    compactFixedWidthEntryDef.val
      ![tableTerm, widthTerm, indexTerm, valueTerm] hcandidate
  rcases Finset.mem_biUnion.mp hsource with
    ⟨coordinate, _, hcoordinate⟩
  cases coordinate using Fin.cases with
  | zero =>
      have hfalse : False := by simpa [htable] using hcoordinate
      exact hfalse.elim
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero =>
          have hfalse : False := by simpa [hwidth] using hcoordinate
          exact hfalse.elim
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero =>
              have hmember : candidate ∈ indexTerm.freeVariables := by
                simpa using hcoordinate
              exact hindex hmember
          | succ coordinate =>
              cases coordinate using Fin.cases with
              | zero =>
                  have hfalse : False := by
                    simpa [hvalue] using hcoordinate
                  exact hfalse.elim
              | succ coordinate => exact Fin.elim0 coordinate

#print axioms fixedWidthOpenIndexAtomicCoordinateScale_le_uniformCeiling
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_uniformCeiling
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexShortNumeralsStructuralPayloadPolynomial_le_uniform
#print axioms
  compactFixedWidthEntryAtValuationShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
#print axioms
  compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
#print axioms
  compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
