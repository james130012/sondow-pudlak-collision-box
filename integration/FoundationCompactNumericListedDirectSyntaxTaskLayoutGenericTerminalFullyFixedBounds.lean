import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed terminal bound for a generic syntax-task layout

The three arbitrary task fields are represented by their short binary
numerals.  The three real token-cell certificates are charged separately
and reassembled in the original right-associated conjunction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def genericTaskLayoutTerminalBitBound (bitBound : Nat) : Nat :=
  bitBound + binaryNumeralTermCodeEnvelope bitBound + 3

def genericTaskLayoutTerminalFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  3 * additiveTokenCellClosedValueFormulaCodeEnvelope
      (genericTaskLayoutTerminalBitBound bitBound) +
    2 * (binaryNatCode 4).length + 1

def genericTaskLayoutTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (genericTaskLayoutTerminalFormulaCodeEnvelope bitBound)
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (genericTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (genericTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (genericTaskLayoutTerminalBitBound bitBound))

private theorem binaryNumeralTermCodeEnvelope_ge_bit_generic
    (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem genericTaskLayout_bit_le (bitBound : Nat) :
    bitBound <= genericTaskLayoutTerminalBitBound bitBound := by
  unfold genericTaskLayoutTerminalBitBound
  omega

private theorem shortNumeral_code_le_genericTerminalEnvelope
    (value bitBound : Nat)
    (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      binaryNumeralTermCodeEnvelope
        (genericTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope value
    (genericTaskLayoutTerminalBitBound bitBound)
    (hsize.trans (genericTaskLayout_bit_le bitBound))

private theorem threeFormulaCode_le_genericTerminalEnvelope
    (formula1 formula2 formula3 : ValuationFormula)
    (bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (genericTaskLayoutTerminalBitBound bitBound))
    (hformula2 : (binaryFormulaCode formula2).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (genericTaskLayoutTerminalBitBound bitBound))
    (hformula3 : (binaryFormulaCode formula3).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (genericTaskLayoutTerminalBitBound bitBound)) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      genericTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
  have hinner := binaryFormulaCode_and_length_le_local formula2 formula3
  have houter := binaryFormulaCode_and_length_le_local formula1
    (formula2 ⋏ formula3)
  unfold genericTaskLayoutTerminalFormulaCodeEnvelope
  omega

theorem
    genericTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount start finish headKind headBinderArity
      headRepeatCount numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hheadKindSize : Nat.size headKind <= bitBound)
    (hheadBinderSize : Nat.size headBinderArity <= bitBound)
    (hheadRepeatSize : Nat.size headRepeatCount <= bitBound)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (headKind, headBinderArity, headRepeatCount)) :
    let binderStart := Classical.choose hlayout
    let countStart := Classical.choose (Classical.choose_spec hlayout)
    let certificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm start) (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm binderStart) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_shortBinaryNumeralTerm] using
                (Classical.choose_spec
                  (Classical.choose_spec hlayout)).1))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm binderStart)
            (shortBinaryNumeralTerm headBinderArity)
            (shortBinaryNumeralTerm countStart) (by
              simpa only [termValue_shortBinaryNumeralTerm] using
                (Classical.choose_spec
                  (Classical.choose_spec hlayout)).2.1))
          (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm countStart) (shortBinaryNumeralTerm headRepeatCount)
            (shortBinaryNumeralTerm finish) (by
              simpa only [termValue_shortBinaryNumeralTerm,
                termValue_shortBinaryNumeralTerm] using
                  (Classical.choose_spec
                    (Classical.choose_spec hlayout)).2.2)))
    hybridFormulaStructuralPayloadBound certificate <=
      genericTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
  dsimp only
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hrepeat := hcells.2.2
  have hstartLe : start <= tokenCount := Nat.le_of_lt hkind.1
  have hbinderStartLe : binderStart <= tokenCount :=
    Nat.le_of_lt hbinder.1
  have hcountStartLe : countStart <= tokenCount :=
    Nat.le_of_lt hrepeat.1
  have hbit := genericTaskLayout_bit_le bitBound
  have hbinderStartSize :
      Nat.size binderStart <= genericTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hbinderStartLe).trans (htokenCountSize.trans hbit)
  have hcountStartSize :
      Nat.size countStart <= genericTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hcountStartLe).trans (htokenCountSize.trans hbit)
  have hkindResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount start binderStart numericBound
      (genericTaskLayoutTerminalBitBound bitBound) (shortBinaryNumeralTerm headKind)
      hwidthValue (hstartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit) (by
        rw [termValue_shortBinaryNumeralTerm]
        exact hheadKindSize.trans hbit)
      hbinderStartSize
      (shortNumeral_code_le_genericTerminalEnvelope headKind bitBound
        hheadKindSize)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headKind) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hkind)
  have hbinderResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount binderStart countStart numericBound
      (genericTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm headBinderArity) hwidthValue
      (hbinderStartLe.trans htokenCountValue) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize (by
        simpa only [termValue_shortBinaryNumeralTerm] using
          hheadBinderSize.trans hbit) hcountStartSize
      (shortNumeral_code_le_genericTerminalEnvelope headBinderArity bitBound
        hheadBinderSize)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbinder)
  have hrepeatResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount countStart finish numericBound
      (genericTaskLayoutTerminalBitBound bitBound) (shortBinaryNumeralTerm headRepeatCount)
      hwidthValue (hcountStartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (by
        rw [termValue_shortBinaryNumeralTerm]
        exact hheadRepeatSize.trans hbit)
      (hfinishSize.trans hbit)
      (shortNumeral_code_le_genericTerminalEnvelope headRepeatCount bitBound
        hheadRepeatSize)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hrepeat)
  let formula1 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
    (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm binderStart)
  let formula2 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm binderStart)
    (shortBinaryNumeralTerm headBinderArity)
    (shortBinaryNumeralTerm countStart)
  let formula3 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm countStart)
    (shortBinaryNumeralTerm headRepeatCount) (shortBinaryNumeralTerm finish)
  have hformula1Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount start binderStart
      (genericTaskLayoutTerminalBitBound bitBound) (shortBinaryNumeralTerm headKind)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit)
      hbinderStartSize
      (shortNumeral_code_le_genericTerminalEnvelope headKind bitBound
        hheadKindSize)
  have hformula2Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount binderStart countStart
      (genericTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm headBinderArity) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize hcountStartSize
      (shortNumeral_code_le_genericTerminalEnvelope headBinderArity bitBound
        hheadBinderSize)
  have hformula3Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount countStart finish
      (genericTaskLayoutTerminalBitBound bitBound) (shortBinaryNumeralTerm headRepeatCount)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (hfinishSize.trans hbit)
      (shortNumeral_code_le_genericTerminalEnvelope headRepeatCount bitBound
        hheadRepeatSize)
  have htotalCode :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        genericTaskLayoutTerminalFormulaCodeEnvelope bitBound :=
    threeFormulaCode_le_genericTerminalEnvelope formula1 formula2 formula3
      bitBound hformula1Code hformula2Code hformula3Code
  have htotalClosed :
      (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and]
    rw [
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount start binderStart (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headKind),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount binderStart countStart
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount countStart finish (shortBinaryNumeralTerm headRepeatCount)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)]
    simp
  have hpositive :
      1 <= genericTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
    unfold genericTaskLayoutTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      layoutZeroValuation formula1 formula2 formula3
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (genericTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (genericTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (genericTaskLayoutTerminalBitBound bitBound))
      (genericTaskLayoutTerminalFormulaCodeEnvelope bitBound)
      hpositive htotalClosed htotalCode
  let certificate1 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
      (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm binderStart) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_shortBinaryNumeralTerm] using hkind)
  let certificate2 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm binderStart)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm countStart) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbinder)
  let certificate3 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm countStart) (shortBinaryNumeralTerm headRepeatCount)
      (shortBinaryNumeralTerm finish) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_shortBinaryNumeralTerm] using hrepeat)
  let certificate23 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate2
      certificate3
  have hcertificate23 := transparentHybridConjunctionPayloadBound_le
    certificate2 certificate3 _ _ hbinderResource hrepeatResource
  let certificate123 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate1
      certificate23
  have hcertificate123 := transparentHybridConjunctionPayloadBound_le
    certificate1 certificate23 _ _ hkindResource hcertificate23
  change hybridFormulaStructuralPayloadBound certificate123 <= _
  exact hcertificate123.trans (by
    simpa only [formula1, formula2, formula3,
      genericTaskLayoutTerminalPayloadEnvelope] using henvelope)

#print axioms
  genericTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericTerminalFullyFixedBounds
