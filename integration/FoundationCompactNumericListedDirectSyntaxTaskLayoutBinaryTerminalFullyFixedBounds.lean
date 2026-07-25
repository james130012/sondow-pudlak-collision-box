import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed terminal bound for a binary syntax-task layout

The binary task stores the genuine native terms `1` and `0`, together with
the short binary numeral for `binderArity`.  The three real token-cell
certificates are charged separately and reassembled in the original
right-associated conjunction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryTerminalFullyFixedBounds

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

def binaryTaskLayoutTerminalBitBound (bitBound : Nat) : Nat :=
  bitBound + binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (nativeNumeralTerm 0)).length +
    (binaryTermCode (nativeNumeralTerm 1)).length + 3

def binaryTaskLayoutTerminalFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  3 * additiveTokenCellClosedValueFormulaCodeEnvelope
      (binaryTaskLayoutTerminalBitBound bitBound) +
    2 * (binaryNatCode 4).length + 1

def binaryTaskLayoutTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (binaryTaskLayoutTerminalFormulaCodeEnvelope bitBound)
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (binaryTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (binaryTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (binaryTaskLayoutTerminalBitBound bitBound))

private theorem binaryNumeralTermCodeEnvelope_ge_bit_binary
    (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem binaryTaskLayout_bit_le (bitBound : Nat) :
    bitBound <= binaryTaskLayoutTerminalBitBound bitBound := by
  unfold binaryTaskLayoutTerminalBitBound
  omega

private theorem nativeNumeralTerm_freeVariables_eq_empty_binary
    (value : Nat) :
    (nativeNumeralTerm value).freeVariables = ∅ := by
  unfold nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem nativeZero_code_le_binaryTerminalEnvelope
    (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 0)).length <=
      binaryNumeralTermCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_binary
      (binaryTaskLayoutTerminalBitBound bitBound))
  unfold binaryTaskLayoutTerminalBitBound
  omega

private theorem nativeOne_code_le_binaryTerminalEnvelope
    (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 1)).length <=
      binaryNumeralTermCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_binary
      (binaryTaskLayoutTerminalBitBound bitBound))
  unfold binaryTaskLayoutTerminalBitBound
  omega

private theorem binderShort_code_le_binaryTerminalEnvelope
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope binderArity
    (binaryTaskLayoutTerminalBitBound bitBound)
    (hbinderSize.trans (binaryTaskLayout_bit_le bitBound))

private theorem threeFormulaCode_le_binaryTerminalEnvelope
    (formula1 formula2 formula3 : ValuationFormula)
    (bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound))
    (hformula2 : (binaryFormulaCode formula2).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound))
    (hformula3 : (binaryFormulaCode formula3).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound)) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      binaryTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
  have hinner := binaryFormulaCode_and_length_le_local formula2 formula3
  have houter := binaryFormulaCode_and_length_le_local formula1
    (formula2 ⋏ formula3)
  unfold binaryTaskLayoutTerminalFormulaCodeEnvelope
  omega

theorem
    binaryTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount start finish binderArity numericBound
      bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (1, binderArity, 0)) :
    let binderStart := Classical.choose hlayout
    let countStart := Classical.choose (Classical.choose_spec hlayout)
    let certificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm start) (nativeNumeralTerm 1)
          (shortBinaryNumeralTerm binderStart) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_nativeNumeralTerm] using
                (Classical.choose_spec
                  (Classical.choose_spec hlayout)).1))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm binderStart)
            (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm countStart) (by
              simpa only [termValue_shortBinaryNumeralTerm] using
                (Classical.choose_spec
                  (Classical.choose_spec hlayout)).2.1))
          (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm countStart) (nativeNumeralTerm 0)
            (shortBinaryNumeralTerm finish) (by
              simpa only [termValue_shortBinaryNumeralTerm,
                termValue_nativeNumeralTerm] using
                  (Classical.choose_spec
                    (Classical.choose_spec hlayout)).2.2)))
    hybridFormulaStructuralPayloadBound certificate <=
      binaryTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
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
  have hbit := binaryTaskLayout_bit_le bitBound
  have hbinderStartSize :
      Nat.size binderStart <= binaryTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hbinderStartLe).trans (htokenCountSize.trans hbit)
  have hcountStartSize :
      Nat.size countStart <= binaryTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hcountStartLe).trans (htokenCountSize.trans hbit)
  have hkindResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount start binderStart numericBound
      (binaryTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 1)
      hwidthValue (hstartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit) (by
        rw [termValue_nativeNumeralTerm]
        exact (by decide : Nat.size 1 <= 1) |>.trans (by
          unfold binaryTaskLayoutTerminalBitBound
          omega))
      hbinderStartSize (nativeOne_code_le_binaryTerminalEnvelope bitBound)
      (nativeNumeralTerm_freeVariables_eq_empty_binary 1) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_nativeNumeralTerm] using hkind)
  have hbinderResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount binderStart countStart numericBound
      (binaryTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm binderArity) hwidthValue
      (hbinderStartLe.trans htokenCountValue) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize (by
        simpa only [termValue_shortBinaryNumeralTerm] using
          hbinderSize.trans hbit) hcountStartSize
      (binderShort_code_le_binaryTerminalEnvelope binderArity bitBound
        hbinderSize)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbinder)
  have hrepeatResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount countStart finish numericBound
      (binaryTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 0)
      hwidthValue (hcountStartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (by
        rw [termValue_nativeNumeralTerm]
        exact Nat.zero_le _)
      (hfinishSize.trans hbit)
      (nativeZero_code_le_binaryTerminalEnvelope bitBound)
      (nativeNumeralTerm_freeVariables_eq_empty_binary 0) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_nativeNumeralTerm] using hrepeat)
  let formula1 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
    (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderStart)
  let formula2 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm binderStart)
    (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm countStart)
  let formula3 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm countStart)
    (nativeNumeralTerm 0) (shortBinaryNumeralTerm finish)
  have hformula1Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount start binderStart
      (binaryTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 1)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit)
      hbinderStartSize (nativeOne_code_le_binaryTerminalEnvelope bitBound)
  have hformula2Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount binderStart countStart
      (binaryTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm binderArity) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize hcountStartSize
      (binderShort_code_le_binaryTerminalEnvelope binderArity bitBound
        hbinderSize)
  have hformula3Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount countStart finish
      (binaryTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 0)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (hfinishSize.trans hbit)
      (nativeZero_code_le_binaryTerminalEnvelope bitBound)
  have htotalCode :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        binaryTaskLayoutTerminalFormulaCodeEnvelope bitBound :=
    threeFormulaCode_le_binaryTerminalEnvelope formula1 formula2 formula3
      bitBound hformula1Code hformula2Code hformula3Code
  have htotalClosed :
      (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and]
    rw [
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount start binderStart (nativeNumeralTerm 1)
        (nativeNumeralTerm_freeVariables_eq_empty_binary 1),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount binderStart countStart
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount countStart finish (nativeNumeralTerm 0)
        (nativeNumeralTerm_freeVariables_eq_empty_binary 0)]
    simp
  have hpositive :
      1 <= binaryTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
    unfold binaryTaskLayoutTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      layoutZeroValuation formula1 formula2 formula3
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (binaryTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (binaryTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (binaryTaskLayoutTerminalBitBound bitBound))
      (binaryTaskLayoutTerminalFormulaCodeEnvelope bitBound)
      hpositive htotalClosed htotalCode
  let certificate1 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderStart) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_nativeNumeralTerm] using hkind)
  let certificate2 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm binderStart)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm countStart) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbinder)
  let certificate3 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm countStart) (nativeNumeralTerm 0)
      (shortBinaryNumeralTerm finish) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_nativeNumeralTerm] using hrepeat)
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
      binaryTaskLayoutTerminalPayloadEnvelope] using henvelope)

#print axioms
  binaryTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryTerminalFullyFixedBounds
