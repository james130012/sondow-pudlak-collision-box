import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed terminal bound for the quantifier syntax-task layout

The quantifier task stores the genuine native terms `1`, `binderArity + 1`,
and `0`.  Native numeral syntax is not identified with short binary-numeral
syntax.  Their actual codes are charged explicitly in one enlarged bit
coordinate before the three real token-cell certificates are assembled.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutTerminalFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def quantifierTaskLayoutTerminalBitBound (bitBound : Nat) : Nat :=
  let successorBit := quantifierBinderSuccessorTokenCellBitBound bitBound
  successorBit + binaryNumeralTermCodeEnvelope successorBit +
    (binaryTermCode (nativeNumeralTerm 0)).length +
    (binaryTermCode (nativeNumeralTerm 1)).length + 3

def quantifierTaskLayoutTerminalFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  3 * additiveTokenCellClosedValueFormulaCodeEnvelope
      (quantifierTaskLayoutTerminalBitBound bitBound) +
    2 * (binaryNatCode 4).length + 1

def quantifierTaskLayoutTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (quantifierTaskLayoutTerminalFormulaCodeEnvelope bitBound)
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (quantifierTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (quantifierTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (quantifierTaskLayoutTerminalBitBound bitBound))

private theorem binaryNumeralTermCodeEnvelope_ge_bit (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem size_add_one_le (value : Nat) :
    Nat.size (value + 1) <= Nat.size value + 1 := by
  rw [Nat.size_le]
  have hvalue : value + 1 <= 2 ^ Nat.size value :=
    Nat.succ_le_iff.mpr (Nat.lt_size_self value)
  exact hvalue.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
      (Nat.lt_succ_self (Nat.size value)))

private theorem nativeNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (nativeNumeralTerm value).freeVariables = ∅ := by
  unfold nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem nativeZero_code_le_terminalEnvelope (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 0)).length <=
      binaryNumeralTermCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_ (binaryNumeralTermCodeEnvelope_ge_bit _)
  simp only [quantifierTaskLayoutTerminalBitBound]
  omega

private theorem nativeOne_code_le_terminalEnvelope (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 1)).length <=
      binaryNumeralTermCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_ (binaryNumeralTermCodeEnvelope_ge_bit _)
  simp only [quantifierTaskLayoutTerminalBitBound]
  omega

private theorem binderSuccessor_code_le_terminalEnvelope
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (binderSuccessorTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound) := by
  apply (binderSuccessorTerm_code_length_le_tokenCellEnvelope
    binderArity bitBound hbinderSize).trans
  apply le_trans ?_ (binaryNumeralTermCodeEnvelope_ge_bit _)
  simp only [quantifierTaskLayoutTerminalBitBound]
  omega

private theorem threeFormulaCode_le_terminalEnvelope
    (formula1 formula2 formula3 : ValuationFormula)
    (bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound))
    (hformula2 : (binaryFormulaCode formula2).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound))
    (hformula3 : (binaryFormulaCode formula3).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound)) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      quantifierTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
  have hinner := binaryFormulaCode_and_length_le_local formula2 formula3
  have houter := binaryFormulaCode_and_length_le_local formula1
    (formula2 ⋏ formula3)
  unfold quantifierTaskLayoutTerminalFormulaCodeEnvelope
  omega

theorem
    quantifierTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
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
      start finish (1, binderArity + 1, 0)) :
    let binderStart := Classical.choose hlayout
    let countStart := Classical.choose (Classical.choose_spec hlayout)
    let values : Fin 2 -> Nat := ![countStart, binderStart]
    let terminal :=
      (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
        tokenCount start finish (nativeNumeralTerm 1)
        (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)
    let certificate :
        CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
          terminal :=
      .cast (by
        dsimp only [terminal, values, binderStart, countStart]
        rw [show
          (fun coordinate : Fin 2 =>
            shortBinaryNumeralTerm (![countStart, binderStart] coordinate)) =
              ![shortBinaryNumeralTerm countStart,
                shortBinaryNumeralTerm binderStart] by
          funext coordinate
          fin_cases coordinate <;> rfl]
        exact
          (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
            tokenTable width tokenCount start finish binderStart countStart
            (nativeNumeralTerm 1) (binderSuccessorTerm binderArity)
            (nativeNumeralTerm 0)).symm)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
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
              (binderSuccessorTerm binderArity)
              (shortBinaryNumeralTerm countStart) (by
                simpa only [termValue_shortBinaryNumeralTerm,
                  termValue_binderSuccessorTerm] using
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
                      (Classical.choose_spec hlayout)).2.2))))
    hybridFormulaStructuralPayloadBound certificate <=
      quantifierTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
  dsimp only
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hrepeat := hcells.2.2
  have hstartLe : start <= tokenCount := by
    exact Nat.le_of_lt hkind.1
  have hbinderStartLe : binderStart <= tokenCount := by
    exact Nat.le_of_lt hbinder.1
  have hcountStartLe : countStart <= tokenCount := by
    exact Nat.le_of_lt hrepeat.1
  have hbit : bitBound <= quantifierTaskLayoutTerminalBitBound bitBound := by
    simp only [quantifierTaskLayoutTerminalBitBound,
      quantifierBinderSuccessorTokenCellBitBound]
    omega
  have hbinderStartSize :
      Nat.size binderStart <= quantifierTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hbinderStartLe).trans (htokenCountSize.trans hbit)
  have hcountStartSize :
      Nat.size countStart <= quantifierTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hcountStartLe).trans (htokenCountSize.trans hbit)
  have hsuccessorSize :
      Nat.size (binderArity + 1) <=
        quantifierTaskLayoutTerminalBitBound bitBound :=
    (size_add_one_le binderArity).trans (by
      apply (Nat.add_le_add_right hbinderSize 1).trans
      simp only [quantifierTaskLayoutTerminalBitBound,
        quantifierBinderSuccessorTokenCellBitBound]
      omega)
  have hkindResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount start binderStart numericBound
      (quantifierTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 1)
      hwidthValue (hstartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit) (by
        rw [termValue_nativeNumeralTerm]
        exact (by decide : Nat.size 1 <= 1) |>.trans (by
          simp only [quantifierTaskLayoutTerminalBitBound,
            quantifierBinderSuccessorTokenCellBitBound]
          omega))
      hbinderStartSize (nativeOne_code_le_terminalEnvelope bitBound)
      (nativeNumeralTerm_freeVariables_eq_empty 1) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_nativeNumeralTerm] using hkind)
  have hbinderResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount binderStart countStart numericBound
      (quantifierTaskLayoutTerminalBitBound bitBound)
      (binderSuccessorTerm binderArity) hwidthValue
      (hbinderStartLe.trans htokenCountValue) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize (by
        simpa only [termValue_binderSuccessorTerm] using hsuccessorSize)
      hcountStartSize
      (binderSuccessor_code_le_terminalEnvelope binderArity bitBound
        hbinderSize)
      (binderSuccessorTerm_freeVariables_eq_empty_fixed binderArity) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_binderSuccessorTerm] using hbinder)
  have hrepeatResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount countStart finish numericBound
      (quantifierTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 0)
      hwidthValue (hcountStartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (by
        rw [termValue_nativeNumeralTerm]
        simpa using
          (Nat.zero_le (quantifierTaskLayoutTerminalBitBound bitBound)))
      (hfinishSize.trans hbit) (nativeZero_code_le_terminalEnvelope bitBound)
      (nativeNumeralTerm_freeVariables_eq_empty 0) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_nativeNumeralTerm] using hrepeat)
  let formula1 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
    (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderStart)
  let formula2 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm binderStart)
    (binderSuccessorTerm binderArity) (shortBinaryNumeralTerm countStart)
  let formula3 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm countStart)
    (nativeNumeralTerm 0) (shortBinaryNumeralTerm finish)
  have hformula1Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount start binderStart
      (quantifierTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 1)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit)
      hbinderStartSize (nativeOne_code_le_terminalEnvelope bitBound)
  have hformula2Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount binderStart countStart
      (quantifierTaskLayoutTerminalBitBound bitBound)
      (binderSuccessorTerm binderArity) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize hcountStartSize
      (binderSuccessor_code_le_terminalEnvelope binderArity bitBound
        hbinderSize)
  have hformula3Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount countStart finish
      (quantifierTaskLayoutTerminalBitBound bitBound) (nativeNumeralTerm 0)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (hfinishSize.trans hbit)
      (nativeZero_code_le_terminalEnvelope bitBound)
  have htotalCode :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        quantifierTaskLayoutTerminalFormulaCodeEnvelope bitBound :=
    threeFormulaCode_le_terminalEnvelope formula1 formula2 formula3 bitBound
      hformula1Code hformula2Code hformula3Code
  have htotalClosed : (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and]
    rw [
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount start binderStart (nativeNumeralTerm 1)
        (nativeNumeralTerm_freeVariables_eq_empty 1),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount binderStart countStart
        (binderSuccessorTerm binderArity)
        (binderSuccessorTerm_freeVariables_eq_empty_fixed binderArity),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount countStart finish (nativeNumeralTerm 0)
        (nativeNumeralTerm_freeVariables_eq_empty 0)]
    simp
  have hpositive :
      1 <= quantifierTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
    unfold quantifierTaskLayoutTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      layoutZeroValuation formula1 formula2 formula3
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (quantifierTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (quantifierTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (quantifierTaskLayoutTerminalBitBound bitBound))
      (quantifierTaskLayoutTerminalFormulaCodeEnvelope bitBound)
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
      (binderSuccessorTerm binderArity)
      (shortBinaryNumeralTerm countStart) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_binderSuccessorTerm] using hbinder)
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
      quantifierTaskLayoutTerminalPayloadEnvelope] using henvelope)

#print axioms nativeZero_code_le_terminalEnvelope
#print axioms nativeOne_code_le_terminalEnvelope
#print axioms binderSuccessor_code_le_terminalEnvelope
#print axioms threeFormulaCode_le_terminalEnvelope
#print axioms
  quantifierTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutTerminalFullyFixedBounds
