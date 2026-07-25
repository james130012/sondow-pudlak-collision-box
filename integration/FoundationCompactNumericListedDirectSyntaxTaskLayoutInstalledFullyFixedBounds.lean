import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of the quantifier syntax-task layout

The genuine three-cell terminal is installed below its two bounded cursor
witnesses.  Its open body has an explicit code envelope and empty free-variable
context, so the arity-two fixed witness theorem applies without a finite sum or
an external syntax bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutInstalledFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayoutTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def quantifierTaskLayoutInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope
    (binaryNumeralTermCodeEnvelope
      (quantifierTaskLayoutTerminalBitBound bitBound))

def quantifierTaskLayoutInstalledPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound)
    (quantifierTaskLayoutTerminalPayloadEnvelope numericBound bitBound)

def quantifierTaskLayoutFormulaCodeEnvelope
    (tokenCount bitBound : Nat) : Nat :=
  let body02 := quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound
  let body01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount body02
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 0 tokenCount body01

private theorem binaryNumeralTermCodeEnvelope_ge_bit (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem nativeNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (nativeNumeralTerm value).freeVariables = ∅ := by
  unfold nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem nativeZero_code_le_installedTermEnvelope (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 0)).length <=
      binaryNumeralTermCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_ (binaryNumeralTermCodeEnvelope_ge_bit _)
  simp only [quantifierTaskLayoutTerminalBitBound]
  omega

private theorem nativeOne_code_le_installedTermEnvelope (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 1)).length <=
      binaryNumeralTermCodeEnvelope
        (quantifierTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_ (binaryNumeralTermCodeEnvelope_ge_bit _)
  simp only [quantifierTaskLayoutTerminalBitBound]
  omega

private theorem binderSuccessor_code_le_installedTermEnvelope
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

theorem quantifierTaskLayoutFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount start finish binderArity bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
        tokenCount start finish (nativeNumeralTerm 1)
        (binderSuccessorTerm binderArity) (nativeNumeralTerm 0))).length <=
      quantifierTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
  let body :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
  have hbit : bitBound <= quantifierTaskLayoutTerminalBitBound bitBound := by
    simp only [quantifierTaskLayoutTerminalBitBound,
      quantifierBinderSuccessorTokenCellBitBound]
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound := by
    apply
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_code_length_le_uniform
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable _
        (htableSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope width _
        (hwidthSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount _
        (htokenCountSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope start _
        (hstartSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope finish _
        (hfinishSize.trans hbit)
    · exact nativeOne_code_le_installedTermEnvelope bitBound
    · exact binderSuccessor_code_le_installedTermEnvelope binderArity
        bitBound hbinderSize
    · exact nativeZero_code_le_installedTermEnvelope bitBound
  let body01 : ArithmeticSemiformula Nat 1 :=
    body.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        1 (shortBinaryNumeralTerm tokenCount))
  have hbody01 :
      (binaryFormulaCode body01).length <=
        explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound) :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound) body hbody
  have hbody00 :
      (binaryFormulaCode
        (body01.bexsLTSucc (shortBinaryNumeralTerm tokenCount))).length <=
        quantifierTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
    have hraw :=
      explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound))
        body01 hbody01
    simpa only [quantifierTaskLayoutFormulaCodeEnvelope, body01,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using hraw
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  simpa only [explicitBoundedWitnessFormula, body, body01,
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
    using hbody00

theorem
    quantifierTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
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
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish 1 (binderArity + 1) 0
          (nativeNumeralTerm 1) (binderSuccessorTerm binderArity)
          (nativeNumeralTerm 0) (termValue_nativeNumeralTerm · 1)
          (termValue_binderSuccessorTerm · binderArity)
          (termValue_nativeNumeralTerm · 0) hlayout) <=
      quantifierTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hrepeat := hcells.2.2
  have hbinderStartLe : binderStart <= tokenCount :=
    Nat.le_of_lt hbinder.1
  have hcountStartLe : countStart <= tokenCount :=
    Nat.le_of_lt hrepeat.1
  let values : Fin 2 -> Nat := ![countStart, binderStart]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact hcountStartLe
    · exact hbinderStartLe
  let body :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
          ![shortBinaryNumeralTerm countStart,
            shortBinaryNumeralTerm binderStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm start) (nativeNumeralTerm 1)
        (shortBinaryNumeralTerm binderStart) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_nativeNumeralTerm] using hkind))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm binderStart)
          (binderSuccessorTerm binderArity)
          (shortBinaryNumeralTerm countStart) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_binderSuccessorTerm] using hbinder))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm countStart) (nativeNumeralTerm 0)
          (shortBinaryNumeralTerm finish) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_nativeNumeralTerm] using hrepeat)))
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
        (body ⇜ fun coordinate =>
          shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount start finish binderStart countStart
          (nativeNumeralTerm 1) (binderSuccessorTerm binderArity)
          (nativeNumeralTerm 0)).symm) terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        quantifierTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
    simpa only [binderStart, countStart, values, body, terminalParts,
      terminal] using
      (quantifierTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount start finish binderArity numericBound
        bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize hstartSize hfinishSize hbinderSize hlayout)
  have hbit : bitBound <= quantifierTaskLayoutTerminalBitBound bitBound := by
    simp only [quantifierTaskLayoutTerminalBitBound,
      quantifierBinderSuccessorTokenCellBitBound]
    omega
  let termCodeBound :=
    binaryNumeralTermCodeEnvelope
      (quantifierTaskLayoutTerminalBitBound bitBound)
  have hbody :
      (binaryFormulaCode body).length <=
        quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound := by
    apply
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_code_length_le_uniform
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable _
        (htableSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope width _
        (hwidthSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount _
        (htokenCountSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope start _
        (hstartSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope finish _
        (hfinishSize.trans hbit)
    · exact nativeOne_code_le_installedTermEnvelope bitBound
    · exact binderSuccessor_code_le_installedTermEnvelope binderArity
        bitBound hbinderSize
    · exact nativeZero_code_le_installedTermEnvelope bitBound
  have hbodyClosed : body.freeVariables = ∅ := by
    exact
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount start finish (nativeNumeralTerm 1)
        (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
        (nativeNumeralTerm_freeVariables_eq_empty 1)
        (binderSuccessorTerm_freeVariables_eq_empty_fixed binderArity)
        (nativeNumeralTerm_freeVariables_eq_empty 0)
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables layoutZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (quantifierTaskLayoutTerminalPayloadEnvelope numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      layoutZeroValuation 0 tokenCount numericBound
      (quantifierTaskLayoutInstalledBodyCodeEnvelope bitBound) body values
      hvalues htokenCountValue hbody hcontext (le_refl
        (quantifierTaskLayoutTerminalPayloadEnvelope numericBound bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
          tokenTable width tokenCount start finish (nativeNumeralTerm 1)
          (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)).symm
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    quantifierTaskLayoutInstalledPayloadEnvelope] using hinstalled

#print axioms
  quantifierTaskLayoutFormula_code_length_le_fullyFixed
#print axioms
  quantifierTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutInstalledFullyFixedBounds
