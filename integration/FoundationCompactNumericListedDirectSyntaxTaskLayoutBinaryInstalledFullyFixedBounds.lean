import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of a binary syntax-task layout

The genuine three-cell terminal is installed below its two bounded cursor
witnesses.  Its open body has a fixed code envelope and empty valuation
context, so no finite sum or caller-supplied syntax bound remains.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 350000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryInstalledFullyFixedBounds

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
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def binaryTaskLayoutInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope
    (binaryNumeralTermCodeEnvelope
      (binaryTaskLayoutTerminalBitBound bitBound))

def binaryTaskLayoutInstalledPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (binaryTaskLayoutInstalledBodyCodeEnvelope bitBound)
    (binaryTaskLayoutTerminalPayloadEnvelope numericBound bitBound)

def binaryTaskLayoutFormulaCodeEnvelope
    (tokenCount bitBound : Nat) : Nat :=
  let body02 := binaryTaskLayoutInstalledBodyCodeEnvelope bitBound
  let body01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount body02
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 0 tokenCount body01

private theorem binaryNumeralTermCodeEnvelope_ge_bit_installed
    (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem nativeNumeralTerm_freeVariables_eq_empty_installed
    (value : Nat) :
    (nativeNumeralTerm value).freeVariables = ∅ := by
  unfold nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem nativeZero_code_le_installedTermEnvelope_binary
    (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 0)).length <=
      binaryNumeralTermCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_installed
      (binaryTaskLayoutTerminalBitBound bitBound))
  unfold binaryTaskLayoutTerminalBitBound
  omega

private theorem nativeOne_code_le_installedTermEnvelope_binary
    (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 1)).length <=
      binaryNumeralTermCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_installed
      (binaryTaskLayoutTerminalBitBound bitBound))
  unfold binaryTaskLayoutTerminalBitBound
  omega

private theorem binderShort_code_le_installedTermEnvelope_binary
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (binaryTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope binderArity
    (binaryTaskLayoutTerminalBitBound bitBound)
    (hbinderSize.trans (by
      unfold binaryTaskLayoutTerminalBitBound
      omega))

private theorem binaryLayoutBexsLTSucc_freeVariables_eq_empty
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    simp [LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_one,
      LO.FirstOrder.Semiterm.Operator.One.term_eq]
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables_eq_union, hbound, hone]
    simp
  have hshifted :
      (Rew.bShift
        (‘!!bound + 1’ : ArithmeticSemiterm Nat arity)).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty _ hsuccessor
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
    LO.FirstOrder.Semiformula.bexsLT LO.FirstOrder.bexs
  rw [LO.FirstOrder.Semiformula.freeVariables_exs,
    LO.FirstOrder.Semiformula.freeVariables_and,
    lessThanFormula_freeVariables, hshifted, hbody]
  simp

theorem binaryTaskLayoutFormula_code_length_le_fullyFixed
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
        (shortBinaryNumeralTerm binderArity)
        (nativeNumeralTerm 0))).length <=
      binaryTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
  let body :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
  have hbit : bitBound <= binaryTaskLayoutTerminalBitBound bitBound := by
    unfold binaryTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        binaryTaskLayoutInstalledBodyCodeEnvelope bitBound := by
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
    · exact nativeOne_code_le_installedTermEnvelope_binary bitBound
    · exact binderShort_code_le_installedTermEnvelope_binary binderArity
        bitBound hbinderSize
    · exact nativeZero_code_le_installedTermEnvelope_binary bitBound
  let body01 : ArithmeticSemiformula Nat 1 :=
    body.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        1 (shortBinaryNumeralTerm tokenCount))
  have hbody01 :
      (binaryFormulaCode body01).length <=
        explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (binaryTaskLayoutInstalledBodyCodeEnvelope bitBound) :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (binaryTaskLayoutInstalledBodyCodeEnvelope bitBound) body hbody
  have hbody00 :
      (binaryFormulaCode
        (body01.bexsLTSucc (shortBinaryNumeralTerm tokenCount))).length <=
        binaryTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
    have hraw :=
      explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (binaryTaskLayoutInstalledBodyCodeEnvelope bitBound))
        body01 hbody01
    simpa only [binaryTaskLayoutFormulaCodeEnvelope, body01,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using hraw
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  simpa only [explicitBoundedWitnessFormula, body, body01,
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
    using hbody00

theorem binaryTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount start finish binderArity : Nat) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount start finish (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)).freeVariables = ∅ := by
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  unfold explicitBoundedWitnessFormula
  have hbody :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount start finish (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
      (nativeNumeralTerm_freeVariables_eq_empty_installed 1)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (nativeNumeralTerm_freeVariables_eq_empty_installed 0)
  change
    (((compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)).bexsLTSucc
        (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
          1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)).freeVariables = ∅
  apply binaryLayoutBexsLTSucc_freeVariables_eq_empty
  · apply binaryLayoutBexsLTSucc_freeVariables_eq_empty
    · exact hbody
    · apply bShift_freeVariables_eq_empty_of_empty
      exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount

theorem
    binaryTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
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
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish 1 binderArity 0
          (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (nativeNumeralTerm 0) (termValue_nativeNumeralTerm · 1)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_nativeNumeralTerm · 0) hlayout) <=
      binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
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
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
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
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm countStart) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hbinder))
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
          (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (nativeNumeralTerm 0)).symm) terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        binaryTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
    change hybridFormulaStructuralPayloadBound terminalParts <= _
    simpa only [binderStart, countStart, terminalParts] using
      (binaryTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount start finish binderArity numericBound
        bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize hstartSize hfinishSize hbinderSize hlayout)
  have hbit : bitBound <= binaryTaskLayoutTerminalBitBound bitBound := by
    unfold binaryTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        binaryTaskLayoutInstalledBodyCodeEnvelope bitBound := by
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
    · exact nativeOne_code_le_installedTermEnvelope_binary bitBound
    · exact binderShort_code_le_installedTermEnvelope_binary binderArity
        bitBound hbinderSize
    · exact nativeZero_code_le_installedTermEnvelope_binary bitBound
  have hbodyClosed : body.freeVariables = ∅ := by
    exact
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount start finish (nativeNumeralTerm 1)
        (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
        (nativeNumeralTerm_freeVariables_eq_empty_installed 1)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
        (nativeNumeralTerm_freeVariables_eq_empty_installed 0)
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables layoutZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (binaryTaskLayoutTerminalPayloadEnvelope numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      layoutZeroValuation 0 tokenCount numericBound
      (binaryTaskLayoutInstalledBodyCodeEnvelope bitBound) body values
      hvalues htokenCountValue hbody hcontext (le_refl
        (binaryTaskLayoutTerminalPayloadEnvelope numericBound bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
          tokenTable width tokenCount start finish (nativeNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity)
          (nativeNumeralTerm 0)).symm
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    binaryTaskLayoutInstalledPayloadEnvelope] using hinstalled

#print axioms binaryTaskLayoutFormula_code_length_le_fullyFixed
#print axioms binaryTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  binaryTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryInstalledFullyFixedBounds
