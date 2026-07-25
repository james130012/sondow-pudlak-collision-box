import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificWitnessFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-! # Fully fixed guards for the two exact Repeat task-row indices -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsGuardFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

@[simp] private theorem termValue_fixedNumeralTerm_repeatGuard
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  simp [fixedNumeralTerm, termValue]

def repeatAtRowsGuardPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (repeatAtRowsTermCodeEnvelope bitBound)

theorem strictCertificate_repeatIndex_structuralPayloadBound_le_fixed
    (count index numericBound bitBound : Nat)
    (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hindexValue : termValue atRowsZeroValuation indexTerm = index)
    (hindexCode :
      (binaryTermCode indexTerm).length <= repeatAtRowsTermCodeEnvelope bitBound)
    (hindex : index < count)
    (hcountSize : Nat.size count <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
          simpa only [hindexValue, termValue_shortBinaryNumeralTerm] using
            hindex)) <=
      repeatAtRowsGuardPayloadEnvelope numericBound bitBound := by
  have hpublic :=
    strictCertificate_structuralPayloadBound_le_public count indexTerm
      hindexClosed (by simpa only [hindexValue] using hindex)
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed atRowsZeroValuation
      Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm count]
      numericBound (repeatAtRowsTermCodeEnvelope bitBound)
      (by
        change indexTerm.freeVariables ⊆ {0}
        rw [hindexClosed]
        simp)
      (by
        change (shortBinaryNumeralTerm count).freeVariables ⊆ {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (Nat.zero_le numericBound) hindexCode
      (shortBinary_code_le_repeatAtRowsTermEnvelope count bitBound hcountSize)
  simpa only [compactAdditiveSyntaxTaskListAtRowsGuardPayloadPolynomial,
    repeatAtRowsGuardPayloadEnvelope] using hpublic.trans hfixed

theorem repeatTaskZeroGuard_structuralPayloadBound_le_fixed
    (count numericBound bitBound : Nat) (hindex : 0 < count)
    (hcountSize : Nat.size count <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (strictCertificate (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm count) (by
            simpa only [termValue_fixedNumeralTerm_repeatGuard,
              FoundationCompactPAValuationTermCompiler.termValue_shortBinaryNumeralTerm]
              using hindex)) <=
      repeatAtRowsGuardPayloadEnvelope numericBound bitBound := by
  exact strictCertificate_repeatIndex_structuralPayloadBound_le_fixed count 0
    numericBound bitBound (fixedNumeralTerm 0) (by simp) (by simp)
    (fixedZero_code_le_repeatAtRowsTermEnvelope bitBound) hindex hcountSize

theorem repeatTaskOneGuard_structuralPayloadBound_le_fixed
    (count numericBound bitBound : Nat) (hindex : 1 < count)
    (hcountSize : Nat.size count <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (strictCertificate (fixedNumeralTerm 1)
          (shortBinaryNumeralTerm count) (by
            simpa only [termValue_fixedNumeralTerm_repeatGuard,
              FoundationCompactPAValuationTermCompiler.termValue_shortBinaryNumeralTerm]
              using hindex)) <=
      repeatAtRowsGuardPayloadEnvelope numericBound bitBound := by
  exact strictCertificate_repeatIndex_structuralPayloadBound_le_fixed count 1
    numericBound bitBound (fixedNumeralTerm 1) (by simp) (by simp)
    (fixedOne_code_le_repeatAtRowsTermEnvelope bitBound) hindex hcountSize

#print axioms repeatTaskZeroGuard_structuralPayloadBound_le_fixed
#print axioms repeatTaskOneGuard_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsGuardFixedBounds
