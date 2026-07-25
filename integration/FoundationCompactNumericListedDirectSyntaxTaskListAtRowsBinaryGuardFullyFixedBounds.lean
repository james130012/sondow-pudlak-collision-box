import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryWitnessFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Fully fixed index guard for a binary syntax-task row

The genuine `index < count` certificate is bounded for the parser-selected
indices zero and one.  Both terms are closed and their code is controlled by
the same fixed term envelope used by the binary row body.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryGuardFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

def syntaxTaskAtRowsBinaryGuardPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound)

private theorem nativeNumeralTerm_freeVariables_eq_empty_binaryGuard
    (value : Nat) :
    (nativeNumeralTerm value).freeVariables = ∅ := by
  unfold nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem nativeSelectedIndex_code_le_binaryGuardEnvelope
    (index bitBound : Nat) (hindex : index < 2) :
    (binaryTermCode (nativeNumeralTerm index)).length <=
      syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound := by
  have hcases : index = 0 ∨ index = 1 := by omega
  rcases hcases with rfl | rfl
  · unfold syntaxTaskAtRowsBinaryTermCodeEnvelope
    exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · unfold syntaxTaskAtRowsBinaryTermCodeEnvelope
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

private theorem shortCount_code_le_binaryGuardEnvelope
    (count bitBound : Nat) (hcountSize : Nat.size count <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm count)).length <=
      syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound := by
  exact
    (binaryNumeralTerm_code_length_le_envelope count bitBound hcountSize).trans
      (Nat.le_max_left _ _)

theorem strictCertificate_binaryIndex_structuralPayloadBound_le_fullyFixed
    (count index numericBound bitBound : Nat)
    (hindexSelected : index < 2)
    (hindex : index < count)
    (hcountSize : Nat.size count <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (strictCertificate (nativeNumeralTerm index)
          (shortBinaryNumeralTerm count) (by
            simpa only [termValue_nativeNumeralTerm,
              termValue_shortBinaryNumeralTerm] using hindex)) <=
      syntaxTaskAtRowsBinaryGuardPayloadEnvelope numericBound bitBound := by
  let indexTerm : ValuationTerm := nativeNumeralTerm index
  let countTerm : ValuationTerm := shortBinaryNumeralTerm count
  let guard :=
    strictCertificate indexTerm countTerm (by
      simpa only [indexTerm, countTerm, termValue_nativeNumeralTerm,
        termValue_shortBinaryNumeralTerm] using hindex)
  have hpublic :=
    strictCertificate_structuralPayloadBound_le_public count indexTerm
      (nativeNumeralTerm_freeVariables_eq_empty_binaryGuard index) (by
        simpa only [indexTerm, termValue_nativeNumeralTerm] using hindex)
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed atRowsZeroValuation
      Language.ORing.Rel.lt ![indexTerm, countTerm] numericBound
      (syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound)
      (by
        change indexTerm.freeVariables ⊆ {0}
        rw [nativeNumeralTerm_freeVariables_eq_empty_binaryGuard]
        simp)
      (by
        change countTerm.freeVariables ⊆ {0}
        dsimp only [countTerm]
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (by exact Nat.zero_le numericBound)
      (nativeSelectedIndex_code_le_binaryGuardEnvelope index bitBound
        hindexSelected)
      (shortCount_code_le_binaryGuardEnvelope count bitBound hcountSize)
  simpa only [guard, indexTerm, countTerm,
    compactAdditiveSyntaxTaskListAtRowsGuardPayloadPolynomial,
    syntaxTaskAtRowsBinaryGuardPayloadEnvelope] using hpublic.trans hfixed

#print axioms
  strictCertificate_binaryIndex_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryGuardFullyFixedBounds
