import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentResources
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailOuterFormulaClosed

/-! # Empty-context normal form of the transparent cons-tail universal payload -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentNormalized

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridBoundedUniversalTransparentPayload
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailOuterFormulaClosed
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentResources

theorem natListConsRowsTailUniversalTransparentPayloadEnvelope_eq_normalized
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    natListConsRowsTailUniversalTransparentPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows =
      compileContextualTermBoundedUniversalPayloadEnvelope ∅ sourceCount
        (Rew.bShift (shortBinaryNumeralTerm sourceCount))
        (natListConsRowsTailUniversalBody tokenTable width tokenCount
          sourceBoundary targetBoundary)
        (compileShiftedBoundEqualityPayloadResource
          natListConsRowsTailUniversalZeroValuation ∅
          (shortBinaryNumeralTerm sourceCount))
        (contextualBranchesUnderBoundPayloadEnvelope ∅ sourceCount
          (Rewriting.free
            (natListConsRowsTailUniversalBody tokenTable width tokenCount
              sourceBoundary targetBoundary))
          (hybridBranchesStructuralPayloadEnvelope sourceCount
            (∅ : Finset Nat)
            (compactAdditiveNatListConsRowsTailUniversalBranchesAtBoundTerm
              tokenTable width tokenCount sourceBoundary sourceCount
              targetBoundary rows))) := by
  unfold natListConsRowsTailUniversalTransparentPayloadEnvelope
    hybridBoundedUniversalTransparentPayloadEnvelope
  simp only [natListConsRowsTailUniversalBoundTerm,
    termValue_shortBinaryNumeralTerm]
  rw [show
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (natListConsRowsTailUniversalBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).freeVariables = ∅ by
      unfold natListConsRowsTailUniversalBody
      exact
        compactAdditiveNatListConsRowsTailOuterFormula_freeVariables_eq_empty
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary]
  simp [valuationContext]

#print axioms
  natListConsRowsTailUniversalTransparentPayloadEnvelope_eq_normalized

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentNormalized
