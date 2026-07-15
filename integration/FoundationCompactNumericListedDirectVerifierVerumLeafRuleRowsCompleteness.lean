import integration.FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows

/-!
# Completeness witnesses for verifier verum leaf rows

This module constructs the numeric leaf rows directly from a typed `Gamma`
layout, and supplies a canonical one-table witness for later table bindings.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerumRuleCheck
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows

theorem CompactNumericVerifierVerumLeafRuleRows.of_gammaRows
    {tokenTable width tokenCount gammaBoundary : Nat}
    {Gamma : List (List Nat)}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma) :
    CompactNumericVerifierVerumLeafRuleRows
      tokenTable width tokenCount 2 0 gammaBoundary Gamma.length
      (compactAdditiveBoolTag (compactVerumRuleCheck Gamma)) := by
  refine ⟨rfl, rfl, ?_⟩
  exact (compactAdditiveVerumRuleCheck_iff hGamma).mpr rfl

theorem CompactNumericVerifierVerumLeafRuleRows.exists_canonical
    (Gamma : List (List Nat)) :
    ∃ tokenTable width tokenCount gammaStart gammaFinish gammaBoundary,
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount gammaStart gammaFinish Gamma ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          gammaBoundary Gamma ∧
      CompactNumericVerifierVerumLeafRuleRows
        tokenTable width tokenCount 2 0 gammaBoundary Gamma.length
        (compactAdditiveBoolTag (compactVerumRuleCheck Gamma)) := by
  have hcanonical := compactAdditiveNatListListDirectLayout_canonical
    [] Gamma []
  dsimp only at hcanonical
  rcases hcanonical with
    ⟨gammaBoundary, hGammaLayout, hGammaRows, hGammaSize⟩
  have htyped : CompactAdditiveNatListListDirectLayout
      (compactFixedWidthTableCode
        (compactBinaryNatPayloadBits (compactAdditiveEncode Gamma)).length
        (compactAdditiveEncode Gamma))
      (compactBinaryNatPayloadBits (compactAdditiveEncode Gamma)).length
      (compactAdditiveEncode Gamma).length 0
      (compactAdditiveEncode Gamma).length Gamma := by
    exact ⟨gammaBoundary, by simpa using hGammaLayout,
      by simpa using hGammaRows, by simpa using hGammaSize⟩
  have hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode
        (compactBinaryNatPayloadBits (compactAdditiveEncode Gamma)).length
        (compactAdditiveEncode Gamma))
      (compactBinaryNatPayloadBits (compactAdditiveEncode Gamma)).length
      (compactAdditiveEncode Gamma).length gammaBoundary Gamma := by
    simpa using hGammaRows
  exact ⟨compactFixedWidthTableCode
      (compactBinaryNatPayloadBits (compactAdditiveEncode Gamma)).length
      (compactAdditiveEncode Gamma),
    (compactBinaryNatPayloadBits (compactAdditiveEncode Gamma)).length,
    (compactAdditiveEncode Gamma).length, 0,
    (compactAdditiveEncode Gamma).length, gammaBoundary,
    htyped, hrows,
    CompactNumericVerifierVerumLeafRuleRows.of_gammaRows hrows⟩

#print axioms CompactNumericVerifierVerumLeafRuleRows.of_gammaRows
#print axioms CompactNumericVerifierVerumLeafRuleRows.exists_canonical

end FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness
