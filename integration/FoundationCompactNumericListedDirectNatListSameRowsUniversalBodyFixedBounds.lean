import integration.FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep02FixedBounds

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep04FixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep03FixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep02FixedBounds

def compactAdditiveNatListSameRowsBodyAfter01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (compactAdditiveNatListSameRowsBodyAfter02 tokenTable width tokenCount
    sourceBoundary targetBoundary).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm tokenCount))

theorem compactAdditiveNatListSameRowsBody_eq_after01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveNatListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary =
      compactAdditiveNatListSameRowsBodyAfter01 tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  rfl

theorem compactAdditiveNatListSameRowsBody_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      sameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
  let body := compactAdditiveNatListSameRowsBodyAfter02 tokenTable width
    tokenCount sourceBoundary targetBoundary
  let bodyCode := sameRowsBodyAfter02FormulaCodePolynomial numericBound bitBound
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode]
    exact compactAdditiveNatListSameRowsBodyAfter02_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hraw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public
      tokenCount bodyCode body hbody
  have hmono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      1 htokenCount (Nat.le_refl bodyCode)
  have htotal := hraw.trans hmono
  rw [compactAdditiveNatListSameRowsBody_eq_after01]
  simpa only [compactAdditiveNatListSameRowsBodyAfter01,
    sameRowsUniversalBodyFormulaCodePolynomial,
    sameRowsBodyAfter04FormulaCodePolynomial,
    sameRowsBodyAfter03FormulaCodePolynomial,
    sameRowsBodyAfter02FormulaCodePolynomial, body, bodyCode,
    sameRowsClosedShift_eq_public, sameRowsPublicClosedShift] using htotal

#print axioms compactAdditiveNatListSameRowsBody_eq_after01
#print axioms compactAdditiveNatListSameRowsBody_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyFixedBounds
