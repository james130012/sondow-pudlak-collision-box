import integration.FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep03FixedBounds

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep02FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep04FixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep03FixedBounds

def compactAdditiveNatListSameRowsBodyAfter02
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 2 :=
  (compactAdditiveNatListSameRowsBodyAfter03 tokenTable width tokenCount
    sourceBoundary targetBoundary).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm tokenCount))

def sameRowsBodyAfter02FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
    (sameRowsBodyAfter03FormulaCodePolynomial numericBound bitBound)

theorem compactAdditiveNatListSameRowsBodyAfter02_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListSameRowsBodyAfter02 tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      sameRowsBodyAfter02FormulaCodePolynomial numericBound bitBound := by
  let body := compactAdditiveNatListSameRowsBodyAfter03 tokenTable width
    tokenCount sourceBoundary targetBoundary
  let bodyCode := sameRowsBodyAfter03FormulaCodePolynomial numericBound bitBound
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode]
    exact compactAdditiveNatListSameRowsBodyAfter03_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hraw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public
      tokenCount bodyCode body hbody
  have hmono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      2 htokenCount (Nat.le_refl bodyCode)
  have htotal := hraw.trans hmono
  simpa only [compactAdditiveNatListSameRowsBodyAfter02,
    sameRowsBodyAfter02FormulaCodePolynomial, body, bodyCode,
    sameRowsClosedShift_eq_public, sameRowsPublicClosedShift] using htotal

#print axioms
  compactAdditiveNatListSameRowsBodyAfter02_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep02FixedBounds
