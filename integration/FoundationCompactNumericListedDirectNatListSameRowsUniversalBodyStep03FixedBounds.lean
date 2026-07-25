import integration.FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep04FixedBounds

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep03FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep04FixedBounds

def compactAdditiveNatListSameRowsBodyAfter03
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 3 :=
  (compactAdditiveNatListSameRowsBodyAfter04 tokenTable width tokenCount
    sourceBoundary targetBoundary).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm tokenCount))

def sameRowsBodyAfter03FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
    (sameRowsBodyAfter04FormulaCodePolynomial numericBound bitBound)

theorem compactAdditiveNatListSameRowsBodyAfter03_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListSameRowsBodyAfter03 tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      sameRowsBodyAfter03FormulaCodePolynomial numericBound bitBound := by
  let body := compactAdditiveNatListSameRowsBodyAfter04 tokenTable width
    tokenCount sourceBoundary targetBoundary
  let bodyCode := sameRowsBodyAfter04FormulaCodePolynomial numericBound bitBound
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode]
    exact compactAdditiveNatListSameRowsBodyAfter04_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hraw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public
      tokenCount bodyCode body hbody
  have hmono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      3 htokenCount (Nat.le_refl bodyCode)
  have htotal := hraw.trans hmono
  simpa only [compactAdditiveNatListSameRowsBodyAfter03,
    sameRowsBodyAfter03FormulaCodePolynomial, body, bodyCode,
    sameRowsClosedShift_eq_public, sameRowsPublicClosedShift] using htotal

#print axioms
  compactAdditiveNatListSameRowsBodyAfter03_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep03FixedBounds
