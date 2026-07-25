import integration.FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep04FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds

def sameRowsPublicClosedShift :
    (arity : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat arity :=
  FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift

@[simp] theorem sameRowsClosedShift_eq_public
    (term : ValuationTerm) :
    forall arity,
      closedShift arity term = sameRowsPublicClosedShift arity term
  | 0 => rfl
  | arity + 1 => by
      simp only [closedShift, sameRowsPublicClosedShift,
        FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift,
        sameRowsClosedShift_eq_public term arity]

def compactAdditiveNatListSameRowsBodyAfter04
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  (compactAdditiveNatListSameRowsTerminal tokenTable width tokenCount
    sourceBoundary targetBoundary).bexsLTSucc
      (closedShift 4 (shortBinaryNumeralTerm tokenCount))

def sameRowsBodyAfter04FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
    (sameRowsUniversalTerminalFormulaCodePolynomial bitBound)

theorem compactAdditiveNatListSameRowsBodyAfter04_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListSameRowsBodyAfter04 tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      sameRowsBodyAfter04FormulaCodePolynomial numericBound bitBound := by
  let terminal := compactAdditiveNatListSameRowsTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary
  let terminalCode := sameRowsUniversalTerminalFormulaCodePolynomial bitBound
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hterminal : (binaryFormulaCode terminal).length <= terminalCode := by
    dsimp only [terminal, terminalCode]
    exact compactAdditiveNatListSameRowsTerminal_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize
  have hraw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public
      tokenCount terminalCode terminal hterminal
  have hmono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      4 htokenCount (Nat.le_refl terminalCode)
  have htotal := hraw.trans hmono
  simpa only [compactAdditiveNatListSameRowsBodyAfter04,
    sameRowsBodyAfter04FormulaCodePolynomial, terminal, terminalCode,
    sameRowsClosedShift_eq_public, sameRowsPublicClosedShift] using htotal

#print axioms
  compactAdditiveNatListSameRowsBodyAfter04_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyStep04FixedBounds
