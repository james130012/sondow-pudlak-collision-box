import integration.FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds
import integration.FoundationCompactPABitAtomArityCodeBounds
import integration.FoundationCompactPAFormulaIffCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed inner-universal bounds for token slices

This module closes the syntax coordinate of the bit-index body before charging
the finite branches and the contextual bounded-universal shell.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitAtomArityCodeBounds
open FoundationCompactPAFormulaIffCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds

def tokenSliceBitUniversalBodyCodePolynomial (bitBound : Nat) : Nat :=
  64 * (bitAtomArityCodePolynomial
    (tokenSliceBitUniversalBodyTermCodePolynomial bitBound) + 1)

theorem tokenSliceAtValuationBitBody_code_length_le_fixed
    (tokenTable width sourceStart targetStart bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    (binaryFormulaCode
      (tokenSliceAtValuationBitBody
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart))).length <=
      tokenSliceBitUniversalBodyCodePolynomial bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (&0 : ValuationTerm)
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift sourceTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift targetTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift tableTerm)
  let sourceSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceShift + !!offsetTerm’
  let targetSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetShift + !!offsetTerm’
  let sourceProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceSum * !!widthShift’
  let targetProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetSum * !!widthShift’
  let sourceIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceProduct + !!bitTerm’
  let targetIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetProduct + !!bitTerm’
  let termBound := tokenSliceBitUniversalBodyTermCodePolynomial bitBound
  let sourceAtom := binaryBitAtomAtTerms sourceIndex tableShift
  let targetAtom := binaryBitAtomAtTerms targetIndex tableShift
  have hterms := tokenSliceBitUniversalTerms_code_le_fixed tokenTable width
    sourceStart targetStart bitBound htableSize hwidthSize hsourceStartSize
    htargetStartSize
  have hsourceIndexBound :
      (binaryTermCode sourceIndex).length <= termBound := by
    simpa only [sourceIndex, sourceProduct, sourceSum, sourceShift, offsetTerm,
      widthShift, bitTerm, tableTerm, widthTerm, sourceTerm, targetTerm,
      termBound] using hterms.1
  have htargetIndexBound :
      (binaryTermCode targetIndex).length <= termBound := by
    simpa only [targetIndex, targetProduct, targetSum, targetShift, offsetTerm,
      widthShift, bitTerm, tableTerm, widthTerm, sourceTerm, targetTerm,
      termBound] using hterms.2.1
  have htableShiftBound :
      (binaryTermCode tableShift).length <= termBound := by
    simpa only [tableShift, tableTerm, widthTerm, sourceTerm, targetTerm,
      termBound] using hterms.2.2
  have hsourceAtom :
      (binaryFormulaCode sourceAtom).length <=
        bitAtomArityCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_arity sourceIndex
      tableShift termBound hsourceIndexBound htableShiftBound
  have htargetAtom :
      (binaryFormulaCode targetAtom).length <=
        bitAtomArityCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_arity targetIndex
      tableShift termBound htargetIndexBound htableShiftBound
  have hiff := binaryFormulaCode_iff_length_le sourceAtom targetAtom
  have hformula :
      tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm targetTerm =
        sourceAtom 🡘 targetAtom := by
    rfl
  rw [hformula]
  unfold tokenSliceBitUniversalBodyCodePolynomial
  dsimp only [termBound] at hsourceAtom htargetAtom
  omega

/-
The direct term-by-term free-variable expansion is retained for reference but
not elaborated: the structural `Rewriting.free` argument below is equivalent
and avoids a multi-minute quoted-formula reduction on small machines.

private theorem binaryFunctionTerm_freeVariables_tokenSliceUniversal
    {boundArity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem bShiftTerm_freeVariables_eq_tokenSliceUniversal
    {boundArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (Rew.bShift term).freeVariables = term.freeVariables := by
  ext candidate
  exact LO.FirstOrder.Semiterm.fvar?_bShift

theorem tokenSliceAtValuationBitBody_freeVariables_subset_singleton
    (tokenTable width sourceStart targetStart : Nat) :
    (tokenSliceAtValuationBitBody
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm sourceStart)
      (shortBinaryNumeralTerm targetStart)).freeVariables ⊆ {0} := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (&0 : ValuationTerm)
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift sourceTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift targetTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift tableTerm)
  let sourceSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceShift + !!offsetTerm’
  let targetSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetShift + !!offsetTerm’
  let sourceProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceSum * !!widthShift’
  let targetProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetSum * !!widthShift’
  let sourceIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceProduct + !!bitTerm’
  let targetIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetProduct + !!bitTerm’
  let sourceAtom := binaryBitAtomAtTerms sourceIndex tableShift
  let targetAtom := binaryBitAtomAtTerms targetIndex tableShift
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hsource : sourceTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty sourceStart
  have htarget : targetTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty targetStart
  have htableFree :=
    shiftedTerm_freeVariables_eq_empty_of_closed tableTerm htable
  have hwidthFree :=
    shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidth
  have hsourceFree :=
    shiftedTerm_freeVariables_eq_empty_of_closed sourceTerm hsource
  have htargetFree :=
    shiftedTerm_freeVariables_eq_empty_of_closed targetTerm htarget
  have htableShift : tableShift.freeVariables = ∅ := by
    dsimp only [tableShift]
    exact bShift_freeVariables_eq_empty_of_empty _ htableFree
  have hwidthShift : widthShift.freeVariables = ∅ := by
    dsimp only [widthShift]
    exact bShift_freeVariables_eq_empty_of_empty _ hwidthFree
  have hsourceShift : sourceShift.freeVariables = ∅ := by
    dsimp only [sourceShift]
    exact bShift_freeVariables_eq_empty_of_empty _ hsourceFree
  have htargetShift : targetShift.freeVariables = ∅ := by
    dsimp only [targetShift]
    exact bShift_freeVariables_eq_empty_of_empty _ htargetFree
  have hoffset : offsetTerm.freeVariables ⊆ {0} := by
    dsimp only [offsetTerm]
    rw [bShiftTerm_freeVariables_eq_tokenSliceUniversal]
    simp
  have hbit : bitTerm.freeVariables ⊆ {0} := by
    simp [bitTerm]
  have hsourceSum : sourceSum.freeVariables ⊆ {0} := by
    dsimp only [sourceSum]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm,
      binaryFunctionTerm_freeVariables_tokenSliceUniversal, hsourceShift]
    simpa using hoffset
  have htargetSum : targetSum.freeVariables ⊆ {0} := by
    dsimp only [targetSum]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm,
      binaryFunctionTerm_freeVariables_tokenSliceUniversal, htargetShift]
    simpa using hoffset
  have hsourceProduct : sourceProduct.freeVariables ⊆ {0} := by
    dsimp only [sourceProduct]
    rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm,
      binaryFunctionTerm_freeVariables_tokenSliceUniversal, hwidthShift,
      Finset.union_empty]
    exact hsourceSum
  have htargetProduct : targetProduct.freeVariables ⊆ {0} := by
    dsimp only [targetProduct]
    rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm,
      binaryFunctionTerm_freeVariables_tokenSliceUniversal, hwidthShift,
      Finset.union_empty]
    exact htargetSum
  have hsourceIndex : sourceIndex.freeVariables ⊆ {0} := by
    dsimp only [sourceIndex]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm,
      binaryFunctionTerm_freeVariables_tokenSliceUniversal]
    exact Finset.union_subset hsourceProduct hbit
  have htargetIndex : targetIndex.freeVariables ⊆ {0} := by
    dsimp only [targetIndex]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm,
      binaryFunctionTerm_freeVariables_tokenSliceUniversal]
    exact Finset.union_subset htargetProduct hbit
  have hsourceAtom :
      sourceAtom.freeVariables ⊆ {0} := by
    dsimp only [sourceAtom]
    exact embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      bitDef.val ![sourceIndex, tableShift] ({0} : Finset Nat) (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hsourceIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                rw [htableShift]
                simp
            | succ coordinate => exact Fin.elim0 coordinate)
  have htargetAtom :
      targetAtom.freeVariables ⊆ {0} := by
    dsimp only [targetAtom]
    exact embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      bitDef.val ![targetIndex, tableShift] ({0} : Finset Nat) (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact htargetIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                rw [htableShift]
                simp
            | succ coordinate => exact Fin.elim0 coordinate)
  have hformula :
      tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm targetTerm =
        sourceAtom 🡘 targetAtom := by
    rfl
  rw [hformula]
  simpa only [LogicalConnective.iff,
    LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_imp] using
      Finset.union_subset
        (Finset.union_subset hsourceAtom htargetAtom)
        (Finset.union_subset htargetAtom hsourceAtom)

-/

#print axioms tokenSliceAtValuationBitBody_code_length_le_fixed

end FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds
