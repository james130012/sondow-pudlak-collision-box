import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

/-!
# Open-index syntax for one bounded sequent-formula step row

The row index is an arbitrary valuation term.  The remaining seven public
coordinates are closed binary numerals, while the eighteen row coordinates
remain explicit bounded witnesses.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

def compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm) :
    Fin 8 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm suffixBoundary,
    shortBinaryNumeralTerm suffixCount,
    shortBinaryNumeralTerm valueBoundary,
    shortBinaryNumeralTerm valueCount,
    indexTerm]

def compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    Fin 9 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount indexTerm)
    ![shortBinaryNumeralTerm valueBound]

def compactSequentFormulaStepRowBoundedAtValuationIndexRawPublicTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm) :
    Fin 8 -> ArithmeticSemiterm Nat 18 :=
  fun coordinate =>
    sourceSubstitutionLift 18
      (compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount indexTerm coordinate)

def compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm) :
    Fin 26 -> ArithmeticSemiterm Nat 18 :=
  Matrix.vecAppend rfl
    (compactSequentFormulaStepRowBoundedAtValuationIndexRawPublicTerms
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount indexTerm)
    compactSequentFormulaStepRowBoundedDirectRawWitnessTerms

def compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm) :
    ArithmeticSemiformula Nat 18 :=
  (Rewriting.emb (ξ := Nat) compactSequentFormulaStepDef.val) ⇜
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      indexTerm

def compactSequentFormulaStepRowBoundedAtOpenIndexRawBody
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat) :
    ArithmeticSemiformula Nat 18 :=
  compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount
    (&0 : ValuationTerm)

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexSourceRawTerms_rewriting
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount valueBound indexTerm) 18 ∘
      compactSequentFormulaStepRowBoundedDirectSourceRawTerms =
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      indexTerm := by
  funext coordinate
  unfold
    compactSequentFormulaStepRowBoundedDirectSourceRawTerms
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · unfold
      compactSequentFormulaStepRowBoundedDirectSourceRawPublicTerms
      compactSequentFormulaStepRowBoundedAtValuationIndexRawPublicTerms
    calc
      sourceSubstitutionQpow
          (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
            tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount valueBound indexTerm) 18
          (#(⟨18 + (⟨coordinate, by omega⟩ : Fin 8).val,
            by omega⟩ : Fin 27)) =
        sourceSubstitutionLift 18
          (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
            tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount valueBound indexTerm
            ⟨coordinate, by omega⟩) := by
              simpa using
                (sourceSubstitutionQpow_shiftedBVar
                  (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
                    tokenTable width tokenCount suffixBoundary suffixCount
                    valueBoundary valueCount valueBound indexTerm)
                  18 ⟨coordinate, by omega⟩)
      _ = sourceSubstitutionLift 18
          (compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms
            tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount indexTerm
            ⟨coordinate, hcoordinate⟩) := by
              simp [
                compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms,
                Matrix.vecAppend_eq_ite, hcoordinate]
  · unfold
      compactSequentFormulaStepRowBoundedDirectSourceRawWitnessTerms
      compactSequentFormulaStepRowBoundedDirectRawWitnessTerms
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexSourceRawTerminal_rewriting
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount valueBound indexTerm) 18 ▹
      compactSequentFormulaStepRowBoundedDirectSourceRawTerminal =
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      indexTerm := by
  unfold compactSequentFormulaStepRowBoundedDirectSourceRawTerminal
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  rw [
    compactSequentFormulaStepRowBoundedAtValuationIndexSourceRawTerms_rewriting]

theorem compactSequentFormulaStepRowBoundedAtValuationIndexFormula_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound indexTerm =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
        (compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount indexTerm) := by
  unfold compactSequentFormulaStepRowBoundedAtValuationIndexFormula
  rw [compactSequentFormulaStepRowBoundedDef_emb_eq_directSourceRawBody]
  unfold compactSequentFormulaStepRowBoundedDirectSourceRawBody
  have hpublicTerms :
      (![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm suffixBoundary,
          shortBinaryNumeralTerm suffixCount,
          shortBinaryNumeralTerm valueBoundary,
          shortBinaryNumeralTerm valueCount,
          indexTerm,
          shortBinaryNumeralTerm valueBound] :
          Fin 9 -> ValuationTerm) =
        compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount valueBound indexTerm := by
    funext coordinate
    fin_cases coordinate <;>
      simp [
        compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms,
        compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms,
        Matrix.vecAppend_eq_ite]
  rw [hpublicTerms]
  change Rew.subst
      (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount valueBound indexTerm) ▹
      sourceBoundedWitnessFormula (#8 : ArithmeticSemiterm Nat 9) 18
        compactSequentFormulaStepRowBoundedDirectSourceRawTerminal = _
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [
    compactSequentFormulaStepRowBoundedAtValuationIndexSourceRawTerminal_rewriting]
  have hbound :
      Rew.subst
          (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
            tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount valueBound indexTerm)
          (#8 : ArithmeticSemiterm Nat 9) =
        shortBinaryNumeralTerm valueBound := by
    change
      compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          valueBound indexTerm ⟨8, by omega⟩ =
        shortBinaryNumeralTerm valueBound
    simp [
      compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms,
      Matrix.vecAppend_eq_ite]
  rw [hbound]
  rfl

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexSourceRawTerms_rewriting
#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexSourceRawTerminal_rewriting
#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexFormula_alignment

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
