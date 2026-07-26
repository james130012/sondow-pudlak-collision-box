import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectEmbeddingAlignment

/-!
# Direct syntax for the eighteen bounded sequent-step witnesses

The original nine-coordinate bounded-row formula is exposed as eighteen
bounded existential witnesses over the exact original twenty-six-coordinate
step terminal.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax

def compactSequentFormulaStepRowBoundedDirectCorePublicTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    Fin 8 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm suffixBoundary,
    shortBinaryNumeralTerm suffixCount,
    shortBinaryNumeralTerm valueBoundary,
    shortBinaryNumeralTerm valueCount,
    shortBinaryNumeralTerm rowIndex]

def compactSequentFormulaStepRowBoundedDirectPublicTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) :
    Fin 9 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactSequentFormulaStepRowBoundedDirectCorePublicTerms tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex)
    ![shortBinaryNumeralTerm valueBound]

def compactSequentFormulaStepRowBoundedDirectClosedFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactSequentFormulaStepRowBoundedDef.val) ⇜
    compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound

def compactSequentFormulaStepRowBoundedDirectRawPublicTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    Fin 8 -> ArithmeticSemiterm Nat 18 :=
  fun coordinate =>
    sourceSubstitutionLift 18
      (compactSequentFormulaStepRowBoundedDirectCorePublicTerms tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex coordinate)

def compactSequentFormulaStepRowBoundedDirectRawWitnessTerms :
    Fin 18 -> ArithmeticSemiterm Nat 18 :=
  fun coordinate =>
    #(
      compactSequentFormulaStepRowBoundedDirectReverseIndex coordinate :
        Fin 18)

def compactSequentFormulaStepRowBoundedDirectRawTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    Fin 26 -> ArithmeticSemiterm Nat 18 :=
  Matrix.vecAppend rfl
    (compactSequentFormulaStepRowBoundedDirectRawPublicTerms tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex)
    compactSequentFormulaStepRowBoundedDirectRawWitnessTerms

def compactSequentFormulaStepRowBoundedDirectRawTerminal
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    ArithmeticSemiformula Nat 18 :=
  (Rewriting.emb (ξ := Nat) compactSequentFormulaStepDef.val) ⇜
    compactSequentFormulaStepRowBoundedDirectRawTerms tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex

theorem
    compactSequentFormulaStepRowBoundedDirectSourceRawTerms_rewriting
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) :
    sourceSubstitutionQpow
        (compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex valueBound) 18 ∘
      compactSequentFormulaStepRowBoundedDirectSourceRawTerms =
    compactSequentFormulaStepRowBoundedDirectRawTerms tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex := by
  funext coordinate
  unfold
    compactSequentFormulaStepRowBoundedDirectSourceRawTerms
    compactSequentFormulaStepRowBoundedDirectRawTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · unfold
      compactSequentFormulaStepRowBoundedDirectSourceRawPublicTerms
      compactSequentFormulaStepRowBoundedDirectRawPublicTerms
    calc
      sourceSubstitutionQpow
          (compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable
            width tokenCount suffixBoundary suffixCount valueBoundary
            valueCount rowIndex valueBound) 18
          (#(⟨18 + (⟨coordinate, by omega⟩ : Fin 8).val,
            by omega⟩ : Fin 27)) =
        sourceSubstitutionLift 18
          (compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable
            width tokenCount suffixBoundary suffixCount valueBoundary
            valueCount rowIndex valueBound
            ⟨coordinate, by omega⟩) := by
              simpa using
                (sourceSubstitutionQpow_shiftedBVar
                  (compactSequentFormulaStepRowBoundedDirectPublicTerms
                    tokenTable width tokenCount suffixBoundary suffixCount
                    valueBoundary valueCount rowIndex valueBound)
                  18 ⟨coordinate, by omega⟩)
      _ = sourceSubstitutionLift 18
          (compactSequentFormulaStepRowBoundedDirectCorePublicTerms tokenTable
            width tokenCount suffixBoundary suffixCount valueBoundary
            valueCount rowIndex ⟨coordinate, hcoordinate⟩) := by
              simp [
                compactSequentFormulaStepRowBoundedDirectPublicTerms,
                Matrix.vecAppend_eq_ite, hcoordinate]
  · unfold
      compactSequentFormulaStepRowBoundedDirectSourceRawWitnessTerms
      compactSequentFormulaStepRowBoundedDirectRawWitnessTerms
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

theorem
    compactSequentFormulaStepRowBoundedDirectSourceRawTerminal_rewriting
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) :
    sourceSubstitutionQpow
        (compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex valueBound) 18 ▹
      compactSequentFormulaStepRowBoundedDirectSourceRawTerminal =
    compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex := by
  unfold compactSequentFormulaStepRowBoundedDirectSourceRawTerminal
    compactSequentFormulaStepRowBoundedDirectRawTerminal
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  rw [
    compactSequentFormulaStepRowBoundedDirectSourceRawTerms_rewriting]

theorem compactSequentFormulaStepRowBoundedDirectClosedFormula_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) :
    compactSequentFormulaStepRowBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
        (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex) := by
  unfold compactSequentFormulaStepRowBoundedDirectClosedFormula
  rw [compactSequentFormulaStepRowBoundedDef_emb_eq_directSourceRawBody]
  unfold compactSequentFormulaStepRowBoundedDirectSourceRawBody
  change Rew.subst
      (compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex valueBound) ▹
      sourceBoundedWitnessFormula (#8 : ArithmeticSemiterm Nat 9) 18
        compactSequentFormulaStepRowBoundedDirectSourceRawTerminal = _
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [
    compactSequentFormulaStepRowBoundedDirectSourceRawTerminal_rewriting]
  have hbound :
      Rew.subst
          (compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable
            width tokenCount suffixBoundary suffixCount valueBoundary
            valueCount rowIndex valueBound)
          (#8 : ArithmeticSemiterm Nat 9) =
        shortBinaryNumeralTerm valueBound := by
    change
      compactSequentFormulaStepRowBoundedDirectPublicTerms tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex valueBound ⟨8, by omega⟩ =
        shortBinaryNumeralTerm valueBound
    simp [compactSequentFormulaStepRowBoundedDirectPublicTerms,
      Matrix.vecAppend_eq_ite]
  rw [hbound]
  rfl

#print axioms compactSequentFormulaStepRowBoundedDef_emb_eq_directSourceRawBody
#print axioms
  compactSequentFormulaStepRowBoundedDirectClosedFormula_alignment

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
