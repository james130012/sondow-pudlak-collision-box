import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax

/-!
# Open-index terminal substitution for the eighteen row witnesses

Installing the checked row coordinates leaves the public row-index term
untouched and recovers the original twenty-six-coordinate step formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax

def compactSequentFormulaStepDirectPublicTermsAtValuationIndex
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactSequentFormulaStepCoordinates) :
    Fin 26 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm suffixBoundary,
    shortBinaryNumeralTerm suffixCount,
    shortBinaryNumeralTerm valueBoundary,
    shortBinaryNumeralTerm valueCount,
    indexTerm,
    shortBinaryNumeralTerm row.current.start,
    shortBinaryNumeralTerm row.current.finish,
    shortBinaryNumeralTerm row.current.boundary,
    shortBinaryNumeralTerm row.current.count,
    shortBinaryNumeralTerm row.current.boundarySize,
    shortBinaryNumeralTerm row.next.start,
    shortBinaryNumeralTerm row.next.finish,
    shortBinaryNumeralTerm row.next.boundary,
    shortBinaryNumeralTerm row.next.count,
    shortBinaryNumeralTerm row.next.boundarySize,
    shortBinaryNumeralTerm row.value.start,
    shortBinaryNumeralTerm row.value.finish,
    shortBinaryNumeralTerm row.value.boundary,
    shortBinaryNumeralTerm row.value.count,
    shortBinaryNumeralTerm row.value.boundarySize,
    shortBinaryNumeralTerm row.parserStateBoundary,
    shortBinaryNumeralTerm row.parserTableWidth,
    shortBinaryNumeralTerm row.parserValueBound]

def compactSequentFormulaStepDirectFormulaAtValuationIndex
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactSequentFormulaStepCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactSequentFormulaStepDef.val) ⇜
    compactSequentFormulaStepDirectPublicTermsAtValuationIndex tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount indexTerm
      row

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms_substitution
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactSequentFormulaStepCoordinates) :
    (Rew.subst (fun coordinate => shortBinaryNumeralTerm
        (compactSequentFormulaStepRowBoundedDirectWitnessValues row
          coordinate))) ∘
      compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        indexTerm =
    compactSequentFormulaStepDirectPublicTermsAtValuationIndex tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        indexTerm row := by
  have hpublicTerms :
      compactSequentFormulaStepDirectPublicTermsAtValuationIndex tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          indexTerm row =
        Matrix.vecAppend rfl
          (compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms
            tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount indexTerm)
          (compactSequentFormulaStepRowBoundedDirectClosedWitnessTerms row) := by
    funext coordinate
    fin_cases coordinate <;>
      simp [compactSequentFormulaStepDirectPublicTermsAtValuationIndex,
        compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms,
        compactSequentFormulaStepRowBoundedDirectClosedWitnessTerms,
        compactSequentFormulaStepRowBoundedDirectWitnessValues,
        compactSequentFormulaStepRowBoundedDirectReverseIndex,
        Matrix.vecAppend_eq_ite]
  rw [hpublicTerms]
  funext coordinate
  unfold
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · simp only [
      compactSequentFormulaStepRowBoundedAtValuationIndexRawPublicTerms]
    simpa only using
      (FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.substitute_sourceSubstitutionLift
        (depth := 18)
        (fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues row
            coordinate))
        (compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount indexTerm ⟨coordinate, hcoordinate⟩))
  · simp [compactSequentFormulaStepRowBoundedDirectRawWitnessTerms,
      compactSequentFormulaStepRowBoundedDirectClosedWitnessTerms,
      Rew.subst_bvar]

theorem compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        indexTerm ⇜
      (fun coordinate => shortBinaryNumeralTerm
        (compactSequentFormulaStepRowBoundedDirectWitnessValues row
          coordinate)) =
    compactSequentFormulaStepDirectFormulaAtValuationIndex tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount indexTerm
      row := by
  change Rew.subst (fun coordinate => shortBinaryNumeralTerm
      (compactSequentFormulaStepRowBoundedDirectWitnessValues row
        coordinate)) ▹
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      indexTerm = _
  unfold
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal
    compactSequentFormulaStepDirectFormulaAtValuationIndex
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  rw [
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms_substitution]

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms_substitution
#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal_alignment

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalAlignment
