import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax

/-! # Terminal substitution for the eighteen bounded sequent-step witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax

def compactSequentFormulaStepRowBoundedDirectWitnessValues
    (row : CompactSequentFormulaStepCoordinates) : Fin 18 -> Nat :=
  ![row.parserValueBound,
    row.parserTableWidth,
    row.parserStateBoundary,
    row.value.boundarySize,
    row.value.count,
    row.value.boundary,
    row.value.finish,
    row.value.start,
    row.next.boundarySize,
    row.next.count,
    row.next.boundary,
    row.next.finish,
    row.next.start,
    row.current.boundarySize,
    row.current.count,
    row.current.boundary,
    row.current.finish,
    row.current.start]

def compactSequentFormulaStepRowBoundedDirectClosedWitnessTerms
    (row : CompactSequentFormulaStepCoordinates) :
    Fin 18 -> ValuationTerm :=
  fun coordinate =>
    shortBinaryNumeralTerm
      (compactSequentFormulaStepRowBoundedDirectWitnessValues row
        (compactSequentFormulaStepRowBoundedDirectReverseIndex coordinate))

def compactSequentFormulaStepRowBoundedDirectClosedTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    Fin 26 -> ValuationTerm :=
  Matrix.vecAppend rfl
    (compactSequentFormulaStepRowBoundedDirectCorePublicTerms tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex)
    (compactSequentFormulaStepRowBoundedDirectClosedWitnessTerms row)

theorem compactSequentFormulaStepRowBoundedDirectClosedTerms_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepRowBoundedDirectClosedTerms tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex row =
      compactSequentFormulaStepDirectPublicTerms tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex row := by
  funext coordinate
  fin_cases coordinate <;>
    simp [compactSequentFormulaStepRowBoundedDirectClosedTerms,
      compactSequentFormulaStepRowBoundedDirectCorePublicTerms,
      compactSequentFormulaStepRowBoundedDirectClosedWitnessTerms,
      compactSequentFormulaStepRowBoundedDirectWitnessValues,
      compactSequentFormulaStepRowBoundedDirectReverseIndex,
      compactSequentFormulaStepDirectPublicTerms,
      Matrix.vecAppend_eq_ite]

private theorem substitute_sourceSubstitutionLift18
    (values : Fin 18 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 18 term) = term := by
  simpa only using
    (FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.substitute_sourceSubstitutionLift
      (depth := 18) values term)

theorem compactSequentFormulaStepRowBoundedDirectRawTerms_substitution
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    (Rew.subst (fun index => shortBinaryNumeralTerm
        (compactSequentFormulaStepRowBoundedDirectWitnessValues row index))) ∘
      compactSequentFormulaStepRowBoundedDirectRawTerms tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex =
      compactSequentFormulaStepRowBoundedDirectClosedTerms tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex row := by
  funext coordinate
  unfold compactSequentFormulaStepRowBoundedDirectRawTerms
    compactSequentFormulaStepRowBoundedDirectClosedTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · simp only [compactSequentFormulaStepRowBoundedDirectRawPublicTerms]
    exact substitute_sourceSubstitutionLift18 _ _
  · simp [compactSequentFormulaStepRowBoundedDirectRawWitnessTerms,
      compactSequentFormulaStepRowBoundedDirectClosedWitnessTerms,
      Rew.subst_bvar]

theorem compactSequentFormulaStepRowBoundedDirectRawTerminal_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex ⇜
      (fun index => shortBinaryNumeralTerm
        (compactSequentFormulaStepRowBoundedDirectWitnessValues row index)) =
    compactSequentFormulaStepDirectClosedFormula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (compactSequentFormulaStepRowBoundedDirectWitnessValues row index)) ▹
    compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex = _
  unfold compactSequentFormulaStepRowBoundedDirectRawTerminal
    compactSequentFormulaStepDirectClosedFormula
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  rw [compactSequentFormulaStepRowBoundedDirectRawTerms_substitution]
  rw [compactSequentFormulaStepRowBoundedDirectClosedTerms_alignment]

#print axioms
  compactSequentFormulaStepRowBoundedDirectClosedTerms_alignment
#print axioms
  compactSequentFormulaStepRowBoundedDirectRawTerms_substitution
#print axioms
  compactSequentFormulaStepRowBoundedDirectRawTerminal_alignment

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
