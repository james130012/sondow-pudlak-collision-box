import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

/-!
# Public structural resource for one additive token cell

The cell consists of a cursor bound, a successor equality, and one checked
fixed-width table entry.  All three children are bounded here without a
caller-supplied proof resource.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 150000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
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

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) : Nat :=
  let valuation := zeroValuation
  let successorTerm : ValuationTerm := ‘!!cursorTerm + 1’
  let cursorFormula : ValuationFormula :=
    “!!cursorTerm < !!tokenCountTerm”
  let successorFormula : ValuationFormula :=
    “!!nextTerm = !!cursorTerm + 1”
  let entryFormula := compactFixedWidthEntryAtValuationFormula
    tokenTableTerm widthTerm cursorTerm valueTerm
  let innerFormula := successorFormula ⋏ entryFormula
  let innerResource := hybridConjunctionStructuralPayloadEnvelope valuation
    successorFormula entryFormula
    (compilePositiveRelationPayloadPolynomial valuation Language.Eq.eq
      ![nextTerm, successorTerm])
    (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial valuation
      tokenTableTerm widthTerm cursorTerm valueTerm)
  hybridConjunctionStructuralPayloadEnvelope valuation cursorFormula
    innerFormula
    (compilePositiveRelationPayloadPolynomial valuation Language.ORing.Rel.lt
      ![cursorTerm, tokenCountTerm])
    innerResource

theorem
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm)
    (htable : tokenTableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (htokenCount : tokenCountTerm.freeVariables = ∅)
    (hcursor : cursorTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hnext : nextTerm.freeVariables = ∅)
    (hcell : CompactAdditiveTokenCell
      (termValue zeroValuation tokenTableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation tokenCountTerm)
      (termValue zeroValuation cursorTerm)
      (termValue zeroValuation valueTerm)
      (termValue zeroValuation nextTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm
          hcell) ≤
      compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm := by
  let successorTerm : ValuationTerm := ‘!!cursorTerm + 1’
  let cursorCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm]
      hcell.1
  let successorCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![nextTerm, successorTerm] (by
        change termValue zeroValuation nextTerm =
          termValue zeroValuation successorTerm
        simpa [successorTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne]
          using hcell.2.1)
  let entryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      tokenTableTerm widthTerm cursorTerm valueTerm hcell.2.2
  have hcursorVars : cursorTerm.freeVariables ⊆ {0} := by
    rw [hcursor]
    simp
  have htokenCountVars : tokenCountTerm.freeVariables ⊆ {0} := by
    rw [htokenCount]
    simp
  have hnextVars : nextTerm.freeVariables ⊆ {0} := by
    rw [hnext]
    simp
  have hsuccessorClosed : successorTerm.freeVariables = ∅ := by
    dsimp only [successorTerm]
    rw [arithmeticAddTerm_freeVariables, hcursor,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hsuccessorVars : successorTerm.freeVariables ⊆ {0} := by
    rw [hsuccessorClosed]
    simp
  have hcursorResource :=
    compilePositiveRelationPayloadResource_le_publicPolynomial zeroValuation
      Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm]
      hcursorVars htokenCountVars
  have hsuccessorResource :=
    compilePositiveRelationPayloadResource_le_publicPolynomial zeroValuation
      Language.Eq.eq ![nextTerm, successorTerm]
      hnextVars hsuccessorVars
  have hentryResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm
      htable hwidth hcursor hvalue hcell.2.2
  have hinner := hybridConjunctionStructuralPayloadBound_le_envelope
    (CheckedHybridValuationBoundedFormulaCertificate.cast
      (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm
      successorCertificate)
    entryCertificate
    (compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
      ![nextTerm, successorTerm])
    (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial zeroValuation
      tokenTableTerm widthTerm cursorTerm valueTerm)
    (by
      simpa only [hybridFormulaStructuralPayloadBound,
        successorCertificate] using hsuccessorResource)
    hentryResource
  have hparts := hybridConjunctionStructuralPayloadBound_le_envelope
    (CheckedHybridValuationBoundedFormulaCertificate.cast
      (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm cursorCertificate)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm
        successorCertificate)
      entryCertificate)
    (compilePositiveRelationPayloadPolynomial zeroValuation
      Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm])
    (hybridConjunctionStructuralPayloadEnvelope zeroValuation
      (“!!nextTerm = !!cursorTerm + 1” : ValuationFormula)
      (compactFixedWidthEntryAtValuationFormula
        tokenTableTerm widthTerm cursorTerm valueTerm)
      (compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
        ![nextTerm, successorTerm])
      (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm))
    (by
      simpa only [hybridFormulaStructuralPayloadBound,
        cursorCertificate] using hcursorResource)
    hinner
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (CheckedHybridValuationBoundedFormulaCertificate.cast
          (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm
          cursorCertificate)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (CheckedHybridValuationBoundedFormulaCertificate.cast
            (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm
            successorCertificate)
          entryCertificate)) ≤ _
  unfold compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
  dsimp only
  exact hparts

#print axioms
  compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds
