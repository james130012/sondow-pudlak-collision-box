import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateAtRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for one adjacent syntax-parser row

The current state row, next state row, and six-branch syntax transition are
charged separately before the original 33-coordinate formula is restored.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
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
  rw [arithmeticAddTerm_eq_func]
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def compactParserSyntaxAdjacentStepRowGraphPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount index row) : Nat := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  have hnextAtTerm : CompactUnifiedParserStateAtRows tokenTable width
      tokenCount stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, compactParserStateAtRowsZeroValuation,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hnext
  let currentFormula := compactUnifiedParserStateAtRowsClosedFormula
    tokenTable width tokenCount stateBoundary stateCount index
    row.currentCoordinates row.currentSize
  let nextFormula := compactUnifiedParserStateAtRowsAtValuationIndexFormula
    tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
    row.nextCoordinates row.nextSize
  let stepFormula := compactUnifiedParserSyntaxStepClosedFormula tokenTable
    width tokenCount row.currentCoordinates row.nextCoordinates
    row.stepWitness
  let currentResource := compactUnifiedParserStateAtRowsPayloadEnvelope
    tokenTable width tokenCount stateBoundary stateCount index
    row.currentCoordinates row.currentSize hcurrent
  let nextResource := compactUnifiedParserStateAtRowsAtIndexTermPayloadEnvelope
    tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
    row.nextCoordinates row.nextSize hnextAtTerm
  let stepResource := compactUnifiedParserSyntaxStepGraphPayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
    row.stepWitness hstep
  let nextStepResource := transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation nextFormula stepFormula nextResource
    stepResource
  exact transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation currentFormula
    (nextFormula ⋏ stepFormula) currentResource nextStepResource

theorem
    compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount index row) :
    hybridFormulaStructuralPayloadBound
        (compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph
          tokenTable width tokenCount stateBoundary stateCount index row
          hgraph) <=
      compactParserSyntaxAdjacentStepRowGraphPayloadEnvelope tokenTable width
        tokenCount stateBoundary stateCount index row hgraph := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hnextAtTerm : CompactUnifiedParserStateAtRows tokenTable width
      tokenCount stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, compactParserStateAtRowsZeroValuation,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hnext
  let currentCertificate :=
    compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount stateBoundary stateCount index row.currentCoordinates
      row.currentSize hcurrent
  let nextCertificate :=
    compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
      row.nextCoordinates row.nextSize hnextAtTerm
  let stepCertificate :=
    compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph tokenTable
      width tokenCount row.currentCoordinates row.nextCoordinates
      row.stepWitness hstep
  have hcurrentResource :=
    compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount stateBoundary stateCount index
      row.currentCoordinates row.currentSize hcurrent
  have hnextResource :=
    compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
      row.nextCoordinates row.nextSize hnextIndexVariables hnextAtTerm
  have hstepResource :=
    compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
      row.stepWitness hstep
  let nextStep := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    nextCertificate stepCertificate
  have hnextStep := transparentHybridConjunctionPayloadBound_le
    nextCertificate stepCertificate _ _ hnextResource hstepResource
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    currentCertificate nextStep
  have hparts := transparentHybridConjunctionPayloadBound_le
    currentCertificate nextStep _ _ hcurrentResource hnextStep
  unfold
    compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph
  unfold compactParserSyntaxAdjacentStepRowGraphPayloadEnvelope
  simp only [hybridFormulaStructuralPayloadBound]
  simpa only [nextIndexTerm, hnextAtTerm, currentCertificate,
    nextCertificate, stepCertificate, nextStep, parts,
    hybridFormulaStructuralPayloadBound] using hparts

#print axioms
  compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepPublicBounds
