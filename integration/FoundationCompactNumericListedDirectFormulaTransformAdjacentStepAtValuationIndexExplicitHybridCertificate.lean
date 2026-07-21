import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Adjacent formula-transform rows at an arbitrary valuation index

The row index is retained as a valuation term. The current lookup uses that
term and the next lookup uses the original arithmetic term `indexTerm + 1`.
Closed row-core certificates are revalued; no numeral is substituted for the
index term.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate

open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def valuationLtCertificate
    (valuation : Nat -> Nat) (leftTerm : ValuationTerm) (right : Nat)
    (hlt : termValue valuation leftTerm < right) :
    HybridCertificate valuation
      “!!leftTerm < !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.ORing.Rel.lt
    ![leftTerm, shortBinaryNumeralTerm right] (by
      change termValue valuation leftTerm <
        termValue valuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

private theorem compactFormulaTransformStateCoreClosedFormula_freeVariables
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    (compactFormulaTransformStateCoreClosedFormula
      tokenTable width tokenCount coordinates sizeWitness).freeVariables = ∅ := by
  unfold compactFormulaTransformStateCoreClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private theorem compactFormulaTransformStepRowsClosedFormula_freeVariables
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount).freeVariables = ∅ := by
  unfold compactFormulaTransformStepRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraphAtValuation
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation indexTerm) coordinates sizeWitness) :
    HybridCertificate valuation
      (compactFormulaTransformStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
        coordinates sizeWitness) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let coreAtZero :=
    compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates sizeWitness hcore
  let coreAtValuation := revalueClosedHybridCertificate coreAtZero
    (compactFormulaTransformStateCoreClosedFormula_freeVariables
      tokenTable width tokenCount coordinates sizeWitness) valuation
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (valuationLtCertificate valuation indexTerm stateCount hindex)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm coordinates.start) (by
          simpa [termValue_shortBinaryNumeralTerm] using hstart))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount) nextIndexTerm
          (shortBinaryNumeralTerm coordinates.finish) (by
            simpa [nextIndexTerm, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne] using hfinish))
        coreAtValuation))
  exact .cast
    (compactFormulaTransformStateAtRowsAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness).symm parts

def compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepRowDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      indexTerm,
      shortBinaryNumeralTerm mode,
      shortBinaryNumeralTerm witnessStart,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm witnessCount,
      shortBinaryNumeralTerm row.currentCoordinates.start,
      shortBinaryNumeralTerm row.currentCoordinates.finish,
      shortBinaryNumeralTerm row.currentCoordinates.parserFinish,
      shortBinaryNumeralTerm row.currentCoordinates.parserTokensFinish,
      shortBinaryNumeralTerm row.currentCoordinates.parserTasksFinish,
      shortBinaryNumeralTerm row.currentCoordinates.parserTokensBoundary,
      shortBinaryNumeralTerm row.currentCoordinates.parserTokensCount,
      shortBinaryNumeralTerm row.currentCoordinates.parserTasksBoundary,
      shortBinaryNumeralTerm row.currentCoordinates.parserTasksCount,
      shortBinaryNumeralTerm row.currentCoordinates.outputBoundary,
      shortBinaryNumeralTerm row.currentCoordinates.outputCount,
      shortBinaryNumeralTerm row.currentSize.parserTokensBoundarySize,
      shortBinaryNumeralTerm row.currentSize.parserTasksBoundarySize,
      shortBinaryNumeralTerm row.currentSize.outputBoundarySize,
      shortBinaryNumeralTerm row.nextCoordinates.start,
      shortBinaryNumeralTerm row.nextCoordinates.finish,
      shortBinaryNumeralTerm row.nextCoordinates.parserFinish,
      shortBinaryNumeralTerm row.nextCoordinates.parserTokensFinish,
      shortBinaryNumeralTerm row.nextCoordinates.parserTasksFinish,
      shortBinaryNumeralTerm row.nextCoordinates.parserTokensBoundary,
      shortBinaryNumeralTerm row.nextCoordinates.parserTokensCount,
      shortBinaryNumeralTerm row.nextCoordinates.parserTasksBoundary,
      shortBinaryNumeralTerm row.nextCoordinates.parserTasksCount,
      shortBinaryNumeralTerm row.nextCoordinates.outputBoundary,
      shortBinaryNumeralTerm row.nextCoordinates.outputCount,
      shortBinaryNumeralTerm row.nextSize.parserTokensBoundarySize,
      shortBinaryNumeralTerm row.nextSize.parserTasksBoundarySize,
      shortBinaryNumeralTerm row.nextSize.outputBoundarySize,
      shortBinaryNumeralTerm row.stepWitness.slot0,
      shortBinaryNumeralTerm row.stepWitness.slot1,
      shortBinaryNumeralTerm row.stepWitness.slot2,
      shortBinaryNumeralTerm row.stepWitness.slot3,
      shortBinaryNumeralTerm row.stepWitness.slot4,
      shortBinaryNumeralTerm row.stepWitness.slot5,
      shortBinaryNumeralTerm row.stepWitness.slot6,
      shortBinaryNumeralTerm row.consumedCount,
      shortBinaryNumeralTerm row.mappedHead]

def compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : ValuationFormula :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  compactFormulaTransformStateAtRowsAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize ⋏
    (compactFormulaTransformStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
        row.nextCoordinates row.nextSize ⋏
      compactFormulaTransformStepRowsClosedFormula
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        mode row.stepWitness row.consumedCount row.mappedHead witnessStart
        witnessFinish witnessCount)

theorem compactFormulaTransformAdjacentStepRowAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm mode
        witnessStart witnessFinish witnessCount row =
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm mode
        witnessStart witnessFinish witnessCount row := by
  unfold compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
  unfold compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitFormula
  unfold compactFormulaTransformAdjacentStepRowDef
  unfold compactFormulaTransformStateAtRowsAtValuationIndexFormula
  unfold compactFormulaTransformStepRowsClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation indexTerm) mode witnessStart witnessFinish
      witnessCount row) :
    HybridCertificate valuation
      (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm mode
        witnessStart witnessFinish witnessCount row) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextAtTerm : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation nextIndexTerm) row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hnext
  let stepAtZero :=
    compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
      mode row.stepWitness row.consumedCount row.mappedHead witnessStart
      witnessFinish witnessCount hstep
  let stepAtValuation := revalueClosedHybridCertificate stepAtZero
    (compactFormulaTransformStepRowsClosedFormula_freeVariables
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
      mode row.stepWitness row.consumedCount row.mappedHead witnessStart
      witnessFinish witnessCount) valuation
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFormulaTransformStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraphAtValuation
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize hcurrent)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFormulaTransformStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraphAtValuation
        valuation tokenTable width tokenCount stateBoundary stateCount
        nextIndexTerm row.nextCoordinates row.nextSize hnextAtTerm)
      stepAtValuation)
  exact .cast
    (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm mode
      witnessStart witnessFinish witnessCount row).symm parts

#print axioms
  compactFormulaTransformStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraphAtValuation
#print axioms compactFormulaTransformAdjacentStepRowAtValuationIndexFormula_alignment
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
