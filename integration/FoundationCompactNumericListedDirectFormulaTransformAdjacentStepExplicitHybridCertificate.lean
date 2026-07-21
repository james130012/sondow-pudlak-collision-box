import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for one adjacent formula-transform step

The original forty-seven-coordinate row keeps the second state index as the
native term `index + 1`. Its certificate combines the two exact state-row
certificates with the exact formula-transform step certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

def compactFormulaTransformAdjacentStepRowClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformAdjacentStepRowDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm index,
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

def compactFormulaTransformAdjacentStepRowExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : ValuationFormula :=
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  compactFormulaTransformStateAtRowsClosedFormula
      tokenTable width tokenCount stateBoundary stateCount index
        row.currentCoordinates row.currentSize ⋏
    (compactFormulaTransformStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
          row.nextCoordinates row.nextSize ⋏
      compactFormulaTransformStepRowsClosedFormula
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
          mode row.stepWitness row.consumedCount row.mappedHead witnessStart
            witnessFinish witnessCount)

theorem compactFormulaTransformAdjacentStepRowClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) :
    compactFormulaTransformAdjacentStepRowClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index mode
          witnessStart witnessFinish witnessCount row =
      compactFormulaTransformAdjacentStepRowExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount index mode
          witnessStart witnessFinish witnessCount row := by
  unfold compactFormulaTransformAdjacentStepRowClosedFormula
  unfold compactFormulaTransformAdjacentStepRowExplicitFormula
  unfold compactFormulaTransformAdjacentStepRowDef
  unfold compactFormulaTransformStateAtRowsClosedFormula
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
    compactFormulaTransformAdjacentStepRowExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row) :
    HybridCertificate
      (compactFormulaTransformAdjacentStepRowClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index mode
          witnessStart witnessFinish witnessCount row) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  have hnextAtTerm : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
        (termValue compactFormulaTransformStateAtRowsZeroValuation nextIndexTerm)
          row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, compactFormulaTransformStateAtRowsZeroValuation,
      termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne] using hnext
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index
        row.currentCoordinates row.currentSize hcurrent)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFormulaTransformStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
        tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
          row.nextCoordinates row.nextSize hnextAtTerm)
      (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
          mode row.stepWitness row.consumedCount row.mappedHead witnessStart
            witnessFinish witnessCount hstep))
  exact .cast
    (compactFormulaTransformAdjacentStepRowClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row).symm parts

noncomputable def
    compileCompactFormulaTransformAdjacentStepRowExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentStepRowClosedFormula
          tokenTable width tokenCount stateBoundary stateCount index mode
            witnessStart witnessFinish witnessCount row).freeVariables
          zeroValuation)
      (compactFormulaTransformAdjacentStepRowClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index mode
          witnessStart witnessFinish witnessCount row) :=
  (compactFormulaTransformAdjacentStepRowExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount row hgraph).compile

noncomputable def
    compactFormulaTransformAdjacentStepRowExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentStepRowExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row hgraph)

theorem
    compileCompactFormulaTransformAdjacentStepRowExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row) :
    (compileCompactFormulaTransformAdjacentStepRowExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row hgraph).payloadLength ≤
      compactFormulaTransformAdjacentStepRowExplicitStructuralResource
        tokenTable width tokenCount stateBoundary stateCount index mode
          witnessStart witnessFinish witnessCount row hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentStepRowExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index mode
        witnessStart witnessFinish witnessCount row hgraph)

#print axioms compactFormulaTransformAdjacentStepRowClosedFormula_alignment
#print axioms
  compactFormulaTransformAdjacentStepRowExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentStepRowExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepExplicitHybridCertificate
