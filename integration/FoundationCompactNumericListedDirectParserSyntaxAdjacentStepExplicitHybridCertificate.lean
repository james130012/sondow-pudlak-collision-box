import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for one adjacent syntax-parser step

The original 33-coordinate row keeps the second state index as the native
term `index + 1`.  Its certificate combines the two exact state-row
certificates with the exact six-branch syntax-step certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate

abbrev compactParserSyntaxAdjacentStepRowZeroValuation : Nat -> Nat :=
  compactParserStateAtRowsZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate
    compactParserStateAtRowsZeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
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

def compactParserSyntaxAdjacentStepRowClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserSyntaxAdjacentStepRowDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm index,
      shortBinaryNumeralTerm row.currentCoordinates.start,
      shortBinaryNumeralTerm row.currentCoordinates.finish,
      shortBinaryNumeralTerm row.currentCoordinates.tokensFinish,
      shortBinaryNumeralTerm row.currentCoordinates.tasksFinish,
      shortBinaryNumeralTerm row.currentCoordinates.tokensBoundary,
      shortBinaryNumeralTerm row.currentCoordinates.tokensCount,
      shortBinaryNumeralTerm row.currentCoordinates.tasksBoundary,
      shortBinaryNumeralTerm row.currentCoordinates.tasksCount,
      shortBinaryNumeralTerm row.currentSize.tokensBoundarySize,
      shortBinaryNumeralTerm row.currentSize.tasksBoundarySize,
      shortBinaryNumeralTerm row.nextCoordinates.start,
      shortBinaryNumeralTerm row.nextCoordinates.finish,
      shortBinaryNumeralTerm row.nextCoordinates.tokensFinish,
      shortBinaryNumeralTerm row.nextCoordinates.tasksFinish,
      shortBinaryNumeralTerm row.nextCoordinates.tokensBoundary,
      shortBinaryNumeralTerm row.nextCoordinates.tokensCount,
      shortBinaryNumeralTerm row.nextCoordinates.tasksBoundary,
      shortBinaryNumeralTerm row.nextCoordinates.tasksCount,
      shortBinaryNumeralTerm row.nextSize.tokensBoundarySize,
      shortBinaryNumeralTerm row.nextSize.tasksBoundarySize,
      shortBinaryNumeralTerm row.stepWitness.slot0,
      shortBinaryNumeralTerm row.stepWitness.slot1,
      shortBinaryNumeralTerm row.stepWitness.slot2,
      shortBinaryNumeralTerm row.stepWitness.slot3,
      shortBinaryNumeralTerm row.stepWitness.slot4,
      shortBinaryNumeralTerm row.stepWitness.slot5,
      shortBinaryNumeralTerm row.stepWitness.slot6]

def compactParserSyntaxAdjacentStepRowExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : ValuationFormula :=
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  compactUnifiedParserStateAtRowsClosedFormula
      tokenTable width tokenCount stateBoundary stateCount index
        row.currentCoordinates row.currentSize ⋏
    (compactUnifiedParserStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
          row.nextCoordinates row.nextSize ⋏
      compactUnifiedParserSyntaxStepClosedFormula
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
          row.stepWitness)

theorem compactParserSyntaxAdjacentStepRowClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserSyntaxAdjacentStepRowClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index row =
      compactParserSyntaxAdjacentStepRowExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount index row := by
  unfold compactParserSyntaxAdjacentStepRowClosedFormula
  unfold compactParserSyntaxAdjacentStepRowExplicitFormula
  unfold compactParserSyntaxAdjacentStepRowDef
  unfold compactUnifiedParserStateAtRowsClosedFormula
  unfold compactUnifiedParserStateAtRowsAtValuationIndexFormula
  unfold compactUnifiedParserSyntaxStepClosedFormula
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

noncomputable def compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row) :
    HybridCertificate
      (compactParserSyntaxAdjacentStepRowClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index row) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  have hnextAtTerm : CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
        (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
          row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, compactParserStateAtRowsZeroValuation,
      termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne] using hnext
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index
        row.currentCoordinates row.currentSize hcurrent)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
        tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
          row.nextCoordinates row.nextSize hnextAtTerm)
      (compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
          row.stepWitness hstep))
  exact .cast
    (compactParserSyntaxAdjacentStepRowClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount index row).symm parts

noncomputable def compileCompactParserSyntaxAdjacentStepRowExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row) :
    CertifiedPAContextProof
      (valuationContext
        (compactParserSyntaxAdjacentStepRowClosedFormula
          tokenTable width tokenCount stateBoundary stateCount index row).freeVariables
            compactParserStateAtRowsZeroValuation)
      (compactParserSyntaxAdjacentStepRowClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index row) :=
  (compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount index row hgraph).compile

noncomputable def compactParserSyntaxAdjacentStepRowExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index row hgraph)

theorem compileCompactParserSyntaxAdjacentStepRowExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row) :
    (compileCompactParserSyntaxAdjacentStepRowExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount index row hgraph).payloadLength ≤
      compactParserSyntaxAdjacentStepRowExplicitStructuralResource
        tokenTable width tokenCount stateBoundary stateCount index row hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index row hgraph)

#print axioms compactParserSyntaxAdjacentStepRowClosedFormula_alignment
#print axioms compactParserSyntaxAdjacentStepRowExplicitHybridCertificateOfGraph
#print axioms
  compileCompactParserSyntaxAdjacentStepRowExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate
