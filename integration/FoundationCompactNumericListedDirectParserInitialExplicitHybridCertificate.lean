import integration.FoundationCompactNumericListedDirectParserInitialFormula
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactPABinaryNumeralAddition

/-!
# Explicit hybrid certificate for the numeric parser initial state

The source token rows, unary one task count, unary zero task index, and unary
zero running-status tag are all preserved in the exact source syntax.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate

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

def compactUnifiedParserInitialStateRowsClosedFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount :
      Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialStateRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tokensFinish,
      shortBinaryNumeralTerm coordinates.tasksFinish,
      shortBinaryNumeralTerm coordinates.tokensBoundary,
      shortBinaryNumeralTerm coordinates.tokensCount,
      shortBinaryNumeralTerm coordinates.tasksBoundary,
      shortBinaryNumeralTerm coordinates.tasksCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm taskKind,
      shortBinaryNumeralTerm taskBinderArity,
      shortBinaryNumeralTerm taskRepeatCount]

def compactUnifiedParserInitialStateRowsExplicitFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount :
      Nat) : ValuationFormula :=
  compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      sourceBoundary sourceCount coordinates.tokensBoundary
        coordinates.tokensCount ⋏
    (“!!(shortBinaryNumeralTerm coordinates.tasksCount) = 1” ⋏
      (compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula tokenTable
          width tokenCount coordinates.tasksBoundary coordinates.tasksCount
          taskKind taskBinderArity taskRepeatCount (‘0’ : ValuationTerm) ⋏
        compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount coordinates.tasksFinish coordinates.finish))

theorem compactUnifiedParserInitialStateRowsClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount :
      Nat) :
    compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount =
      compactUnifiedParserInitialStateRowsExplicitFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount := by
  unfold compactUnifiedParserInitialStateRowsClosedFormula
  unfold compactUnifiedParserInitialStateRowsExplicitFormula
  unfold compactUnifiedParserInitialStateRowsDef
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def unaryOneEqualityCertificate
    (value : Nat) (hvalue : value = 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm value) = 1” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, (‘1’ : ValuationTerm)] (by
      change termValue zeroValuation (shortBinaryNumeralTerm value) =
        termValue zeroValuation (‘1’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticOne] using hvalue)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

noncomputable def compactUnifiedParserInitialStateRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount :
      Nat)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates sourceBoundary sourceCount taskKind taskBinderArity
        taskRepeatCount) :
    HybridCertificate
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount) := by
  rcases hgraph with ⟨hsame, htaskCount, htask, hrunning⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount
        coordinates.tokensBoundary coordinates.tokensCount hsame)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (unaryOneEqualityCertificate coordinates.tasksCount htaskCount)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveSyntaxTaskListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates.tasksBoundary
            coordinates.tasksCount 0 taskKind taskBinderArity taskRepeatCount
            (‘0’ : ValuationTerm) (by
              change termValue (fun _ => 0) (‘0’ : ValuationTerm) = 0
              exact termValue_arithmeticZero _)
            htask)
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates.tasksFinish
            coordinates.finish hrunning)))
  exact .cast
    (compactUnifiedParserInitialStateRowsClosedFormula_alignment tokenTable
      width tokenCount coordinates sourceBoundary sourceCount taskKind
        taskBinderArity taskRepeatCount).symm parts

#print axioms compactUnifiedParserInitialStateRowsClosedFormula_alignment
#print axioms
  compactUnifiedParserInitialStateRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
