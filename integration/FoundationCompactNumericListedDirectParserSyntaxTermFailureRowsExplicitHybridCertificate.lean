import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the syntax-term failure rows

The original twenty-one-coordinate formula is assembled from the failed
status, token-list equality, and syntax-task-list equality certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate

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

def compactUnifiedParserSyntaxTermFailureClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactUnifiedParserSyntaxTermFailureRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm current.start,
      shortBinaryNumeralTerm current.finish,
      shortBinaryNumeralTerm current.tokensFinish,
      shortBinaryNumeralTerm current.tasksFinish,
      shortBinaryNumeralTerm current.tokensBoundary,
      shortBinaryNumeralTerm current.tokensCount,
      shortBinaryNumeralTerm current.tasksBoundary,
      shortBinaryNumeralTerm current.tasksCount,
      shortBinaryNumeralTerm next.start,
      shortBinaryNumeralTerm next.finish,
      shortBinaryNumeralTerm next.tokensFinish,
      shortBinaryNumeralTerm next.tasksFinish,
      shortBinaryNumeralTerm next.tokensBoundary,
      shortBinaryNumeralTerm next.tokensCount,
      shortBinaryNumeralTerm next.tasksBoundary,
      shortBinaryNumeralTerm next.tasksCount,
      shortBinaryNumeralTerm tailBoundary,
      shortBinaryNumeralTerm tailCount]

def compactUnifiedParserSyntaxTermFailureExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) : ValuationFormula :=
  compactBinaryNatFailedStatusSliceClosedFormula
      tokenTable width tokenCount next.tasksFinish next.finish ⋏
    (compactAdditiveNatListSameRowsClosedFormula
        tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount ⋏
      compactAdditiveSyntaxTaskListSameRowsClosedFormula
        tokenTable width tokenCount tailBoundary tailCount
        next.tasksBoundary next.tasksCount)

theorem compactUnifiedParserSyntaxTermFailureClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) :
    compactUnifiedParserSyntaxTermFailureClosedFormula
        tokenTable width tokenCount current next tailBoundary tailCount =
      compactUnifiedParserSyntaxTermFailureExplicitFormula
        tokenTable width tokenCount current next tailBoundary tailCount := by
  unfold compactUnifiedParserSyntaxTermFailureClosedFormula
  unfold compactUnifiedParserSyntaxTermFailureExplicitFormula
  unfold compactUnifiedParserSyntaxTermFailureRowsDef
  unfold compactBinaryNatFailedStatusSliceClosedFormula
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListSameRowsClosedFormula
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

noncomputable def
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateFromGraphData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hfailed : CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (htasks : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermFailureClosedFormula
        tokenTable width tokenCount current next tailBoundary tailCount) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hfailed)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount htokens)
      (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount tailBoundary tailCount
        next.tasksBoundary next.tasksCount htasks))
  exact .cast
    (compactUnifiedParserSyntaxTermFailureClosedFormula_alignment
      tokenTable width tokenCount current next tailBoundary tailCount).symm
      parts

noncomputable def
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows
      tokenTable width tokenCount current next tailBoundary tailCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxTermFailureClosedFormula
        tokenTable width tokenCount current next tailBoundary tailCount) :=
  compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateFromGraphData
    tokenTable width tokenCount current next tailBoundary tailCount hgraph.1
    hgraph.2.1 hgraph.2.2

noncomputable def
    compileCompactUnifiedParserSyntaxTermFailureExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows
      tokenTable width tokenCount current next tailBoundary tailCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxTermFailureClosedFormula
          tokenTable width tokenCount current next tailBoundary tailCount).freeVariables
        zeroValuation)
      (compactUnifiedParserSyntaxTermFailureClosedFormula
        tokenTable width tokenCount current next tailBoundary tailCount) :=
  (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current next tailBoundary tailCount hgraph).compile

noncomputable def
    compactUnifiedParserSyntaxTermFailureExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows
      tokenTable width tokenCount current next tailBoundary tailCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next tailBoundary tailCount hgraph)

theorem
    compileCompactUnifiedParserSyntaxTermFailureExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows
      tokenTable width tokenCount current next tailBoundary tailCount) :
    (compileCompactUnifiedParserSyntaxTermFailureExplicitHybridContext
      tokenTable width tokenCount current next tailBoundary tailCount
        hgraph).payloadLength ≤
      compactUnifiedParserSyntaxTermFailureExplicitStructuralResource
        tokenTable width tokenCount current next tailBoundary tailCount
          hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next tailBoundary tailCount hgraph)

#print axioms compactUnifiedParserSyntaxTermFailureClosedFormula_alignment
#print axioms
  compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
#print axioms
  compileCompactUnifiedParserSyntaxTermFailureExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
