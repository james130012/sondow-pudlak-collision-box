import integration.FoundationCompactNumericListedDirectParserDoneFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the finished parser branch

The constructor follows the original twenty-six-coordinate formula.  The two
list equalities and the failed/completed status alternative are assembled from
their explicit certificates; no Sigma-zero truth conversion is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

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

def compactUnifiedParserDoneClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserDoneGraphRowsDef.val) ⇜
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
      shortBinaryNumeralTerm witness.sourceOutputStart,
      shortBinaryNumeralTerm witness.sourceOutputBoundary,
      shortBinaryNumeralTerm witness.sourceOutputBoundarySize,
      shortBinaryNumeralTerm witness.targetOutputStart,
      shortBinaryNumeralTerm witness.targetOutputBoundary,
      shortBinaryNumeralTerm witness.targetOutputBoundarySize,
      shortBinaryNumeralTerm witness.outputCount]

def compactUnifiedParserDoneExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListSameRowsClosedFormula
      tokenTable width tokenCount
      current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount ⋏
    (compactAdditiveSyntaxTaskListSameRowsClosedFormula
        tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        next.tasksBoundary next.tasksCount ⋏
      ((compactBinaryNatFailedStatusSliceClosedFormula
          tokenTable width tokenCount current.tasksFinish current.finish ⋏
        compactBinaryNatFailedStatusSliceClosedFormula
          tokenTable width tokenCount next.tasksFinish next.finish) ⋎
        compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
          tokenTable width tokenCount
          current.tasksFinish current.finish
          next.tasksFinish next.finish
          witness.sourceOutputStart witness.sourceOutputBoundary
          witness.sourceOutputBoundarySize
          witness.targetOutputStart witness.targetOutputBoundary
          witness.targetOutputBoundarySize witness.outputCount))

theorem compactUnifiedParserDoneClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    compactUnifiedParserDoneClosedFormula
        tokenTable width tokenCount current next witness =
      compactUnifiedParserDoneExplicitFormula
        tokenTable width tokenCount current next witness := by
  unfold compactUnifiedParserDoneClosedFormula
  unfold compactUnifiedParserDoneExplicitFormula
  unfold compactUnifiedParserDoneGraphRowsDef
  unfold compactAdditiveSyntaxTaskListSameRowsClosedFormula
  unfold compactBinaryNatFailedStatusSliceClosedFormula
  unfold compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactNatSizeClosedFormula
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

noncomputable def compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hstatus :
      (CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsWithSize tokenTable width tokenCount
        current.tasksFinish current.finish next.tasksFinish next.finish
        witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount) :
    HybridCertificate
      ((compactBinaryNatFailedStatusSliceClosedFormula tokenTable width
          tokenCount current.tasksFinish current.finish ⋏
        compactBinaryNatFailedStatusSliceClosedFormula tokenTable width
          tokenCount next.tasksFinish next.finish) ⋎
        compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
          tokenTable width tokenCount current.tasksFinish current.finish
          next.tasksFinish next.finish witness.sourceOutputStart
          witness.sourceOutputBoundary witness.sourceOutputBoundarySize
          witness.targetOutputStart witness.targetOutputBoundary
          witness.targetOutputBoundarySize witness.outputCount) := by
  by_cases hfailed :
      CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish
  · exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tasksFinish current.finish
          hfailed.1)
        (compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount next.tasksFinish next.finish hfailed.2))
  · have hcompleted : CompactBinaryNatCompletedStatusSameRowsWithSize
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount := by
      rcases hstatus with hfailed' | hcompleted
      · exact False.elim (hfailed hfailed')
      · exact hcompleted
    exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount hcompleted)

noncomputable def compactUnifiedParserDoneExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hgraph : CompactUnifiedParserDoneGraphRows
      tokenTable width tokenCount current next witness) :
    HybridCertificate
      (compactUnifiedParserDoneClosedFormula
        tokenTable width tokenCount current next witness) := by
  rcases hgraph with ⟨htokens, htasks, hstatus⟩
  let status := compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current next witness hstatus
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount
      current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        next.tasksBoundary next.tasksCount htasks)
      status)
  exact .cast
    (compactUnifiedParserDoneClosedFormula_alignment
      tokenTable width tokenCount current next witness).symm parts

noncomputable def compileCompactUnifiedParserDoneExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hgraph : CompactUnifiedParserDoneGraphRows
      tokenTable width tokenCount current next witness) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserDoneClosedFormula
          tokenTable width tokenCount current next witness).freeVariables
        zeroValuation)
      (compactUnifiedParserDoneClosedFormula
        tokenTable width tokenCount current next witness) :=
  (compactUnifiedParserDoneExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current next witness hgraph).compile

noncomputable def compactUnifiedParserDoneExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hgraph : CompactUnifiedParserDoneGraphRows
      tokenTable width tokenCount current next witness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserDoneExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness hgraph)

theorem compileCompactUnifiedParserDoneExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hgraph : CompactUnifiedParserDoneGraphRows
      tokenTable width tokenCount current next witness) :
    (compileCompactUnifiedParserDoneExplicitHybridContext
      tokenTable width tokenCount current next witness hgraph).payloadLength ≤
      compactUnifiedParserDoneExplicitStructuralResource
        tokenTable width tokenCount current next witness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserDoneExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness hgraph)

#print axioms compactUnifiedParserDoneClosedFormula_alignment
#print axioms compactUnifiedParserDoneExplicitHybridCertificateOfGraph
#print axioms
  compileCompactUnifiedParserDoneExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
