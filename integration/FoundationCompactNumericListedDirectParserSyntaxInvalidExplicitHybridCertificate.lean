import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the invalid syntax-task branch

The original twenty-five-coordinate formula is assembled from the running
status, exact task-list uncons, three native-numeral disequalities, and the
checked failure transition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
  cases h
  rfl

def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator (Semiterm.Operator.numeral ℒₒᵣ value) ![]

@[simp] private theorem termValue_fixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

def fixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

def fixedNeFormula (value expected : Nat) : ValuationFormula :=
  ∼(fixedEqFormula value expected)

noncomputable def fixedNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    HybridCertificate (fixedNeFormula value expected) := by
  unfold fixedNeFormula fixedEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] (by
      change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
        termValue zeroValuation (fixedNumeralTerm expected)
      simpa [termValue_shortBinaryNumeralTerm, termValue_fixedNumeralTerm] using hne)
  exact .cast
    (congrArg (fun formula : ValuationFormula => ∼formula)
      (Semiformula.Operator.eq_def _ _).symm) direct

def compactUnifiedParserSyntaxInvalidClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxInvalidRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm current.start,
      shortBinaryNumeralTerm current.finish, shortBinaryNumeralTerm current.tokensFinish,
      shortBinaryNumeralTerm current.tasksFinish,
      shortBinaryNumeralTerm current.tokensBoundary,
      shortBinaryNumeralTerm current.tokensCount,
      shortBinaryNumeralTerm current.tasksBoundary,
      shortBinaryNumeralTerm current.tasksCount, shortBinaryNumeralTerm next.start,
      shortBinaryNumeralTerm next.finish, shortBinaryNumeralTerm next.tokensFinish,
      shortBinaryNumeralTerm next.tasksFinish,
      shortBinaryNumeralTerm next.tokensBoundary,
      shortBinaryNumeralTerm next.tokensCount,
      shortBinaryNumeralTerm next.tasksBoundary,
      shortBinaryNumeralTerm next.tasksCount,
      shortBinaryNumeralTerm witness.tailBoundary,
      shortBinaryNumeralTerm witness.tailCount,
      shortBinaryNumeralTerm witness.tailBoundarySize,
      shortBinaryNumeralTerm witness.kind,
      shortBinaryNumeralTerm witness.binderArity,
      shortBinaryNumeralTerm witness.repeatCount]

def compactUnifiedParserSyntaxInvalidExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      current.tasksFinish current.finish ⋏
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula tokenTable width tokenCount
        current.tasksBoundary current.tasksCount witness.tailBoundary witness.tailCount
        witness.tailBoundarySize witness.kind witness.binderArity witness.repeatCount ⋏
      (fixedNeFormula witness.kind 0 ⋏
        (fixedNeFormula witness.kind 1 ⋏
          (fixedNeFormula witness.kind 2 ⋏
            compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
              current next witness.tailBoundary witness.tailCount))))

theorem compactUnifiedParserSyntaxInvalidClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount current next
        witness =
      compactUnifiedParserSyntaxInvalidExplicitFormula tokenTable width tokenCount current next
        witness := by
  unfold compactUnifiedParserSyntaxInvalidClosedFormula
  unfold compactUnifiedParserSyntaxInvalidExplicitFormula
  unfold compactUnifiedParserSyntaxInvalidRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
  unfold compactUnifiedParserSyntaxTermFailureClosedFormula
  unfold fixedNeFormula fixedEqFormula fixedNumeralTerm
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

noncomputable def compactUnifiedParserSyntaxInvalidExplicitHybridCertificateFromGraphData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize witness.kind
      witness.binderArity witness.repeatCount)
    (hzero : witness.kind ≠ 0)
    (hone : witness.kind ≠ 1)
    (htwo : witness.kind ≠ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    HybridCertificate
      (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount current next
        witness) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width
      tokenCount current.tasksFinish current.finish hrunning)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
        witness.tailCount witness.tailBoundarySize witness.kind witness.binderArity
        witness.repeatCount huncons)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (fixedNeCertificate witness.kind 0 hzero)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (fixedNeCertificate witness.kind 1 hone)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedNeCertificate witness.kind 2 htwo)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph tokenTable
              width tokenCount current next witness.tailBoundary witness.tailCount hfailure)))))
  exact .cast
    (compactUnifiedParserSyntaxInvalidClosedFormula_alignment tokenTable width tokenCount current
      next witness).symm parts

noncomputable def compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount current next
      witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount current next
        witness) :=
  compactUnifiedParserSyntaxInvalidExplicitHybridCertificateFromGraphData
    tokenTable width tokenCount current next witness hgraph.1 hgraph.2.1
    hgraph.2.2.1 hgraph.2.2.2.1 hgraph.2.2.2.2.1 hgraph.2.2.2.2.2

noncomputable def compileCompactUnifiedParserSyntaxInvalidExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount current next
      witness) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount current next
          witness).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount current next
        witness) :=
  (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph tokenTable width tokenCount
    current next witness hgraph).compile

noncomputable def compactUnifiedParserSyntaxInvalidExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount current next
      witness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next witness hgraph)

theorem compileCompactUnifiedParserSyntaxInvalidExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount current next
      witness) :
    (compileCompactUnifiedParserSyntaxInvalidExplicitHybridContext tokenTable width tokenCount
      current next witness hgraph).payloadLength ≤
      compactUnifiedParserSyntaxInvalidExplicitStructuralResource tokenTable width tokenCount
        current next witness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next witness hgraph)

#print axioms compactUnifiedParserSyntaxInvalidClosedFormula_alignment
#print axioms compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
#print axioms compileCompactUnifiedParserSyntaxInvalidExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
