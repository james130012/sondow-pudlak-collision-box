import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormula
import integration.FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for an ordinary syntax-parser step

The original 26-coordinate formula is the checked disjunction of the six
already certified syntax-parser branches.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate

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
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate

def compactUnifiedParserSyntaxStepZeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate
    compactUnifiedParserSyntaxStepZeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
  cases h
  rfl

def compactUnifiedParserSyntaxStepClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxStepRowsDef.val) ⇜
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
      shortBinaryNumeralTerm witness.slot0,
      shortBinaryNumeralTerm witness.slot1,
      shortBinaryNumeralTerm witness.slot2,
      shortBinaryNumeralTerm witness.slot3,
      shortBinaryNumeralTerm witness.slot4,
      shortBinaryNumeralTerm witness.slot5,
      shortBinaryNumeralTerm witness.slot6]

def compactUnifiedParserSyntaxStepExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : ValuationFormula :=
  compactUnifiedParserDoneClosedFormula tokenTable width tokenCount current next witness.done ⋎
    compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount current next witness.empty ⋎
    compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount current next
      witness.slot0 witness.slot1 witness.repeat ⋎
    compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount current next
      witness.slot0 witness.term ⋎
    compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount current next
      witness.slot0 witness.formula ⋎
    compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount current next
      witness.invalid

theorem compactUnifiedParserSyntaxStepClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount current next witness =
      compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount current next
        witness := by
  unfold compactUnifiedParserSyntaxStepClosedFormula
  unfold compactUnifiedParserSyntaxStepExplicitFormula
  unfold compactUnifiedParserSyntaxStepRowsDef
  unfold compactUnifiedParserDoneClosedFormula
  unfold compactUnifiedParserEmptyClosedFormula
  unfold compactUnifiedParserSyntaxRepeatClosedFormula
  unfold compactUnifiedParserSyntaxTermClosedFormula
  unfold compactUnifiedParserSyntaxFormulaClosedFormula
  unfold compactUnifiedParserSyntaxInvalidClosedFormula
  simp [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.empty,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.invalid,
    FoundationCompactNumericListedDirectParserDoneFormula.compactUnifiedParserDoneWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserEmptyFormula.compactUnifiedParserEmptyWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxRepeatFormula.compactSyntaxRepeatTaskWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxTermFormula.compactSyntaxTermTaskWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula.compactSyntaxFormulaTaskWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxInvalidFormula.compactSyntaxInvalidTaskWitnessCoordinatesOf,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
  all_goals
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

inductive CompactUnifiedParserSyntaxStepCheckedBranchData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Type where
  | done
      (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
        current next witness.done)
  | empty
      (hgraph : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
        current next witness.empty)
  | repeatBranch
      (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
        current next witness.slot0 witness.slot1 witness.repeat)
  | term
      (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
        current next witness.slot0 witness.term)
  | formula
      (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
        current next witness.slot0 witness.formula)
  | invalid
      (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
        current next witness.invalid)

theorem compactUnifiedParserSyntaxStepCheckedBranchData_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount current next witness) :
    Nonempty (CompactUnifiedParserSyntaxStepCheckedBranchData tokenTable width
      tokenCount current next witness) := by
  rcases hgraph with hdone | hempty | hrepeat | hterm | hformula | hinvalid
  · exact ⟨.done hdone⟩
  · exact ⟨.empty hempty⟩
  · exact ⟨.repeatBranch hrepeat⟩
  · exact ⟨.term hterm⟩
  · exact ⟨.formula hformula⟩
  · exact ⟨.invalid hinvalid⟩

noncomputable def compactUnifiedParserSyntaxStepCheckedBranchDataOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount
      current next witness) :
    CompactUnifiedParserSyntaxStepCheckedBranchData tokenTable width tokenCount
      current next witness :=
  Classical.choice
    (compactUnifiedParserSyntaxStepCheckedBranchData_nonempty tokenTable width
      tokenCount current next witness hgraph)

noncomputable def compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (data : CompactUnifiedParserSyntaxStepCheckedBranchData tokenTable width
      tokenCount current next witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness) := by
  unfold compactUnifiedParserSyntaxStepExplicitFormula
  cases data with
  | done hgraph =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (compactUnifiedParserDoneExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness.done hgraph)
  | empty hgraph =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph tokenTable
            width tokenCount current next witness.empty hgraph))
  | repeatBranch hgraph =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.slot0
              witness.slot1 witness.repeat hgraph)))
  | term hgraph =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.slot0
                witness.term hgraph))))
  | formula hgraph =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current next witness.slot0
                  witness.formula hgraph)))))
  | invalid hgraph =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current next witness.invalid
                  hgraph)))))

noncomputable def compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount current next witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount current next
        witness) :=
  .cast (compactUnifiedParserSyntaxStepClosedFormula_alignment tokenTable width tokenCount current
      next witness).symm
    (compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData tokenTable
      width tokenCount current next witness
      (compactUnifiedParserSyntaxStepCheckedBranchDataOfGraph tokenTable width
        tokenCount current next witness hgraph))

noncomputable def compileCompactUnifiedParserSyntaxStepExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount current next witness) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount current next
          witness).freeVariables compactUnifiedParserSyntaxStepZeroValuation)
      (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount current next witness) :=
  (compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph tokenTable width tokenCount current
    next witness hgraph).compile

noncomputable def compactUnifiedParserSyntaxStepExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount current next witness) :
    Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph tokenTable width tokenCount current
      next witness hgraph)

theorem compileCompactUnifiedParserSyntaxStepExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount current next witness) :
    (compileCompactUnifiedParserSyntaxStepExplicitHybridContext tokenTable width tokenCount current
      next witness hgraph).payloadLength ≤
      compactUnifiedParserSyntaxStepExplicitStructuralResource tokenTable width tokenCount current
        next witness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next witness hgraph)

#print axioms compactUnifiedParserSyntaxStepClosedFormula_alignment
#print axioms compactUnifiedParserSyntaxStepCheckedBranchData_nonempty
#print axioms compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData
#print axioms compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph
#print axioms compileCompactUnifiedParserSyntaxStepExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
