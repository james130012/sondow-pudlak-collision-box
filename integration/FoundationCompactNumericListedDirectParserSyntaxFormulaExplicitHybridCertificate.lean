import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for the complete syntax-formula transition

Every native numeral and every branch of the original 26-coordinate formula
is retained and certified from the concrete row relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactArithmeticSymbolCode
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate

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

def nativeEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

def nativeNeFormula (value expected : Nat) : ValuationFormula :=
  ∼nativeEqFormula value expected

def termLeFormula (leftTerm rightTerm : ValuationTerm) : ValuationFormula :=
  “!!leftTerm ≤ !!rightTerm”

def shortNativeLeFormula (left right : Nat) : ValuationFormula :=
  termLeFormula (shortBinaryNumeralTerm left) (fixedNumeralTerm right)

def nativeShortLeFormula (left right : Nat) : ValuationFormula :=
  termLeFormula (fixedNumeralTerm left) (shortBinaryNumeralTerm right)

noncomputable def nativeEqCertificate
    (value expected : Nat) (heq : value = expected) :
    HybridCertificate (nativeEqFormula value expected) := by
  unfold nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] (by
        change termValue zeroValuation (shortBinaryNumeralTerm value) =
          termValue zeroValuation (fixedNumeralTerm expected)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

noncomputable def nativeNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    HybridCertificate (nativeNeFormula value expected) := by
  unfold nativeNeFormula nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] (by
        change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
          termValue zeroValuation (fixedNumeralTerm expected)
        simpa [termValue_shortBinaryNumeralTerm] using hne)
  exact .cast
    (congrArg (fun formula : ValuationFormula => ∼formula)
      (Semiformula.Operator.eq_def _ _).symm) direct

noncomputable def termLeCertificate
    (left right : Nat) (leftTerm rightTerm : ValuationTerm)
    (hleft : termValue zeroValuation leftTerm = left)
    (hright : termValue zeroValuation rightTerm = right)
    (hle : left ≤ right) :
    HybridCertificate (termLeFormula leftTerm rightTerm) := by
  unfold termLeFormula
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] (by
        change termValue zeroValuation leftTerm = termValue zeroValuation rightTerm
        simpa [hleft, hright] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] (by
        change termValue zeroValuation leftTerm < termValue zeroValuation rightTerm
        simpa [hleft, hright] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionRight strict)

noncomputable def shortNativeLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate (shortNativeLeFormula left right) := by
  unfold shortNativeLeFormula
  exact termLeCertificate left right (shortBinaryNumeralTerm left) (fixedNumeralTerm right)
    (by simp [termValue_shortBinaryNumeralTerm]) (by simp) hle

noncomputable def nativeShortLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate (nativeShortLeFormula left right) := by
  unfold nativeShortLeFormula
  exact termLeCertificate left right (fixedNumeralTerm left) (shortBinaryNumeralTerm right)
    (by simp) (by simp [termValue_shortBinaryNumeralTerm]) hle

inductive NativeEqEitherCheckedData
    (value left right : Nat) : Type where
  | left (hleft : value = left)
  | right (hright : value = right)

theorem nativeEqEitherCheckedData_nonempty
    (value left right : Nat) (heither : value = left ∨ value = right) :
    Nonempty (NativeEqEitherCheckedData value left right) := by
  rcases heither with hleft | hright
  · exact ⟨.left hleft⟩
  · exact ⟨.right hright⟩

noncomputable def nativeEqEitherCheckedDataOfProof
    (value left right : Nat) (heither : value = left ∨ value = right) :
    NativeEqEitherCheckedData value left right :=
  Classical.choice
    (nativeEqEitherCheckedData_nonempty value left right heither)

noncomputable def nativeEqEitherCertificateFromData
    (value left right : Nat)
    (data : NativeEqEitherCheckedData value left right) :
    HybridCertificate
      (nativeEqFormula value left ⋎ nativeEqFormula value right) :=
  match data with
  | .left hleft =>
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (nativeEqCertificate value left hleft)
  | .right hright =>
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (nativeEqCertificate value right hright)

noncomputable def nativeEqEitherCertificate
    (value left right : Nat) (heither : value = left ∨ value = right) :
    HybridCertificate
      (nativeEqFormula value left ⋎ nativeEqFormula value right) :=
  nativeEqEitherCertificateFromData value left right
    (nativeEqEitherCheckedDataOfProof value left right heither)

def compactUnifiedParserSyntaxFormulaClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxFormulaRowsDef.val) ⇜
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
      shortBinaryNumeralTerm next.tasksCount, shortBinaryNumeralTerm binderArity,
      shortBinaryNumeralTerm witness.tailBoundary,
      shortBinaryNumeralTerm witness.tailCount,
      shortBinaryNumeralTerm witness.tailBoundarySize,
      shortBinaryNumeralTerm witness.tag,
      shortBinaryNumeralTerm witness.relationArity,
      shortBinaryNumeralTerm witness.relationCode]

def compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  let failureBranch := compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
    current next witness.tailBoundary witness.tailCount
  let functionBranch :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable width tokenCount
      current next witness.tailBoundary witness.tailCount binderArity witness.relationArity
  let atArity := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width tokenCount
    current.tokensBoundary current.tokensCount witness.relationArity (fixedNumeralTerm 1)
  let atCode := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width tokenCount
    current.tokensBoundary current.tokensCount witness.relationCode (fixedNumeralTerm 2)
  (shortNativeLeFormula current.tokensCount 2 ⋏ failureBranch) ⋎
    (nativeShortLeFormula 3 current.tokensCount ⋏
      atArity ⋏
      atCode ⋏
      ((compactAdditiveArithmeticRelCodeValidClosedFormula witness.relationArity
          witness.relationCode ⋏ functionBranch) ⋎
       (compactAdditiveArithmeticRelCodeInvalidClosedFormula witness.relationArity
          witness.relationCode ⋏ failureBranch)))

def compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  let failureBranch := compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
    current next witness.tailBoundary witness.tailCount
  let continueBranch :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable width tokenCount
      current next witness.tailBoundary witness.tailCount 1
  let binaryBranch := compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width tokenCount
    current next witness.tailBoundary witness.tailCount binderArity
  let quantifierBranch := compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width
    tokenCount current next witness.tailBoundary witness.tailCount binderArity
  ((nativeEqFormula witness.tag 0 ⋎ nativeEqFormula witness.tag 1) ⋏
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable width tokenCount
        current next binderArity witness) ⋎
   ((nativeEqFormula witness.tag 2 ⋎ nativeEqFormula witness.tag 3) ⋏ continueBranch) ⋎
   ((nativeEqFormula witness.tag 4 ⋎ nativeEqFormula witness.tag 5) ⋏ binaryBranch) ⋎
   ((nativeEqFormula witness.tag 6 ⋎ nativeEqFormula witness.tag 7) ⋏ quantifierBranch) ⋎
   (nativeNeFormula witness.tag 0 ⋏
    nativeNeFormula witness.tag 1 ⋏
    nativeNeFormula witness.tag 2 ⋏
    nativeNeFormula witness.tag 3 ⋏
    nativeNeFormula witness.tag 4 ⋏
    nativeNeFormula witness.tag 5 ⋏
    nativeNeFormula witness.tag 6 ⋏
    nativeNeFormula witness.tag 7 ⋏ failureBranch)

def compactUnifiedParserSyntaxFormulaBranchExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  let failureBranch := compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width tokenCount
    current next witness.tailBoundary witness.tailCount
  let atTag := compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width tokenCount
    current.tokensBoundary current.tokensCount witness.tag (fixedNumeralTerm 0)
  (nativeEqFormula current.tokensCount 0 ⋏ failureBranch) ⋎
    (nativeShortLeFormula 1 current.tokensCount ⋏
      atTag ⋏
      compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable width tokenCount current
        next binderArity witness)

def compactUnifiedParserSyntaxFormulaExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      current.tasksFinish current.finish ⋏
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula tokenTable width
        tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary witness.tailCount
          witness.tailBoundarySize (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
            (fixedNumeralTerm 0) ⋏
      compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width tokenCount current next
        binderArity witness)

theorem compactUnifiedParserSyntaxFormulaClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount current next
        binderArity witness =
      compactUnifiedParserSyntaxFormulaExplicitFormula tokenTable width tokenCount current next
        binderArity witness := by
  unfold compactUnifiedParserSyntaxFormulaClosedFormula
  unfold compactUnifiedParserSyntaxFormulaExplicitFormula
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitFormula
  unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
  unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
  unfold compactUnifiedParserSyntaxFormulaRowsDef
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
  unfold compactUnifiedParserSyntaxTermFailureClosedFormula
  unfold compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
  unfold compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
  unfold compactUnifiedParserSyntaxFormulaBinaryClosedFormula
  unfold compactUnifiedParserSyntaxFormulaQuantifierClosedFormula
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  unfold compactAdditiveArithmeticRelCodeInvalidClosedFormula
  unfold compactAdditiveArithmeticRelCodeValidClosedFormula
  unfold compactAdditiveArithmeticRelCodeValidDef
  unfold nativeEqFormula nativeNeFormula shortNativeLeFormula nativeShortLeFormula termLeFormula
  simp [fixedNumeralTerm,
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
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

private theorem compactUnifiedParserSyntaxFormulaBranchCertificate_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount current next
      binderArity witness) :
    Nonempty
      (HybridCertificate
        (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width tokenCount current
          next binderArity witness)) := by
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitFormula
  rcases hgraph.2.2 with hempty | henough
  · let failureCertificate :=
      compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount hempty.2
    exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqCertificate current.tokensCount 0 hempty.1) failureCertificate)⟩
  · let tagCertificate := compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
        (fixedNumeralTerm 0) (by simp) henough.2.1
    have branchCertificateNonempty : Nonempty (HybridCertificate
        (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable width tokenCount
          current next binderArity witness)) := by
      unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
      rcases henough.2.2 with hrelation | hrest
      · rcases hrelation.2 with hshort | hlong
        · let relationTagCertificate := nativeEqEitherCertificate witness.tag 0 1 hrelation.1
          let relationBodyCertificate : HybridCertificate
              (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable width
                tokenCount current next binderArity witness) := by
            unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
            exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (shortNativeLeCertificate current.tokensCount 2 hshort.1)
                (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph tokenTable
                  width tokenCount current next witness.tailBoundary witness.tailCount hshort.2))
          let relationCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
            relationTagCertificate relationBodyCertificate
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            relationCertificate⟩
        · rcases hlong.2.2.2 with hvalid | hinvalid
          · let relationBodyCertificate : HybridCertificate
                (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable width
                  tokenCount current next binderArity witness) := by
              unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
              exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeShortLeCertificate 3 current.tokensCount hlong.1)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
                        witness.relationArity (fixedNumeralTerm 1) (by simp) hlong.2.1)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                        tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
                          witness.relationCode (fixedNumeralTerm 2) (by simp) hlong.2.2.1)
                      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                          (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
                            witness.relationArity witness.relationCode hvalid.1)
                          (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                            tokenTable width tokenCount current next witness.tailBoundary
                              witness.tailCount binderArity witness.relationArity hvalid.2))))))
            let relationCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeEqEitherCertificate witness.tag 0 1 hrelation.1) relationBodyCertificate
            exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              relationCertificate⟩
          · let relationBodyCertificate : HybridCertificate
                (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable width
                  tokenCount current next binderArity witness) := by
              unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
              exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeShortLeCertificate 3 current.tokensCount hlong.1)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
                        witness.relationArity (fixedNumeralTerm 1) (by simp) hlong.2.1)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                        tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
                          witness.relationCode (fixedNumeralTerm 2) (by simp) hlong.2.2.1)
                      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                          (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
                            witness.relationArity witness.relationCode hinvalid.1)
                          (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                            tokenTable width tokenCount current next witness.tailBoundary
                              witness.tailCount hinvalid.2))))))
            let relationCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeEqEitherCertificate witness.tag 0 1 hrelation.1) relationBodyCertificate
            exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              relationCertificate⟩
      · rcases hrest with hlogical | hrest
        · let logicalCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqEitherCertificate witness.tag 2 3 hlogical.1)
            (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary witness.tailCount 1
                hlogical.2)
          exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft logicalCertificate)⟩
        · rcases hrest with hbinary | hrest
          · let binaryCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeEqEitherCertificate witness.tag 4 5 hbinary.1)
              (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph tokenTable
                width tokenCount current next witness.tailBoundary witness.tailCount binderArity
                  hbinary.2)
            exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  binaryCertificate))⟩
          · rcases hrest with hquantifier | hinvalidTag
            · let quantifierCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (nativeEqEitherCertificate witness.tag 6 7 hquantifier.1)
                (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current next witness.tailBoundary witness.tailCount
                    binderArity hquantifier.2)
              exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                      quantifierCertificate)))⟩
            · let invalidCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (nativeNeCertificate witness.tag 0 hinvalidTag.1)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeNeCertificate witness.tag 1 hinvalidTag.2.1)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (nativeNeCertificate witness.tag 2 hinvalidTag.2.2.1)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (nativeNeCertificate witness.tag 3 hinvalidTag.2.2.2.1)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (nativeNeCertificate witness.tag 4 hinvalidTag.2.2.2.2.1)
                        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                          (nativeNeCertificate witness.tag 5 hinvalidTag.2.2.2.2.2.1)
                          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                            (nativeNeCertificate witness.tag 6 hinvalidTag.2.2.2.2.2.2.1)
                            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                              (nativeNeCertificate witness.tag 7
                                hinvalidTag.2.2.2.2.2.2.2.1)
                              (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                                tokenTable width tokenCount current next witness.tailBoundary
                                  witness.tailCount hinvalidTag.2.2.2.2.2.2.2.2))))))))
              exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                      invalidCertificate)))⟩
    let branchCertificate := Classical.choice branchCertificateNonempty
    let enoughCertificate := CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeShortLeCertificate 1 current.tokensCount henough.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction tagCertificate branchCertificate)
    exact ⟨CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight enoughCertificate⟩

inductive CompactSyntaxFormulaCheckedBranchData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Type where
  | empty
      (hcount : current.tokensCount = 0)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  | relationShort
      (hcount : 1 <= current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (htag : NativeEqEitherCheckedData witness.tag 0 1)
      (hshort : current.tokensCount <= 2)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  | relationValid
      (hcount : 1 <= current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (htag : NativeEqEitherCheckedData witness.tag 0 1)
      (hthree : 3 <= current.tokensCount)
      (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.relationArity)
      (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 2 witness.relationCode)
      (hvalid : ArithmeticRelCodeValid witness.relationArity
        witness.relationCode)
      (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount
        binderArity witness.relationArity)
  | relationInvalid
      (hcount : 1 <= current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (htag : NativeEqEitherCheckedData witness.tag 0 1)
      (hthree : 3 <= current.tokensCount)
      (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 1 witness.relationArity)
      (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 2 witness.relationCode)
      (hinvalid : ¬ ArithmeticRelCodeValid witness.relationArity
        witness.relationCode)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  | logical
      (hcount : 1 <= current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (htag : NativeEqEitherCheckedData witness.tag 2 3)
      (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount 1)
  | binary
      (hcount : 1 <= current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (htag : NativeEqEitherCheckedData witness.tag 4 5)
      (hbinary : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount
        binderArity)
  | quantifier
      (hcount : 1 <= current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (htag : NativeEqEitherCheckedData witness.tag 6 7)
      (hquantifier : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable
        width tokenCount current next witness.tailBoundary witness.tailCount
        binderArity)
  | invalidTag
      (hcount : 1 <= current.tokensCount)
      (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
        current.tokensBoundary current.tokensCount 0 witness.tag)
      (hne0 : witness.tag ≠ 0)
      (hne1 : witness.tag ≠ 1)
      (hne2 : witness.tag ≠ 2)
      (hne3 : witness.tag ≠ 3)
      (hne4 : witness.tag ≠ 4)
      (hne5 : witness.tag ≠ 5)
      (hne6 : witness.tag ≠ 6)
      (hne7 : witness.tag ≠ 7)
      (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)

theorem compactSyntaxFormulaCheckedBranchData_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    Nonempty (CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) := by
  rcases hgraph.2.2 with hempty | henough
  · exact ⟨.empty hempty.1 hempty.2⟩
  · rcases henough.2.2 with hrelation | hrest
    · rcases nativeEqEitherCheckedData_nonempty witness.tag 0 1
        hrelation.1 with ⟨htag⟩
      rcases hrelation.2 with hshort | hlong
      · exact ⟨.relationShort henough.1 henough.2.1 htag hshort.1
          hshort.2⟩
      · rcases hlong.2.2.2 with hvalid | hinvalid
        · exact ⟨.relationValid henough.1 henough.2.1 htag hlong.1
            hlong.2.1 hlong.2.2.1 hvalid.1 hvalid.2⟩
        · exact ⟨.relationInvalid henough.1 henough.2.1 htag hlong.1
            hlong.2.1 hlong.2.2.1 hinvalid.1 hinvalid.2⟩
    · rcases hrest with hlogical | hrest
      · rcases nativeEqEitherCheckedData_nonempty witness.tag 2 3
          hlogical.1 with ⟨htag⟩
        exact ⟨.logical henough.1 henough.2.1 htag hlogical.2⟩
      · rcases hrest with hbinary | hrest
        · rcases nativeEqEitherCheckedData_nonempty witness.tag 4 5
            hbinary.1 with ⟨htag⟩
          exact ⟨.binary henough.1 henough.2.1 htag hbinary.2⟩
        · rcases hrest with hquantifier | hinvalidTag
          · rcases nativeEqEitherCheckedData_nonempty witness.tag 6 7
              hquantifier.1 with ⟨htag⟩
            exact ⟨.quantifier henough.1 henough.2.1 htag hquantifier.2⟩
          · exact ⟨.invalidTag henough.1 henough.2.1 hinvalidTag.1
              hinvalidTag.2.1 hinvalidTag.2.2.1
              hinvalidTag.2.2.2.1 hinvalidTag.2.2.2.2.1
              hinvalidTag.2.2.2.2.2.1
              hinvalidTag.2.2.2.2.2.2.1
              hinvalidTag.2.2.2.2.2.2.2.1
              hinvalidTag.2.2.2.2.2.2.2.2⟩

noncomputable def compactSyntaxFormulaCheckedBranchDataOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount current
      next binderArity witness :=
  Classical.choice (compactSyntaxFormulaCheckedBranchData_nonempty tokenTable
    width tokenCount current next binderArity witness hgraph)

noncomputable def
    compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxFormulaBranchExplicitFormula
  cases data with
  | empty hcount hfailure =>
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqCertificate current.tokensCount 0 hcount)
          (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount hfailure))
  | relationShort hcount hatTag htag hshort hfailure =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let relationTagCertificate :=
        nativeEqEitherCertificateFromData witness.tag 0 1 htag
      let relationBodyCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
            tokenTable width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortNativeLeCertificate current.tokensCount 2 hshort)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure))
      let tagBranchCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            relationTagCertificate relationBodyCertificate)
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))
  | relationValid hcount hatTag htag hthree hatArity hatCode hvalid
      hfunction =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let relationTagCertificate :=
        nativeEqEitherCertificateFromData witness.tag 0 1 htag
      let relationBodyCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
            tokenTable width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 1 witness.relationArity
                (fixedNumeralTerm 1) (by simp) hatArity)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.relationCode
                  (fixedNumeralTerm 2) (by simp) hatCode)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
                      witness.relationArity witness.relationCode hvalid)
                    (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount binderArity
                      witness.relationArity hfunction))))))
      let tagBranchCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            relationTagCertificate relationBodyCertificate)
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))
  | relationInvalid hcount hatTag htag hthree hatArity hatCode hinvalid
      hfailure =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let relationTagCertificate :=
        nativeEqEitherCertificateFromData witness.tag 0 1 htag
      let relationBodyCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
            tokenTable width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 1 witness.relationArity
                (fixedNumeralTerm 1) (by simp) hatArity)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.relationCode
                  (fixedNumeralTerm 2) (by simp) hatCode)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
                      witness.relationArity witness.relationCode hinvalid)
                    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount hfailure))))))
      let tagBranchCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            relationTagCertificate relationBodyCertificate)
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))
  | logical hcount hatTag htag hcontinue =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let logicalCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
          (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount 1 hcontinue)
      let tagBranchCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            logicalCertificate)
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))
  | binary hcount hatTag htag hbinary =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let binaryCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
          (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount binderArity hbinary)
      let tagBranchCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              binaryCertificate))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))
  | quantifier hcount hatTag htag hquantifier =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let quantifierCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
          (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount binderArity hquantifier)
      let tagBranchCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                quantifierCertificate)))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))
  | invalidTag hcount hatTag hne0 hne1 hne2 hne3 hne4 hne5 hne6 hne7
      hfailure =>
      let tagCertificate :=
        compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag
      let invalidCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeNeCertificate witness.tag 0 hne0)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeNeCertificate witness.tag 1 hne1)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeNeCertificate witness.tag 2 hne2)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (nativeNeCertificate witness.tag 3 hne3)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeNeCertificate witness.tag 4 hne4)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (nativeNeCertificate witness.tag 5 hne5)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (nativeNeCertificate witness.tag 6 hne6)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (nativeNeCertificate witness.tag 7 hne7)
                        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                          tokenTable width tokenCount current next
                          witness.tailBoundary witness.tailCount hfailure))))))))
      let tagBranchCertificate : HybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                invalidCertificate)))
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 1 current.tokensCount hcount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tagCertificate tagBranchCertificate))

noncomputable def compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount current next
      binderArity witness) :
    HybridCertificate
      (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount current next
        binderArity witness) := by
  let branchData := compactSyntaxFormulaCheckedBranchDataOfGraph tokenTable
    width tokenCount current next binderArity witness hgraph
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current.tasksFinish current.finish hgraph.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
          witness.tailCount witness.tailBoundarySize 1 binderArity 0 (fixedNumeralTerm 1)
            (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) (fun valuation => by simp)
              (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
                (fun valuation => by simp) hgraph.2.1)
      (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        tokenTable width tokenCount current next binderArity witness
        branchData))
  exact .cast
    (compactUnifiedParserSyntaxFormulaClosedFormula_alignment tokenTable width tokenCount current next
      binderArity witness).symm parts

noncomputable def compileCompactUnifiedParserSyntaxFormulaExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount current next
      binderArity witness) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount current next
          binderArity witness).freeVariables zeroValuation)
      (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount current next
        binderArity witness) :=
  (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph tokenTable width tokenCount
    current next binderArity witness hgraph).compile

noncomputable def compactUnifiedParserSyntaxFormulaExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount current next
      binderArity witness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph)

theorem compileCompactUnifiedParserSyntaxFormulaExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount current next
      binderArity witness) :
    (compileCompactUnifiedParserSyntaxFormulaExplicitHybridContext tokenTable width tokenCount current
      next binderArity witness hgraph).payloadLength ≤
      compactUnifiedParserSyntaxFormulaExplicitStructuralResource tokenTable width tokenCount current
        next binderArity witness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph)

#print axioms compactUnifiedParserSyntaxFormulaClosedFormula_alignment
#print axioms compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
#print axioms compileCompactUnifiedParserSyntaxFormulaExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
