import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactPABinaryNumeralAddition

/-!
# Explicit hybrid certificate for one syntax-task-list row

The endpoint preserves an arbitrary index term in the source syntax.  The two
boundary cursors are installed explicitly, and the selected row terminates in
the concrete three-cell syntax-task layout certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

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

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro coordinate
          exact Fin.elim0 coordinate
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ k ih =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun coordinate : Fin k => values coordinate.succ) := by
        apply Rew.ext
        · intro coordinate
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift) (closedShift k term) := by
              simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun coordinate : Fin k => values coordinate.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := ih _

theorem explicitBoundedWitnessFormula_two_eq
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 2) :
    explicitBoundedWitnessFormula bound 2 body =
      (body.bexsLTSucc (closedShift 1 bound)).bexsLTSucc bound := by
  rfl

def successorIndexTerm (indexTerm : ValuationTerm) : ValuationTerm :=
  ‘!!indexTerm + 1’

def compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskListAtRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm boundaryTable,
      shortBinaryNumeralTerm count,
      indexTerm,
      kindTerm,
      binderArityTerm,
      repeatCountTerm]

def compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal
    (tokenTable width tokenCount boundaryTable : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 indexTerm,
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2 (successorIndexTerm indexTerm),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactSyntaxTaskDirectLayoutDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 2),
          (#0 : ArithmeticSemiterm Nat 2),
          closedShift 2 kindTerm,
          closedShift 2 binderArityTerm,
          closedShift 2 repeatCountTerm]))

def compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
    (tokenTable width tokenCount boundaryTable : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  ((compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width tokenCount
      boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm).bexsLTSucc
        (closedShift 1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
          (shortBinaryNumeralTerm tokenCount)

def compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  “!!indexTerm < !!(shortBinaryNumeralTerm count)” ⋏
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable width
      tokenCount boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm

def compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula
    (tokenTable width tokenCount boundaryTable count
      kind binderArity repeatCount : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width tokenCount
    boundaryTable count indexTerm (shortBinaryNumeralTerm kind)
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

def compactAdditiveSyntaxTaskListAtRowsTerminal
    (tokenTable width tokenCount boundaryTable
      kind binderArity repeatCount : Nat)
    (indexTerm : ValuationTerm) : ArithmeticSemiformula Nat 2 :=
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width tokenCount
    boundaryTable indexTerm (shortBinaryNumeralTerm kind)
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

def compactAdditiveSyntaxTaskListAtRowsWitnessFormula
    (tokenTable width tokenCount boundaryTable
      kind binderArity repeatCount : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable width tokenCount
    boundaryTable indexTerm (shortBinaryNumeralTerm kind)
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

def compactAdditiveSyntaxTaskListAtRowsExplicitFormula
    (tokenTable width tokenCount boundaryTable count
      kind binderArity repeatCount : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula tokenTable width tokenCount
    boundaryTable count indexTerm (shortBinaryNumeralTerm kind)
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

theorem compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
          repeatCountTerm =
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula tokenTable width
        tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
          repeatCountTerm := by
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal
  unfold compactAdditiveSyntaxTaskListAtRowsDef
  unfold successorIndexTerm
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  · congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate

theorem compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula_alignment
    (tokenTable width tokenCount boundaryTable count
      kind binderArity repeatCount : Nat)
    (indexTerm : ValuationTerm) :
    compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula tokenTable
        width tokenCount boundaryTable count kind binderArity repeatCount
          indexTerm =
      compactAdditiveSyntaxTaskListAtRowsExplicitFormula tokenTable width
        tokenCount boundaryTable count kind binderArity repeatCount
          indexTerm := by
  simpa [compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula,
    compactAdditiveSyntaxTaskListAtRowsExplicitFormula] using
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment tokenTable width
        tokenCount boundaryTable count indexTerm (shortBinaryNumeralTerm kind)
          (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

theorem compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
    (tokenTable width tokenCount boundaryTable left right : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width tokenCount
      boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm) ⇜
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          indexTerm
          (shortBinaryNumeralTerm left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (successorIndexTerm indexTerm)
            (shortBinaryNumeralTerm right) ⋏
          compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
            tokenCount left right kindTerm binderArityTerm repeatCountTerm)) := by
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactAdditiveSyntaxTaskListAtRowsTerminal_substitution_alignment
    (tokenTable width tokenCount boundaryTable
      kind binderArity repeatCount left right : Nat)
    (indexTerm : ValuationTerm) :
    (compactAdditiveSyntaxTaskListAtRowsTerminal tokenTable width tokenCount
      boundaryTable kind binderArity repeatCount indexTerm) ⇜
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          indexTerm
          (shortBinaryNumeralTerm left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (successorIndexTerm indexTerm)
            (shortBinaryNumeralTerm right) ⋏
          compactSyntaxTaskDirectLayoutClosedFormula tokenTable width
            tokenCount left right kind binderArity repeatCount)) := by
  simpa [compactAdditiveSyntaxTaskListAtRowsTerminal,
    compactSyntaxTaskDirectLayoutClosedFormula] using
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
        tokenTable width tokenCount boundaryTable left right indexTerm
          (shortBinaryNumeralTerm kind) (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm repeatCount)

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

noncomputable def strictCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hstrict : termValue zeroValuation leftTerm <
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm < !!rightTerm” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hstrict
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

noncomputable def
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hkindValue : ∀ valuation, termValue valuation kindTerm = kind)
    (hbinderArityValue : ∀ valuation, termValue valuation binderArityTerm = binderArity)
    (hrepeatCountValue : ∀ valuation, termValue valuation repeatCountTerm = repeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount) :
    HybridCertificate
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
          repeatCountTerm) := by
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  have hleftLe := hleftData.1
  have hrightLe := hrightData.1
  have hleftEntry := hrightData.2.1
  have hrightEntry := hrightData.2.2.1
  have hlayout := hrightData.2.2.2
  let values : Fin 2 → Nat := ![right, left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm right,
          shortBinaryNumeralTerm left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        indexTerm
        (shortBinaryNumeralTerm left) (by
          simpa [left, right, termValue_shortBinaryNumeralTerm,
            hindexValue,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using hleftEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (successorIndexTerm indexTerm)
          (shortBinaryNumeralTerm right) (by
            simpa [left, right, successorIndexTerm,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              hindexValue,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using hrightEntry))
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount left right kind binderArity repeatCount
            kindTerm binderArityTerm repeatCountTerm hkindValue hbinderArityValue
              hrepeatCountValue (by simpa [left, right] using hlayout)))
  let terminal : HybridCertificate
      ((compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width tokenCount
        boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount boundaryTable left right indexTerm kindTerm
            binderArityTerm repeatCountTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width tokenCount
      boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact hrightLe
      · exact hleftLe) terminal
  let witness : HybridCertificate
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable width
        tokenCount boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm) :=
    .cast (by
      unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
      rw [explicitBoundedWitnessFormula_two_eq]) installed
  let guard := strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
    simpa [termValue_shortBinaryNumeralTerm, hindexValue] using hgraph.1)
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guard witness
  exact .cast
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment
      tokenTable width tokenCount boundaryTable count indexTerm kindTerm
      binderArityTerm repeatCountTerm).symm parts

noncomputable def
    compactAdditiveSyntaxTaskListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount : Nat)
    (indexTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount) :
    HybridCertificate
      (compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula tokenTable
        width tokenCount boundaryTable count kind binderArity repeatCount
          indexTerm) := by
  simpa [compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula] using
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount boundaryTable count index kind binderArity repeatCount
        indexTerm (shortBinaryNumeralTerm kind) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm repeatCount) hindexValue
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hgraph

#print axioms
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment
#print axioms
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
#print axioms
  compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula_alignment
#print axioms compactAdditiveSyntaxTaskListAtRowsTerminal_substitution_alignment
#print axioms
  compactAdditiveSyntaxTaskListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
