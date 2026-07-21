import integration.FoundationCompactNumericListedDirectSyntaxTaskRowRealization
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactBinaryNumeralTerm
import integration.FoundationCompactPABinaryNumeralAddition

/-!
# Explicit hybrid certificate for one syntax-task layout

The two internal cursors are installed explicitly.  Their bounds follow from
the three concrete token cells, and the terminal certificate uses those same
cells in the exact source-formula order.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

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

private theorem explicitBoundedWitnessFormula_two_eq
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 2) :
    explicitBoundedWitnessFormula bound 2 body =
      (body.bexsLTSucc (closedShift 1 bound)).bexsLTSucc bound := by
  rfl

def compactSyntaxTaskDirectLayoutAtValuationTermsFormula
    (tokenTable width tokenCount start finish : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactSyntaxTaskDirectLayoutDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish,
      kindTerm,
      binderArityTerm,
      repeatCountTerm]

def compactSyntaxTaskDirectLayoutAtValuationTermsTerminal
    (tokenTable width tokenCount start finish : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (shortBinaryNumeralTerm start),
        closedShift 2 kindTerm,
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 2),
          closedShift 2 binderArityTerm,
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#0 : ArithmeticSemiterm Nat 2),
          closedShift 2 repeatCountTerm,
          closedShift 2 (shortBinaryNumeralTerm finish)]))

def compactSyntaxTaskDirectLayoutClosedFormula
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat) : ValuationFormula :=
  compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width tokenCount
    start finish (shortBinaryNumeralTerm kind)
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

def compactSyntaxTaskDirectLayoutTerminal
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat) :
    ArithmeticSemiformula Nat 2 :=
  compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width tokenCount
    start finish (shortBinaryNumeralTerm kind)
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

theorem compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
    (tokenTable width tokenCount start finish : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width tokenCount
        start finish kindTerm binderArityTerm repeatCountTerm =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm tokenCount) 2
        (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width tokenCount
          start finish kindTerm binderArityTerm repeatCountTerm) := by
  rw [explicitBoundedWitnessFormula_two_eq]
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsFormula
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsTerminal
  unfold compactSyntaxTaskDirectLayoutDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply arithmeticRewritingApp_congr
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

theorem compactSyntaxTaskDirectLayoutClosedFormula_alignment
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat) :
    compactSyntaxTaskDirectLayoutClosedFormula tokenTable width tokenCount
        start finish kind binderArity repeatCount =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm tokenCount) 2
        (compactSyntaxTaskDirectLayoutTerminal tokenTable width tokenCount
          start finish kind binderArity repeatCount) := by
  simpa [compactSyntaxTaskDirectLayoutClosedFormula,
    compactSyntaxTaskDirectLayoutTerminal] using
      compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment tokenTable width
        tokenCount start finish (shortBinaryNumeralTerm kind)
          (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm repeatCount)

theorem compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
    (tokenTable width tokenCount start finish binderStart countStart : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width tokenCount
      start finish kindTerm binderArityTerm repeatCountTerm) ⇜
        ![shortBinaryNumeralTerm countStart,
          shortBinaryNumeralTerm binderStart] =
      (compactAdditiveTokenCellAtValuationFormula
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm start)
          kindTerm
          (shortBinaryNumeralTerm binderStart) ⋏
        (compactAdditiveTokenCellAtValuationFormula
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm binderStart)
            binderArityTerm
            (shortBinaryNumeralTerm countStart) ⋏
          compactAdditiveTokenCellAtValuationFormula
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm countStart)
            repeatCountTerm
            (shortBinaryNumeralTerm finish))) := by
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsTerminal
  unfold compactAdditiveTokenCellAtValuationFormula
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

theorem compactSyntaxTaskDirectLayoutTerminal_substitution_alignment
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount binderStart countStart : Nat) :
    (compactSyntaxTaskDirectLayoutTerminal tokenTable width tokenCount
      start finish kind binderArity repeatCount) ⇜
        ![shortBinaryNumeralTerm countStart,
          shortBinaryNumeralTerm binderStart] =
      (compactAdditiveTokenCellAtValuationFormula
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm start)
          (shortBinaryNumeralTerm kind)
          (shortBinaryNumeralTerm binderStart) ⋏
        (compactAdditiveTokenCellAtValuationFormula
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm binderStart)
            (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm countStart) ⋏
          compactAdditiveTokenCellAtValuationFormula
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm countStart)
            (shortBinaryNumeralTerm repeatCount)
            (shortBinaryNumeralTerm finish))) := by
  simpa [compactSyntaxTaskDirectLayoutTerminal] using
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
      tokenTable width tokenCount start finish binderStart countStart
        (shortBinaryNumeralTerm kind) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm repeatCount)

noncomputable def compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hkindValue : ∀ valuation, termValue valuation kindTerm = kind)
    (hbinderArityValue : ∀ valuation, termValue valuation binderArityTerm = binderArity)
    (hrepeatCountValue : ∀ valuation, termValue valuation repeatCountTerm = repeatCount)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (kind, binderArity, repeatCount)) :
    HybridCertificate
      (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width tokenCount
        start finish kindTerm binderArityTerm repeatCountTerm) := by
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hrepeat := hcells.2.2
  have hbinderStartLe : binderStart ≤ tokenCount := by
    have hstart := hkind.1
    have hnext := hkind.2.1
    omega
  have hcountStartLe : countStart ≤ tokenCount := by
    have hstart := hbinder.1
    have hnext := hbinder.2.1
    omega
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm start)
        kindTerm
        (shortBinaryNumeralTerm binderStart) (by
          simpa [binderStart, countStart,
            termValue_shortBinaryNumeralTerm, hkindValue _] using hkind))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm binderStart)
          binderArityTerm
          (shortBinaryNumeralTerm countStart) (by
            simpa [binderStart, countStart,
              termValue_shortBinaryNumeralTerm, hbinderArityValue _] using hbinder))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm countStart)
          repeatCountTerm
          (shortBinaryNumeralTerm finish) (by
            simpa [binderStart, countStart,
              termValue_shortBinaryNumeralTerm, hrepeatCountValue _] using hrepeat)))
  let values : Fin 2 → Nat := ![countStart, binderStart]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm countStart,
          shortBinaryNumeralTerm binderStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : HybridCertificate
      ((compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width tokenCount
        start finish kindTerm binderArityTerm repeatCountTerm) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount start finish binderStart countStart
            kindTerm binderArityTerm repeatCountTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width tokenCount
      start finish kindTerm binderArityTerm repeatCountTerm)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact hcountStartLe
      · exact hbinderStartLe) terminal
  exact .cast
    (compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment tokenTable width
      tokenCount start finish kindTerm binderArityTerm repeatCountTerm).symm installed

noncomputable def compactSyntaxTaskDirectLayoutExplicitHybridCertificateOfLayout
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (kind, binderArity, repeatCount)) :
    HybridCertificate
      (compactSyntaxTaskDirectLayoutClosedFormula tokenTable width tokenCount
        start finish kind binderArity repeatCount) := by
  simpa [compactSyntaxTaskDirectLayoutClosedFormula] using
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
      tokenTable width tokenCount start finish kind binderArity repeatCount
        (shortBinaryNumeralTerm kind) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm repeatCount)
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
        (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hlayout

#print axioms compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
#print axioms compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
#print axioms compactSyntaxTaskDirectLayoutClosedFormula_alignment
#print axioms compactSyntaxTaskDirectLayoutTerminal_substitution_alignment
#print axioms compactSyntaxTaskDirectLayoutExplicitHybridCertificateOfLayout

end FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
