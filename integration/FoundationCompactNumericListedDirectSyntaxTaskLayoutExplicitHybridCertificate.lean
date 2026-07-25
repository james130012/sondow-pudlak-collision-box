import integration.FoundationCompactNumericListedDirectSyntaxTaskRowRealization
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactBinaryNumeralTerm
import integration.FoundationCompactPABinaryNumeralAddition
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Explicit hybrid certificate for one syntax-task layout

The two internal cursors are installed explicitly.  Their bounds follow from
the three concrete token cells, and the terminal certificate uses those same
cells in the exact source-formula order.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
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

def compactSyntaxTaskDirectLayoutTerminalImageCodeEnvelope
    (termCodeBound : Nat) : Nat :=
  5 * termCodeBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 2)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 2)).length + 1

def compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope
    (termCodeBound : Nat) : Nat :=
  let cellCode :=
    uniformRewritingFormulaCodeEnvelope
      (compactSyntaxTaskDirectLayoutTerminalImageCodeEnvelope termCodeBound)
      (binaryFormulaCode
        (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)).length
  3 * cellCode + 2 * (binaryNatCode 4).length + 1

private theorem closedShift_two_code_length_le_five_layout
    (term : ValuationTerm) (termCodeBound : Nat)
    (hterm : (binaryTermCode term).length <= termCodeBound) :
    (binaryTermCode (closedShift 2 term)).length <= 5 * termCodeBound := by
  have hsymbols : termSymbolCount term <= termCodeBound :=
    (termSymbolCount_le_binaryTermCode_length term).trans hterm
  have hfirstRaw := binaryTermCode_bShift_length_le_add_symbols term
  have hfirst : (binaryTermCode (Rew.bShift term)).length <=
      3 * termCodeBound := by
    omega
  have hshiftedSymbols :
      termSymbolCount (Rew.bShift term) <= termCodeBound := by
    rw [termSymbolCount_bShift]
    exact hsymbols
  have hsecondRaw :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift term)
  change
    (binaryTermCode (Rew.bShift (Rew.bShift term))).length <=
      5 * termCodeBound
  omega

theorem compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_code_length_le_uniform
    (tokenTable width tokenCount start finish : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (termCodeBound : Nat)
    (htable : (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <=
      termCodeBound)
    (hwidth : (binaryTermCode (shortBinaryNumeralTerm width)).length <=
      termCodeBound)
    (htokenCount :
      (binaryTermCode (shortBinaryNumeralTerm tokenCount)).length <=
        termCodeBound)
    (hstart : (binaryTermCode (shortBinaryNumeralTerm start)).length <=
      termCodeBound)
    (hfinish : (binaryTermCode (shortBinaryNumeralTerm finish)).length <=
      termCodeBound)
    (hkind : (binaryTermCode kindTerm).length <= termCodeBound)
    (hbinder : (binaryTermCode binderArityTerm).length <= termCodeBound)
    (hrepeat : (binaryTermCode repeatCountTerm).length <= termCodeBound) :
    (binaryFormulaCode
      (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
        tokenCount start finish kindTerm binderArityTerm
        repeatCountTerm)).length <=
      compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope termCodeBound := by
  let imageBound :=
    compactSyntaxTaskDirectLayoutTerminalImageCodeEnvelope termCodeBound
  have himageShift (term : ValuationTerm)
      (hterm : (binaryTermCode term).length <= termCodeBound) :
      (binaryTermCode (closedShift 2 term)).length <= imageBound := by
    exact (closedShift_two_code_length_le_five_layout term termCodeBound
      hterm).trans (by
        unfold imageBound
          compactSyntaxTaskDirectLayoutTerminalImageCodeEnvelope
        omega)
  have himageBvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 2)).length <=
        imageBound := by
    unfold imageBound compactSyntaxTaskDirectLayoutTerminalImageCodeEnvelope
    omega
  have himageBvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 2)).length <=
        imageBound := by
    unfold imageBound compactSyntaxTaskDirectLayoutTerminalImageCodeEnvelope
    omega
  let formula1 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (shortBinaryNumeralTerm start),
        closedShift 2 kindTerm, (#1 : ArithmeticSemiterm Nat 2)]
  let formula2 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#1 : ArithmeticSemiterm Nat 2), closedShift 2 binderArityTerm,
        (#0 : ArithmeticSemiterm Nat 2)]
  let formula3 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#0 : ArithmeticSemiterm Nat 2), closedShift 2 repeatCountTerm,
        closedShift 2 (shortBinaryNumeralTerm finish)]
  have hformula1 :
      (binaryFormulaCode formula1).length <=
        uniformRewritingFormulaCodeEnvelope imageBound
          (binaryFormulaCode
            (Rewriting.emb (ξ := Nat)
              compactAdditiveTokenCellDef.val)).length := by
    let rewriting : Rew ℒₒᵣ Nat 6 Nat 2 := Rew.subst
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (shortBinaryNumeralTerm start),
        closedShift 2 kindTerm, (#1 : ArithmeticSemiterm Nat 2)]
    have hrewriting : RewritingImageCodeBound rewriting imageBound := by
      constructor
      · intro coordinate
        dsimp only [rewriting]
        rw [Rew.subst_bvar]
        fin_cases coordinate
        · exact himageShift _ htable
        · exact himageShift _ hwidth
        · exact himageShift _ htokenCount
        · exact himageShift _ hstart
        · exact himageShift _ hkind
        · exact himageBvar1
      · intro coordinate
        dsimp only [rewriting]
        simp
    have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
      imageBound hrewriting
      (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)
    simpa only [formula1, rewriting] using hraw
  have hformula2 :
      (binaryFormulaCode formula2).length <=
        uniformRewritingFormulaCodeEnvelope imageBound
          (binaryFormulaCode
            (Rewriting.emb (ξ := Nat)
              compactAdditiveTokenCellDef.val)).length := by
    let rewriting : Rew ℒₒᵣ Nat 6 Nat 2 := Rew.subst
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#1 : ArithmeticSemiterm Nat 2), closedShift 2 binderArityTerm,
        (#0 : ArithmeticSemiterm Nat 2)]
    have hrewriting : RewritingImageCodeBound rewriting imageBound := by
      constructor
      · intro coordinate
        dsimp only [rewriting]
        rw [Rew.subst_bvar]
        fin_cases coordinate
        · exact himageShift _ htable
        · exact himageShift _ hwidth
        · exact himageShift _ htokenCount
        · exact himageBvar1
        · exact himageShift _ hbinder
        · exact himageBvar0
      · intro coordinate
        dsimp only [rewriting]
        simp
    have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
      imageBound hrewriting
      (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)
    simpa only [formula2, rewriting] using hraw
  have hformula3 :
      (binaryFormulaCode formula3).length <=
        uniformRewritingFormulaCodeEnvelope imageBound
          (binaryFormulaCode
            (Rewriting.emb (ξ := Nat)
              compactAdditiveTokenCellDef.val)).length := by
    let rewriting : Rew ℒₒᵣ Nat 6 Nat 2 := Rew.subst
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#0 : ArithmeticSemiterm Nat 2), closedShift 2 repeatCountTerm,
        closedShift 2 (shortBinaryNumeralTerm finish)]
    have hrewriting : RewritingImageCodeBound rewriting imageBound := by
      constructor
      · intro coordinate
        dsimp only [rewriting]
        rw [Rew.subst_bvar]
        fin_cases coordinate
        · exact himageShift _ htable
        · exact himageShift _ hwidth
        · exact himageShift _ htokenCount
        · exact himageBvar0
        · exact himageShift _ hrepeat
        · exact himageShift _ hfinish
      · intro coordinate
        dsimp only [rewriting]
        simp
    have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
      imageBound hrewriting
      (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)
    simpa only [formula3, rewriting] using hraw
  have hinner :
      (binaryFormulaCode (formula2 ⋏ formula3)).length <=
        (binaryFormulaCode formula2).length +
          (binaryFormulaCode formula3).length +
          (binaryNatCode 4).length := by
    simp [binaryFormulaCode]
    omega
  have houter :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        (binaryFormulaCode formula1).length +
          (binaryFormulaCode (formula2 ⋏ formula3)).length +
          (binaryNatCode 4).length := by
    simp [binaryFormulaCode]
    omega
  change (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <= _
  dsimp only [imageBound] at hformula1 hformula2 hformula3
  simp only [compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope]
  omega

theorem
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount start finish : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hkind : kindTerm.freeVariables = ∅)
    (hbinder : binderArityTerm.freeVariables = ∅)
    (hrepeat : repeatCountTerm.freeVariables = ∅) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish kindTerm binderArityTerm
      repeatCountTerm).freeVariables = ∅ := by
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsTerminal
  have hshift (term : ValuationTerm)
      (hterm : term.freeVariables = ∅) :
      (closedShift 2 term).freeVariables = ∅ := by
    unfold closedShift
    exact bShift_freeVariables_eq_empty_of_empty _
      (bShift_freeVariables_eq_empty_of_empty _ hterm)
  have hformula1 :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactAdditiveTokenCellDef.val
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (shortBinaryNumeralTerm start),
        closedShift 2 kindTerm, (#1 : ArithmeticSemiterm Nat 2)] (by
          intro coordinate
          fin_cases coordinate
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ hkind
          · simp)
  have hformula2 :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactAdditiveTokenCellDef.val
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#1 : ArithmeticSemiterm Nat 2), closedShift 2 binderArityTerm,
        (#0 : ArithmeticSemiterm Nat 2)] (by
          intro coordinate
          fin_cases coordinate
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · simp
          · exact hshift _ hbinder
          · simp)
  have hformula3 :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactAdditiveTokenCellDef.val
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#0 : ArithmeticSemiterm Nat 2), closedShift 2 repeatCountTerm,
        closedShift 2 (shortBinaryNumeralTerm finish)] (by
          intro coordinate
          fin_cases coordinate
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
          · simp
          · exact hshift _ hrepeat
          · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _))
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and, hformula1, hformula2,
    hformula3]
  simp

#print axioms
  compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_code_length_le_uniform
#print axioms
  compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty

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
