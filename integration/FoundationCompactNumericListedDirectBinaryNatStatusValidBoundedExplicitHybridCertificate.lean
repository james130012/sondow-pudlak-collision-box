import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidity
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Explicit certificate for bounded binary-Nat status validity

The four witnesses are installed in their actual de Bruijn order.  The
terminal then selects the running, failed, or completed status certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

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

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private theorem emb_comp_subst_eq_subst_comp_emb
    {predicateArity targetArity : Nat}
    (sourceTerms : Fin predicateArity ->
      ArithmeticSemiterm Empty targetArity)
    (targetTerms : Fin predicateArity ->
      ArithmeticSemiterm Nat targetArity)
    (hterms : forall coordinate,
      (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity)
          (sourceTerms coordinate) = targetTerms coordinate) :
    (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity).comp
        (Rew.subst sourceTerms) =
      (Rew.subst targetTerms).comp
        (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity) := by
  apply Rew.ext
  · intro coordinate
    simpa [Rew.comp_app, Rew.subst_bvar] using hterms coordinate
  · intro coordinate
    exact Empty.elim coordinate

@[simp] private theorem embedding_substitutedFormula
    {formulaArity targetArity : Nat}
    (formula : ArithmeticSemiformula Empty formulaArity)
    (terms : Fin formulaArity ->
      ArithmeticSemiterm Empty targetArity) :
    (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity) ▹
        (formula ⇜ terms) =
      (Rewriting.emb (ξ := Nat) formula) ⇜
        (fun index =>
          (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity)
            (terms index)) := by
  have hcomposition :
      (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity).comp
          (Rew.subst terms) =
        (Rew.subst (fun index =>
          (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity)
            (terms index))).comp
          (Rew.emb : Rew ℒₒᵣ Empty formulaArity Nat formulaArity) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    rfl
  calc
    (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity) ▹
        (formula ⇜ terms) =
      ((Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity).comp
        (Rew.subst terms)) ▹ formula := by
          rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst (fun index =>
          (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity)
            (terms index))).comp
          (Rew.emb : Rew ℒₒᵣ Empty formulaArity Nat formulaArity)) ▹
        formula := by rw [hcomposition]
    _ = (Rewriting.emb (ξ := Nat) formula) ⇜
        (fun index =>
          (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity)
            (terms index)) := by
          rw [TransitiveRewriting.comp_app]

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

@[simp] private theorem substitute_closedShift
    {depth : Nat} (values : Fin depth -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift depth term) = term := by
  induction depth with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) =
          Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ depth inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin depth => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (depth + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (closedShift depth term) := by
                simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin depth => values index.succ)
              (closedShift depth term) := by rw [hrew]
        _ = term := inductionHypothesis _

def compactBinaryNatStatusValidBoundedClosedFormula
    (tokenTable width tokenCount start finish valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm valueBound]

theorem compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start finish valueBound : Nat) :
    (compactBinaryNatStatusValidBoundedClosedFormula
      tokenTable width tokenCount start finish valueBound).freeVariables = ∅ := by
  unfold compactBinaryNatStatusValidBoundedClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private def compactBinaryNatStatusValidBoundedSourceTerms
    (tokenTable width tokenCount start finish valueBound : Nat) :
    Fin 6 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm start,
    shortBinaryNumeralTerm finish,
    shortBinaryNumeralTerm valueBound]

private def compactBinaryNatStatusValidBoundedSourceTerminal :
    ArithmeticSemiformula Nat 10 :=
  ((Rewriting.emb (ξ := Nat) compactBinaryNatRunningStatusSliceDef.val) ⇜
      ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #7, #8]) ⋎
    (((Rewriting.emb (ξ := Nat) compactBinaryNatFailedStatusSliceDef.val) ⇜
        ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #7, #8]) ⋎
      (((Rewriting.emb (ξ := Nat)
            compactBinaryNatCompletedStatusPrefixDef.val) ⇜
          ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #7, #3]) ⋏
        (((Rewriting.emb (ξ := Nat)
              compactAdditiveStructuredListLayoutDef.val) ⇜
            ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #3, #0, #8, #2]) ⋏
          (((Rewriting.emb (ξ := Nat)
                compactAdditiveUnitBoundaryRowsDef.val) ⇜
              ![(#6 : ArithmeticSemiterm Nat 10), #0, #2]) ⋏
            (((Rewriting.emb (ξ := Nat) compactNatSizeDef.val) ⇜
                ![(#1 : ArithmeticSemiterm Nat 10), #2]) ⋏
              “#1 ≤ (#0 + 1) * #6”)))))

def compactBinaryNatStatusValidBoundedRawTerminal
    (tokenTable width tokenCount start finish : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactBinaryNatRunningStatusSliceDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
        closedShift 4 (shortBinaryNumeralTerm width),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 (shortBinaryNumeralTerm start),
        closedShift 4 (shortBinaryNumeralTerm finish)]) ⋎
    (((Rewriting.emb (ξ := Nat) compactBinaryNatFailedStatusSliceDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4 (shortBinaryNumeralTerm start),
          closedShift 4 (shortBinaryNumeralTerm finish)]) ⋎
      (((Rewriting.emb (ξ := Nat)
            compactBinaryNatCompletedStatusPrefixDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
            closedShift 4 (shortBinaryNumeralTerm width),
            closedShift 4 (shortBinaryNumeralTerm tokenCount),
            closedShift 4 (shortBinaryNumeralTerm start),
            (#3 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat)
              compactAdditiveStructuredListLayoutDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              (#3 : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4),
              closedShift 4 (shortBinaryNumeralTerm finish),
              (#2 : ArithmeticSemiterm Nat 4)]) ⋏
          (((Rewriting.emb (ξ := Nat)
                compactAdditiveUnitBoundaryRowsDef.val) ⇜
              ![closedShift 4 (shortBinaryNumeralTerm tokenCount),
                (#0 : ArithmeticSemiterm Nat 4),
                (#2 : ArithmeticSemiterm Nat 4)]) ⋏
            (((Rewriting.emb (ξ := Nat) compactNatSizeDef.val) ⇜
                ![(#1 : ArithmeticSemiterm Nat 4),
                  (#2 : ArithmeticSemiterm Nat 4)]) ⋏
              “#1 ≤ (#0 + 1) *
                !!(closedShift 4 (shortBinaryNumeralTerm tokenCount))”)))))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
private theorem compactBinaryNatStatusValidBoundedDef_emb_eq_sourceBody :
    Rewriting.emb (ξ := Nat) compactBinaryNatStatusValidBoundedDef.val =
      sourceBoundedWitnessFormula
        (#5 : ArithmeticSemiterm Nat 6) 4
          compactBinaryNatStatusValidBoundedSourceTerminal := by
  have hstatusTerms :
      (fun index : Fin 5 =>
        (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10)
          (![(#4 : ArithmeticSemiterm Empty 10), #5, #6, #7, #8]
            index)) =
        ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #7, #8] := by
    funext index
    fin_cases index <;> simp
  have hprefixTerms :
      (fun index : Fin 5 =>
        (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10)
          (![(#4 : ArithmeticSemiterm Empty 10), #5, #6, #7, #3]
            index)) =
        ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #7, #3] := by
    funext index
    fin_cases index <;> simp
  have hlayoutTerms :
      (fun index : Fin 7 =>
        (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10)
          (![(#4 : ArithmeticSemiterm Empty 10), #5, #6, #3, #0, #8, #2]
            index)) =
        ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #3, #0, #8, #2] := by
    funext index
    fin_cases index <;> simp
  have hunitTerms :
      (fun index : Fin 3 =>
        (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10)
          (![(#6 : ArithmeticSemiterm Empty 10), #0, #2] index)) =
        ![(#6 : ArithmeticSemiterm Nat 10), #0, #2] := by
    funext index
    fin_cases index <;> simp
  have hsizeTerms :
      (fun index : Fin 2 =>
        (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10)
          (![(#1 : ArithmeticSemiterm Empty 10), #2] index)) =
        ![(#1 : ArithmeticSemiterm Nat 10), #2] := by
    funext index
    fin_cases index <;> simp
  unfold compactBinaryNatStatusValidBoundedDef
  simp [sourceBoundedWitnessFormula,
    compactBinaryNatStatusValidBoundedSourceTerminal,
    embedding_substitutedFormula,
    sourceSubstitutionLift, hstatusTerms, hprefixTerms, hlayoutTerms,
    hunitTerms, hsizeTerms]

set_option maxRecDepth 4096 in
private theorem compactBinaryNatStatusValidBoundedSourceTerminal_rewriting
    (tokenTable width tokenCount start finish valueBound : Nat) :
    sourceSubstitutionQpow
        (compactBinaryNatStatusValidBoundedSourceTerms
          tokenTable width tokenCount start finish valueBound) 4 ▹
      compactBinaryNatStatusValidBoundedSourceTerminal =
    compactBinaryNatStatusValidBoundedRawTerminal
      tokenTable width tokenCount start finish := by
  let lifted := sourceSubstitutionQpow
    (compactBinaryNatStatusValidBoundedSourceTerms
      tokenTable width tokenCount start finish valueBound) 4
  have hstatusTerms :
      lifted ∘
          ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #7, #8] =
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4 (shortBinaryNumeralTerm start),
          closedShift 4 (shortBinaryNumeralTerm finish)] := by
    funext index
    fin_cases index <;> simp [Function.comp_apply]
    all_goals
      dsimp [lifted]
      rw [sourceSubstitutionQpow_bvar]
      simp [sourceSubstitutionNormalizedBVarResult,
        compactBinaryNatStatusValidBoundedSourceTerms,
        sourceSubstitutionLift, closedShift]
  have hprefixTerms :
      lifted ∘
          ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #7, #3] =
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4 (shortBinaryNumeralTerm start),
          (#3 : ArithmeticSemiterm Nat 4)] := by
    funext index
    fin_cases index <;> simp [Function.comp_apply]
    all_goals
      dsimp [lifted]
      rw [sourceSubstitutionQpow_bvar]
      simp [sourceSubstitutionNormalizedBVarResult,
        compactBinaryNatStatusValidBoundedSourceTerms,
        sourceSubstitutionLift, closedShift]
  have hlayoutTerms :
      lifted ∘
          ![(#4 : ArithmeticSemiterm Nat 10), #5, #6, #3, #0, #8, #2] =
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          (#3 : ArithmeticSemiterm Nat 4),
          (#0 : ArithmeticSemiterm Nat 4),
          closedShift 4 (shortBinaryNumeralTerm finish),
          (#2 : ArithmeticSemiterm Nat 4)] := by
    funext index
    fin_cases index <;> simp [Function.comp_apply]
    all_goals
      dsimp [lifted]
      rw [sourceSubstitutionQpow_bvar]
      simp [sourceSubstitutionNormalizedBVarResult,
        compactBinaryNatStatusValidBoundedSourceTerms,
        sourceSubstitutionLift, closedShift]
  have hunitTerms :
      lifted ∘ ![(#6 : ArithmeticSemiterm Nat 10), #0, #2] =
        ![closedShift 4 (shortBinaryNumeralTerm tokenCount),
          (#0 : ArithmeticSemiterm Nat 4),
          (#2 : ArithmeticSemiterm Nat 4)] := by
    funext index
    fin_cases index <;> simp [Function.comp_apply]
    all_goals
      dsimp [lifted]
      rw [sourceSubstitutionQpow_bvar]
      simp [sourceSubstitutionNormalizedBVarResult,
        compactBinaryNatStatusValidBoundedSourceTerms,
        sourceSubstitutionLift, closedShift]
  have hsizeTerms :
      lifted ∘ ![(#1 : ArithmeticSemiterm Nat 10), #2] =
        ![(#1 : ArithmeticSemiterm Nat 4), #2] := by
    funext index
    fin_cases index <;> simp [Function.comp_apply]
    all_goals
      dsimp [lifted]
      rw [sourceSubstitutionQpow_bvar]
      simp [sourceSubstitutionNormalizedBVarResult]
  have hlifted0 :
      lifted (#0 : ArithmeticSemiterm Nat 10) =
        (#0 : ArithmeticSemiterm Nat 4) := by
    dsimp [lifted]
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]
  have hlifted1 :
      lifted (#1 : ArithmeticSemiterm Nat 10) =
        (#1 : ArithmeticSemiterm Nat 4) := by
    dsimp [lifted]
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]
  have hlifted6 :
      lifted (#6 : ArithmeticSemiterm Nat 10) =
        closedShift 4 (shortBinaryNumeralTerm tokenCount) := by
    dsimp [lifted]
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult,
      compactBinaryNatStatusValidBoundedSourceTerms,
      sourceSubstitutionLift, closedShift]
  unfold compactBinaryNatStatusValidBoundedSourceTerminal
  unfold compactBinaryNatStatusValidBoundedRawTerminal
  change lifted ▹ _ = _
  simp [rewriting_embeddedFormulaSubstitution, hstatusTerms, hprefixTerms,
    hlayoutTerms, hunitTerms, hsizeTerms, hlifted0, hlifted1, hlifted6]

private theorem sourceBoundedWitnessFormula_four_eq_explicit
    (bound : ValuationTerm)
    (body : ArithmeticSemiformula Nat 4) :
    sourceBoundedWitnessFormula bound 4 body =
      explicitBoundedWitnessFormula bound 4 body := by
  rfl

set_option maxRecDepth 4096 in
theorem compactBinaryNatStatusValidBoundedClosedFormula_alignment
    (tokenTable width tokenCount start finish valueBound : Nat) :
    compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 4
        (compactBinaryNatStatusValidBoundedRawTerminal
          tokenTable width tokenCount start finish) := by
  unfold compactBinaryNatStatusValidBoundedClosedFormula
  rw [compactBinaryNatStatusValidBoundedDef_emb_eq_sourceBody]
  change Rew.subst
      (compactBinaryNatStatusValidBoundedSourceTerms
        tokenTable width tokenCount start finish valueBound) ▹
      sourceBoundedWitnessFormula
        (#5 : ArithmeticSemiterm Nat 6) 4
          compactBinaryNatStatusValidBoundedSourceTerminal = _
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactBinaryNatStatusValidBoundedSourceTerminal_rewriting]
  change sourceBoundedWitnessFormula
      (shortBinaryNumeralTerm valueBound) 4
        (compactBinaryNatStatusValidBoundedRawTerminal
          tokenTable width tokenCount start finish) = _
  exact sourceBoundedWitnessFormula_four_eq_explicit
    (shortBinaryNumeralTerm valueBound)
    (compactBinaryNatStatusValidBoundedRawTerminal
      tokenTable width tokenCount start finish)

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality : HybridCertificate
        (LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![leftTerm, rightTerm]) :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.LT.lt
          ![leftTerm, rightTerm]) equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict : HybridCertificate
        (LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![leftTerm, rightTerm]) :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![leftTerm, rightTerm]) strict)

noncomputable def completedAreaCertificate
    (tokenCount outputCount outputBoundarySize : Nat)
    (hbound : outputBoundarySize ≤ (outputCount + 1) * tokenCount) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
        (!!(shortBinaryNumeralTerm outputCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  exact valuationLeCertificate
    (shortBinaryNumeralTerm outputBoundarySize) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne] using hbound)

/-- The five checked leaves of the completed-status branch. -/
noncomputable def compactBinaryNatCompletedStatusExplicitHybridCertificate
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf
          outputStart outputBoundary outputBoundarySize outputCount)) :
    HybridCertificate
      (compactBinaryNatCompletedStatusPrefixClosedFormula
          tokenTable width tokenCount start outputStart ⋏
        (compactAdditiveStructuredListLayoutClosedFormula
            tokenTable width tokenCount outputStart outputCount finish
              outputBoundary ⋏
          (compactAdditiveUnitBoundaryRowsClosedFormula
              tokenCount outputCount outputBoundary ⋏
            (compactNatSizeClosedFormula
                outputBoundarySize outputBoundary ⋏
              “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
                (!!(shortBinaryNumeralTerm outputCount) + 1) *
                  !!(shortBinaryNumeralTerm tokenCount)”)))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hcompleted.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
        tokenTable width tokenCount outputStart outputCount finish
          outputBoundary hcompleted.2.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
          tokenCount outputCount outputBoundary hcompleted.2.2.1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactNatSizeExplicitHybridCertificateOfEq
            outputBoundarySize outputBoundary hcompleted.2.2.2.1)
          (completedAreaCertificate tokenCount outputCount
            outputBoundarySize hcompleted.2.2.2.2))))

private theorem compactBinaryNatStatusValidBoundedRawTerminal_alignment
    (tokenTable width tokenCount start finish
      outputStart outputBoundary outputBoundarySize outputCount : Nat) :
    compactBinaryNatStatusValidBoundedRawTerminal
        tokenTable width tokenCount start finish ⇜
      ![shortBinaryNumeralTerm outputCount,
        shortBinaryNumeralTerm outputBoundarySize,
        shortBinaryNumeralTerm outputBoundary,
        shortBinaryNumeralTerm outputStart] =
      (compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount start finish ⋎
        (compactBinaryNatFailedStatusSliceClosedFormula
            tokenTable width tokenCount start finish ⋎
          (compactBinaryNatCompletedStatusPrefixClosedFormula
              tokenTable width tokenCount start outputStart ⋏
            (compactAdditiveStructuredListLayoutClosedFormula
                tokenTable width tokenCount outputStart outputCount finish
                  outputBoundary ⋏
              (compactAdditiveUnitBoundaryRowsClosedFormula
                  tokenCount outputCount outputBoundary ⋏
                (compactNatSizeClosedFormula
                    outputBoundarySize outputBoundary ⋏
                  “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm outputCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”)))))) := by
  unfold compactBinaryNatStatusValidBoundedRawTerminal
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactBinaryNatFailedStatusSliceClosedFormula
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactAdditiveUnitBoundaryRowsClosedFormula
  unfold compactNatSizeClosedFormula
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

structure CompactBinaryNatStatusValidBoundedData
    (tokenTable width tokenCount start finish valueBound : Nat) where
  outputStart : Nat
  outputStart_le_valueBound : outputStart <= valueBound
  outputBoundary : Nat
  outputBoundary_le_valueBound : outputBoundary <= valueBound
  outputBoundarySize : Nat
  outputBoundarySize_le_valueBound : outputBoundarySize <= valueBound
  outputCount : Nat
  outputCount_le_valueBound : outputCount <= valueBound
  rows : CompactBinaryNatStatusValidRows tokenTable width tokenCount
    start finish (compactBinaryNatStatusValidityWitnessOf outputStart
      outputBoundary outputBoundarySize outputCount)

noncomputable def compactBinaryNatStatusValidBoundedDataOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound := by
  let outputStart := Classical.choose hgraph
  have houtputStart := Classical.choose_spec hgraph
  let outputBoundary := Classical.choose houtputStart.2
  have houtputBoundary := Classical.choose_spec houtputStart.2
  let outputBoundarySize := Classical.choose houtputBoundary.2
  have houtputBoundarySize := Classical.choose_spec houtputBoundary.2
  let outputCount := Classical.choose houtputBoundarySize.2
  have houtputCount := Classical.choose_spec houtputBoundarySize.2
  exact
    { outputStart := outputStart
      outputStart_le_valueBound := houtputStart.1
      outputBoundary := outputBoundary
      outputBoundary_le_valueBound := houtputBoundary.1
      outputBoundarySize := outputBoundarySize
      outputBoundarySize_le_valueBound := houtputBoundarySize.1
      outputCount := outputCount
      outputCount_le_valueBound := houtputCount.1
      rows := houtputCount.2 }

def compactBinaryNatStatusValidBoundedValues
    {tokenTable width tokenCount start finish valueBound : Nat}
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) : Fin 4 -> Nat :=
  ![data.outputCount, data.outputBoundarySize,
    data.outputBoundary, data.outputStart]

theorem compactBinaryNatStatusValidBoundedValues_le
    {tokenTable width tokenCount start finish valueBound : Nat}
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound)
    (index : Fin 4) :
    compactBinaryNatStatusValidBoundedValues data index <= valueBound := by
  fin_cases index
  · exact data.outputCount_le_valueBound
  · exact data.outputBoundarySize_le_valueBound
  · exact data.outputBoundary_le_valueBound
  · exact data.outputStart_le_valueBound

theorem compactBinaryNatCompletedStatusValidRows_of_data
    {tokenTable width tokenCount start finish valueBound : Nat}
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound)
    (hrunning : ¬ CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish)
    (hfailed : ¬ CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish) :
    CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf data.outputStart
          data.outputBoundary data.outputBoundarySize data.outputCount) := by
  rcases data.rows with hrun | hfail | hdone
  · exact False.elim (hrunning hrun)
  · exact False.elim (hfailed hfail)
  · exact hdone

noncomputable def compactBinaryNatStatusValidBoundedTerminalPartsOfData
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    HybridCertificate
      (compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount start finish ⋎
        (compactBinaryNatFailedStatusSliceClosedFormula
            tokenTable width tokenCount start finish ⋎
          (compactBinaryNatCompletedStatusPrefixClosedFormula
              tokenTable width tokenCount start data.outputStart ⋏
            (compactAdditiveStructuredListLayoutClosedFormula
                tokenTable width tokenCount data.outputStart data.outputCount
                  finish data.outputBoundary ⋏
              (compactAdditiveUnitBoundaryRowsClosedFormula
                  tokenCount data.outputCount data.outputBoundary ⋏
                (compactNatSizeClosedFormula
                    data.outputBoundarySize data.outputBoundary ⋏
                  “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”)))))) := by
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right :=
        compactBinaryNatFailedStatusSliceClosedFormula
            tokenTable width tokenCount start finish ⋎
          (compactBinaryNatCompletedStatusPrefixClosedFormula
              tokenTable width tokenCount start data.outputStart ⋏
            (compactAdditiveStructuredListLayoutClosedFormula
                tokenTable width tokenCount data.outputStart data.outputCount
                  finish data.outputBoundary ⋏
              (compactAdditiveUnitBoundaryRowsClosedFormula
                  tokenCount data.outputCount data.outputBoundary ⋏
                (compactNatSizeClosedFormula
                    data.outputBoundarySize data.outputBoundary ⋏
                  “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”)))))
      (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount start finish hrunning)
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount start finish)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            compactBinaryNatCompletedStatusPrefixClosedFormula
                tokenTable width tokenCount start data.outputStart ⋏
              (compactAdditiveStructuredListLayoutClosedFormula
                  tokenTable width tokenCount data.outputStart data.outputCount
                    finish data.outputBoundary ⋏
                (compactAdditiveUnitBoundaryRowsClosedFormula
                    tokenCount data.outputCount data.outputBoundary ⋏
                  (compactNatSizeClosedFormula
                      data.outputBoundarySize data.outputBoundary ⋏
                    “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
                      (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                        !!(shortBinaryNumeralTerm tokenCount)”))))
          (compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
            tokenTable width tokenCount start finish hfailed))
    · let hcompleted := compactBinaryNatCompletedStatusValidRows_of_data
        data hrunning hfailed
      let completed :=
        compactBinaryNatCompletedStatusExplicitHybridCertificate
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize data.outputCount
              hcompleted
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount start finish)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := compactBinaryNatFailedStatusSliceClosedFormula
            tokenTable width tokenCount start finish)
          completed)

noncomputable def compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    ExplicitBoundedWitnessHybridTerminal zeroValuation valueBound
      (compactBinaryNatStatusValidBoundedRawTerminal
        tokenTable width tokenCount start finish) := by
  let values := compactBinaryNatStatusValidBoundedValues data
  let terminalParts := compactBinaryNatStatusValidBoundedTerminalPartsOfData
    tokenTable width tokenCount start finish valueBound data
  have hterminalFormula :
      (compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount start finish ⋎
        (compactBinaryNatFailedStatusSliceClosedFormula
            tokenTable width tokenCount start finish ⋎
          (compactBinaryNatCompletedStatusPrefixClosedFormula
              tokenTable width tokenCount start data.outputStart ⋏
            (compactAdditiveStructuredListLayoutClosedFormula
                tokenTable width tokenCount data.outputStart data.outputCount
                  finish data.outputBoundary ⋏
              (compactAdditiveUnitBoundaryRowsClosedFormula
                  tokenCount data.outputCount data.outputBoundary ⋏
                (compactNatSizeClosedFormula
                    data.outputBoundarySize data.outputBoundary ⋏
                  “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”)))))) =
        (compactBinaryNatStatusValidBoundedRawTerminal
            tokenTable width tokenCount start finish ⇜
          fun index => shortBinaryNumeralTerm (values index)) := by
    have hvalueTerms :
        (fun index : Fin 4 => shortBinaryNumeralTerm (values index)) =
          ![shortBinaryNumeralTerm data.outputCount,
            shortBinaryNumeralTerm data.outputBoundarySize,
            shortBinaryNumeralTerm data.outputBoundary,
            shortBinaryNumeralTerm data.outputStart] := by
      funext index
      fin_cases index <;> rfl
    rw [hvalueTerms]
    exact
      (compactBinaryNatStatusValidBoundedRawTerminal_alignment
        tokenTable width tokenCount start finish data.outputStart
          data.outputBoundary data.outputBoundarySize data.outputCount).symm
  let terminal : HybridCertificate
      (compactBinaryNatStatusValidBoundedRawTerminal
          tokenTable width tokenCount start finish ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast hterminalFormula terminalParts
  exact
    { values := values
      values_le := compactBinaryNatStatusValidBoundedValues_le data
      terminal := terminal }

noncomputable def compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    ExplicitBoundedWitnessHybridTerminal zeroValuation valueBound
      (compactBinaryNatStatusValidBoundedRawTerminal
        tokenTable width tokenCount start finish) :=
  compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData
    tokenTable width tokenCount start finish valueBound
    (compactBinaryNatStatusValidBoundedDataOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    HybridCertificate
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound) := by
  let data := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  let raw := buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactBinaryNatStatusValidBoundedRawTerminal
      tokenTable width tokenCount start finish)
    data.values data.values_le data.terminal
  exact .cast
    (compactBinaryNatStatusValidBoundedClosedFormula_alignment
      tokenTable width tokenCount start finish valueBound).symm raw

noncomputable def compactBinaryNatStatusValidBoundedDirectPayloadEnvelopeOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  let data := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  explicitBoundedWitnessDirectPayloadEnvelope zeroValuation valueBound
    (compactBinaryNatStatusValidBoundedRawTerminal
      tokenTable width tokenCount start finish)
    data.values (hybridFormulaStructuralPayloadBound data.terminal)

noncomputable def compileCompactBinaryNatStatusValidBoundedDirectOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount start finish valueBound).freeVariables
        zeroValuation)
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound) := by
  let data := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  let rawBody := compactBinaryNatStatusValidBoundedRawTerminal
    tokenTable width tokenCount start finish
  let terminalResource := hybridFormulaStructuralPayloadBound data.terminal
  let rawProof := compileExplicitBoundedWitnessDirectArity4
    valueBound rawBody data.values data.values_le terminalResource
      data.terminal.compile
      (compile_payloadLength_le_structuralPayloadBound data.terminal)
  have hformula :
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 4
          rawBody =
        compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount start finish valueBound :=
    (compactBinaryNatStatusValidBoundedClosedFormula_alignment
      tokenTable width tokenCount start finish valueBound).symm
  exact castValuationContextProof hformula rawProof

theorem compileCompactBinaryNatStatusValidBoundedDirectOfGraph_payloadLength_le
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedDirectOfGraph
      tokenTable width tokenCount start finish valueBound hgraph).payloadLength ≤
      compactBinaryNatStatusValidBoundedDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let data := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  let rawBody := compactBinaryNatStatusValidBoundedRawTerminal
    tokenTable width tokenCount start finish
  let terminalResource := hybridFormulaStructuralPayloadBound data.terminal
  let rawProof := compileExplicitBoundedWitnessDirectArity4
    valueBound rawBody data.values data.values_le terminalResource
      data.terminal.compile
      (compile_payloadLength_le_structuralPayloadBound data.terminal)
  have hformula :
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 4
          rawBody =
        compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount start finish valueBound :=
    (compactBinaryNatStatusValidBoundedClosedFormula_alignment
      tokenTable width tokenCount start finish valueBound).symm
  change (castValuationContextProof hformula rawProof).payloadLength ≤ _
  rw [castValuationContextProof_payloadLength_eq]
  change rawProof.payloadLength ≤
    explicitBoundedWitnessDirectPayloadEnvelope zeroValuation valueBound
      rawBody data.values terminalResource
  exact compileExplicitBoundedWitnessDirectArity4_payloadLength_le
    valueBound rawBody data.values data.values_le terminalResource
      data.terminal.compile
      (compile_payloadLength_le_structuralPayloadBound data.terminal)

noncomputable def compileCompactBinaryNatStatusValidBoundedDirectAtValuationOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount start finish valueBound).freeVariables
        valuation)
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound) := by
  let raw := compileCompactBinaryNatStatusValidBoundedDirectOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          zeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

theorem
    compileCompactBinaryNatStatusValidBoundedDirectAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedDirectAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
        hgraph).payloadLength ≤
      compactBinaryNatStatusValidBoundedDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let raw := compileCompactBinaryNatStatusValidBoundedDirectOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          zeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  change (CertifiedPAContextProof.castContext hcontext raw).payloadLength ≤ _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact compileCompactBinaryNatStatusValidBoundedDirectOfGraph_payloadLength_le
    tokenTable width tokenCount start finish valueBound hgraph

noncomputable def compileCompactBinaryNatStatusValidBoundedExplicitHybridContext
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount start finish valueBound).freeVariables
        zeroValuation)
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound) :=
  (compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount start finish valueBound hgraph).compile

noncomputable def compactBinaryNatStatusValidBoundedExplicitStructuralResource
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

theorem compileCompactBinaryNatStatusValidBoundedExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedExplicitHybridContext
      tokenTable width tokenCount start finish valueBound hgraph).payloadLength ≤
      compactBinaryNatStatusValidBoundedExplicitStructuralResource
        tokenTable width tokenCount start finish valueBound hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

#print axioms compactBinaryNatStatusValidBoundedClosedFormula_alignment
#print axioms compactBinaryNatCompletedStatusExplicitHybridCertificate
#print axioms
  compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
#print axioms compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
#print axioms compileCompactBinaryNatStatusValidBoundedDirectOfGraph
#print axioms
  compileCompactBinaryNatStatusValidBoundedDirectOfGraph_payloadLength_le
#print axioms
  compileCompactBinaryNatStatusValidBoundedDirectAtValuationOfGraph
#print axioms
  compileCompactBinaryNatStatusValidBoundedDirectAtValuationOfGraph_payloadLength_le
#print axioms
  compileCompactBinaryNatStatusValidBoundedExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
