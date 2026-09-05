import integration.FoundationCompactNumericListedDirectBinaryNatDefaultStatusValidity
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler

/-!
# Direct syntax for the positive default-status formula

This module exposes the exact four-witness terminal and proves that the
closed source formula is the three-way disjunction used by the direct PA
compiler.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectBinaryNatDefaultStatusDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatDefaultStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

def compactBinaryNatDefaultStatusValidBoundedClosedFormula
    (tokenTable width tokenCount start finish valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactBinaryNatDefaultStatusValidBoundedDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm valueBound]

theorem compactBinaryNatDefaultStatusValidBoundedClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start finish valueBound : Nat) :
    (compactBinaryNatDefaultStatusValidBoundedClosedFormula tokenTable width
      tokenCount start finish valueBound).freeVariables = ∅ := by
  unfold compactBinaryNatDefaultStatusValidBoundedClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

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

def compactBinaryNatDefaultStatusSourceTerms
    (tokenTable width tokenCount start finish valueBound : Nat) :
    Fin 6 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm start,
    shortBinaryNumeralTerm finish,
    shortBinaryNumeralTerm valueBound]

def compactBinaryNatDefaultCompletedSourceTerminal :
    ArithmeticSemiformula Nat 10 :=
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
          “#1 ≤ (#0 + 1) * #6”)))) ⋏
    “0 < #0”

def compactBinaryNatDefaultStatusSourceFormula :
    ArithmeticSemiformula Nat 6 :=
  ((Rewriting.emb (ξ := Nat) compactBinaryNatRunningStatusSliceDef.val) ⇜
      ![(#0 : ArithmeticSemiterm Nat 6), #1, #2, #3, #4]) ⋎
    (((Rewriting.emb (ξ := Nat) compactBinaryNatFailedStatusSliceDef.val) ⇜
        ![(#0 : ArithmeticSemiterm Nat 6), #1, #2, #3, #4]) ⋎
      sourceBoundedWitnessFormula (#5 : ArithmeticSemiterm Nat 6) 4
        compactBinaryNatDefaultCompletedSourceTerminal)

private theorem compactBinaryNatDefaultStatusDef_emb_eq_sourceFormula :
    Rewriting.emb (ξ := Nat)
        compactBinaryNatDefaultStatusValidBoundedDef.val =
      compactBinaryNatDefaultStatusSourceFormula := by
  have hstatusTerms :
      (fun index : Fin 5 =>
        (Rew.emb : Rew ℒₒᵣ Empty 6 Nat 6)
          (![(#0 : ArithmeticSemiterm Empty 6), #1, #2, #3, #4]
            index)) =
        ![(#0 : ArithmeticSemiterm Nat 6), #1, #2, #3, #4] := by
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
  unfold compactBinaryNatDefaultStatusValidBoundedDef
  simp [compactBinaryNatDefaultStatusSourceFormula,
    sourceBoundedWitnessFormula,
    compactBinaryNatDefaultCompletedSourceTerminal,
    sourceSubstitutionLift,
    hstatusTerms, hprefixTerms, hlayoutTerms, hunitTerms, hsizeTerms]

def compactBinaryNatDefaultCompletedRawTerminal
    (tokenTable width tokenCount start finish : Nat) :
    ArithmeticSemiformula Nat 4 :=
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
            !!(closedShift 4 (shortBinaryNumeralTerm tokenCount))”)))) ⋏
    “0 < #0”

private theorem compactBinaryNatDefaultCompletedSourceTerminal_rewriting
    (tokenTable width tokenCount start finish valueBound : Nat) :
    sourceSubstitutionQpow
        (compactBinaryNatDefaultStatusSourceTerms tokenTable width tokenCount
          start finish valueBound) 4 ▹
      compactBinaryNatDefaultCompletedSourceTerminal =
    compactBinaryNatDefaultCompletedRawTerminal
      tokenTable width tokenCount start finish := by
  let lifted := sourceSubstitutionQpow
    (compactBinaryNatDefaultStatusSourceTerms tokenTable width tokenCount start
      finish valueBound) 4
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
        compactBinaryNatDefaultStatusSourceTerms,
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
        compactBinaryNatDefaultStatusSourceTerms,
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
        compactBinaryNatDefaultStatusSourceTerms,
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
  have hlifted0 : lifted (#0 : ArithmeticSemiterm Nat 10) =
      (#0 : ArithmeticSemiterm Nat 4) := by
    dsimp [lifted]
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]
  have hlifted1 : lifted (#1 : ArithmeticSemiterm Nat 10) =
      (#1 : ArithmeticSemiterm Nat 4) := by
    dsimp [lifted]
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]
  have hlifted6 : lifted (#6 : ArithmeticSemiterm Nat 10) =
      closedShift 4 (shortBinaryNumeralTerm tokenCount) := by
    dsimp [lifted]
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult,
      compactBinaryNatDefaultStatusSourceTerms,
      sourceSubstitutionLift, closedShift]
  unfold compactBinaryNatDefaultCompletedSourceTerminal
  unfold compactBinaryNatDefaultCompletedRawTerminal
  change lifted ▹ _ = _
  simp [rewriting_embeddedFormulaSubstitution, hprefixTerms, hlayoutTerms,
    hunitTerms, hsizeTerms, hlifted0, hlifted1, hlifted6]

def compactBinaryNatDefaultCompletedBoundedClosedFormula
    (tokenTable width tokenCount start finish valueBound : Nat) :
    ValuationFormula :=
  explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 4
    (compactBinaryNatDefaultCompletedRawTerminal tokenTable width tokenCount
      start finish)

def compactBinaryNatDefaultStatusDecomposedClosedFormula
    (tokenTable width tokenCount start finish valueBound : Nat) :
    ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      start finish ⋎
    (compactBinaryNatFailedStatusSliceClosedFormula tokenTable width tokenCount
        start finish ⋎
      compactBinaryNatDefaultCompletedBoundedClosedFormula tokenTable width
        tokenCount start finish valueBound)

theorem compactBinaryNatDefaultStatusValidBoundedClosedFormula_alignment
    (tokenTable width tokenCount start finish valueBound : Nat) :
    compactBinaryNatDefaultStatusValidBoundedClosedFormula tokenTable width
        tokenCount start finish valueBound =
      compactBinaryNatDefaultStatusDecomposedClosedFormula tokenTable width
        tokenCount start finish valueBound := by
  unfold compactBinaryNatDefaultStatusValidBoundedClosedFormula
  rw [compactBinaryNatDefaultStatusDef_emb_eq_sourceFormula]
  change Rew.subst
      (compactBinaryNatDefaultStatusSourceTerms tokenTable width tokenCount
        start finish valueBound) ▹
      compactBinaryNatDefaultStatusSourceFormula = _
  unfold compactBinaryNatDefaultStatusSourceFormula
  change
    (Rew.subst
        (compactBinaryNatDefaultStatusSourceTerms tokenTable width tokenCount
          start finish valueBound) ▹
      ((Rewriting.emb (ξ := Nat)
          compactBinaryNatRunningStatusSliceDef.val) ⇜
        ![(#0 : ArithmeticSemiterm Nat 6), #1, #2, #3, #4])) ⋎
      ((Rew.subst
          (compactBinaryNatDefaultStatusSourceTerms tokenTable width tokenCount
            start finish valueBound) ▹
        ((Rewriting.emb (ξ := Nat)
            compactBinaryNatFailedStatusSliceDef.val) ⇜
          ![(#0 : ArithmeticSemiterm Nat 6), #1, #2, #3, #4])) ⋎
        (Rew.subst
          (compactBinaryNatDefaultStatusSourceTerms tokenTable width tokenCount
            start finish valueBound) ▹
          sourceBoundedWitnessFormula (#5 : ArithmeticSemiterm Nat 6) 4
            compactBinaryNatDefaultCompletedSourceTerminal)) = _
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactBinaryNatDefaultCompletedSourceTerminal_rewriting]
  unfold compactBinaryNatDefaultStatusDecomposedClosedFormula
  unfold compactBinaryNatDefaultCompletedBoundedClosedFormula
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  unfold compactBinaryNatFailedStatusSliceClosedFormula
  have hstatusTerms :
      (⇑(Rew.subst
          (compactBinaryNatDefaultStatusSourceTerms tokenTable width tokenCount
            start finish valueBound)) ∘
        ![(#0 : ArithmeticSemiterm Nat 6), #1, #2, #3, #4]) =
      ![shortBinaryNumeralTerm tokenTable,
        shortBinaryNumeralTerm width,
        shortBinaryNumeralTerm tokenCount,
        shortBinaryNumeralTerm start,
        shortBinaryNumeralTerm finish] := by
    funext index
    fin_cases index <;>
      simp [compactBinaryNatDefaultStatusSourceTerms, Rew.subst_bvar]
  have hbounded :
      sourceBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 4
          (compactBinaryNatDefaultCompletedRawTerminal tokenTable width
            tokenCount start finish) =
        explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 4
          (compactBinaryNatDefaultCompletedRawTerminal tokenTable width
            tokenCount start finish) := by
    rfl
  simp [rewriting_embeddedFormulaSubstitution, hstatusTerms]
  simpa [compactBinaryNatDefaultStatusSourceTerms] using hbounded

def compactBinaryNatDefaultCompletedClosedFormula
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : ValuationFormula :=
  compactBinaryNatCompletedStatusUniformDirectFormula tokenTable width
      tokenCount start finish outputStart outputBoundary outputBoundarySize
      outputCount ⋏
    “0 < !!(shortBinaryNumeralTerm outputCount)”

theorem compactBinaryNatDefaultCompletedRawTerminal_alignment
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) :
    compactBinaryNatDefaultCompletedRawTerminal tokenTable width tokenCount
        start finish ⇜
      ![shortBinaryNumeralTerm outputCount,
        shortBinaryNumeralTerm outputBoundarySize,
        shortBinaryNumeralTerm outputBoundary,
        shortBinaryNumeralTerm outputStart] =
      compactBinaryNatDefaultCompletedClosedFormula tokenTable width tokenCount
        start finish outputStart outputBoundary outputBoundarySize
        outputCount := by
  unfold compactBinaryNatDefaultCompletedRawTerminal
  unfold compactBinaryNatDefaultCompletedClosedFormula
  unfold compactBinaryNatCompletedStatusUniformDirectFormula
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsClosedFormula
  unfold compactNatSizeClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    first
    | simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    | apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate

#print axioms
  compactBinaryNatDefaultStatusValidBoundedClosedFormula_alignment
#print axioms compactBinaryNatDefaultCompletedRawTerminal_alignment

end FoundationCompactNumericListedDirectBinaryNatDefaultStatusDirectSyntax
