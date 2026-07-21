import integration.FoundationCompactNumericListedDirectChildResultBoundedRowsEquality
import integration.FoundationCompactNumericListedDirectChildResultRowEqGraphExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectChildResultBoundedHeadEqExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-!
# Explicit hybrid certificate for bounded child-result row equality

The fourteen bounded parser coordinates are installed explicitly.  The
terminal certificate checks the four selected boundary-table entries and then
uses the public closed certificate for the complete child-result row graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectChildResultBoundedRowsEqExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectChildResultBoundedRowsEquality
open FoundationCompactNumericListedDirectChildResultRowEquality
open FoundationCompactNumericListedDirectChildResultRowEqGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables

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
      (Rewriting.app right :
        ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
          ArithmeticSemiformula targetVariables targetArity) := by
  cases h
  rfl

private theorem emb_comp_subst_eq_subst_comp_emb
    {predicateArity targetArity : Nat}
    (sourceTerms : Fin predicateArity ->
      ArithmeticSemiterm Empty targetArity)
    (targetTerms : Fin predicateArity ->
      ArithmeticSemiterm Nat targetArity)
    (hterms : ∀ coordinate,
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
    rfl

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

private def sourceSubstitutionQpow
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity) :
    (depth : Nat) ->
      Rew ℒₒᵣ Nat (sourceArity + depth) Nat (targetArity + depth)
  | 0 => Rew.subst terms
  | depth + 1 => (sourceSubstitutionQpow terms depth).q

private def sourceSubstitutionLift
    {targetArity : Nat} :
    (depth : Nat) -> ArithmeticSemiterm Nat targetArity ->
      ArithmeticSemiterm Nat (targetArity + depth)
  | 0, term => term
  | depth + 1, term => Rew.bShift (sourceSubstitutionLift depth term)

private def sourceSubstitutionNormalizedBVarResult
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (depth : Nat) (index : Fin (sourceArity + depth)) :
    ArithmeticSemiterm Nat (targetArity + depth) :=
  if hlocal : index.val < depth then
    (#(⟨index.val, by omega⟩ : Fin (targetArity + depth)) :
      ArithmeticSemiterm Nat (targetArity + depth))
  else
    sourceSubstitutionLift depth
      (terms ⟨index.val - depth, by omega⟩)

private theorem sourceSubstitutionNormalizedBVarResult_eq
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity) :
    ∀ (depth : Nat) (index : Fin (sourceArity + depth)),
      sourceSubstitutionNormalizedBVarResult terms depth index =
        sourceSubstitutionQpow terms depth
          (#index : ArithmeticSemiterm Nat (sourceArity + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      simp [sourceSubstitutionNormalizedBVarResult,
        sourceSubstitutionQpow, sourceSubstitutionLift,
        Rew.subst_bvar]
  | succ depth inductionHypothesis =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [sourceSubstitutionNormalizedBVarResult,
            sourceSubstitutionQpow]
      | succ index =>
          rw [show
            sourceSubstitutionQpow terms (depth + 1)
                (#index.succ : ArithmeticSemiterm Nat
                  (sourceArity + (depth + 1))) =
              Rew.bShift
                (sourceSubstitutionQpow terms depth
                  (#index : ArithmeticSemiterm Nat
                    (sourceArity + depth))) by
            change (sourceSubstitutionQpow terms depth).q
                (#index.succ) = _
            rw [Rew.q_bvar_succ]]
          rw [← inductionHypothesis index]
          by_cases hlocal : index.val < depth
          · have hlocalSucc : index.val + 1 < depth + 1 := by omega
            simp [sourceSubstitutionNormalizedBVarResult,
              hlocal, hlocalSucc]
          · have hlocalSucc : ¬index.val + 1 < depth + 1 := by omega
            simp [sourceSubstitutionNormalizedBVarResult,
              hlocal, hlocalSucc, sourceSubstitutionLift]

@[simp] private theorem sourceSubstitutionQpow_bvar
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (depth : Nat) (index : Fin (sourceArity + depth)) :
    sourceSubstitutionQpow terms depth
        (#index : ArithmeticSemiterm Nat (sourceArity + depth)) =
      sourceSubstitutionNormalizedBVarResult terms depth index :=
  (sourceSubstitutionNormalizedBVarResult_eq terms depth index).symm

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

@[simp] private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

@[simp] private theorem sourceSubstitutionQpow_bexsLTSucc
    {sourceArity targetArity depth : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (bound : ArithmeticSemiterm Nat (sourceArity + depth))
    (body : ArithmeticSemiformula Nat (sourceArity + (depth + 1))) :
    sourceSubstitutionQpow terms depth ▹ body.bexsLTSucc bound =
      (sourceSubstitutionQpow terms (depth + 1) ▹ body).bexsLTSucc
        (sourceSubstitutionQpow terms depth bound) := by
  simp [sourceSubstitutionQpow]

private theorem substituteClosedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ k inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin k => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (closedShift k term) := by
                simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := inductionHypothesis _

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

/-- The eight public row-equality inputs closed by short binary numerals. -/
def compactNumericChildResultBoundedRowsEqClosedFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedRowsEqDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm sourceIndex,
      shortBinaryNumeralTerm targetIndex]

private def compactNumericChildResultBoundedRowsEqSourceTerms
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndex targetIndex : ValuationTerm) :
    Fin 8 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm sourceBoundary,
    shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm valueBound,
    sourceIndex,
    targetIndex]

private def compactNumericChildResultBoundedRowsEqRawTerminal :
    ArithmeticSemiformula Nat 22 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![(#17 : ArithmeticSemiterm Nat 22), #16, #20, #13]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![(#17 : ArithmeticSemiterm Nat 22), #16, ‘#20 + 1’, #12]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![(#18 : ArithmeticSemiterm Nat 22), #16, #21, #6]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![(#18 : ArithmeticSemiterm Nat 22), #16, ‘#21 + 1’, #5]) ⋏
          ((Rewriting.emb (ξ := Nat)
              compactNumericChildResultRowEqGraphDef.val) ⇜
            ![(#14 : ArithmeticSemiterm Nat 22), #15, #16,
              #13, #12, #11, #10, #9, #8, #7,
              #6, #5, #4, #3, #2, #1, #0]))))

private def compactNumericChildResultBoundedRowsEqRawBody :
    ArithmeticSemiformula Nat 8 :=
  ((((((((((((((compactNumericChildResultBoundedRowsEqRawTerminal.bexsLTSucc
      (#18 : ArithmeticSemiterm Nat 21)).bexsLTSucc
      (#17 : ArithmeticSemiterm Nat 20)).bexsLTSucc
      (#16 : ArithmeticSemiterm Nat 19)).bexsLTSucc
      (#15 : ArithmeticSemiterm Nat 18)).bexsLTSucc
      (#14 : ArithmeticSemiterm Nat 17)).bexsLTSucc
      (#13 : ArithmeticSemiterm Nat 16)).bexsLTSucc
      (#12 : ArithmeticSemiterm Nat 15)).bexsLTSucc
      (#11 : ArithmeticSemiterm Nat 14)).bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 13)).bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#7 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#6 : ArithmeticSemiterm Nat 9)).bexsLTSucc
      (#5 : ArithmeticSemiterm Nat 8))

private theorem compactNumericChildResultBoundedRowsEqDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedRowsEqDef.val =
      compactNumericChildResultBoundedRowsEqRawBody := by
  have hsourceStart :
      (Rew.emb : Rew ℒₒᵣ Empty 22 Nat 22).comp
          (Rew.subst
            ![(#17 : ArithmeticSemiterm Empty 22), #16, #20, #13]) =
        (Rew.subst
          ![(#17 : ArithmeticSemiterm Nat 22), #16, #20, #13]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hsourceFinish :
      (Rew.emb : Rew ℒₒᵣ Empty 22 Nat 22).comp
          (Rew.subst
            ![(#17 : ArithmeticSemiterm Empty 22), #16, ‘#20 + 1’, #12]) =
        (Rew.subst
          ![(#17 : ArithmeticSemiterm Nat 22), #16, ‘#20 + 1’, #12]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have htargetStart :
      (Rew.emb : Rew ℒₒᵣ Empty 22 Nat 22).comp
          (Rew.subst
            ![(#18 : ArithmeticSemiterm Empty 22), #16, #21, #6]) =
        (Rew.subst
          ![(#18 : ArithmeticSemiterm Nat 22), #16, #21, #6]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have htargetFinish :
      (Rew.emb : Rew ℒₒᵣ Empty 22 Nat 22).comp
          (Rew.subst
            ![(#18 : ArithmeticSemiterm Empty 22), #16, ‘#21 + 1’, #5]) =
        (Rew.subst
          ![(#18 : ArithmeticSemiterm Nat 22), #16, ‘#21 + 1’, #5]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hrowEq :
      (Rew.emb : Rew ℒₒᵣ Empty 22 Nat 22).comp
          (Rew.subst
            ![(#14 : ArithmeticSemiterm Empty 22), #15, #16,
              #13, #12, #11, #10, #9, #8, #7,
              #6, #5, #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#14 : ArithmeticSemiterm Nat 22), #15, #16,
            #13, #12, #11, #10, #9, #8, #7,
            #6, #5, #4, #3, #2, #1, #0]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 17 Nat 17) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactNumericChildResultBoundedRowsEqDef
  unfold compactNumericChildResultBoundedRowsEqRawBody
  unfold compactNumericChildResultBoundedRowsEqRawTerminal
  simp [← TransitiveRewriting.comp_app]
  rw [hsourceStart, hsourceFinish, htargetStart, htargetFinish, hrowEq]

@[simp] private theorem compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) (depth : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) depth
        (#(⟨depth + 5, by omega⟩ : Fin (8 + depth)) :
          ArithmeticSemiterm Nat (8 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm valueBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactNumericChildResultBoundedRowsEqSourceTerms]

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound0
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 0
        (#5 : ArithmeticSemiterm Nat 8) =
      closedShift 0 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 0)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound1
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 1
        (#6 : ArithmeticSemiterm Nat 9) =
      closedShift 1 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 1)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound2
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 2
        (#7 : ArithmeticSemiterm Nat 10) =
      closedShift 2 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 2)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound3
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 3
        (#8 : ArithmeticSemiterm Nat 11) =
      closedShift 3 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 3)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound4
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 4
        (#9 : ArithmeticSemiterm Nat 12) =
      closedShift 4 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 4)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound5
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 5
        (#10 : ArithmeticSemiterm Nat 13) =
      closedShift 5 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 5)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound6
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 6
        (#11 : ArithmeticSemiterm Nat 14) =
      closedShift 6 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 6)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound7
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 7
        (#12 : ArithmeticSemiterm Nat 15) =
      closedShift 7 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 7)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound8
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 8
        (#13 : ArithmeticSemiterm Nat 16) =
      closedShift 8 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 8)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound9
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 9
        (#14 : ArithmeticSemiterm Nat 17) =
      closedShift 9 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 9)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound10
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 10
        (#15 : ArithmeticSemiterm Nat 18) =
      closedShift 10 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 10)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound11
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 11
        (#16 : ArithmeticSemiterm Nat 19) =
      closedShift 11 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 11)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound12
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 12
        (#17 : ArithmeticSemiterm Nat 20) =
      closedShift 12 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 12)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow_bound13
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 13
        (#18 : ArithmeticSemiterm Nat 21) =
      closedShift 13 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowsEqSourceQpow_valueBound
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex 13)

private theorem compactNumericChildResultBoundedRowsEqSourceQpow14_bvar
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) (index : Fin 22) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 14
        (#index : ArithmeticSemiterm Nat 22) =
      sourceSubstitutionNormalizedBVarResult
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 14 index := by
  simpa using
    (sourceSubstitutionQpow_bvar
      (compactNumericChildResultBoundedRowsEqSourceTerms
      tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex) 14 index)

private def compactNumericChildResultBoundedRowsEqSourceQpow14Terms
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    Fin 22 -> ArithmeticSemiterm Nat 14 :=
  ![(#0 : ArithmeticSemiterm Nat 14), #1, #2, #3, #4, #5, #6,
    #7, #8, #9, #10, #11, #12, #13,
    closedShift 14 (shortBinaryNumeralTerm tokenTable),
    closedShift 14 (shortBinaryNumeralTerm width),
    closedShift 14 (shortBinaryNumeralTerm tokenCount),
    closedShift 14 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 14 (shortBinaryNumeralTerm targetBoundary),
    closedShift 14 (shortBinaryNumeralTerm valueBound),
    closedShift 14 sourceIndex,
    closedShift 14 targetIndex]

private theorem
    compactNumericChildResultBoundedRowsEqSourceQpow14_bvar_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) (index : Fin 22) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 14
        (#index : ArithmeticSemiterm Nat 22) =
      compactNumericChildResultBoundedRowsEqSourceQpow14Terms
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex index := by
  rw [compactNumericChildResultBoundedRowsEqSourceQpow14_bvar]
  fin_cases index <;>
    simp [sourceSubstitutionNormalizedBVarResult,
      compactNumericChildResultBoundedRowsEqSourceTerms,
      compactNumericChildResultBoundedRowsEqSourceQpow14Terms,
      sourceSubstitutionLift, closedShift]

private theorem
    compactNumericChildResultBoundedRowsEqSourceQpow14_eq_subst
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 14 =
      Rew.subst
        (compactNumericChildResultBoundedRowsEqSourceQpow14Terms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) := by
  apply Rew.ext
  · intro coordinate
    simpa [Rew.subst_bvar] using
      (compactNumericChildResultBoundedRowsEqSourceQpow14_bvar_alignment
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex coordinate)
  · intro coordinate
    rfl

/-- The five checked conjuncts beneath the fourteen bounded witnesses. -/
private def compactNumericChildResultBoundedRowsEqTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    ArithmeticSemiformula Nat 14 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 14 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 14 (shortBinaryNumeralTerm tokenCount),
        closedShift 14 sourceIndex,
        (#13 : ArithmeticSemiterm Nat 14)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 14 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          (‘!!(closedShift 14 sourceIndex) + 1’ :
            ArithmeticSemiterm Nat 14),
          (#12 : ArithmeticSemiterm Nat 14)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 14 (shortBinaryNumeralTerm targetBoundary),
            closedShift 14 (shortBinaryNumeralTerm tokenCount),
            closedShift 14 targetIndex,
            (#6 : ArithmeticSemiterm Nat 14)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 14 (shortBinaryNumeralTerm targetBoundary),
              closedShift 14 (shortBinaryNumeralTerm tokenCount),
              (‘!!(closedShift 14 targetIndex) + 1’ :
                ArithmeticSemiterm Nat 14),
              (#5 : ArithmeticSemiterm Nat 14)]) ⋏
          ((Rewriting.emb (ξ := Nat)
              compactNumericChildResultRowEqGraphDef.val) ⇜
            ![closedShift 14 (shortBinaryNumeralTerm tokenTable),
              closedShift 14 (shortBinaryNumeralTerm width),
              closedShift 14 (shortBinaryNumeralTerm tokenCount),
              (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8,
              #7, #6, #5, #4, #3, #2, #1, #0]))))

private theorem compactNumericChildResultBoundedRowsEqRawTerminal_rewriting
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 14 ▹
      compactNumericChildResultBoundedRowsEqRawTerminal =
    compactNumericChildResultBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndex targetIndex := by
  rw [compactNumericChildResultBoundedRowsEqSourceQpow14_eq_subst]
  unfold compactNumericChildResultBoundedRowsEqRawTerminal
  unfold compactNumericChildResultBoundedRowsEqTerminal
  simp [rewriting_embeddedFormulaSubstitution,
    compactNumericChildResultBoundedRowsEqSourceQpow14Terms,
    Rew.subst_bvar]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Rew.subst_bvar]

private def compactNumericChildResultBoundedRowsEqTerminalPartsFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat)
    (sourceIndex targetIndex : ValuationTerm)
    (sourceStart sourceFinish sourceGammaFinish
      sourceGammaCount sourceGammaBoundary sourceBoolValue
      sourceGammaBoundarySize targetStart targetFinish targetGammaFinish
      targetGammaCount targetGammaBoundary targetBoolValue
      targetGammaBoundarySize : Nat) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm sourceBoundary)
      (shortBinaryNumeralTerm tokenCount)
      sourceIndex
      (shortBinaryNumeralTerm sourceStart) ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!sourceIndex + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm sourceFinish) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          targetIndex
          (shortBinaryNumeralTerm targetStart) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘!!targetIndex + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm targetFinish) ⋏
          (compactNumericChildResultRowEqGraphClosedFormula
            tokenTable width tokenCount
            (compactNumericChildResultRowCoordinatesOf
              sourceStart sourceFinish sourceGammaFinish sourceGammaCount
              sourceGammaBoundary sourceBoolValue)
            (compactNumericChildResultRowCoordinatesOf
              targetStart targetFinish targetGammaFinish targetGammaCount
              targetGammaBoundary targetBoolValue)
            { gammaBoundarySize := sourceGammaBoundarySize }
            { gammaBoundarySize := targetGammaBoundarySize }))))

private theorem compactNumericChildResultBoundedRowsEqTerminal_substitution_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat)
    (sourceIndex targetIndex : ValuationTerm)
    (sourceStart sourceFinish sourceGammaFinish
      sourceGammaCount sourceGammaBoundary sourceBoolValue
      sourceGammaBoundarySize targetStart targetFinish targetGammaFinish
      targetGammaCount targetGammaBoundary targetBoolValue
      targetGammaBoundarySize : Nat) :
    (compactNumericChildResultBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndex targetIndex) ⇜
      ![shortBinaryNumeralTerm targetGammaBoundarySize,
        shortBinaryNumeralTerm targetBoolValue,
        shortBinaryNumeralTerm targetGammaBoundary,
        shortBinaryNumeralTerm targetGammaCount,
        shortBinaryNumeralTerm targetGammaFinish,
        shortBinaryNumeralTerm targetFinish,
        shortBinaryNumeralTerm targetStart,
        shortBinaryNumeralTerm sourceGammaBoundarySize,
        shortBinaryNumeralTerm sourceBoolValue,
        shortBinaryNumeralTerm sourceGammaBoundary,
        shortBinaryNumeralTerm sourceGammaCount,
        shortBinaryNumeralTerm sourceGammaFinish,
        shortBinaryNumeralTerm sourceFinish,
        shortBinaryNumeralTerm sourceStart] =
      compactNumericChildResultBoundedRowsEqTerminalPartsFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndex targetIndex sourceStart sourceFinish sourceGammaFinish
        sourceGammaCount sourceGammaBoundary sourceBoolValue
        sourceGammaBoundarySize targetStart targetFinish targetGammaFinish
        targetGammaCount targetGammaBoundary targetBoolValue
        targetGammaBoundarySize := by
  let witnessTerms : Fin 14 -> ValuationTerm :=
    ![shortBinaryNumeralTerm targetGammaBoundarySize,
      shortBinaryNumeralTerm targetBoolValue,
      shortBinaryNumeralTerm targetGammaBoundary,
      shortBinaryNumeralTerm targetGammaCount,
      shortBinaryNumeralTerm targetGammaFinish,
      shortBinaryNumeralTerm targetFinish,
      shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm sourceGammaBoundarySize,
      shortBinaryNumeralTerm sourceBoolValue,
      shortBinaryNumeralTerm sourceGammaBoundary,
      shortBinaryNumeralTerm sourceGammaCount,
      shortBinaryNumeralTerm sourceGammaFinish,
      shortBinaryNumeralTerm sourceFinish,
      shortBinaryNumeralTerm sourceStart]
  unfold compactNumericChildResultBoundedRowsEqTerminal
  unfold compactNumericChildResultBoundedRowsEqTerminalPartsFormula
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactNumericChildResultRowEqGraphClosedFormula
  unfold compactNumericChildResultRowCoordinatesOf
  simp only [LogicalConnective.HomClass.map_and,
    rewriting_embeddedFormulaSubstitution]
  congr 1
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.subst_bvar, substituteClosedShift]
    · intro coordinate
      simp
  · congr 1
    · apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.subst_bvar, substituteClosedShift]
      · intro coordinate
        simp
    · congr 1
      · apply Rewriting.smul_ext'
        apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [Rew.subst_bvar, substituteClosedShift]
        · intro coordinate
          simp
      · congr 1
        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.subst_bvar, substituteClosedShift]
          · intro coordinate
            simp

        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.subst_bvar, substituteClosedShift]
          · intro coordinate
            simp

private def compactNumericChildResultBoundedRowsEqExplicitFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndex targetIndex : ValuationTerm) :
    ValuationFormula :=
  ((((((((((((((compactNumericChildResultBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndex targetIndex).bexsLTSucc
      (closedShift 13 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 12 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 11 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 10 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 9 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 8 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 7 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 6 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 5 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 4 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 0 (shortBinaryNumeralTerm valueBound))

private theorem compactNumericChildResultBoundedRowsEqExplicitFormula_eq_generic
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndex targetIndex : ValuationTerm) :
    compactNumericChildResultBoundedRowsEqExplicitFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 14
        (compactNumericChildResultBoundedRowsEqTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            sourceIndex targetIndex) := by
  rfl

/-- Exact fourteen-witness presentation of the quoted row-equality predicate. -/
theorem compactNumericChildResultBoundedRowsEqClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) :
    compactNumericChildResultBoundedRowsEqClosedFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex =
      compactNumericChildResultBoundedRowsEqExplicitFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (shortBinaryNumeralTerm sourceIndex)
            (shortBinaryNumeralTerm targetIndex) := by
  unfold compactNumericChildResultBoundedRowsEqClosedFormula
  rw [compactNumericChildResultBoundedRowsEqDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (shortBinaryNumeralTerm sourceIndex)
              (shortBinaryNumeralTerm targetIndex)) 0 ▹
      compactNumericChildResultBoundedRowsEqRawBody = _
  unfold compactNumericChildResultBoundedRowsEqExplicitFormula
  unfold compactNumericChildResultBoundedRowsEqRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactNumericChildResultBoundedRowsEqSourceQpow_bound0,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound1,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound2,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound3,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound4,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound5,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound6,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound7,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound8,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound9,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound10,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound11,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound12,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound13,
    compactNumericChildResultBoundedRowsEqRawTerminal_rewriting]

/-- The bounded row-equality predicate with both row indices represented by
valuation terms, as required beneath an enclosing bounded universal. -/
def compactNumericChildResultBoundedRowsEqAtValuationFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndex targetIndex : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedRowsEqDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm valueBound,
      sourceIndex,
      targetIndex]

theorem compactNumericChildResultBoundedRowsEqAtValuationFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndex targetIndex : ValuationTerm) :
    compactNumericChildResultBoundedRowsEqAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndex targetIndex =
      compactNumericChildResultBoundedRowsEqExplicitFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndex targetIndex := by
  unfold compactNumericChildResultBoundedRowsEqAtValuationFormula
  rw [compactNumericChildResultBoundedRowsEqDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowsEqSourceTerms
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound sourceIndex targetIndex) 0 ▹
      compactNumericChildResultBoundedRowsEqRawBody = _
  unfold compactNumericChildResultBoundedRowsEqExplicitFormula
  unfold compactNumericChildResultBoundedRowsEqRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactNumericChildResultBoundedRowsEqSourceQpow_bound0,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound1,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound2,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound3,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound4,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound5,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound6,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound7,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound8,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound9,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound10,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound11,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound12,
    compactNumericChildResultBoundedRowsEqSourceQpow_bound13,
    compactNumericChildResultBoundedRowsEqRawTerminal_rewriting]

private structure CompactNumericChildResultBoundedRowsEqWitnessData
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) where
  sourceStart : Nat
  sourceFinish : Nat
  sourceGammaFinish : Nat
  sourceGammaCount : Nat
  sourceGammaBoundary : Nat
  sourceBoolValue : Nat
  sourceGammaBoundarySize : Nat
  targetStart : Nat
  targetFinish : Nat
  targetGammaFinish : Nat
  targetGammaCount : Nat
  targetGammaBoundary : Nat
  targetBoolValue : Nat
  targetGammaBoundarySize : Nat
  sourceStartBound : sourceStart ≤ valueBound
  sourceFinishBound : sourceFinish ≤ valueBound
  sourceGammaFinishBound : sourceGammaFinish ≤ valueBound
  sourceGammaCountBound : sourceGammaCount ≤ valueBound
  sourceGammaBoundaryBound : sourceGammaBoundary ≤ valueBound
  sourceBoolValueBound : sourceBoolValue ≤ valueBound
  sourceGammaBoundarySizeBound : sourceGammaBoundarySize ≤ valueBound
  targetStartBound : targetStart ≤ valueBound
  targetFinishBound : targetFinish ≤ valueBound
  targetGammaFinishBound : targetGammaFinish ≤ valueBound
  targetGammaCountBound : targetGammaCount ≤ valueBound
  targetGammaBoundaryBound : targetGammaBoundary ≤ valueBound
  targetBoolValueBound : targetBoolValue ≤ valueBound
  targetGammaBoundarySizeBound : targetGammaBoundarySize ≤ valueBound
  sourceStartEntry : CompactFixedWidthEntry sourceBoundary tokenCount
    sourceIndex sourceStart
  sourceFinishEntry : CompactFixedWidthEntry sourceBoundary tokenCount
    (sourceIndex + 1) sourceFinish
  targetStartEntry : CompactFixedWidthEntry targetBoundary tokenCount
    targetIndex targetStart
  targetFinishEntry : CompactFixedWidthEntry targetBoundary tokenCount
    (targetIndex + 1) targetFinish
  rowEq : CompactNumericChildResultRowEqGraph tokenTable width tokenCount
    (compactNumericChildResultRowCoordinatesOf
      sourceStart sourceFinish sourceGammaFinish sourceGammaCount
        sourceGammaBoundary sourceBoolValue)
    (compactNumericChildResultRowCoordinatesOf
      targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBoolValue)
    { gammaBoundarySize := sourceGammaBoundarySize }
    { gammaBoundarySize := targetGammaBoundarySize }

private theorem
    compactNumericChildResultBoundedRowsEqWitnessData_nonempty
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (hrows : CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    Nonempty (CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) := by
  rcases hrows with
    ⟨sourceStart, sourceStartBound,
      sourceFinish, sourceFinishBound,
      sourceGammaFinish, sourceGammaFinishBound,
      sourceGammaCount, sourceGammaCountBound,
      sourceGammaBoundary, sourceGammaBoundaryBound,
      sourceBoolValue, sourceBoolValueBound,
      sourceGammaBoundarySize, sourceGammaBoundarySizeBound,
      targetStart, targetStartBound,
      targetFinish, targetFinishBound,
      targetGammaFinish, targetGammaFinishBound,
      targetGammaCount, targetGammaCountBound,
      targetGammaBoundary, targetGammaBoundaryBound,
      targetBoolValue, targetBoolValueBound,
      targetGammaBoundarySize, targetGammaBoundarySizeBound,
      sourceStartEntry, sourceFinishEntry,
      targetStartEntry, targetFinishEntry, rowEq⟩
  exact ⟨{
    sourceStart := sourceStart
    sourceFinish := sourceFinish
    sourceGammaFinish := sourceGammaFinish
    sourceGammaCount := sourceGammaCount
    sourceGammaBoundary := sourceGammaBoundary
    sourceBoolValue := sourceBoolValue
    sourceGammaBoundarySize := sourceGammaBoundarySize
    targetStart := targetStart
    targetFinish := targetFinish
    targetGammaFinish := targetGammaFinish
    targetGammaCount := targetGammaCount
    targetGammaBoundary := targetGammaBoundary
    targetBoolValue := targetBoolValue
    targetGammaBoundarySize := targetGammaBoundarySize
    sourceStartBound := sourceStartBound
    sourceFinishBound := sourceFinishBound
    sourceGammaFinishBound := sourceGammaFinishBound
    sourceGammaCountBound := sourceGammaCountBound
    sourceGammaBoundaryBound := sourceGammaBoundaryBound
    sourceBoolValueBound := sourceBoolValueBound
    sourceGammaBoundarySizeBound := sourceGammaBoundarySizeBound
    targetStartBound := targetStartBound
    targetFinishBound := targetFinishBound
    targetGammaFinishBound := targetGammaFinishBound
    targetGammaCountBound := targetGammaCountBound
    targetGammaBoundaryBound := targetGammaBoundaryBound
    targetBoolValueBound := targetBoolValueBound
    targetGammaBoundarySizeBound := targetGammaBoundarySizeBound
    sourceStartEntry := sourceStartEntry
    sourceFinishEntry := sourceFinishEntry
    targetStartEntry := targetStartEntry
    targetFinishEntry := targetFinishEntry
    rowEq := rowEq }⟩

private noncomputable def
    compactNumericChildResultBoundedRowsEqWitnessDataOf
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (hrows : CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex :=
  Classical.choice
    (compactNumericChildResultBoundedRowsEqWitnessData_nonempty
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex hrows)

private def compactNumericChildResultBoundedRowsEqWitnessValues
    {tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat}
    (witness : CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) : Fin 14 -> Nat :=
  ![witness.targetGammaBoundarySize, witness.targetBoolValue,
    witness.targetGammaBoundary, witness.targetGammaCount,
    witness.targetGammaFinish, witness.targetFinish, witness.targetStart,
    witness.sourceGammaBoundarySize, witness.sourceBoolValue,
    witness.sourceGammaBoundary, witness.sourceGammaCount,
    witness.sourceGammaFinish, witness.sourceFinish, witness.sourceStart]

private theorem compactNumericChildResultBoundedRowsEqWitnessValues_le
    {tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat}
    (witness : CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) (coordinate : Fin 14) :
    compactNumericChildResultBoundedRowsEqWitnessValues witness coordinate ≤
      valueBound := by
  fin_cases coordinate
  · exact witness.targetGammaBoundarySizeBound
  · exact witness.targetBoolValueBound
  · exact witness.targetGammaBoundaryBound
  · exact witness.targetGammaCountBound
  · exact witness.targetGammaFinishBound
  · exact witness.targetFinishBound
  · exact witness.targetStartBound
  · exact witness.sourceGammaBoundarySizeBound
  · exact witness.sourceBoolValueBound
  · exact witness.sourceGammaBoundaryBound
  · exact witness.sourceGammaCountBound
  · exact witness.sourceGammaFinishBound
  · exact witness.sourceFinishBound
  · exact witness.sourceStartBound

private noncomputable def
    compactNumericChildResultBoundedRowsEqTerminalPartsCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (witness : CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    HybridCertificate
      (compactNumericChildResultBoundedRowsEqTerminalPartsFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
        (shortBinaryNumeralTerm sourceIndex)
        (shortBinaryNumeralTerm targetIndex)
        witness.sourceStart witness.sourceFinish
        witness.sourceGammaFinish witness.sourceGammaCount
        witness.sourceGammaBoundary witness.sourceBoolValue
        witness.sourceGammaBoundarySize witness.targetStart
        witness.targetFinish witness.targetGammaFinish witness.targetGammaCount
        witness.targetGammaBoundary witness.targetBoolValue
        witness.targetGammaBoundarySize) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm sourceBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm sourceIndex)
      (shortBinaryNumeralTerm witness.sourceStart) (by
        simpa [termValue_shortBinaryNumeralTerm] using
          witness.sourceStartEntry))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!(shortBinaryNumeralTerm sourceIndex) + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm witness.sourceFinish) (by
          simpa [termValue_shortBinaryNumeralTerm,
            termValue_arithmeticAdd, termValue_arithmeticOne] using
            witness.sourceFinishEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm targetIndex)
          (shortBinaryNumeralTerm witness.targetStart) (by
            simpa [termValue_shortBinaryNumeralTerm] using
              witness.targetStartEntry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            zeroValuation
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘!!(shortBinaryNumeralTerm targetIndex) + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm witness.targetFinish) (by
              simpa [termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticOne] using
                witness.targetFinishEntry))
          (compactNumericChildResultRowEqGraphExplicitHybridCertificate
            witness.rowEq))))

private noncomputable def
    compactNumericChildResultBoundedRowsEqTerminalForBuilder
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (witness : CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    HybridCertificate
      ((compactNumericChildResultBoundedRowsEqTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            (shortBinaryNumeralTerm sourceIndex)
            (shortBinaryNumeralTerm targetIndex)) ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactNumericChildResultBoundedRowsEqWitnessValues
            witness coordinate)) := by
  have hvalues :
      (fun coordinate => shortBinaryNumeralTerm
          (compactNumericChildResultBoundedRowsEqWitnessValues
            witness coordinate)) =
        ![shortBinaryNumeralTerm witness.targetGammaBoundarySize,
          shortBinaryNumeralTerm witness.targetBoolValue,
          shortBinaryNumeralTerm witness.targetGammaBoundary,
          shortBinaryNumeralTerm witness.targetGammaCount,
          shortBinaryNumeralTerm witness.targetGammaFinish,
          shortBinaryNumeralTerm witness.targetFinish,
          shortBinaryNumeralTerm witness.targetStart,
          shortBinaryNumeralTerm witness.sourceGammaBoundarySize,
          shortBinaryNumeralTerm witness.sourceBoolValue,
          shortBinaryNumeralTerm witness.sourceGammaBoundary,
          shortBinaryNumeralTerm witness.sourceGammaCount,
          shortBinaryNumeralTerm witness.sourceGammaFinish,
          shortBinaryNumeralTerm witness.sourceFinish,
          shortBinaryNumeralTerm witness.sourceStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [hvalues]
  exact .cast
    (compactNumericChildResultBoundedRowsEqTerminal_substitution_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary
      (shortBinaryNumeralTerm sourceIndex)
      (shortBinaryNumeralTerm targetIndex)
      witness.sourceStart witness.sourceFinish
      witness.sourceGammaFinish witness.sourceGammaCount
      witness.sourceGammaBoundary witness.sourceBoolValue
      witness.sourceGammaBoundarySize witness.targetStart
      witness.targetFinish witness.targetGammaFinish witness.targetGammaCount
      witness.targetGammaBoundary witness.targetBoolValue
      witness.targetGammaBoundarySize).symm
    (compactNumericChildResultBoundedRowsEqTerminalPartsCertificate
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex witness)

private noncomputable def
    compactNumericChildResultBoundedRowsEqAtValuationTerminalPartsCertificate
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (sourceIndexTerm targetIndexTerm : ValuationTerm)
    (hsourceIndex : termValue valuation sourceIndexTerm = sourceIndex)
    (htargetIndex : termValue valuation targetIndexTerm = targetIndex)
    (witness : CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactNumericChildResultBoundedRowsEqTerminalPartsFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndexTerm targetIndexTerm
        witness.sourceStart witness.sourceFinish witness.sourceGammaFinish
        witness.sourceGammaCount witness.sourceGammaBoundary
        witness.sourceBoolValue witness.sourceGammaBoundarySize
        witness.targetStart witness.targetFinish witness.targetGammaFinish
        witness.targetGammaCount witness.targetGammaBoundary
        witness.targetBoolValue witness.targetGammaBoundarySize) := by
  let rowAtZero :=
    compactNumericChildResultRowEqGraphExplicitHybridCertificate witness.rowEq
  let rowAtValuation := revalueClosedHybridCertificate rowAtZero (by
    unfold compactNumericChildResultRowEqGraphClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _) valuation
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation
      (shortBinaryNumeralTerm sourceBoundary)
      (shortBinaryNumeralTerm tokenCount)
      sourceIndexTerm
      (shortBinaryNumeralTerm witness.sourceStart) (by
        simpa [termValue_shortBinaryNumeralTerm, hsourceIndex] using
          witness.sourceStartEntry))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation
        (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!sourceIndexTerm + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm witness.sourceFinish) (by
          simpa [termValue_shortBinaryNumeralTerm,
            termValue_arithmeticAdd, termValue_arithmeticOne,
            hsourceIndex] using witness.sourceFinishEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          targetIndexTerm
          (shortBinaryNumeralTerm witness.targetStart) (by
            simpa [termValue_shortBinaryNumeralTerm, htargetIndex] using
              witness.targetStartEntry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            valuation
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘!!targetIndexTerm + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm witness.targetFinish) (by
              simpa [termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticOne,
                htargetIndex] using witness.targetFinishEntry))
          rowAtValuation)))

private noncomputable def
    compactNumericChildResultBoundedRowsEqAtValuationTerminalForBuilder
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (sourceIndexTerm targetIndexTerm : ValuationTerm)
    (hsourceIndex : termValue valuation sourceIndexTerm = sourceIndex)
    (htargetIndex : termValue valuation targetIndexTerm = targetIndex)
    (witness : CompactNumericChildResultBoundedRowsEqWitnessData
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactNumericChildResultBoundedRowsEqTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            sourceIndexTerm targetIndexTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactNumericChildResultBoundedRowsEqWitnessValues
            witness coordinate)) := by
  have hvalues :
      (fun coordinate => shortBinaryNumeralTerm
          (compactNumericChildResultBoundedRowsEqWitnessValues
            witness coordinate)) =
        ![shortBinaryNumeralTerm witness.targetGammaBoundarySize,
          shortBinaryNumeralTerm witness.targetBoolValue,
          shortBinaryNumeralTerm witness.targetGammaBoundary,
          shortBinaryNumeralTerm witness.targetGammaCount,
          shortBinaryNumeralTerm witness.targetGammaFinish,
          shortBinaryNumeralTerm witness.targetFinish,
          shortBinaryNumeralTerm witness.targetStart,
          shortBinaryNumeralTerm witness.sourceGammaBoundarySize,
          shortBinaryNumeralTerm witness.sourceBoolValue,
          shortBinaryNumeralTerm witness.sourceGammaBoundary,
          shortBinaryNumeralTerm witness.sourceGammaCount,
          shortBinaryNumeralTerm witness.sourceGammaFinish,
          shortBinaryNumeralTerm witness.sourceFinish,
          shortBinaryNumeralTerm witness.sourceStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [hvalues]
  exact .cast
    (compactNumericChildResultBoundedRowsEqTerminal_substitution_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary
      sourceIndexTerm targetIndexTerm
      witness.sourceStart witness.sourceFinish witness.sourceGammaFinish
      witness.sourceGammaCount witness.sourceGammaBoundary
      witness.sourceBoolValue witness.sourceGammaBoundarySize
      witness.targetStart witness.targetFinish witness.targetGammaFinish
      witness.targetGammaCount witness.targetGammaBoundary
      witness.targetBoolValue witness.targetGammaBoundarySize).symm
    (compactNumericChildResultBoundedRowsEqAtValuationTerminalPartsCertificate
      valuation tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex sourceIndexTerm targetIndexTerm
      hsourceIndex htargetIndex witness)

/-- Build the complete certificate directly from the fourteen semantic witnesses. -/
noncomputable def compactNumericChildResultBoundedRowsEqExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (hrows : CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    HybridCertificate
      (compactNumericChildResultBoundedRowsEqClosedFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex) := by
  let witness := compactNumericChildResultBoundedRowsEqWitnessDataOf
    tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex hrows
  let installed := buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactNumericChildResultBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        (shortBinaryNumeralTerm sourceIndex)
        (shortBinaryNumeralTerm targetIndex))
    (compactNumericChildResultBoundedRowsEqWitnessValues witness)
    (compactNumericChildResultBoundedRowsEqWitnessValues_le witness)
    (compactNumericChildResultBoundedRowsEqTerminalForBuilder
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex witness)
  exact .cast
    (compactNumericChildResultBoundedRowsEqClosedFormula_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex).symm
    (.cast
      (compactNumericChildResultBoundedRowsEqExplicitFormula_eq_generic
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (shortBinaryNumeralTerm sourceIndex)
            (shortBinaryNumeralTerm targetIndex)).symm
      installed)

/-- Explicit row-equality certificate at an arbitrary valuation.  The two
index terms are checked against the semantic row indices, while all fourteen
bounded witnesses and the complete row-equality graph remain explicit. -/
noncomputable def
    compactNumericChildResultBoundedRowsEqAtValuationExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (sourceIndexTerm targetIndexTerm : ValuationTerm)
    (hsourceIndex : termValue valuation sourceIndexTerm = sourceIndex)
    (htargetIndex : termValue valuation targetIndexTerm = targetIndex)
    (hrows : CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactNumericChildResultBoundedRowsEqAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndexTerm targetIndexTerm) := by
  let witness := compactNumericChildResultBoundedRowsEqWitnessDataOf
    tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex hrows
  let installed := buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactNumericChildResultBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndexTerm targetIndexTerm)
    (compactNumericChildResultBoundedRowsEqWitnessValues witness)
    (compactNumericChildResultBoundedRowsEqWitnessValues_le witness)
    (compactNumericChildResultBoundedRowsEqAtValuationTerminalForBuilder
      valuation tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex sourceIndexTerm targetIndexTerm
      hsourceIndex htargetIndex witness)
  exact .cast
    (compactNumericChildResultBoundedRowsEqAtValuationFormula_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary valueBound
        sourceIndexTerm targetIndexTerm).symm
    (.cast
      (compactNumericChildResultBoundedRowsEqExplicitFormula_eq_generic
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndexTerm targetIndexTerm).symm
      installed)

#print axioms compactNumericChildResultBoundedRowsEqClosedFormula
#print axioms compactNumericChildResultBoundedRowsEqTerminal_substitution_alignment
#print axioms compactNumericChildResultBoundedRowsEqClosedFormula_alignment
#print axioms compactNumericChildResultBoundedRowsEqExplicitHybridCertificate
#print axioms compactNumericChildResultBoundedRowsEqAtValuationFormula_alignment
#print axioms compactNumericChildResultBoundedRowsEqAtValuationExplicitHybridCertificate

end FoundationCompactNumericListedDirectChildResultBoundedRowsEqExplicitHybridCertificate
