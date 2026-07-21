import integration.FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
import integration.FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-!
# Explicit hybrid certificate for a bounded child-result head

Seven bounded parser coordinates are installed as explicit witnesses.  The
terminal certificate independently checks both boundary entries, the complete
child-result core, equality with the prescribed context rows, and the Boolean
tag.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectChildResultBoundedHeadEqExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListSameRows
open FoundationCompactNumericListedDirectNatListListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

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
    exact Empty.elim coordinate

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
  | depth + 1, term =>
      Rew.bShift (sourceSubstitutionLift depth term)

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

/-- All nine public coordinates closed by short numerals. -/
def compactNumericChildResultBoundedHeadEqClosedFormula
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedHeadEqDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm expectedGammaBoundary,
      shortBinaryNumeralTerm expectedGammaCount,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm targetIndex,
      shortBinaryNumeralTerm expectedBool]

private def compactNumericChildResultBoundedHeadEqSourceTerms
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    Fin 9 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm expectedGammaBoundary,
    shortBinaryNumeralTerm expectedGammaCount,
    shortBinaryNumeralTerm valueBound,
    shortBinaryNumeralTerm targetIndex,
    shortBinaryNumeralTerm expectedBool]

private def compactNumericChildResultBoundedHeadEqRawTerminal :
    ArithmeticSemiformula Nat 16 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![(#10 : ArithmeticSemiterm Nat 16), #9, #14, #6]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![(#10 : ArithmeticSemiterm Nat 16), #9, ‘#14 + 1’, #5]) ⋏
      (((Rewriting.emb (ξ := Nat)
          compactNumericChildResultCoreGraphDef.val) ⇜
        ![(#7 : ArithmeticSemiterm Nat 16), #8, #9, #6, #5, #4,
          #3, #2, #1, #0]) ⋏
        (((Rewriting.emb (ξ := Nat)
            compactAdditiveNatListListSameRowsDef.val) ⇜
          ![(#7 : ArithmeticSemiterm Nat 16), #8, #9, #11, #12,
            #2, #3]) ⋏
          “#1 = #15”)))

private def compactNumericChildResultBoundedHeadEqRawBody :
    ArithmeticSemiformula Nat 9 :=
  (((((((compactNumericChildResultBoundedHeadEqRawTerminal.bexsLTSucc
      (#12 : ArithmeticSemiterm Nat 15)).bexsLTSucc
      (#11 : ArithmeticSemiterm Nat 14)).bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 13)).bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#7 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#6 : ArithmeticSemiterm Nat 9))

private theorem compactNumericChildResultBoundedHeadEqDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedHeadEqDef.val =
      compactNumericChildResultBoundedHeadEqRawBody := by
  have hstart :
      (Rew.emb : Rew ℒₒᵣ Empty 16 Nat 16).comp
          (Rew.subst
            ![(#10 : ArithmeticSemiterm Empty 16), #9, #14, #6]) =
        (Rew.subst
          ![(#10 : ArithmeticSemiterm Nat 16), #9, #14, #6]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hfinish :
      (Rew.emb : Rew ℒₒᵣ Empty 16 Nat 16).comp
          (Rew.subst
            ![(#10 : ArithmeticSemiterm Empty 16), #9, ‘#14 + 1’, #5]) =
        (Rew.subst
          ![(#10 : ArithmeticSemiterm Nat 16), #9, ‘#14 + 1’, #5]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hcore :
      (Rew.emb : Rew ℒₒᵣ Empty 16 Nat 16).comp
          (Rew.subst
            ![(#7 : ArithmeticSemiterm Empty 16), #8, #9, #6, #5,
              #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#7 : ArithmeticSemiterm Nat 16), #8, #9, #6, #5,
            #4, #3, #2, #1, #0]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hrows :
      (Rew.emb : Rew ℒₒᵣ Empty 16 Nat 16).comp
          (Rew.subst
            ![(#7 : ArithmeticSemiterm Empty 16), #8, #9, #11, #12,
              #2, #3]) =
        (Rew.subst
          ![(#7 : ArithmeticSemiterm Nat 16), #8, #9, #11, #12,
            #2, #3]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactNumericChildResultBoundedHeadEqDef
  unfold compactNumericChildResultBoundedHeadEqRawBody
  unfold compactNumericChildResultBoundedHeadEqRawTerminal
  simp [← TransitiveRewriting.comp_app]
  rw [hstart, hfinish, hcore, hrows]

@[simp] private theorem compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool depth : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) depth
        (#(⟨depth + 6, by omega⟩ : Fin (9 + depth)) :
          ArithmeticSemiterm Nat (9 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm valueBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactNumericChildResultBoundedHeadEqSourceTerms]

private theorem compactNumericChildResultBoundedHeadEqSourceQpow_bound0
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 0
        (#6 : ArithmeticSemiterm Nat 9) =
      closedShift 0 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool 0)

private theorem compactNumericChildResultBoundedHeadEqSourceQpow_bound1
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 1
        (#7 : ArithmeticSemiterm Nat 10) =
      closedShift 1 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool 1)

private theorem compactNumericChildResultBoundedHeadEqSourceQpow_bound2
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 2
        (#8 : ArithmeticSemiterm Nat 11) =
      closedShift 2 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool 2)

private theorem compactNumericChildResultBoundedHeadEqSourceQpow_bound3
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 3
        (#9 : ArithmeticSemiterm Nat 12) =
      closedShift 3 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool 3)

private theorem compactNumericChildResultBoundedHeadEqSourceQpow_bound4
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 4
        (#10 : ArithmeticSemiterm Nat 13) =
      closedShift 4 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool 4)

private theorem compactNumericChildResultBoundedHeadEqSourceQpow_bound5
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 5
        (#11 : ArithmeticSemiterm Nat 14) =
      closedShift 5 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool 5)

private theorem compactNumericChildResultBoundedHeadEqSourceQpow_bound6
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 6
        (#12 : ArithmeticSemiterm Nat 15) =
      closedShift 6 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedHeadEqSourceQpow_valueBound
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool 6)

private def compactNumericChildResultBoundedHeadEqTerminal
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount targetIndex expectedBool : Nat) :
    ArithmeticSemiformula Nat 7 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 7 (shortBinaryNumeralTerm targetBoundary),
        closedShift 7 (shortBinaryNumeralTerm tokenCount),
        closedShift 7 (shortBinaryNumeralTerm targetIndex),
        (#6 : ArithmeticSemiterm Nat 7)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 7 (shortBinaryNumeralTerm targetBoundary),
          closedShift 7 (shortBinaryNumeralTerm tokenCount),
          closedShift 7
            (‘!!(shortBinaryNumeralTerm targetIndex) + 1’ : ValuationTerm),
          (#5 : ArithmeticSemiterm Nat 7)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactNumericChildResultCoreGraphDef.val) ⇜
          ![closedShift 7 (shortBinaryNumeralTerm tokenTable),
            closedShift 7 (shortBinaryNumeralTerm width),
            closedShift 7 (shortBinaryNumeralTerm tokenCount),
            (#6 : ArithmeticSemiterm Nat 7), #5, #4, #3, #2, #1, #0]) ⋏
        (((Rewriting.emb (ξ := Nat) compactAdditiveNatListListSameRowsDef.val) ⇜
            ![closedShift 7 (shortBinaryNumeralTerm tokenTable),
              closedShift 7 (shortBinaryNumeralTerm width),
              closedShift 7 (shortBinaryNumeralTerm tokenCount),
              closedShift 7 (shortBinaryNumeralTerm expectedGammaBoundary),
              closedShift 7 (shortBinaryNumeralTerm expectedGammaCount),
              (#2 : ArithmeticSemiterm Nat 7), #3]) ⋏
          “#1 = !!(closedShift 7
            (shortBinaryNumeralTerm expectedBool))”)))

private theorem compactNumericChildResultBoundedHeadEqRawTerminal_rewriting
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 7 ▹
      compactNumericChildResultBoundedHeadEqRawTerminal =
    compactNumericChildResultBoundedHeadEqTerminal
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount targetIndex expectedBool := by
  unfold compactNumericChildResultBoundedHeadEqRawTerminal
  unfold compactNumericChildResultBoundedHeadEqTerminal
  simp [← TransitiveRewriting.comp_app,
    sourceSubstitutionQpow, Rew.q,
    compactNumericChildResultBoundedHeadEqSourceTerms, closedShift]
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

private def compactNumericChildResultBoundedHeadEqTerminalPartsFormula
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount targetIndex expectedBool start finish gammaFinish
      gammaCount gammaBoundary boolValue gammaBoundarySize : Nat) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm targetBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm targetIndex)
      (shortBinaryNumeralTerm start) ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!(shortBinaryNumeralTerm targetIndex) + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm finish) ⋏
      (compactNumericChildResultCoreClosedFormula tokenTable width tokenCount
          (compactNumericChildResultRowCoordinatesOf
            start finish gammaFinish gammaCount gammaBoundary boolValue)
          { gammaBoundarySize := gammaBoundarySize } ⋏
        (compactAdditiveNatListListSameRowsClosedFormula
            tokenTable width tokenCount expectedGammaBoundary
              expectedGammaCount gammaBoundary gammaCount ⋏
          “!!(shortBinaryNumeralTerm boolValue) =
            !!(shortBinaryNumeralTerm expectedBool)”)))

private theorem compactNumericChildResultBoundedHeadEqTerminal_substitution_alignment
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount targetIndex expectedBool start finish gammaFinish
      gammaCount gammaBoundary boolValue gammaBoundarySize : Nat) :
    (compactNumericChildResultBoundedHeadEqTerminal
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount targetIndex expectedBool) ⇜
      ![shortBinaryNumeralTerm gammaBoundarySize,
        shortBinaryNumeralTerm boolValue,
        shortBinaryNumeralTerm gammaBoundary,
        shortBinaryNumeralTerm gammaCount,
        shortBinaryNumeralTerm gammaFinish,
        shortBinaryNumeralTerm finish,
        shortBinaryNumeralTerm start] =
      compactNumericChildResultBoundedHeadEqTerminalPartsFormula
        tokenTable width tokenCount targetBoundary expectedGammaBoundary
          expectedGammaCount targetIndex expectedBool start finish gammaFinish
          gammaCount gammaBoundary boolValue gammaBoundarySize := by
  let witnessTerms : Fin 7 -> ValuationTerm :=
    ![shortBinaryNumeralTerm gammaBoundarySize,
      shortBinaryNumeralTerm boolValue,
      shortBinaryNumeralTerm gammaBoundary,
      shortBinaryNumeralTerm gammaCount,
      shortBinaryNumeralTerm gammaFinish,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm start]
  unfold compactNumericChildResultBoundedHeadEqTerminal
  unfold compactNumericChildResultBoundedHeadEqTerminalPartsFormula
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactNumericChildResultCoreClosedFormula
  unfold compactAdditiveNatListListSameRowsClosedFormula
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
        · simp [Rew.subst_bvar, substituteClosedShift]

private def compactNumericChildResultBoundedHeadEqExplicitFormula
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    ValuationFormula :=
  (((((((compactNumericChildResultBoundedHeadEqTerminal
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount targetIndex expectedBool).bexsLTSucc
      (closedShift 6 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 5 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 4 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 0 (shortBinaryNumeralTerm valueBound))

private theorem compactNumericChildResultBoundedHeadEqExplicitFormula_eq_generic
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    compactNumericChildResultBoundedHeadEqExplicitFormula
        tokenTable width tokenCount targetBoundary expectedGammaBoundary
          expectedGammaCount valueBound targetIndex expectedBool =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 7
        (compactNumericChildResultBoundedHeadEqTerminal
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount targetIndex expectedBool) := by
  rfl

theorem compactNumericChildResultBoundedHeadEqClosedFormula_alignment
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat) :
    compactNumericChildResultBoundedHeadEqClosedFormula
        tokenTable width tokenCount targetBoundary expectedGammaBoundary
          expectedGammaCount valueBound targetIndex expectedBool =
      compactNumericChildResultBoundedHeadEqExplicitFormula
        tokenTable width tokenCount targetBoundary expectedGammaBoundary
          expectedGammaCount valueBound targetIndex expectedBool := by
  unfold compactNumericChildResultBoundedHeadEqClosedFormula
  rw [compactNumericChildResultBoundedHeadEqDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedHeadEqSourceTerms
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount valueBound targetIndex expectedBool) 0 ▹
      compactNumericChildResultBoundedHeadEqRawBody = _
  unfold compactNumericChildResultBoundedHeadEqExplicitFormula
  unfold compactNumericChildResultBoundedHeadEqRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactNumericChildResultBoundedHeadEqSourceQpow_bound0,
    compactNumericChildResultBoundedHeadEqSourceQpow_bound1,
    compactNumericChildResultBoundedHeadEqSourceQpow_bound2,
    compactNumericChildResultBoundedHeadEqSourceQpow_bound3,
    compactNumericChildResultBoundedHeadEqSourceQpow_bound4,
    compactNumericChildResultBoundedHeadEqSourceQpow_bound5,
    compactNumericChildResultBoundedHeadEqSourceQpow_bound6,
    compactNumericChildResultBoundedHeadEqRawTerminal_rewriting]

noncomputable def compactNumericChildResultBoundedHeadEqExplicitHybridCertificate
    (tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat)
    (hhead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool) :
    HybridCertificate
      (compactNumericChildResultBoundedHeadEqClosedFormula
        tokenTable width tokenCount targetBoundary expectedGammaBoundary
          expectedGammaCount valueBound targetIndex expectedBool) := by
  let start := Classical.choose hhead
  have hstartData := Classical.choose_spec hhead
  let finish := Classical.choose hstartData.2
  have hfinishData := Classical.choose_spec hstartData.2
  let gammaFinish := Classical.choose hfinishData.2
  have hgammaFinishData := Classical.choose_spec hfinishData.2
  let gammaCount := Classical.choose hgammaFinishData.2
  have hgammaCountData := Classical.choose_spec hgammaFinishData.2
  let gammaBoundary := Classical.choose hgammaCountData.2
  have hgammaBoundaryData := Classical.choose_spec hgammaCountData.2
  let boolValue := Classical.choose hgammaBoundaryData.2
  have hboolValueData := Classical.choose_spec hgammaBoundaryData.2
  let gammaBoundarySize := Classical.choose hboolValueData.2
  have hterminalData := Classical.choose_spec hboolValueData.2
  have hstartBound : start ≤ valueBound := by
    exact hstartData.1
  have hfinishBound : finish ≤ valueBound := by
    exact hfinishData.1
  have hgammaFinishBound : gammaFinish ≤ valueBound := by
    exact hgammaFinishData.1
  have hgammaCountBound : gammaCount ≤ valueBound := by
    exact hgammaCountData.1
  have hgammaBoundaryBound : gammaBoundary ≤ valueBound := by
    exact hgammaBoundaryData.1
  have hboolValueBound : boolValue ≤ valueBound := by
    exact hboolValueData.1
  have hgammaBoundarySizeBound : gammaBoundarySize ≤ valueBound := by
    exact hterminalData.1
  have hstartEntry : CompactFixedWidthEntry targetBoundary tokenCount
      targetIndex start := by
    exact hterminalData.2.1
  have hfinishEntry : CompactFixedWidthEntry targetBoundary tokenCount
      (targetIndex + 1) finish := by
    exact hterminalData.2.2.1
  have hcore : CompactNumericChildResultCoreGraph tokenTable width tokenCount
      (compactNumericChildResultRowCoordinatesOf
        start finish gammaFinish gammaCount gammaBoundary boolValue)
      { gammaBoundarySize := gammaBoundarySize } := by
    exact hterminalData.2.2.2.1
  have hrows : CompactAdditiveNatListListSameRows tokenTable width tokenCount
      expectedGammaBoundary expectedGammaCount gammaBoundary gammaCount := by
    exact hterminalData.2.2.2.2.1
  have hbool : boolValue = expectedBool := by
    exact hterminalData.2.2.2.2.2
  let values : Fin 7 -> Nat :=
    ![gammaBoundarySize, boolValue, gammaBoundary, gammaCount,
      gammaFinish, finish, start]
  let boolCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm boolValue,
        shortBinaryNumeralTerm expectedBool] (by
          change termValue zeroValuation (shortBinaryNumeralTerm boolValue) =
            termValue zeroValuation (shortBinaryNumeralTerm expectedBool)
          simpa [termValue_shortBinaryNumeralTerm] using hbool)
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm targetIndex)
        (shortBinaryNumeralTerm start) (by
          simpa [termValue_shortBinaryNumeralTerm] using hstartEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (‘!!(shortBinaryNumeralTerm targetIndex) + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm finish) (by
            simpa [termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne]
              using hfinishEntry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactNumericChildResultCoreExplicitHybridCertificate hcore)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListListSameRowsExplicitHybridCertificate
              tokenTable width tokenCount expectedGammaBoundary
                expectedGammaCount gammaBoundary gammaCount hrows)
            boolCertificate)))
  let terminal : HybridCertificate
      ((compactNumericChildResultBoundedHeadEqTerminal
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount targetIndex expectedBool) ⇜
        ![shortBinaryNumeralTerm gammaBoundarySize,
          shortBinaryNumeralTerm boolValue,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm start]) :=
    .cast
      (compactNumericChildResultBoundedHeadEqTerminal_substitution_alignment
        tokenTable width tokenCount targetBoundary expectedGammaBoundary
          expectedGammaCount targetIndex expectedBool start finish gammaFinish
          gammaCount gammaBoundary boolValue gammaBoundarySize).symm
      terminalParts
  let terminalForBuilder : HybridCertificate
      ((compactNumericChildResultBoundedHeadEqTerminal
          tokenTable width tokenCount targetBoundary expectedGammaBoundary
            expectedGammaCount targetIndex expectedBool) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) := by
    have hvalues :
        (fun coordinate => shortBinaryNumeralTerm (values coordinate)) =
          ![shortBinaryNumeralTerm gammaBoundarySize,
            shortBinaryNumeralTerm boolValue,
            shortBinaryNumeralTerm gammaBoundary,
            shortBinaryNumeralTerm gammaCount,
            shortBinaryNumeralTerm gammaFinish,
            shortBinaryNumeralTerm finish,
            shortBinaryNumeralTerm start] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [hvalues]
    exact terminal
  let installed := buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactNumericChildResultBoundedHeadEqTerminal
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount targetIndex expectedBool)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact hgammaBoundarySizeBound
      · exact hboolValueBound
      · exact hgammaBoundaryBound
      · exact hgammaCountBound
      · exact hgammaFinishBound
      · exact hfinishBound
      · exact hstartBound) terminalForBuilder
  exact .cast
    (compactNumericChildResultBoundedHeadEqClosedFormula_alignment
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
        expectedGammaCount valueBound targetIndex expectedBool).symm
    (.cast
      (compactNumericChildResultBoundedHeadEqExplicitFormula_eq_generic
        tokenTable width tokenCount targetBoundary expectedGammaBoundary
          expectedGammaCount valueBound targetIndex expectedBool).symm
      installed)

#print axioms compactNumericChildResultBoundedHeadEqClosedFormula
#print axioms compactNumericChildResultBoundedHeadEqClosedFormula_alignment
#print axioms compactNumericChildResultBoundedHeadEqExplicitHybridCertificate

end FoundationCompactNumericListedDirectChildResultBoundedHeadEqExplicitHybridCertificate
