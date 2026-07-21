import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleEndpointExplicitHybridCertificate
import integration.FoundationCompactPAExplicitWitnessExsClosureBuilder

/-!
# Explicit hybrid certificate for the bounded simple certificate-node graph

The six bounded coordinates are installed directly as short-binary witnesses.
The terminal payload is the existing explicit certificate for the original
fourteen-coordinate endpoint graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSimpleEndpointExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAExplicitWitnessExsClosureBuilder

private abbrev zeroValuation : Nat -> Nat := fun _ => 0

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

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

/-- The original 9-coordinate bounded formula after its public inputs are
closed by short binary numerals. -/
def compactCertificateNodeSimpleEndpointBoundedGraphClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSimpleEndpointBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm suffixStart,
      shortBinaryNumeralTerm suffixFinish,
      shortBinaryNumeralTerm tag,
      shortBinaryNumeralTerm endpointBound]

/-- The original endpoint matrix beneath the six bounded existential layers.
The local coordinates retain the de Bruijn order induced by the source
formula: suffix-boundary size is `#0` and input boundary is `#5`. -/
private def compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat) :
    ArithmeticSemiformula Nat 6 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSimpleEndpointGraphDef.val) ⇜
    ![closedShift 6 (shortBinaryNumeralTerm tokenTable),
      closedShift 6 (shortBinaryNumeralTerm width),
      closedShift 6 (shortBinaryNumeralTerm tokenCount),
      closedShift 6 (shortBinaryNumeralTerm inputStart),
      closedShift 6 (shortBinaryNumeralTerm inputFinish),
      closedShift 6 (shortBinaryNumeralTerm suffixStart),
      closedShift 6 (shortBinaryNumeralTerm suffixFinish),
      closedShift 6 (shortBinaryNumeralTerm tag),
      (#5 : ArithmeticSemiterm Nat 6),
      (#4 : ArithmeticSemiterm Nat 6),
      (#3 : ArithmeticSemiterm Nat 6),
      (#2 : ArithmeticSemiterm Nat 6),
      (#1 : ArithmeticSemiterm Nat 6),
      (#0 : ArithmeticSemiterm Nat 6)]

/-- The graph call before any of the nine public coordinates are closed. -/
private def compactCertificateNodeSimpleEndpointBoundedGraphSourceRawTerminal :
    ArithmeticSemiformula Nat 15 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSimpleEndpointGraphDef.val) ⇜
    ![(#6 : ArithmeticSemiterm Nat 15), #7, #8, #9, #10, #11, #12, #13,
      #5, #4, #3, #2, #1, #0]

/-- The source formula with its original six bounded existential binders. -/
private def compactCertificateNodeSimpleEndpointBoundedGraphSourceRawBody :
    ArithmeticSemiformula Nat 9 :=
  ((((((compactCertificateNodeSimpleEndpointBoundedGraphSourceRawTerminal.bexsLTSucc
      (#13 : ArithmeticSemiterm Nat 14)).bexsLTSucc
      (#12 : ArithmeticSemiterm Nat 13)).bexsLTSucc
      (#11 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 9))

/-- A literal recursive presentation of bounded existential closure. -/
private def explicitBoundedWitnessFormula (bound : ValuationTerm) :
    (k : Nat) -> ArithmeticSemiformula Nat k -> ValuationFormula
  | 0, body => body
  | k + 1, body =>
      explicitBoundedWitnessFormula bound k
        (body.bexsLTSucc (closedShift k bound))

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

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat)
        compactCertificateNodeSimpleEndpointBoundedGraphDef.val =
      compactCertificateNodeSimpleEndpointBoundedGraphSourceRawBody := by
  have hgraph :
      (Rew.emb : Rew ℒₒᵣ Empty 15 Nat 15).comp
          (Rew.subst
            ![(#6 : ArithmeticSemiterm Empty 15), #7, #8, #9, #10,
              #11, #12, #13, #5, #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#6 : ArithmeticSemiterm Nat 15), #7, #8, #9, #10,
            #11, #12, #13, #5, #4, #3, #2, #1, #0]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactCertificateNodeSimpleEndpointBoundedGraphDef
  unfold compactCertificateNodeSimpleEndpointBoundedGraphSourceRawBody
  unfold compactCertificateNodeSimpleEndpointBoundedGraphSourceRawTerminal
  simp [rewriting_bexsLTSucc,
    rewriting_embeddedFormulaSubstitution,
    Rew.q_bvar_zero, Rew.q_bvar_succ,
    ← TransitiveRewriting.comp_app]
  rw [hgraph]

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

@[simp] private theorem sourceSubstitutionQpow_bexsLTSucc
    {sourceArity targetArity depth : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (bound : ArithmeticSemiterm Nat (sourceArity + depth))
    (body : ArithmeticSemiformula Nat (sourceArity + (depth + 1))) :
    sourceSubstitutionQpow terms depth ▹ body.bexsLTSucc bound =
      (sourceSubstitutionQpow terms (depth + 1) ▹ body).bexsLTSucc
        (sourceSubstitutionQpow terms depth bound) := by
  simpa [sourceSubstitutionQpow] using
    (rewriting_bexsLTSucc
      (sourceSubstitutionQpow terms depth) bound body)

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
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

private theorem shortBinarySubstitution_bexsLTSucc_tail
    {k : Nat}
    (bound : ValuationTerm)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) :
    (body.bexsLTSucc (closedShift k bound)) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ)) =
      (explicitWitnessBodyAfterTail body values).bexsLTSucc bound := by
  unfold Semiformula.bexsLTSucc
  unfold Semiformula.bexsLT
  have hbound :
      Rew.subst (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))
          (closedShift k bound) = bound := by
    exact substitute_closedShift _ bound
  simp [explicitWitnessBodyAfterTail, hbound]

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

private noncomputable def boundedWitnessGuardCertificate
    (value bound : Nat) (hvalue : value ≤ bound) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm value) <
        !!(shortBinaryNumeralTerm bound) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm value, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm value) <
        termValue zeroValuation rightTerm
      simp only [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne]
      omega)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

/-- Install each bounded witness and its `≤ endpointBound` guard directly. -/
private noncomputable def buildExplicitBoundedWitnessHybridCertificate :
    {k : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (∀ index, values index ≤ bound) ->
    HybridCertificate
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)) ->
    HybridCertificate
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) k body)
  | 0, bound, body, values, hbounds, terminal => by
      simpa [explicitBoundedWitnessFormula] using terminal
  | k + 1, bound, body, values, hbounds, terminal => by
      let tailValues : Fin k -> Nat := fun index => values index.succ
      let witnessBody := explicitWitnessBodyAfterTail body values
      let guard : ValuationFormula :=
        “!!(shortBinaryNumeralTerm (values 0)) <
          !!(shortBinaryNumeralTerm bound) + 1”
      let guardCertificate :=
        boundedWitnessGuardCertificate (values 0) bound (hbounds 0)
      have hbodySubstitution :
          witnessBody/[shortBinaryNumeralTerm (values 0)] =
            body ⇜ fun index =>
              shortBinaryNumeralTerm (values index) :=
        explicitWitnessBodyAfterTail_subst_head body values
      let installed : HybridCertificate
          (witnessBody/[shortBinaryNumeralTerm (values 0)]) :=
        .cast hbodySubstitution.symm terminal
      let guarded :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          guardCertificate installed
      let inner : HybridCertificate
          (witnessBody.bexsLTSucc
            (shortBinaryNumeralTerm bound)) := by
        let boundedMatrix : ArithmeticSemiformula Nat 1 :=
          Semiformula.Operator.LT.lt.operator
              ![(#0 : ArithmeticSemiterm Nat 1),
                Rew.bShift
                  ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
            witnessBody
        let direct : HybridCertificate (∃⁰ boundedMatrix) :=
          .existsWitness boundedMatrix (values 0) (.cast (by
            simp [boundedMatrix, guard,
              ← TransitiveRewriting.comp_app]) guarded)
        exact .cast (by rfl) direct
      let recursiveTerminal : HybridCertificate
          ((body.bexsLTSucc
              (closedShift k (shortBinaryNumeralTerm bound))) ⇜
            (fun index : Fin k =>
              shortBinaryNumeralTerm (tailValues index))) :=
        .cast
          (shortBinarySubstitution_bexsLTSucc_tail
            (shortBinaryNumeralTerm bound) body values).symm inner
      simpa only [explicitBoundedWitnessFormula] using
        buildExplicitBoundedWitnessHybridCertificate bound
          (body.bexsLTSucc
            (closedShift k (shortBinaryNumeralTerm bound)))
          tailValues (fun index => hbounds index.succ) recursiveTerminal

private def compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    Fin 9 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm suffixStart,
    shortBinaryNumeralTerm suffixFinish,
    shortBinaryNumeralTerm tag,
    shortBinaryNumeralTerm endpointBound]

@[simp] private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_endpointBound
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound depth : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) depth
        (#(⟨depth + 8, by omega⟩ : Fin (9 + depth)) :
          ArithmeticSemiterm Nat (9 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm endpointBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms]

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound0
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 0
        (#8 : ArithmeticSemiterm Nat 9) =
      closedShift 0 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound 0)

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound1
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 1
        (#9 : ArithmeticSemiterm Nat 10) =
      closedShift 1 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound 1)

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound2
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 2
        (#10 : ArithmeticSemiterm Nat 11) =
      closedShift 2 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound 2)

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound3
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 3
        (#11 : ArithmeticSemiterm Nat 12) =
      closedShift 3 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound 3)

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound4
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 4
        (#12 : ArithmeticSemiterm Nat 13) =
      closedShift 4 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound 4)

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound5
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 5
        (#13 : ArithmeticSemiterm Nat 14) =
      closedShift 5 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound 5)

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphSourceRawTerminal_rewriting
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 6 ▹
      compactCertificateNodeSimpleEndpointBoundedGraphSourceRawTerminal =
    compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag := by
  unfold compactCertificateNodeSimpleEndpointBoundedGraphSourceRawTerminal
  unfold compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [sourceSubstitutionQpow,
      Rew.q, Rew.q_bvar_zero, Rew.q_bvar_succ,
      Rew.comp_app, Rew.subst_bvar,
      compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms,
      sourceSubstitutionLift, closedShift]

private theorem compactCertificateNodeSimpleEndpointClosedFormula_eq_direct
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    compactCertificateNodeSimpleEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag coordinates =
      (Rewriting.emb (ξ := Nat)
          compactCertificateNodeSimpleEndpointGraphDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm inputStart,
          shortBinaryNumeralTerm inputFinish,
          shortBinaryNumeralTerm suffixStart,
          shortBinaryNumeralTerm suffixFinish,
          shortBinaryNumeralTerm tag,
          shortBinaryNumeralTerm coordinates.inputBoundary,
          shortBinaryNumeralTerm coordinates.inputCount,
          shortBinaryNumeralTerm coordinates.inputBoundarySize,
          shortBinaryNumeralTerm coordinates.suffixBoundary,
          shortBinaryNumeralTerm coordinates.suffixCount,
          shortBinaryNumeralTerm coordinates.suffixBoundarySize] := by
  rfl

private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal_vector_alignment
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag ⇜
      ![shortBinaryNumeralTerm coordinates.suffixBoundarySize,
        shortBinaryNumeralTerm coordinates.suffixCount,
        shortBinaryNumeralTerm coordinates.suffixBoundary,
        shortBinaryNumeralTerm coordinates.inputBoundarySize,
        shortBinaryNumeralTerm coordinates.inputCount,
        shortBinaryNumeralTerm coordinates.inputBoundary] =
      compactCertificateNodeSimpleEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag coordinates := by
  rw [compactCertificateNodeSimpleEndpointClosedFormula_eq_direct]
  unfold compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
  let witnessTerms : Fin 6 -> ValuationTerm :=
    ![shortBinaryNumeralTerm coordinates.suffixBoundarySize,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm coordinates.suffixBoundary,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundary]
  let rawTerms : Fin 14 -> ArithmeticSemiterm Nat 6 :=
    ![closedShift 6 (shortBinaryNumeralTerm tokenTable),
      closedShift 6 (shortBinaryNumeralTerm width),
      closedShift 6 (shortBinaryNumeralTerm tokenCount),
      closedShift 6 (shortBinaryNumeralTerm inputStart),
      closedShift 6 (shortBinaryNumeralTerm inputFinish),
      closedShift 6 (shortBinaryNumeralTerm suffixStart),
      closedShift 6 (shortBinaryNumeralTerm suffixFinish),
      closedShift 6 (shortBinaryNumeralTerm tag), #5, #4, #3, #2, #1, #0]
  let finalTerms : Fin 14 -> ValuationTerm :=
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm suffixStart,
      shortBinaryNumeralTerm suffixFinish,
      shortBinaryNumeralTerm tag,
      shortBinaryNumeralTerm coordinates.inputBoundary,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.suffixBoundary,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm coordinates.suffixBoundarySize]
  change Rew.subst witnessTerms ▹
      ((Rewriting.emb (ξ := Nat)
        compactCertificateNodeSimpleEndpointGraphDef.val) ⇜ rawTerms) =
    (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSimpleEndpointGraphDef.val) ⇜ finalTerms
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [witnessTerms, rawTerms, finalTerms, Rew.comp_app,
      Rew.subst_bvar, substitute_closedShift]

/-- Function-form normalization required by the bounded-witness builder. -/
private theorem
    compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal_installed_alignment
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag ⇜
      (fun index : Fin 6 => shortBinaryNumeralTerm
        (![coordinates.suffixBoundarySize,
          coordinates.suffixCount,
          coordinates.suffixBoundary,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
      compactCertificateNodeSimpleEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag coordinates := by
  have hvalueTerms :
      (fun index : Fin 6 => shortBinaryNumeralTerm
        (![coordinates.suffixBoundarySize,
          coordinates.suffixCount,
          coordinates.suffixBoundary,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
        ![shortBinaryNumeralTerm coordinates.suffixBoundarySize,
          shortBinaryNumeralTerm coordinates.suffixCount,
          shortBinaryNumeralTerm coordinates.suffixBoundary,
          shortBinaryNumeralTerm coordinates.inputBoundarySize,
          shortBinaryNumeralTerm coordinates.inputCount,
          shortBinaryNumeralTerm coordinates.inputBoundary] := by
    funext index
    fin_cases index <;> rfl
  rw [hvalueTerms]
  exact
    compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal_vector_alignment
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag coordinates

/-- Exact alignment of the original six `<⁺ endpointBound` layers with the
explicit bounded-witness presentation. -/
theorem compactCertificateNodeSimpleEndpointBoundedGraphClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    compactCertificateNodeSimpleEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag endpointBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm endpointBound) 6
        (compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag) := by
  unfold compactCertificateNodeSimpleEndpointBoundedGraphClosedFormula
  rw [compactCertificateNodeSimpleEndpointBoundedGraphDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactCertificateNodeSimpleEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound) 0 ▹
      compactCertificateNodeSimpleEndpointBoundedGraphSourceRawBody = _
  unfold compactCertificateNodeSimpleEndpointBoundedGraphSourceRawBody
  unfold explicitBoundedWitnessFormula
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound0,
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound1,
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound2,
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound3,
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound4,
    compactCertificateNodeSimpleEndpointBoundedGraphSourceQpow_bound5,
    compactCertificateNodeSimpleEndpointBoundedGraphSourceRawTerminal_rewriting]
  rfl

/-- Checked hybrid certificate for the original 9-coordinate bounded graph.
All six named endpoint coordinates and their guards are supplied explicitly;
the terminal is the existing 14-coordinate raw endpoint certificate. -/
noncomputable def
    compactCertificateNodeSimpleEndpointBoundedGraphExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates)
    (hinputBoundary : coordinates.inputBoundary ≤ endpointBound)
    (hinputCount : coordinates.inputCount ≤ endpointBound)
    (hinputBoundarySize : coordinates.inputBoundarySize ≤ endpointBound)
    (hsuffixBoundary : coordinates.suffixBoundary ≤ endpointBound)
    (hsuffixCount : coordinates.suffixCount ≤ endpointBound)
    (hsuffixBoundarySize : coordinates.suffixBoundarySize ≤ endpointBound)
    (hgraph : CompactCertificateNodeSimpleEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag coordinates) :
    HybridCertificate
      (compactCertificateNodeSimpleEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag endpointBound) := by
  rw [compactCertificateNodeSimpleEndpointBoundedGraphClosedFormula_alignment]
  let values : Fin 6 -> Nat :=
    ![coordinates.suffixBoundarySize,
      coordinates.suffixCount,
      coordinates.suffixBoundary,
      coordinates.inputBoundarySize,
      coordinates.inputCount,
      coordinates.inputBoundary]
  let rawCertificate :=
    compactCertificateNodeSimpleEndpointExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag coordinates hgraph
  let terminal : HybridCertificate
      (compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal_installed_alignment
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag coordinates).symm) rawCertificate
  exact buildExplicitBoundedWitnessHybridCertificate endpointBound
    (compactCertificateNodeSimpleEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag)
    values (by
      intro index
      fin_cases index
      · exact hsuffixBoundarySize
      · exact hsuffixCount
      · exact hsuffixBoundary
      · exact hinputBoundarySize
      · exact hinputCount
      · exact hinputBoundary) terminal

#print axioms compactCertificateNodeSimpleEndpointBoundedGraphClosedFormula_alignment
#print axioms compactCertificateNodeSimpleEndpointBoundedGraphExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedGraphExplicitHybridCertificate
