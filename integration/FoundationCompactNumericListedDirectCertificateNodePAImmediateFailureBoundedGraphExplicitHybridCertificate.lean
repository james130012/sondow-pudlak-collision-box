import integration.FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpointExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

/-!
# Explicit hybrid certificate for the bounded immediate PA-failure graph

The fourteen endpoint coordinates are installed as genuine bounded-existential
witnesses.  The terminal is the existing certificate for the original
nineteen-coordinate endpoint graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint
open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpointExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

private def closedShift :
    (depth : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat depth
  | 0, term => term
  | depth + 1, term => Rew.bShift (closedShift depth term)

/-- The original bounded graph with its six public inputs closed. -/
def compactCertificateNodePAImmediateFailureEndpointBoundedGraphClosedFormula
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm endpointBound]

/-- The original endpoint matrix beneath all fourteen bounded binders. -/
private def compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
    (tokenTable width tokenCount inputStart inputFinish : Nat) :
    ArithmeticSemiformula Nat 14 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodePAImmediateFailureEndpointGraphDef.val) ⇜
    ![closedShift 14 (shortBinaryNumeralTerm tokenTable),
      closedShift 14 (shortBinaryNumeralTerm width),
      closedShift 14 (shortBinaryNumeralTerm tokenCount),
      closedShift 14 (shortBinaryNumeralTerm inputStart),
      closedShift 14 (shortBinaryNumeralTerm inputFinish),
      (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]

/-- The unclosed terminal has five public coordinates and fourteen local
coordinates, hence source arity twenty. -/
private def compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawTerminal :
    ArithmeticSemiformula Nat 20 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodePAImmediateFailureEndpointGraphDef.val) ⇜
    ![(#14 : ArithmeticSemiterm Nat 20), #15, #16, #17, #18,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

/-- Literal source presentation of the original fourteen `<⁺ endpointBound`
binders.  The endpoint-bound coordinate is `#18` at arity nineteen down to
`#5` at arity six. -/
private def compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawBody :
  ArithmeticSemiformula Nat 6 :=
  ((((((((((((((compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawTerminal.bexsLTSucc
      (#18 : ArithmeticSemiterm Nat 19)).bexsLTSucc
      (#17 : ArithmeticSemiterm Nat 18)).bexsLTSucc
      (#16 : ArithmeticSemiterm Nat 17)).bexsLTSucc
      (#15 : ArithmeticSemiterm Nat 16)).bexsLTSucc
      (#14 : ArithmeticSemiterm Nat 15)).bexsLTSucc
      (#13 : ArithmeticSemiterm Nat 14)).bexsLTSucc
      (#12 : ArithmeticSemiterm Nat 13)).bexsLTSucc
      (#11 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 9)).bexsLTSucc
      (#7 : ArithmeticSemiterm Nat 8)).bexsLTSucc
      (#6 : ArithmeticSemiterm Nat 7)).bexsLTSucc
      (#5 : ArithmeticSemiterm Nat 6))

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat)
        compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef.val =
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawBody := by
  have hgraph :
      (Rew.emb : Rew ℒₒᵣ Empty 20 Nat 20).comp
          (Rew.subst
            ![(#14 : ArithmeticSemiterm Empty 20), #15, #16, #17, #18,
              #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#14 : ArithmeticSemiterm Nat 20), #15, #16, #17, #18,
            #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 19 Nat 19) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawBody
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawTerminal
  simp [rewriting_bexsLTSucc, rewriting_embeddedFormulaSubstitution,
    Rew.q_bvar_zero, Rew.q_bvar_succ,
    ← TransitiveRewriting.comp_app]
  rw [hgraph]

private def compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    Fin 6 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm endpointBound]

@[simp] private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
    (tokenTable width tokenCount inputStart inputFinish endpointBound depth : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) depth
        (#(⟨depth + 5, by omega⟩ : Fin (6 + depth)) :
          ArithmeticSemiterm Nat (6 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm endpointBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms]

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound0
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 0
        (#5 : ArithmeticSemiterm Nat 6) =
      closedShift 0 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 0)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound1
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 1
        (#6 : ArithmeticSemiterm Nat 7) =
      closedShift 1 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 1)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound2
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 2
        (#7 : ArithmeticSemiterm Nat 8) =
      closedShift 2 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 2)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound3
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 3
        (#8 : ArithmeticSemiterm Nat 9) =
      closedShift 3 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 3)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound4
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 4
        (#9 : ArithmeticSemiterm Nat 10) =
      closedShift 4 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 4)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound5
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 5
        (#10 : ArithmeticSemiterm Nat 11) =
      closedShift 5 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 5)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound6
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 6
        (#11 : ArithmeticSemiterm Nat 12) =
      closedShift 6 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 6)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound7
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 7
        (#12 : ArithmeticSemiterm Nat 13) =
      closedShift 7 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 7)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound8
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 8
        (#13 : ArithmeticSemiterm Nat 14) =
      closedShift 8 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 8)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound9
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 9
        (#14 : ArithmeticSemiterm Nat 15) =
      closedShift 9 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 9)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound10
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 10
        (#15 : ArithmeticSemiterm Nat 16) =
      closedShift 10 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 10)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound11
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 11
        (#16 : ArithmeticSemiterm Nat 17) =
      closedShift 11 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 11)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound12
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 12
        (#17 : ArithmeticSemiterm Nat 18) =
      closedShift 12 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 12)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound13
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 13
        (#18 : ArithmeticSemiterm Nat 19) =
      closedShift 13 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish endpointBound 13)

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawTerminal_rewriting
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 14 ▹
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawTerminal =
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish := by
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawTerminal
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [sourceSubstitutionQpow, Rew.q, Rew.q_bvar_zero, Rew.q_bvar_succ,
      Rew.comp_app, Rew.subst_bvar,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms,
      sourceSubstitutionLift, closedShift]

private theorem substitute_closedShift
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
            ((Rew.subst values).comp Rew.bShift) (closedShift k term) := by
              simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := inductionHypothesis _

private theorem compactCertificateNodePAImmediateFailureEndpointClosedFormula_eq_direct
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    compactCertificateNodePAImmediateFailureEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish coordinates =
      (Rewriting.emb (ξ := Nat)
          compactCertificateNodePAImmediateFailureEndpointGraphDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm inputStart,
          shortBinaryNumeralTerm inputFinish,
          shortBinaryNumeralTerm coordinates.inputBoundary,
          shortBinaryNumeralTerm coordinates.inputCount,
          shortBinaryNumeralTerm coordinates.inputBoundarySize,
          shortBinaryNumeralTerm coordinates.tailStart,
          shortBinaryNumeralTerm coordinates.tailFinish,
          shortBinaryNumeralTerm coordinates.tailBoundary,
          shortBinaryNumeralTerm coordinates.tailCount,
          shortBinaryNumeralTerm coordinates.tailBoundarySize,
          shortBinaryNumeralTerm coordinates.bodyStart,
          shortBinaryNumeralTerm coordinates.bodyFinish,
          shortBinaryNumeralTerm coordinates.bodyBoundary,
          shortBinaryNumeralTerm coordinates.bodyCount,
          shortBinaryNumeralTerm coordinates.bodyBoundarySize,
          shortBinaryNumeralTerm coordinates.paTag] := by
  rfl

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal_vector_alignment
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish ⇜
      ![shortBinaryNumeralTerm coordinates.paTag,
        shortBinaryNumeralTerm coordinates.bodyBoundarySize,
        shortBinaryNumeralTerm coordinates.bodyCount,
        shortBinaryNumeralTerm coordinates.bodyBoundary,
        shortBinaryNumeralTerm coordinates.bodyFinish,
        shortBinaryNumeralTerm coordinates.bodyStart,
        shortBinaryNumeralTerm coordinates.tailBoundarySize,
        shortBinaryNumeralTerm coordinates.tailCount,
        shortBinaryNumeralTerm coordinates.tailBoundary,
        shortBinaryNumeralTerm coordinates.tailFinish,
        shortBinaryNumeralTerm coordinates.tailStart,
        shortBinaryNumeralTerm coordinates.inputBoundarySize,
        shortBinaryNumeralTerm coordinates.inputCount,
        shortBinaryNumeralTerm coordinates.inputBoundary] =
      compactCertificateNodePAImmediateFailureEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rw [compactCertificateNodePAImmediateFailureEndpointClosedFormula_eq_direct]
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
  let witnessTerms : Fin 14 -> ValuationTerm :=
    ![shortBinaryNumeralTerm coordinates.paTag,
      shortBinaryNumeralTerm coordinates.bodyBoundarySize,
      shortBinaryNumeralTerm coordinates.bodyCount,
      shortBinaryNumeralTerm coordinates.bodyBoundary,
      shortBinaryNumeralTerm coordinates.bodyFinish,
      shortBinaryNumeralTerm coordinates.bodyStart,
      shortBinaryNumeralTerm coordinates.tailBoundarySize,
      shortBinaryNumeralTerm coordinates.tailCount,
      shortBinaryNumeralTerm coordinates.tailBoundary,
      shortBinaryNumeralTerm coordinates.tailFinish,
      shortBinaryNumeralTerm coordinates.tailStart,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundary]
  let rawTerms : Fin 19 -> ArithmeticSemiterm Nat 14 :=
    ![closedShift 14 (shortBinaryNumeralTerm tokenTable),
      closedShift 14 (shortBinaryNumeralTerm width),
      closedShift 14 (shortBinaryNumeralTerm tokenCount),
      closedShift 14 (shortBinaryNumeralTerm inputStart),
      closedShift 14 (shortBinaryNumeralTerm inputFinish),
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]
  let finalTerms : Fin 19 -> ValuationTerm :=
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm coordinates.inputBoundary,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.tailStart,
      shortBinaryNumeralTerm coordinates.tailFinish,
      shortBinaryNumeralTerm coordinates.tailBoundary,
      shortBinaryNumeralTerm coordinates.tailCount,
      shortBinaryNumeralTerm coordinates.tailBoundarySize,
      shortBinaryNumeralTerm coordinates.bodyStart,
      shortBinaryNumeralTerm coordinates.bodyFinish,
      shortBinaryNumeralTerm coordinates.bodyBoundary,
      shortBinaryNumeralTerm coordinates.bodyCount,
      shortBinaryNumeralTerm coordinates.bodyBoundarySize,
      shortBinaryNumeralTerm coordinates.paTag]
  change Rew.subst witnessTerms ▹
      ((Rewriting.emb (ξ := Nat)
        compactCertificateNodePAImmediateFailureEndpointGraphDef.val) ⇜ rawTerms) =
    (Rewriting.emb (ξ := Nat)
      compactCertificateNodePAImmediateFailureEndpointGraphDef.val) ⇜ finalTerms
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [witnessTerms, rawTerms, finalTerms, Rew.comp_app,
      Rew.subst_bvar, substitute_closedShift]

private theorem
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal_installed_alignment
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish ⇜
      (fun index : Fin 14 => shortBinaryNumeralTerm
        (![coordinates.paTag,
          coordinates.bodyBoundarySize,
          coordinates.bodyCount,
          coordinates.bodyBoundary,
          coordinates.bodyFinish,
          coordinates.bodyStart,
          coordinates.tailBoundarySize,
          coordinates.tailCount,
          coordinates.tailBoundary,
          coordinates.tailFinish,
          coordinates.tailStart,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
      compactCertificateNodePAImmediateFailureEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  have hvalueTerms :
      (fun index : Fin 14 => shortBinaryNumeralTerm
        (![coordinates.paTag,
          coordinates.bodyBoundarySize,
          coordinates.bodyCount,
          coordinates.bodyBoundary,
          coordinates.bodyFinish,
          coordinates.bodyStart,
          coordinates.tailBoundarySize,
          coordinates.tailCount,
          coordinates.tailBoundary,
          coordinates.tailFinish,
          coordinates.tailStart,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
        ![shortBinaryNumeralTerm coordinates.paTag,
          shortBinaryNumeralTerm coordinates.bodyBoundarySize,
          shortBinaryNumeralTerm coordinates.bodyCount,
          shortBinaryNumeralTerm coordinates.bodyBoundary,
          shortBinaryNumeralTerm coordinates.bodyFinish,
          shortBinaryNumeralTerm coordinates.bodyStart,
          shortBinaryNumeralTerm coordinates.tailBoundarySize,
          shortBinaryNumeralTerm coordinates.tailCount,
          shortBinaryNumeralTerm coordinates.tailBoundary,
          shortBinaryNumeralTerm coordinates.tailFinish,
          shortBinaryNumeralTerm coordinates.tailStart,
          shortBinaryNumeralTerm coordinates.inputBoundarySize,
          shortBinaryNumeralTerm coordinates.inputCount,
          shortBinaryNumeralTerm coordinates.inputBoundary] := by
    funext index
    fin_cases index <;> rfl
  rw [hvalueTerms]
  exact
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal_vector_alignment
      tokenTable width tokenCount inputStart inputFinish coordinates

/-- Exact syntactic alignment with the original fourteen bounded binders. -/
theorem compactCertificateNodePAImmediateFailureEndpointBoundedGraphClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish endpointBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm endpointBound) 14
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish) := by
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphClosedFormula
  rw [compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish endpointBound) 0 ▹
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawBody = _
  unfold compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawBody
  unfold explicitBoundedWitnessFormula
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound0,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound1,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound2,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound3,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound4,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound5,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound6,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound7,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound8,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound9,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound10,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound11,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound12,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceQpow_bound13,
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphSourceRawTerminal_rewriting]
  rfl

/-- Checked certificate for the original six-coordinate bounded graph.  The
fourteen local endpoint witnesses and their `<= endpointBound` guards are
installed directly before reusing the nineteen-coordinate endpoint terminal. -/
noncomputable def
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates)
    (hinputBoundary : coordinates.inputBoundary <= endpointBound)
    (hinputCount : coordinates.inputCount <= endpointBound)
    (hinputBoundarySize : coordinates.inputBoundarySize <= endpointBound)
    (htailStart : coordinates.tailStart <= endpointBound)
    (htailFinish : coordinates.tailFinish <= endpointBound)
    (htailBoundary : coordinates.tailBoundary <= endpointBound)
    (htailCount : coordinates.tailCount <= endpointBound)
    (htailBoundarySize : coordinates.tailBoundarySize <= endpointBound)
    (hbodyStart : coordinates.bodyStart <= endpointBound)
    (hbodyFinish : coordinates.bodyFinish <= endpointBound)
    (hbodyBoundary : coordinates.bodyBoundary <= endpointBound)
    (hbodyCount : coordinates.bodyCount <= endpointBound)
    (hbodyBoundarySize : coordinates.bodyBoundarySize <= endpointBound)
    (hpaTag : coordinates.paTag <= endpointBound)
    (hgraph : CompactCertificateNodePAImmediateFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    HybridCertificate
      (compactCertificateNodePAImmediateFailureEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish endpointBound) := by
  rw [compactCertificateNodePAImmediateFailureEndpointBoundedGraphClosedFormula_alignment]
  let values : Fin 14 -> Nat :=
    ![coordinates.paTag,
      coordinates.bodyBoundarySize,
      coordinates.bodyCount,
      coordinates.bodyBoundary,
      coordinates.bodyFinish,
      coordinates.bodyStart,
      coordinates.tailBoundarySize,
      coordinates.tailCount,
      coordinates.tailBoundary,
      coordinates.tailFinish,
      coordinates.tailStart,
      coordinates.inputBoundarySize,
      coordinates.inputCount,
      coordinates.inputBoundary]
  let rawCertificate :=
    compactCertificateNodePAImmediateFailureEndpointExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart inputFinish coordinates hgraph
  let terminal : HybridCertificate
      (compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal_installed_alignment
          tokenTable width tokenCount inputStart inputFinish coordinates).symm) rawCertificate
  exact buildExplicitBoundedWitnessHybridCertificate endpointBound
    (compactCertificateNodePAImmediateFailureEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish)
    values (by
      intro index
      fin_cases index
      · exact hpaTag
      · exact hbodyBoundarySize
      · exact hbodyCount
      · exact hbodyBoundary
      · exact hbodyFinish
      · exact hbodyStart
      · exact htailBoundarySize
      · exact htailCount
      · exact htailBoundary
      · exact htailFinish
      · exact htailStart
      · exact hinputBoundarySize
      · exact hinputCount
      · exact hinputBoundary) terminal

#print axioms compactCertificateNodePAImmediateFailureEndpointBoundedGraphClosedFormula_alignment
#print axioms compactCertificateNodePAImmediateFailureEndpointBoundedGraphExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedGraphExplicitHybridCertificate
