import integration.FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpointExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for the bounded outer-failure endpoint graph

The seven local endpoint coordinates are installed as explicit bounded
witnesses.  The terminal payload is the existing fourteen-coordinate outer
failure endpoint certificate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint
open FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpointExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

/-- The original eight-coordinate bounded formula with all public inputs
closed by short binary numerals. -/
def compactCertificateNodeOuterFailureEndpointBoundedGraphClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeOuterFailureEndpointBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm tailStart,
      shortBinaryNumeralTerm tailFinish,
      shortBinaryNumeralTerm endpointBound]

/-- The endpoint matrix below the seven original bounded existential layers.
The local coordinates retain the source de Bruijn order: tag is `#0` and
input boundary is `#6`. -/
private def compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat) :
    ArithmeticSemiformula Nat 7 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeOuterFailureEndpointGraphDef.val) ⇜
    ![closedShift 7 (shortBinaryNumeralTerm tokenTable),
      closedShift 7 (shortBinaryNumeralTerm width),
      closedShift 7 (shortBinaryNumeralTerm tokenCount),
      closedShift 7 (shortBinaryNumeralTerm inputStart),
      closedShift 7 (shortBinaryNumeralTerm inputFinish),
      closedShift 7 (shortBinaryNumeralTerm tailStart),
      closedShift 7 (shortBinaryNumeralTerm tailFinish),
      (#6 : ArithmeticSemiterm Nat 7),
      (#5 : ArithmeticSemiterm Nat 7),
      (#4 : ArithmeticSemiterm Nat 7),
      (#3 : ArithmeticSemiterm Nat 7),
      (#2 : ArithmeticSemiterm Nat 7),
      (#1 : ArithmeticSemiterm Nat 7),
      (#0 : ArithmeticSemiterm Nat 7)]

private def compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawTerminal :
    ArithmeticSemiformula Nat 15 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeOuterFailureEndpointGraphDef.val) ⇜
    ![(#7 : ArithmeticSemiterm Nat 15), #8, #9, #10, #11, #12, #13,
      #6, #5, #4, #3, #2, #1, #0]

private def compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawBody :
    ArithmeticSemiformula Nat 8 :=
  (((((((compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawTerminal.bexsLTSucc
      (#13 : ArithmeticSemiterm Nat 14)).bexsLTSucc
      (#12 : ArithmeticSemiterm Nat 13)).bexsLTSucc
      (#11 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 9)).bexsLTSucc
      (#7 : ArithmeticSemiterm Nat 8))

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
    compactCertificateNodeOuterFailureEndpointBoundedGraphDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat)
        compactCertificateNodeOuterFailureEndpointBoundedGraphDef.val =
      compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawBody := by
  have hgraph :
      (Rew.emb : Rew ℒₒᵣ Empty 15 Nat 15).comp
          (Rew.subst
            ![(#7 : ArithmeticSemiterm Empty 15), #8, #9, #10, #11,
              #12, #13, #6, #5, #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#7 : ArithmeticSemiterm Nat 15), #8, #9, #10, #11,
            #12, #13, #6, #5, #4, #3, #2, #1, #0]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphDef
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawBody
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawTerminal
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

private def compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    Fin 8 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm tailStart,
    shortBinaryNumeralTerm tailFinish,
    shortBinaryNumeralTerm endpointBound]

@[simp] private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound depth : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) depth
        (#(⟨depth + 7, by omega⟩ : Fin (8 + depth)) :
          ArithmeticSemiterm Nat (8 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm endpointBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms]

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound0
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 0
        (#7 : ArithmeticSemiterm Nat 8) =
      closedShift 0 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound 0)

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound1
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 1
        (#8 : ArithmeticSemiterm Nat 9) =
      closedShift 1 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound 1)

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound2
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 2
        (#9 : ArithmeticSemiterm Nat 10) =
      closedShift 2 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound 2)

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound3
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 3
        (#10 : ArithmeticSemiterm Nat 11) =
      closedShift 3 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound 3)

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound4
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 4
        (#11 : ArithmeticSemiterm Nat 12) =
      closedShift 4 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound 4)

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound5
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 5
        (#12 : ArithmeticSemiterm Nat 13) =
      closedShift 5 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound 5)

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound6
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 6
        (#13 : ArithmeticSemiterm Nat 14) =
      closedShift 6 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound 6)

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawTerminal_rewriting
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 7 ▹
      compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawTerminal =
    compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish tailStart tailFinish := by
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawTerminal
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [sourceSubstitutionQpow,
      Rew.q, Rew.q_bvar_zero, Rew.q_bvar_succ,
      Rew.comp_app, Rew.subst_bvar,
      compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms,
      sourceSubstitutionLift, closedShift]

private theorem compactCertificateNodeOuterFailureEndpointClosedFormula_eq_direct
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    compactCertificateNodeOuterFailureEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish tailStart tailFinish coordinates =
      (Rewriting.emb (ξ := Nat)
          compactCertificateNodeOuterFailureEndpointGraphDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm inputStart,
          shortBinaryNumeralTerm inputFinish,
          shortBinaryNumeralTerm tailStart,
          shortBinaryNumeralTerm tailFinish,
          shortBinaryNumeralTerm coordinates.inputBoundary,
          shortBinaryNumeralTerm coordinates.inputCount,
          shortBinaryNumeralTerm coordinates.inputBoundarySize,
          shortBinaryNumeralTerm coordinates.tailBoundary,
          shortBinaryNumeralTerm coordinates.tailCount,
          shortBinaryNumeralTerm coordinates.tailBoundarySize,
          shortBinaryNumeralTerm coordinates.tag] := by
  rfl

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal_vector_alignment
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish ⇜
      ![shortBinaryNumeralTerm coordinates.tag,
        shortBinaryNumeralTerm coordinates.tailBoundarySize,
        shortBinaryNumeralTerm coordinates.tailCount,
        shortBinaryNumeralTerm coordinates.tailBoundary,
        shortBinaryNumeralTerm coordinates.inputBoundarySize,
        shortBinaryNumeralTerm coordinates.inputCount,
        shortBinaryNumeralTerm coordinates.inputBoundary] =
      compactCertificateNodeOuterFailureEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish tailStart tailFinish coordinates := by
  rw [compactCertificateNodeOuterFailureEndpointClosedFormula_eq_direct]
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
  let witnessTerms : Fin 7 -> ValuationTerm :=
    ![shortBinaryNumeralTerm coordinates.tag,
      shortBinaryNumeralTerm coordinates.tailBoundarySize,
      shortBinaryNumeralTerm coordinates.tailCount,
      shortBinaryNumeralTerm coordinates.tailBoundary,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundary]
  let rawTerms : Fin 14 -> ArithmeticSemiterm Nat 7 :=
    ![closedShift 7 (shortBinaryNumeralTerm tokenTable),
      closedShift 7 (shortBinaryNumeralTerm width),
      closedShift 7 (shortBinaryNumeralTerm tokenCount),
      closedShift 7 (shortBinaryNumeralTerm inputStart),
      closedShift 7 (shortBinaryNumeralTerm inputFinish),
      closedShift 7 (shortBinaryNumeralTerm tailStart),
      closedShift 7 (shortBinaryNumeralTerm tailFinish),
      #6, #5, #4, #3, #2, #1, #0]
  let finalTerms : Fin 14 -> ValuationTerm :=
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm tailStart,
      shortBinaryNumeralTerm tailFinish,
      shortBinaryNumeralTerm coordinates.inputBoundary,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.tailBoundary,
      shortBinaryNumeralTerm coordinates.tailCount,
      shortBinaryNumeralTerm coordinates.tailBoundarySize,
      shortBinaryNumeralTerm coordinates.tag]
  change Rew.subst witnessTerms ▹
      ((Rewriting.emb (ξ := Nat)
        compactCertificateNodeOuterFailureEndpointGraphDef.val) ⇜ rawTerms) =
    (Rewriting.emb (ξ := Nat)
      compactCertificateNodeOuterFailureEndpointGraphDef.val) ⇜ finalTerms
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [witnessTerms, rawTerms, finalTerms, Rew.comp_app,
      Rew.subst_bvar, substitute_closedShift]

private theorem
    compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal_installed_alignment
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish ⇜
      (fun index : Fin 7 => shortBinaryNumeralTerm
        (![coordinates.tag,
          coordinates.tailBoundarySize,
          coordinates.tailCount,
          coordinates.tailBoundary,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
      compactCertificateNodeOuterFailureEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish tailStart tailFinish coordinates := by
  have hvalueTerms :
      (fun index : Fin 7 => shortBinaryNumeralTerm
        (![coordinates.tag,
          coordinates.tailBoundarySize,
          coordinates.tailCount,
          coordinates.tailBoundary,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
        ![shortBinaryNumeralTerm coordinates.tag,
          shortBinaryNumeralTerm coordinates.tailBoundarySize,
          shortBinaryNumeralTerm coordinates.tailCount,
          shortBinaryNumeralTerm coordinates.tailBoundary,
          shortBinaryNumeralTerm coordinates.inputBoundarySize,
          shortBinaryNumeralTerm coordinates.inputCount,
          shortBinaryNumeralTerm coordinates.inputBoundary] := by
    funext index
    fin_cases index <;> rfl
  rw [hvalueTerms]
  exact
    compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal_vector_alignment
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish coordinates

/-- Exact alignment of the original seven `<⁺ endpointBound` layers with the
public explicit bounded-witness presentation. -/
theorem compactCertificateNodeOuterFailureEndpointBoundedGraphClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    compactCertificateNodeOuterFailureEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm endpointBound) 7
        (compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish) := by
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphClosedFormula
  rw [compactCertificateNodeOuterFailureEndpointBoundedGraphDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactCertificateNodeOuterFailureEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound) 0 ▹
      compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawBody = _
  unfold compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawBody
  unfold explicitBoundedWitnessFormula
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound0,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound1,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound2,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound3,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound4,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound5,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceQpow_bound6,
    compactCertificateNodeOuterFailureEndpointBoundedGraphSourceRawTerminal_rewriting]
  rfl

/-- Checked hybrid certificate for the original eight-coordinate bounded
graph.  Each local endpoint coordinate and its guard is supplied explicitly;
the terminal is the existing fourteen-coordinate endpoint certificate. -/
noncomputable def
    compactCertificateNodeOuterFailureEndpointBoundedGraphExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates)
    (hinputBoundary : coordinates.inputBoundary ≤ endpointBound)
    (hinputCount : coordinates.inputCount ≤ endpointBound)
    (hinputBoundarySize : coordinates.inputBoundarySize ≤ endpointBound)
    (htailBoundary : coordinates.tailBoundary ≤ endpointBound)
    (htailCount : coordinates.tailCount ≤ endpointBound)
    (htailBoundarySize : coordinates.tailBoundarySize ≤ endpointBound)
    (htag : coordinates.tag ≤ endpointBound)
    (hgraph : CompactCertificateNodeOuterFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish coordinates) :
    HybridCertificate
      (compactCertificateNodeOuterFailureEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound) := by
  rw [compactCertificateNodeOuterFailureEndpointBoundedGraphClosedFormula_alignment]
  let values : Fin 7 -> Nat :=
    ![coordinates.tag,
      coordinates.tailBoundarySize,
      coordinates.tailCount,
      coordinates.tailBoundary,
      coordinates.inputBoundarySize,
      coordinates.inputCount,
      coordinates.inputBoundary]
  let rawCertificate :=
    compactCertificateNodeOuterFailureEndpointExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish coordinates hgraph
  let terminal : HybridCertificate
      (compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal_installed_alignment
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish coordinates).symm) rawCertificate
  exact buildExplicitBoundedWitnessHybridCertificate endpointBound
    (compactCertificateNodeOuterFailureEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish tailStart tailFinish)
    values (by
      intro index
      fin_cases index
      · exact htag
      · exact htailBoundarySize
      · exact htailCount
      · exact htailBoundary
      · exact hinputBoundarySize
      · exact hinputCount
      · exact hinputBoundary) terminal

#print axioms compactCertificateNodeOuterFailureEndpointBoundedGraphClosedFormula_alignment
#print axioms compactCertificateNodeOuterFailureEndpointBoundedGraphExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedGraphExplicitHybridCertificate
