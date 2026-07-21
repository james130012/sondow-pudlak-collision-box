import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpointExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

/-!
# Explicit hybrid certificate for the bounded fixed-PA graph

The fifteen endpoint coordinates are installed as genuine bounded-existential
witnesses.  The terminal is the existing certificate for the original
twenty-five-coordinate endpoint graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpointExplicitHybridCertificate
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

/-- The original bounded graph with its eleven public inputs closed. -/
def compactCertificateNodeFixedPAEndpointBoundedGraphClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeFixedPAEndpointBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm axiomStart,
      shortBinaryNumeralTerm axiomFinish,
      shortBinaryNumeralTerm suffixStart,
      shortBinaryNumeralTerm suffixFinish,
      shortBinaryNumeralTerm certificateTag,
      shortBinaryNumeralTerm endpointBound]

/-- The original endpoint matrix beneath all fifteen bounded binders. -/
private def compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat) :
    ArithmeticSemiformula Nat 15 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeFixedPAEndpointGraphDef.val) ⇜
    ![closedShift 15 (shortBinaryNumeralTerm tokenTable),
      closedShift 15 (shortBinaryNumeralTerm width),
      closedShift 15 (shortBinaryNumeralTerm tokenCount),
      closedShift 15 (shortBinaryNumeralTerm inputStart),
      closedShift 15 (shortBinaryNumeralTerm inputFinish),
      closedShift 15 (shortBinaryNumeralTerm axiomStart),
      closedShift 15 (shortBinaryNumeralTerm axiomFinish),
      closedShift 15 (shortBinaryNumeralTerm suffixStart),
      closedShift 15 (shortBinaryNumeralTerm suffixFinish),
      closedShift 15 (shortBinaryNumeralTerm certificateTag),
      (#14 : ArithmeticSemiterm Nat 15), #13, #12, #11, #10, #9, #8,
      #7, #6, #5, #4, #3, #2, #1, #0]

/-- The unclosed terminal has ten public coordinates and fifteen local
coordinates, hence source arity twenty-six. -/
private def compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal :
    ArithmeticSemiformula Nat 26 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeFixedPAEndpointGraphDef.val) ⇜
    ![(#15 : ArithmeticSemiterm Nat 26), #16, #17, #18, #19,
      #20, #21, #22, #23, #24,
      #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

/-- Literal source presentation of the original fifteen `<⁺ endpointBound`
binders.  The endpoint-bound coordinate is `#24` at arity twenty-five down to
`#10` at arity eleven. -/
private def compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawBody :
  ArithmeticSemiformula Nat 11 :=
  (((((((((((((((compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal.bexsLTSucc
      (#24 : ArithmeticSemiterm Nat 25)).bexsLTSucc
      (#23 : ArithmeticSemiterm Nat 24)).bexsLTSucc
      (#22 : ArithmeticSemiterm Nat 23)).bexsLTSucc
      (#21 : ArithmeticSemiterm Nat 22)).bexsLTSucc
      (#20 : ArithmeticSemiterm Nat 21)).bexsLTSucc
      (#19 : ArithmeticSemiterm Nat 20)).bexsLTSucc
      (#18 : ArithmeticSemiterm Nat 19)).bexsLTSucc
      (#17 : ArithmeticSemiterm Nat 18)).bexsLTSucc
      (#16 : ArithmeticSemiterm Nat 17)).bexsLTSucc
      (#15 : ArithmeticSemiterm Nat 16)).bexsLTSucc
      (#14 : ArithmeticSemiterm Nat 15)).bexsLTSucc
      (#13 : ArithmeticSemiterm Nat 14)).bexsLTSucc
      (#12 : ArithmeticSemiterm Nat 13)).bexsLTSucc
      (#11 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 11))

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat)
        compactCertificateNodeFixedPAEndpointBoundedGraphDef.val =
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawBody := by
  have hgraph :
      (Rew.emb : Rew ℒₒᵣ Empty 26 Nat 26).comp
          (Rew.subst
            ![(#15 : ArithmeticSemiterm Empty 26), #16, #17, #18, #19,
              #20, #21, #22, #23, #24,
              #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#15 : ArithmeticSemiterm Nat 26), #16, #17, #18, #19,
            #20, #21, #22, #23, #24,
            #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 25 Nat 25) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphDef
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawBody
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal
  simp [rewriting_bexsLTSucc, rewriting_embeddedFormulaSubstitution,
    Rew.q_bvar_zero, Rew.q_bvar_succ,
    ← TransitiveRewriting.comp_app]
  rw [hgraph]

private def compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat) :
    Fin 11 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm axiomStart,
    shortBinaryNumeralTerm axiomFinish,
    shortBinaryNumeralTerm suffixStart,
    shortBinaryNumeralTerm suffixFinish,
    shortBinaryNumeralTerm certificateTag,
    shortBinaryNumeralTerm endpointBound]

@[simp] private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound depth : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) depth
        (#(⟨depth + 10, by omega⟩ : Fin (11 + depth)) :
          ArithmeticSemiterm Nat (11 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm endpointBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms]

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound0
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 0
        (#10 : ArithmeticSemiterm Nat 11) =
      closedShift 0 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 0)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound1
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 1
        (#11 : ArithmeticSemiterm Nat 12) =
      closedShift 1 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 1)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound2
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 2
        (#12 : ArithmeticSemiterm Nat 13) =
      closedShift 2 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 2)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound3
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 3
        (#13 : ArithmeticSemiterm Nat 14) =
      closedShift 3 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 3)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound4
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 4
        (#14 : ArithmeticSemiterm Nat 15) =
      closedShift 4 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 4)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound5
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 5
        (#15 : ArithmeticSemiterm Nat 16) =
      closedShift 5 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 5)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound6
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 6
        (#16 : ArithmeticSemiterm Nat 17) =
      closedShift 6 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 6)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound7
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 7
        (#17 : ArithmeticSemiterm Nat 18) =
      closedShift 7 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 7)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound8
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 8
        (#18 : ArithmeticSemiterm Nat 19) =
      closedShift 8 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 8)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound9
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 9
        (#19 : ArithmeticSemiterm Nat 20) =
      closedShift 9 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 9)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound10
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 10
        (#20 : ArithmeticSemiterm Nat 21) =
      closedShift 10 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 10)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound11
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 11
        (#21 : ArithmeticSemiterm Nat 22) =
      closedShift 11 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 11)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound12
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 12
        (#22 : ArithmeticSemiterm Nat 23) =
      closedShift 12 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 12)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound13
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 13
        (#23 : ArithmeticSemiterm Nat 24) =
      closedShift 13 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 13)

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound14
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 14
        (#24 : ArithmeticSemiterm Nat 25) =
      closedShift 14 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag endpointBound 14)

set_option maxHeartbeats 800000 in
private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal_terms_rewriting
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    (sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 15) ∘
      (![(#15 : ArithmeticSemiterm Nat 26), #16, #17, #18, #19,
        #20, #21, #22, #23, #24,
        #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1,
        #0] : Fin 25 -> ArithmeticSemiterm Nat 26) =
      (![closedShift 15 (shortBinaryNumeralTerm tokenTable),
        closedShift 15 (shortBinaryNumeralTerm width),
        closedShift 15 (shortBinaryNumeralTerm tokenCount),
        closedShift 15 (shortBinaryNumeralTerm inputStart),
        closedShift 15 (shortBinaryNumeralTerm inputFinish),
        closedShift 15 (shortBinaryNumeralTerm axiomStart),
        closedShift 15 (shortBinaryNumeralTerm axiomFinish),
        closedShift 15 (shortBinaryNumeralTerm suffixStart),
        closedShift 15 (shortBinaryNumeralTerm suffixFinish),
        closedShift 15 (shortBinaryNumeralTerm certificateTag),
        (#14 : ArithmeticSemiterm Nat 15), #13, #12, #11, #10, #9, #8, #7,
        #6, #5, #4, #3, #2, #1, #0] :
          Fin 25 -> ArithmeticSemiterm Nat 15) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, sourceSubstitutionQpow, Rew.q,
      Rew.q_bvar_zero, Rew.q_bvar_succ, Rew.comp_app, Rew.subst_bvar,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms,
      sourceSubstitutionLift, closedShift]

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal_rewriting
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 15 ▹
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal =
    compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag := by
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  rw [compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal_terms_rewriting]

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

private theorem compactCertificateNodeFixedPAEndpointClosedFormula_eq_direct
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    compactCertificateNodeFixedPAEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag coordinates =
      (Rewriting.emb (ξ := Nat)
          compactCertificateNodeFixedPAEndpointGraphDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm inputStart,
          shortBinaryNumeralTerm inputFinish,
          shortBinaryNumeralTerm axiomStart,
          shortBinaryNumeralTerm axiomFinish,
          shortBinaryNumeralTerm suffixStart,
          shortBinaryNumeralTerm suffixFinish,
          shortBinaryNumeralTerm certificateTag,
          shortBinaryNumeralTerm coordinates.inputBoundary,
          shortBinaryNumeralTerm coordinates.inputCount,
          shortBinaryNumeralTerm coordinates.inputBoundarySize,
          shortBinaryNumeralTerm coordinates.tailStart,
          shortBinaryNumeralTerm coordinates.tailFinish,
          shortBinaryNumeralTerm coordinates.tailBoundary,
          shortBinaryNumeralTerm coordinates.tailCount,
          shortBinaryNumeralTerm coordinates.tailBoundarySize,
          shortBinaryNumeralTerm coordinates.axiomBoundary,
          shortBinaryNumeralTerm coordinates.axiomCount,
          shortBinaryNumeralTerm coordinates.axiomBoundarySize,
          shortBinaryNumeralTerm coordinates.suffixBoundary,
          shortBinaryNumeralTerm coordinates.suffixCount,
          shortBinaryNumeralTerm coordinates.suffixBoundarySize,
          shortBinaryNumeralTerm coordinates.paTag] := by
  rfl

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal_vector_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag ⇜
      ![shortBinaryNumeralTerm coordinates.paTag,
        shortBinaryNumeralTerm coordinates.suffixBoundarySize,
        shortBinaryNumeralTerm coordinates.suffixCount,
        shortBinaryNumeralTerm coordinates.suffixBoundary,
        shortBinaryNumeralTerm coordinates.axiomBoundarySize,
        shortBinaryNumeralTerm coordinates.axiomCount,
        shortBinaryNumeralTerm coordinates.axiomBoundary,
        shortBinaryNumeralTerm coordinates.tailBoundarySize,
        shortBinaryNumeralTerm coordinates.tailCount,
        shortBinaryNumeralTerm coordinates.tailBoundary,
        shortBinaryNumeralTerm coordinates.tailFinish,
        shortBinaryNumeralTerm coordinates.tailStart,
        shortBinaryNumeralTerm coordinates.inputBoundarySize,
        shortBinaryNumeralTerm coordinates.inputCount,
        shortBinaryNumeralTerm coordinates.inputBoundary] =
      compactCertificateNodeFixedPAEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag coordinates := by
  rw [compactCertificateNodeFixedPAEndpointClosedFormula_eq_direct]
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
  let witnessTerms : Fin 15 -> ValuationTerm :=
    ![shortBinaryNumeralTerm coordinates.paTag,
      shortBinaryNumeralTerm coordinates.suffixBoundarySize,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm coordinates.suffixBoundary,
      shortBinaryNumeralTerm coordinates.axiomBoundarySize,
      shortBinaryNumeralTerm coordinates.axiomCount,
      shortBinaryNumeralTerm coordinates.axiomBoundary,
      shortBinaryNumeralTerm coordinates.tailBoundarySize,
      shortBinaryNumeralTerm coordinates.tailCount,
      shortBinaryNumeralTerm coordinates.tailBoundary,
      shortBinaryNumeralTerm coordinates.tailFinish,
      shortBinaryNumeralTerm coordinates.tailStart,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundary]
  let rawTerms : Fin 25 -> ArithmeticSemiterm Nat 15 :=
    ![closedShift 15 (shortBinaryNumeralTerm tokenTable),
      closedShift 15 (shortBinaryNumeralTerm width),
      closedShift 15 (shortBinaryNumeralTerm tokenCount),
      closedShift 15 (shortBinaryNumeralTerm inputStart),
      closedShift 15 (shortBinaryNumeralTerm inputFinish),
      closedShift 15 (shortBinaryNumeralTerm axiomStart),
      closedShift 15 (shortBinaryNumeralTerm axiomFinish),
      closedShift 15 (shortBinaryNumeralTerm suffixStart),
      closedShift 15 (shortBinaryNumeralTerm suffixFinish),
      closedShift 15 (shortBinaryNumeralTerm certificateTag),
      #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]
  let finalTerms : Fin 25 -> ValuationTerm :=
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm axiomStart,
      shortBinaryNumeralTerm axiomFinish,
      shortBinaryNumeralTerm suffixStart,
      shortBinaryNumeralTerm suffixFinish,
      shortBinaryNumeralTerm certificateTag,
      shortBinaryNumeralTerm coordinates.inputBoundary,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.tailStart,
      shortBinaryNumeralTerm coordinates.tailFinish,
      shortBinaryNumeralTerm coordinates.tailBoundary,
      shortBinaryNumeralTerm coordinates.tailCount,
      shortBinaryNumeralTerm coordinates.tailBoundarySize,
      shortBinaryNumeralTerm coordinates.axiomBoundary,
      shortBinaryNumeralTerm coordinates.axiomCount,
      shortBinaryNumeralTerm coordinates.axiomBoundarySize,
      shortBinaryNumeralTerm coordinates.suffixBoundary,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm coordinates.suffixBoundarySize,
      shortBinaryNumeralTerm coordinates.paTag]
  change Rew.subst witnessTerms ▹
      ((Rewriting.emb (ξ := Nat)
        compactCertificateNodeFixedPAEndpointGraphDef.val) ⇜ rawTerms) =
    (Rewriting.emb (ξ := Nat)
      compactCertificateNodeFixedPAEndpointGraphDef.val) ⇜ finalTerms
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [witnessTerms, rawTerms, finalTerms, Rew.comp_app,
      Rew.subst_bvar, substitute_closedShift]

private theorem
    compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal_installed_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag ⇜
      (fun index : Fin 15 => shortBinaryNumeralTerm
        (![coordinates.paTag,
          coordinates.suffixBoundarySize,
          coordinates.suffixCount,
          coordinates.suffixBoundary,
          coordinates.axiomBoundarySize,
          coordinates.axiomCount,
          coordinates.axiomBoundary,
          coordinates.tailBoundarySize,
          coordinates.tailCount,
          coordinates.tailBoundary,
          coordinates.tailFinish,
          coordinates.tailStart,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
      compactCertificateNodeFixedPAEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag coordinates := by
  have hvalueTerms :
      (fun index : Fin 15 => shortBinaryNumeralTerm
        (![coordinates.paTag,
          coordinates.suffixBoundarySize,
          coordinates.suffixCount,
          coordinates.suffixBoundary,
          coordinates.axiomBoundarySize,
          coordinates.axiomCount,
          coordinates.axiomBoundary,
          coordinates.tailBoundarySize,
          coordinates.tailCount,
          coordinates.tailBoundary,
          coordinates.tailFinish,
          coordinates.tailStart,
          coordinates.inputBoundarySize,
          coordinates.inputCount,
          coordinates.inputBoundary] index)) =
        ![shortBinaryNumeralTerm coordinates.paTag,
          shortBinaryNumeralTerm coordinates.suffixBoundarySize,
          shortBinaryNumeralTerm coordinates.suffixCount,
          shortBinaryNumeralTerm coordinates.suffixBoundary,
          shortBinaryNumeralTerm coordinates.axiomBoundarySize,
          shortBinaryNumeralTerm coordinates.axiomCount,
          shortBinaryNumeralTerm coordinates.axiomBoundary,
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
    compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal_vector_alignment
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates

/-- Exact syntactic alignment with the original fifteen bounded binders. -/
theorem compactCertificateNodeFixedPAEndpointBoundedGraphClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    compactCertificateNodeFixedPAEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm endpointBound) 15
        (compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag) := by
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphClosedFormula
  rw [compactCertificateNodeFixedPAEndpointBoundedGraphDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactCertificateNodeFixedPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 0 ▹
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawBody = _
  unfold compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawBody
  unfold explicitBoundedWitnessFormula
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound0,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound1,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound2,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound3,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound4,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound5,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound6,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound7,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound8,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound9,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound10,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound11,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound12,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound13,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceQpow_bound14,
      compactCertificateNodeFixedPAEndpointBoundedGraphSourceRawTerminal_rewriting]
  rfl

/-- Checked certificate for the original eleven-coordinate bounded graph.  The
fifteen local endpoint witnesses and their `<= endpointBound` guards are
installed directly before reusing the twenty-five-coordinate endpoint terminal. -/
noncomputable def
    compactCertificateNodeFixedPAEndpointBoundedGraphExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates)
    (hinputBoundary : coordinates.inputBoundary <= endpointBound)
    (hinputCount : coordinates.inputCount <= endpointBound)
    (hinputBoundarySize : coordinates.inputBoundarySize <= endpointBound)
    (htailStart : coordinates.tailStart <= endpointBound)
    (htailFinish : coordinates.tailFinish <= endpointBound)
    (htailBoundary : coordinates.tailBoundary <= endpointBound)
    (htailCount : coordinates.tailCount <= endpointBound)
    (htailBoundarySize : coordinates.tailBoundarySize <= endpointBound)
    (haxiomBoundary : coordinates.axiomBoundary <= endpointBound)
    (haxiomCount : coordinates.axiomCount <= endpointBound)
    (haxiomBoundarySize : coordinates.axiomBoundarySize <= endpointBound)
    (hsuffixBoundary : coordinates.suffixBoundary <= endpointBound)
    (hsuffixCount : coordinates.suffixCount <= endpointBound)
    (hsuffixBoundarySize : coordinates.suffixBoundarySize <= endpointBound)
    (hpaTag : coordinates.paTag <= endpointBound)
    (hgraph : CompactCertificateNodeFixedPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates) :
    HybridCertificate
      (compactCertificateNodeFixedPAEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) := by
  rw [compactCertificateNodeFixedPAEndpointBoundedGraphClosedFormula_alignment]
  let values : Fin 15 -> Nat :=
    ![coordinates.paTag,
      coordinates.suffixBoundarySize,
      coordinates.suffixCount,
      coordinates.suffixBoundary,
      coordinates.axiomBoundarySize,
      coordinates.axiomCount,
      coordinates.axiomBoundary,
      coordinates.tailBoundarySize,
      coordinates.tailCount,
      coordinates.tailBoundary,
      coordinates.tailFinish,
      coordinates.tailStart,
      coordinates.inputBoundarySize,
      coordinates.inputCount,
      coordinates.inputBoundary]
  let rawCertificate :=
    compactCertificateNodeFixedPAEndpointExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates hgraph
  let terminal : HybridCertificate
      (compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal_installed_alignment
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag coordinates).symm)
      rawCertificate
  exact buildExplicitBoundedWitnessHybridCertificate endpointBound
    (compactCertificateNodeFixedPAEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag)
    values (by
      intro index
      fin_cases index
      · exact hpaTag
      · exact hsuffixBoundarySize
      · exact hsuffixCount
      · exact hsuffixBoundary
      · exact haxiomBoundarySize
      · exact haxiomCount
      · exact haxiomBoundary
      · exact htailBoundarySize
      · exact htailCount
      · exact htailBoundary
      · exact htailFinish
      · exact htailStart
      · exact hinputBoundarySize
      · exact hinputCount
      · exact hinputBoundary) terminal

#print axioms compactCertificateNodeFixedPAEndpointBoundedGraphClosedFormula_alignment
#print axioms compactCertificateNodeFixedPAEndpointBoundedGraphExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedGraphExplicitHybridCertificate
