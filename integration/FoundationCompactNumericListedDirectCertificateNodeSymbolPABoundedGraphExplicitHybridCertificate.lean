import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpointExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

/-!
# Explicit hybrid certificate for the bounded symbol-PA graph

The seventeen endpoint coordinates are installed as genuine bounded-existential
witnesses.  The terminal is the existing certificate for the original
twenty-seven-coordinate endpoint graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpointExplicitHybridCertificate
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
def compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSymbolPAEndpointBoundedGraphDef.val) ⇜
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

/-- The original endpoint matrix beneath all seventeen bounded binders. -/
private def compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat) :
    ArithmeticSemiformula Nat 17 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSymbolPAEndpointGraphDef.val) ⇜
    ![closedShift 17 (shortBinaryNumeralTerm tokenTable),
      closedShift 17 (shortBinaryNumeralTerm width),
      closedShift 17 (shortBinaryNumeralTerm tokenCount),
      closedShift 17 (shortBinaryNumeralTerm inputStart),
      closedShift 17 (shortBinaryNumeralTerm inputFinish),
      closedShift 17 (shortBinaryNumeralTerm axiomStart),
      closedShift 17 (shortBinaryNumeralTerm axiomFinish),
      closedShift 17 (shortBinaryNumeralTerm suffixStart),
      closedShift 17 (shortBinaryNumeralTerm suffixFinish),
      closedShift 17 (shortBinaryNumeralTerm certificateTag),
      (#16 : ArithmeticSemiterm Nat 17), #15, #14, #13, #12, #11, #10,
      #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

/-- The unclosed terminal has ten public coordinates and seventeen local
coordinates, hence source arity twenty-eight. -/
private def compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal :
    ArithmeticSemiformula Nat 28 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSymbolPAEndpointGraphDef.val) ⇜
    ![(#17 : ArithmeticSemiterm Nat 28), #18, #19, #20, #21,
      #22, #23, #24, #25, #26,
      #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
      #2, #1, #0]

/-- Literal source presentation of the original seventeen `<⁺ endpointBound`
binders.  The endpoint-bound coordinate is `#26` at arity twenty-seven down to
`#10` at arity eleven. -/
private def compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawBody :
  ArithmeticSemiformula Nat 11 :=
  (((((((((((((((((compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal.bexsLTSucc
      (#26 : ArithmeticSemiterm Nat 27)).bexsLTSucc
      (#25 : ArithmeticSemiterm Nat 26)).bexsLTSucc
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
    compactCertificateNodeSymbolPAEndpointBoundedGraphDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat)
        compactCertificateNodeSymbolPAEndpointBoundedGraphDef.val =
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawBody := by
  have hgraph :
      (Rew.emb : Rew ℒₒᵣ Empty 28 Nat 28).comp
          (Rew.subst
            ![(#17 : ArithmeticSemiterm Empty 28), #18, #19, #20, #21,
              #22, #23, #24, #25, #26,
              #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5,
              #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#17 : ArithmeticSemiterm Nat 28), #18, #19, #20, #21,
            #22, #23, #24, #25, #26,
            #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5,
            #4, #3, #2, #1, #0]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 27 Nat 27) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphDef
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawBody
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal
  simp [rewriting_bexsLTSucc, rewriting_embeddedFormulaSubstitution,
    Rew.q_bvar_zero, Rew.q_bvar_succ,
    ← TransitiveRewriting.comp_app]
  rw [hgraph]

private def compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
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
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound depth : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) depth
        (#(⟨depth + 10, by omega⟩ : Fin (11 + depth)) :
          ArithmeticSemiterm Nat (11 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm endpointBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms]

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound0
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 0
        (#10 : ArithmeticSemiterm Nat 11) =
      closedShift 0 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 0)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound1
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 1
        (#11 : ArithmeticSemiterm Nat 12) =
      closedShift 1 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 1)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound2
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 2
        (#12 : ArithmeticSemiterm Nat 13) =
      closedShift 2 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 2)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound3
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 3
        (#13 : ArithmeticSemiterm Nat 14) =
      closedShift 3 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 3)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound4
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 4
        (#14 : ArithmeticSemiterm Nat 15) =
      closedShift 4 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 4)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound5
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 5
        (#15 : ArithmeticSemiterm Nat 16) =
      closedShift 5 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 5)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound6
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 6
        (#16 : ArithmeticSemiterm Nat 17) =
      closedShift 6 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 6)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound7
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 7
        (#17 : ArithmeticSemiterm Nat 18) =
      closedShift 7 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 7)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound8
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 8
        (#18 : ArithmeticSemiterm Nat 19) =
      closedShift 8 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 8)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound9
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 9
        (#19 : ArithmeticSemiterm Nat 20) =
      closedShift 9 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 9)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound10
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 10
        (#20 : ArithmeticSemiterm Nat 21) =
      closedShift 10 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 10)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound11
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 11
        (#21 : ArithmeticSemiterm Nat 22) =
      closedShift 11 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 11)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound12
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 12
        (#22 : ArithmeticSemiterm Nat 23) =
      closedShift 12 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 12)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound13
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 13
        (#23 : ArithmeticSemiterm Nat 24) =
      closedShift 13 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound 13)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound14
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 14
        (#24 : ArithmeticSemiterm Nat 25) =
      closedShift 14 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag endpointBound 14)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound15
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 15
        (#25 : ArithmeticSemiterm Nat 26) =
      closedShift 15 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag endpointBound 15)

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound16
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 16
        (#26 : ArithmeticSemiterm Nat 27) =
      closedShift 16 (shortBinaryNumeralTerm endpointBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_endpointBound
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag endpointBound 16)

set_option maxHeartbeats 800000 in
private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal_terms_rewriting
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    (sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 17) ∘
      (![(#17 : ArithmeticSemiterm Nat 28), #18, #19, #20, #21,
        #22, #23, #24, #25, #26,
        #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
        #2, #1, #0] : Fin 27 -> ArithmeticSemiterm Nat 28) =
      (![closedShift 17 (shortBinaryNumeralTerm tokenTable),
        closedShift 17 (shortBinaryNumeralTerm width),
        closedShift 17 (shortBinaryNumeralTerm tokenCount),
        closedShift 17 (shortBinaryNumeralTerm inputStart),
        closedShift 17 (shortBinaryNumeralTerm inputFinish),
        closedShift 17 (shortBinaryNumeralTerm axiomStart),
        closedShift 17 (shortBinaryNumeralTerm axiomFinish),
        closedShift 17 (shortBinaryNumeralTerm suffixStart),
        closedShift 17 (shortBinaryNumeralTerm suffixFinish),
        closedShift 17 (shortBinaryNumeralTerm certificateTag),
        (#16 : ArithmeticSemiterm Nat 17), #15, #14, #13, #12, #11, #10,
        #9, #8, #7, #6, #5, #4, #3, #2, #1, #0] :
          Fin 27 -> ArithmeticSemiterm Nat 17) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, sourceSubstitutionQpow, Rew.q,
      Rew.q_bvar_zero, Rew.q_bvar_succ, Rew.comp_app, Rew.subst_bvar,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms,
      sourceSubstitutionLift, closedShift]

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal_rewriting
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound) 17 ▹
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal =
    compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag := by
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  rw [compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal_terms_rewriting]

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

private theorem compactCertificateNodeSymbolPAEndpointClosedFormula_eq_direct
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    compactCertificateNodeSymbolPAEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag coordinates =
      (Rewriting.emb (ξ := Nat)
          compactCertificateNodeSymbolPAEndpointGraphDef.val) ⇜
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
          shortBinaryNumeralTerm coordinates.paTag,
          shortBinaryNumeralTerm coordinates.arity,
          shortBinaryNumeralTerm coordinates.symbolCode] := by
  rfl

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal_vector_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag ⇜
      ![shortBinaryNumeralTerm coordinates.symbolCode,
        shortBinaryNumeralTerm coordinates.arity,
        shortBinaryNumeralTerm coordinates.paTag,
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
      compactCertificateNodeSymbolPAEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag coordinates := by
  rw [compactCertificateNodeSymbolPAEndpointClosedFormula_eq_direct]
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
  let witnessTerms : Fin 17 -> ValuationTerm :=
    ![shortBinaryNumeralTerm coordinates.symbolCode,
      shortBinaryNumeralTerm coordinates.arity,
      shortBinaryNumeralTerm coordinates.paTag,
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
  let rawTerms : Fin 27 -> ArithmeticSemiterm Nat 17 :=
    ![closedShift 17 (shortBinaryNumeralTerm tokenTable),
      closedShift 17 (shortBinaryNumeralTerm width),
      closedShift 17 (shortBinaryNumeralTerm tokenCount),
      closedShift 17 (shortBinaryNumeralTerm inputStart),
      closedShift 17 (shortBinaryNumeralTerm inputFinish),
      closedShift 17 (shortBinaryNumeralTerm axiomStart),
      closedShift 17 (shortBinaryNumeralTerm axiomFinish),
      closedShift 17 (shortBinaryNumeralTerm suffixStart),
      closedShift 17 (shortBinaryNumeralTerm suffixFinish),
      closedShift 17 (shortBinaryNumeralTerm certificateTag),
      #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
      #2, #1, #0]
  let finalTerms : Fin 27 -> ValuationTerm :=
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
      shortBinaryNumeralTerm coordinates.paTag,
      shortBinaryNumeralTerm coordinates.arity,
      shortBinaryNumeralTerm coordinates.symbolCode]
  change Rew.subst witnessTerms ▹
      ((Rewriting.emb (ξ := Nat)
        compactCertificateNodeSymbolPAEndpointGraphDef.val) ⇜ rawTerms) =
    (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSymbolPAEndpointGraphDef.val) ⇜ finalTerms
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [witnessTerms, rawTerms, finalTerms, Rew.comp_app,
      Rew.subst_bvar, substitute_closedShift]

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal_installed_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag ⇜
      (fun index : Fin 17 => shortBinaryNumeralTerm
        (![coordinates.symbolCode,
          coordinates.arity,
          coordinates.paTag,
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
      compactCertificateNodeSymbolPAEndpointClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag coordinates := by
  have hvalueTerms :
      (fun index : Fin 17 => shortBinaryNumeralTerm
        (![coordinates.symbolCode,
          coordinates.arity,
          coordinates.paTag,
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
        ![shortBinaryNumeralTerm coordinates.symbolCode,
          shortBinaryNumeralTerm coordinates.arity,
          shortBinaryNumeralTerm coordinates.paTag,
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
    compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal_vector_alignment
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates

/-- Exact syntactic alignment with the original seventeen bounded binders. -/
theorem compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm endpointBound) 17
        (compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag) := by
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula
  rw [compactCertificateNodeSymbolPAEndpointBoundedGraphDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactCertificateNodeSymbolPAEndpointBoundedGraphSourceTerms
          tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) 0 ▹
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawBody = _
  unfold compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawBody
  unfold explicitBoundedWitnessFormula
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound0,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound1,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound2,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound3,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound4,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound5,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound6,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound7,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound8,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound9,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound10,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound11,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound12,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound13,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound14,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound15,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceQpow_bound16,
      compactCertificateNodeSymbolPAEndpointBoundedGraphSourceRawTerminal_rewriting]
  rfl

/-- Checked certificate for the original eleven-coordinate bounded graph.  The
seventeen local endpoint witnesses and their `<= endpointBound` guards are
installed directly before reusing the twenty-seven-coordinate endpoint terminal. -/
noncomputable def
    compactCertificateNodeSymbolPAEndpointBoundedGraphExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates)
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
    (harity : coordinates.arity <= endpointBound)
    (hsymbolCode : coordinates.symbolCode <= endpointBound)
    (hgraph : CompactCertificateNodeSymbolPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates) :
    HybridCertificate
      (compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish certificateTag endpointBound) := by
  rw [compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula_alignment]
  let values : Fin 17 -> Nat :=
    ![coordinates.symbolCode,
      coordinates.arity,
      coordinates.paTag,
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
    compactCertificateNodeSymbolPAEndpointExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates hgraph
  let terminal : HybridCertificate
      (compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal_installed_alignment
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag coordinates).symm)
      rawCertificate
  exact buildExplicitBoundedWitnessHybridCertificate endpointBound
    (compactCertificateNodeSymbolPAEndpointBoundedGraphRawTerminal
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag)
    values (by
      intro index
      fin_cases index
      · exact hsymbolCode
      · exact harity
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

private theorem
    compactCertificateNodeSymbolPAEndpointBoundedGraphCertificate_nonempty
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat)
    (hbounded : CompactCertificateNodeSymbolPAEndpointBoundedGraph tokenTable
      width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
      suffixFinish certificateTag endpointBound) :
    Nonempty
      (HybridCertificate
        (compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula
          tokenTable width tokenCount inputStart inputFinish axiomStart
            axiomFinish suffixStart suffixFinish certificateTag endpointBound)) := by
  rcases hbounded with
    ⟨inputBoundary, hinputBoundary, inputCount, hinputCount,
      inputBoundarySize, hinputBoundarySize, tailStart, htailStart,
      tailFinish, htailFinish, tailBoundary, htailBoundary,
      tailCount, htailCount, tailBoundarySize, htailBoundarySize,
      axiomBoundary, haxiomBoundary, axiomCount, haxiomCount,
      axiomBoundarySize, haxiomBoundarySize, suffixBoundary, hsuffixBoundary,
      suffixCount, hsuffixCount, suffixBoundarySize, hsuffixBoundarySize,
      paTag, hpaTag, arity, harity, symbolCode, hsymbolCode, hgraph⟩
  let coordinates := compactCertificateNodeSymbolPAEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize tailStart tailFinish
      tailBoundary tailCount tailBoundarySize axiomBoundary axiomCount
      axiomBoundarySize suffixBoundary suffixCount suffixBoundarySize
      paTag arity symbolCode
  exact ⟨compactCertificateNodeSymbolPAEndpointBoundedGraphExplicitHybridCertificateOfGraph
    tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound coordinates
    hinputBoundary hinputCount hinputBoundarySize htailStart htailFinish
      htailBoundary htailCount htailBoundarySize haxiomBoundary haxiomCount
      haxiomBoundarySize hsuffixBoundary hsuffixCount hsuffixBoundarySize
      hpaTag harity hsymbolCode (by simpa [coordinates] using hgraph)⟩

/-- Public checked certificate whose only premise is the original bounded
SymbolPA graph.  All seventeen witnesses and guards are extracted internally. -/
noncomputable def
    compactCertificateNodeSymbolPAEndpointBoundedGraphExplicitHybridCertificate
    (tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat)
    (hbounded : CompactCertificateNodeSymbolPAEndpointBoundedGraph tokenTable
      width tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
      suffixFinish certificateTag endpointBound) :
    HybridCertificate
      (compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish certificateTag endpointBound) :=
  Classical.choice
    (compactCertificateNodeSymbolPAEndpointBoundedGraphCertificate_nonempty
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag endpointBound hbounded)

#print axioms compactCertificateNodeSymbolPAEndpointBoundedGraphClosedFormula_alignment
#print axioms compactCertificateNodeSymbolPAEndpointBoundedGraphExplicitHybridCertificateOfGraph
#print axioms compactCertificateNodeSymbolPAEndpointBoundedGraphExplicitHybridCertificate

end FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedGraphExplicitHybridCertificate
