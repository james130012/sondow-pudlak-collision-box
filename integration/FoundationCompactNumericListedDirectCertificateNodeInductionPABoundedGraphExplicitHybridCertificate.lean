import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpointExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

/-!
# Staged explicit hybrid certificate for the bounded induction PA graph

This file fixes the original bounded source formula, its twenty-one witness
coordinates, and the direct witness installer.  The syntactic equality from
the source formula to that installer is kept as an explicit goal until the
twenty-one-binder rewriting normalization is discharged.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpointExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

private def boundedOuterTerms
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    Fin 13 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm axiomStart,
    shortBinaryNumeralTerm axiomFinish,
    shortBinaryNumeralTerm formulaStart,
    shortBinaryNumeralTerm formulaFinish,
    shortBinaryNumeralTerm suffixStart,
    shortBinaryNumeralTerm suffixFinish,
    shortBinaryNumeralTerm certificateTag,
    shortBinaryNumeralTerm endpointBound]

/-- The original thirteen-public-coordinate bounded source formula. -/
def compactCertificateNodeInductionPAEndpointBoundedGraphClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeInductionPAEndpointBoundedGraphDef.val) ⇜
    boundedOuterTerms tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish suffixStart suffixFinish
      certificateTag endpointBound

/-- The endpoint matrix under the original twenty-one bounded binders.
`#0` is the parser value bound and `#20` is the input boundary. -/
def compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat) :
    ArithmeticSemiformula Nat 21 :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeInductionPAEndpointGraphDef.val) ⇜
    ![closedShift 21 (shortBinaryNumeralTerm tokenTable),
      closedShift 21 (shortBinaryNumeralTerm width),
      closedShift 21 (shortBinaryNumeralTerm tokenCount),
      closedShift 21 (shortBinaryNumeralTerm inputStart),
      closedShift 21 (shortBinaryNumeralTerm inputFinish),
      closedShift 21 (shortBinaryNumeralTerm axiomStart),
      closedShift 21 (shortBinaryNumeralTerm axiomFinish),
      closedShift 21 (shortBinaryNumeralTerm formulaStart),
      closedShift 21 (shortBinaryNumeralTerm formulaFinish),
      closedShift 21 (shortBinaryNumeralTerm suffixStart),
      closedShift 21 (shortBinaryNumeralTerm suffixFinish),
      closedShift 21 (shortBinaryNumeralTerm certificateTag),
      (#20 : ArithmeticSemiterm Nat 21), #19, #18, #17, #16, #15, #14,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

/-- The explicit witness installation with the exact original endpoint matrix. -/
def compactCertificateNodeInductionPAEndpointBoundedGraphExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    ValuationFormula :=
  explicitBoundedWitnessFormula (shortBinaryNumeralTerm endpointBound) 21
    (compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal tokenTable
      width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag)

/-- The remaining purely syntactic bridge for the original 21-binder source.
It is a definition, rather than an unproved theorem, so downstream callers
must provide the equality before obtaining a certificate for the source form. -/
def compactCertificateNodeInductionPAEndpointBoundedGraphAlignmentGoal
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) : Prop :=
  compactCertificateNodeInductionPAEndpointBoundedGraphClosedFormula tokenTable
      width tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
      formulaFinish suffixStart suffixFinish certificateTag endpointBound =
    compactCertificateNodeInductionPAEndpointBoundedGraphExplicitFormula
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag
      endpointBound

private def boundedWitnessValues
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    Fin 21 -> Nat :=
  ![coordinates.parser.valueBound,
    coordinates.parser.tableWidth,
    coordinates.parser.stateCount,
    coordinates.parser.stateBoundary,
    coordinates.parser.expectedBoundarySize,
    coordinates.parser.expectedCount,
    coordinates.parser.expectedBoundary,
    coordinates.parser.inputBoundarySize,
    coordinates.parser.inputCount,
    coordinates.parser.inputBoundary,
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

theorem compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal tokenTable
        width tokenCount inputStart inputFinish axiomStart axiomFinish
        formulaStart formulaFinish suffixStart suffixFinish certificateTag ⇜
      (fun index => shortBinaryNumeralTerm (boundedWitnessValues coordinates index)) =
    compactCertificateNodeInductionPAEndpointClosedFormula tokenTable width
      tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
      formulaFinish suffixStart suffixFinish certificateTag coordinates := by
  unfold compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal
    compactCertificateNodeInductionPAEndpointClosedFormula
    boundedWitnessValues boundedOuterTerms
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]

/-- Install all twenty-one bounded witnesses.  The parser terminal and the
source-to-installer alignment remain explicit inputs; all other endpoint and
bounded-witness work is closed constructively. -/
noncomputable def
    compactCertificateNodeInductionPAEndpointBoundedGraphExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates)
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
    (hformulaBoundary : coordinates.parser.inputBoundary <= endpointBound)
    (hformulaCount : coordinates.parser.inputCount <= endpointBound)
    (hformulaBoundarySize : coordinates.parser.inputBoundarySize <= endpointBound)
    (hsuffixBoundary : coordinates.parser.expectedBoundary <= endpointBound)
    (hsuffixCount : coordinates.parser.expectedCount <= endpointBound)
    (hsuffixBoundarySize : coordinates.parser.expectedBoundarySize <= endpointBound)
    (hstateBoundary : coordinates.parser.stateBoundary <= endpointBound)
    (hstateCount : coordinates.parser.stateCount <= endpointBound)
    (htableWidth : coordinates.parser.tableWidth <= endpointBound)
    (hvalueBound : coordinates.parser.valueBound <= endpointBound)
    (hgraph : CompactCertificateNodeInductionPAEndpointGraph tokenTable width
      tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
      formulaFinish suffixStart suffixFinish certificateTag coordinates)
    (parserCertificate : InductionPAEndpointHybridCertificate
      (compactParserSyntaxExactEndpointClosedFormula tokenTable width tokenCount
        formulaStart formulaFinish suffixStart suffixFinish coordinates.parser))
    (halignment : compactCertificateNodeInductionPAEndpointBoundedGraphAlignmentGoal
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag
      endpointBound) :
    HybridCertificate
      (compactCertificateNodeInductionPAEndpointBoundedGraphClosedFormula
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        formulaStart formulaFinish suffixStart suffixFinish certificateTag
        endpointBound) := by
  unfold compactCertificateNodeInductionPAEndpointBoundedGraphAlignmentGoal at halignment
  rw [halignment]
  let values := boundedWitnessValues coordinates
  let endpointCertificate :=
    compactCertificateNodeInductionPAEndpointExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag
      coordinates hgraph parserCertificate
  let terminal : HybridCertificate
      (compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal tokenTable
          width tokenCount inputStart inputFinish axiomStart axiomFinish
          formulaStart formulaFinish suffixStart suffixFinish certificateTag ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal_alignment
          tokenTable width tokenCount inputStart inputFinish axiomStart
          axiomFinish formulaStart formulaFinish suffixStart suffixFinish
          certificateTag coordinates).symm) endpointCertificate
  exact buildExplicitBoundedWitnessHybridCertificate endpointBound
    (compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal tokenTable
      width tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
      formulaFinish suffixStart suffixFinish certificateTag)
    values (by
      intro index
      fin_cases index
      · exact hvalueBound
      · exact htableWidth
      · exact hstateCount
      · exact hstateBoundary
      · exact hsuffixBoundarySize
      · exact hsuffixCount
      · exact hsuffixBoundary
      · exact hformulaBoundarySize
      · exact hformulaCount
      · exact hformulaBoundary
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

#print axioms compactCertificateNodeInductionPAEndpointBoundedGraphRawTerminal_alignment
#print axioms compactCertificateNodeInductionPAEndpointBoundedGraphExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedGraphExplicitHybridCertificate
