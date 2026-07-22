import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedPublicDirectCompiler
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAExplicitDirectUniversalBranches
import integration.FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactPAExponentialValuationContextCompiler
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAValuationShiftedBoundCompilerBounds

/-!
# Explicit certificate for all bounded adjacent transform rows

The universal enumerates exactly `rowCount` rows.  Its branch index remains a
free valuation term through all thirty-seven bounded witnesses.  The separate
exponential conjunct certifies only the common value bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate

open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def zeroValuation : Nat -> Nat := fun _ => 0

def adjacentRowsBranchValuation (rowIndex : Nat) : Nat -> Nat :=
  extendValuation rowIndex zeroValuation

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

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

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)),
            Rew.bShift bound] =
        ![(#0 : ArithmeticSemiterm targetVariables (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

def compactFormulaTransformAdjacentRowsBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentRowsBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm rowCount,
      shortBinaryNumeralTerm mode,
      shortBinaryNumeralTerm witnessStart,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm witnessCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
    (tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) expDef.val) ⇜
    ![shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm tableWidth]

def compactFormulaTransformAdjacentRowsBoundedUniversalBody
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentCurrentBoundedDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm stateBoundary),
      Rew.bShift (shortBinaryNumeralTerm stateCount),
      (#0 : ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm mode),
      Rew.bShift (shortBinaryNumeralTerm witnessStart),
      Rew.bShift (shortBinaryNumeralTerm witnessFinish),
      Rew.bShift (shortBinaryNumeralTerm witnessCount),
      Rew.bShift (shortBinaryNumeralTerm valueBound)]

def compactFormulaTransformAdjacentRowsBoundedExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
      tableWidth valueBound ⋏
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).ballLT
        (shortBinaryNumeralTerm rowCount)

theorem compactFormulaTransformAdjacentRowsBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat) :
    compactFormulaTransformAdjacentRowsBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount tableWidth valueBound =
      compactFormulaTransformAdjacentRowsBoundedExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount tableWidth valueBound := by
  unfold compactFormulaTransformAdjacentRowsBoundedClosedFormula
  unfold compactFormulaTransformAdjacentRowsBoundedExplicitFormula
  unfold compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
  unfold compactFormulaTransformAdjacentRowsBoundedUniversalBody
  unfold compactFormulaTransformAdjacentRowsBoundedGraphDef
  simp [rewriting_ballLT, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactFormulaTransformAdjacentRowsBoundedUniversalBody_free_alignment
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    Rewriting.free
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode
          witnessStart witnessFinish witnessCount valueBound) =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount
        (&0 : ValuationTerm) mode witnessStart witnessFinish witnessCount
        valueBound := by
  unfold compactFormulaTransformAdjacentRowsBoundedUniversalBody
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_def, adjacentCurrentSourceTerms]

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedExponentialCertificate
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    HybridCertificate zeroValuation
      (compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
        tableWidth valueBound) := by
  change HybridCertificate zeroValuation
    (exponentialAtValuationFormula
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))
  exact .exponential zeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedBranchCertificate
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    HybridCertificate (adjacentRowsBranchValuation rowIndex)
      (Rewriting.free
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode
          witnessStart witnessFinish witnessCount valueBound)) := by
  exact .cast
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).symm
    (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificateOfGraph
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound (by
        simpa [adjacentRowsBranchValuation, zeroValuation] using hrow))

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedUniversalCertificate
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    HybridCertificate zeroValuation
      ((compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).ballLT
          (shortBinaryNumeralTerm rowCount)) := by
  let body := compactFormulaTransformAdjacentRowsBoundedUniversalBody
    tokenTable width tokenCount stateBoundary stateCount mode witnessStart
    witnessFinish witnessCount valueBound
  let branches := buildExplicitHybridUniversalBranches rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedBranchCertificate
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm rowCount) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm rowCount)) body) =
        body.ballLT (shortBinaryNumeralTerm rowCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-! ## Direct closed-bound universal route -/

theorem
    compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).freeVariables = ∅ := by
  unfold compactFormulaTransformAdjacentRowsBoundedUniversalBody
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  all_goals
    first
    | exact bShift_freeVariables_eq_empty_of_empty _
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    | simp

/-! ## Fully direct finite branches -/

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectBranchProof
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactFormulaTransformAdjacentRowsBoundedUniversalBody
            tokenTable width tokenCount stateBoundary stateCount mode
            witnessStart witnessFinish witnessCount valueBound)).freeVariables
        (extendValuation rowIndex zeroValuation))
      (Rewriting.free
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)) := by
  have hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue (adjacentRowsBranchValuation rowIndex) (&0 : ValuationTerm))
      mode witnessStart witnessFinish witnessCount valueBound := by
    simpa [adjacentRowsBranchValuation, zeroValuation] using hrow
  let raw :=
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound hcurrent
  exact castValuationContextProof
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).symm raw

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectBranchPayloadResource
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
    (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
    stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
    witnessFinish witnessCount valueBound (by
      simpa [adjacentRowsBranchValuation, zeroValuation] using hrow)

theorem
    compactFormulaTransformAdjacentRowsBoundedDirectBranchProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex hrow).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedDirectBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex hrow := by
  unfold compactFormulaTransformAdjacentRowsBoundedDirectBranchProof
    compactFormulaTransformAdjacentRowsBoundedDirectBranchPayloadResource
  rw [castValuationContextProof_payloadLength_eq]
  exact
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le_publicFinite
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound _ (by simp)

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  ∑ rowIndex : Fin rowCount,
    compactFormulaTransformAdjacentRowsBoundedDirectBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex rowIndex.isLt)

private theorem
    compactFormulaTransformAdjacentRowsBoundedDirectBranchProof_le_leafSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactFormulaTransformAdjacentRowsBoundedDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex hrowIndex)).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows := by
  let finiteIndex : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hleaf :=
    compactFormulaTransformAdjacentRowsBoundedDirectBranchProof_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex hrowIndex)
  have hmember :
      compactFormulaTransformAdjacentRowsBoundedDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound finiteIndex
          (hrows finiteIndex finiteIndex.isLt) <=
        compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows := by
    unfold
      compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin rowCount) _ => Nat.zero_le
        (compactFormulaTransformAdjacentRowsBoundedDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound candidate
          (hrows candidate candidate.isLt)))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hmember
  exact hleaf.trans hmember

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)) rowCount := by
  have hbodyVariables :
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound) ∅
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows) rowCount

theorem
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches_structuralPayloadBound_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows).structuralPayloadBound
        rowCount <=
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows := by
  have hbodyVariables :
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows)
    rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedDirectBranchProof_le_leafSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound rowIndex hrows
        hrowIndex)

theorem
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)
        (compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows) := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows)
    (fun _ => Nat.le_refl _)

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectHybridBranches
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound) rowCount :=
  buildExplicitHybridUniversalBranches rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedBranchCertificate
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectLeafStructuralResourceSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  ∑ rowIndex : Fin rowCount,
    hybridFormulaStructuralPayloadBound
      (compactFormulaTransformAdjacentRowsBoundedBranchCertificate
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex rowIndex.isLt))

private theorem
    compactFormulaTransformAdjacentRowsBoundedDirectHybridBranches_leafPayloadBound
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    HybridBranchesLeafPayloadBound
      (compactFormulaTransformAdjacentRowsBoundedDirectLeafStructuralResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows)
      (compactFormulaTransformAdjacentRowsBoundedDirectHybridBranches
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows) := by
  unfold compactFormulaTransformAdjacentRowsBoundedDirectHybridBranches
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro rowIndex hrowIndex
  let finiteIndex : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hmember :
      hybridFormulaStructuralPayloadBound
          (compactFormulaTransformAdjacentRowsBoundedBranchCertificate
            tokenTable width tokenCount stateBoundary stateCount mode
            witnessStart witnessFinish witnessCount valueBound finiteIndex
            (hrows finiteIndex finiteIndex.isLt)) <=
        compactFormulaTransformAdjacentRowsBoundedDirectLeafStructuralResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows := by
    unfold
      compactFormulaTransformAdjacentRowsBoundedDirectLeafStructuralResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin rowCount) _ => Nat.zero_le
        (hybridFormulaStructuralPayloadBound
          (compactFormulaTransformAdjacentRowsBoundedBranchCertificate
            tokenTable width tokenCount stateBoundary stateCount mode
            witnessStart witnessFinish witnessCount valueBound candidate
            (hrows candidate candidate.isLt))))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hmember
  exact hmember

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectBranchesLeafSumEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  explicitHybridUniversalBranchesPayloadPolynomial rowCount
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound)
    (compactFormulaTransformAdjacentRowsBoundedDirectLeafStructuralResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)

theorem
    compactFormulaTransformAdjacentRowsBoundedDirectBranches_le_leafSumEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    hybridBranchesStructuralPayloadEnvelope rowCount (∅ : Finset Nat)
        (compactFormulaTransformAdjacentRowsBoundedDirectHybridBranches
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows) <=
      compactFormulaTransformAdjacentRowsBoundedDirectBranchesLeafSumEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows := by
  exact hybridBranchesStructuralPayloadEnvelope_le_polynomial
    (compactFormulaTransformAdjacentRowsBoundedDirectLeafStructuralResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)
    (compactFormulaTransformAdjacentRowsBoundedDirectHybridBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)
    (compactFormulaTransformAdjacentRowsBoundedDirectHybridBranches_leafPayloadBound
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectBoundEquality
    (rowCount : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 rowCount) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm rowCount)))” :
        ValuationFormula) := by
  let raw := compileClosedShortBoundEquality rowCount
  have hformula :
      (“!!(iteratedSuccessorTerm 0 rowCount) =
        !!(shortBinaryNumeralTerm rowCount)” : ValuationFormula) =
      (“!!(iteratedSuccessorTerm 0 rowCount) =
        !!(Rew.free
          (Rew.bShift (shortBinaryNumeralTerm rowCount)))” :
        ValuationFormula) := by
    simp
  exact CertifiedPAContextProof.castContext (by simp)
    (CertifiedPAContextProof.cast hformula raw)

noncomputable def
    compileCompactFormulaTransformAdjacentRowsBoundedDirectUniversalContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    CertifiedPAContextProof ∅
      ((compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).ballLT
          (shortBinaryNumeralTerm rowCount)) := by
  let body := compactFormulaTransformAdjacentRowsBoundedUniversalBody
    tokenTable width tokenCount stateBoundary stateCount mode witnessStart
    witnessFinish witnessCount valueBound
  let branches :=
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows
  let boundEquality :=
    compactFormulaTransformAdjacentRowsBoundedDirectBoundEquality rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
    boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm rowCount)) body) =
        body.ballLT (shortBinaryNumeralTerm rowCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectUniversalResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount))
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound)
    (closedShortBoundEqualityPayloadPolynomial rowCount)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
      (Rewriting.free
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound))
      (compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows))

theorem
    compileCompactFormulaTransformAdjacentRowsBoundedDirectUniversalContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentRowsBoundedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedDirectUniversalResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows := by
  let body := compactFormulaTransformAdjacentRowsBoundedUniversalBody
    tokenTable width tokenCount stateBoundary stateCount mode witnessStart
    witnessFinish witnessCount valueBound
  let branches :=
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows
  let boundEquality :=
    compactFormulaTransformAdjacentRowsBoundedDirectBoundEquality rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
    boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial rowCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial rowCount := by
    simpa only [boundEquality,
      compactFormulaTransformAdjacentRowsBoundedDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesRaw :=
    compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches_structuralPayloadBound_le
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows
  have hbranchesCore : branches.structuralPayloadBound rowCount <=
      compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows := by
    exact hbranchesRaw
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
    (Rewriting.free body)
    (compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)
  have hbranches :
      branches.compileUnderBoundAssumptionStructuralPayloadBound <=
        branchResource := by
    unfold branchResource contextualBranchesUnderBoundPayloadEnvelope
      CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumptionStructuralPayloadBound
      CertifiedContextFiniteUniversalBranches.underExhaustionStructuralPayloadBound
    dsimp only [body] at hbranchesCore ⊢
    simp only [Finset.image_empty] at hbranchesCore ⊢
    omega
  have hstructural :=
    compileContextualTermBoundedUniversal_payloadLength_le_structural
      (Gamma := ∅) rowCount
      (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
      boundEquality branches
  have henvelope :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) rowCount
      (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
      boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial rowCount)
      branchResource
      hbound hbranches
  unfold compileCompactFormulaTransformAdjacentRowsBoundedDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by
    rfl))

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    HybridCertificate zeroValuation
      (compactFormulaTransformAdjacentRowsBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount tableWidth valueBound) := by
  rw [compactFormulaTransformAdjacentRowsBoundedClosedFormula_alignment]
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFormulaTransformAdjacentRowsBoundedExponentialCertificate
      tableWidth valueBound hgraph.1)
    (compactFormulaTransformAdjacentRowsBoundedUniversalCertificate
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hgraph.2)

noncomputable def
    compileCompactFormulaTransformAdjacentRowsBoundedExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentRowsBoundedClosedFormula
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount tableWidth
          valueBound).freeVariables zeroValuation)
      (compactFormulaTransformAdjacentRowsBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount tableWidth valueBound) :=
  (compactFormulaTransformAdjacentRowsBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount rowCount mode
    witnessStart witnessFinish witnessCount tableWidth valueBound hgraph).compile

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentRowsBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound hgraph)

theorem
    compileCompactFormulaTransformAdjacentRowsBoundedExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    (compileCompactFormulaTransformAdjacentRowsBoundedExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound
      hgraph).payloadLength ≤
    compactFormulaTransformAdjacentRowsBoundedExplicitStructuralResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentRowsBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound hgraph)

#print axioms compactFormulaTransformAdjacentRowsBoundedClosedFormula_alignment
#print axioms
  compactFormulaTransformAdjacentRowsBoundedUniversalBody_free_alignment
#print axioms
  compactFormulaTransformAdjacentRowsBoundedExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedExplicitHybridContext_payloadLength_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty
#print axioms
  compactFormulaTransformAdjacentRowsBoundedDirectBranchProof_payloadLength_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedDirectUniversalContext_payloadLength_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedDirectBranches_le_leafSumEnvelope

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
