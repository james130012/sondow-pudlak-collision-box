import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFixedCorePublicDirectCompiler

/-!
# Fixed-core direct bounds for all adjacent rows

Each row uses the fixed-core `14 + 14 + 9` witness compiler with the fixed sum
of all six adjacent-step terminal resources. Rows are aggregated only over
`Fin rowCount`.

The declarations whose names contain `AllRowsFinite` additionally use the
logical finite-exhaustion envelope from the terminal module.  They verify that
no row is omitted, but their `(valueBound + 1)^37` resource is not an admissible
bit-width polynomial for `A04.18` and is not a submission-route endpoint.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFixedCoreDirectBounds

open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFixedCorePublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAExponentialValuationContextCompilerBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
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
  have hindexVariables : (&0 : ValuationTerm).freeVariables ⊆ {0} := by
    simp
  let raw :=
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound hindexVariables hcurrent
  exact castValuationContextProof
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).symm raw

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchPayloadResource
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (_hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
    (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
    stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
    witnessFinish witnessCount valueBound

theorem
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex hrow).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex hrow := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchPayloadResource
  rw [castValuationContextProof_payloadLength_eq]
  exact
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph_payloadLength_le_allRowsFinite
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound (by simp) _

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  ∑ rowIndex : Fin rowCount,
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex rowIndex.isLt)

theorem
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_le_leafSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex hrowIndex)).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows := by
  let finiteIndex : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hleaf :=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex hrowIndex)
  have hmember :
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound finiteIndex
          (hrows finiteIndex finiteIndex.isLt) <=
        compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows := by
    unfold
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin rowCount) _ => Nat.zero_le
        (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound candidate
          (hrows candidate candidate.isLt)))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hmember
  exact hleaf.trans hmember

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  ∑ rowIndex : Fin rowCount,
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound

theorem
    compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_le_allRowsFiniteLeafSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex hrow).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound := by
  let finiteIndex : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hleaf :
      (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex hrow).payloadLength <=
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
        (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
        stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
        witnessFinish witnessCount valueBound := by
    simpa only [
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchPayloadResource] using
      (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_payloadLength_le
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex hrow)
  have hmember :
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
          (adjacentRowsBranchValuation finiteIndex) tokenTable width tokenCount
          stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
          witnessFinish witnessCount valueBound <=
        compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound := by
    unfold
      compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin rowCount) _ => Nat.zero_le
        (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
          (adjacentRowsBranchValuation candidate) tokenTable width tokenCount
          stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
          witnessFinish witnessCount valueBound))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hmember
  exact hleaf.trans hmember

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
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
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound) ∅
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows) rowCount

theorem
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches_structuralPayloadBound_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows).structuralPayloadBound
        rowCount <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows := by
  have hbodyVariables :
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows)
    rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_le_leafSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound rowIndex hrows
        hrowIndex)

theorem
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)
        (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows) := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows)
    (fun _ => Nat.le_refl _)

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound) ∅
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound) rowCount

theorem
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches_structuralPayloadBound_le_allRowsFinite
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows).structuralPayloadBound
        rowCount <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound := by
  have hbodyVariables :
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound)
    rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_le_allRowsFiniteLeafSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex) hrowIndex)

theorem
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)
        (compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound) := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound)
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound)
    (fun _ => Nat.le_refl _)

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectBoundEquality
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
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
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
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows
  let boundEquality :=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectBoundEquality
      rowCount
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
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
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
      (compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound))

theorem
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound := by
  let body := compactFormulaTransformAdjacentRowsBoundedUniversalBody
    tokenTable width tokenCount stateBoundary stateCount mode witnessStart
    witnessFinish witnessCount valueBound
  let branches :=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows
  let boundEquality :=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectBoundEquality
      rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
    boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial rowCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial rowCount := by
    simpa only [boundEquality,
      compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound rowCount <=
      compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound :=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches_structuralPayloadBound_le_allRowsFinite
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
    (Rewriting.free body)
    (compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound)
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
      branchResource hbound hbranches
  unfold
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

private noncomputable def
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialAtValuationDirectContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (exponentialAtValuationFormula
        (shortBinaryNumeralTerm valueBound)
        (shortBinaryNumeralTerm tableWidth)) := by
  let raw := compileExponentialAtValuation zeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)
  have hvaluationContext :
      exponentialValuationContext zeroValuation
          (shortBinaryNumeralTerm valueBound)
          (shortBinaryNumeralTerm tableWidth) =
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          zeroValuation := by
    unfold exponentialValuationContext
    rw [exponentialAtValuationFormula_freeVariables]
  let atValuation := CertifiedPAContextProof.castContext
    hvaluationContext raw
  have hempty :
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          zeroValuation = ∅ := by
    rw [exponentialAtValuationFormula_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hempty atValuation

noncomputable def
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
        tableWidth valueBound) := by
  let raw :=
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialAtValuationDirectContext
      tableWidth valueBound hvalueBound
  have hformula :
      exponentialAtValuationFormula
          (shortBinaryNumeralTerm valueBound)
          (shortBinaryNumeralTerm tableWidth) =
        compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
          tableWidth valueBound := by
    rfl
  exact CertifiedPAContextProof.cast hformula raw

def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectResource
    (tableWidth valueBound : Nat) : Nat :=
  exponentialValuationCompilerPayloadPolynomial
    (compileExponentialAtValuationPayloadResource zeroValuation
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))

theorem
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext_payloadLength_le
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext
      tableWidth valueBound hvalueBound).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectResource
      tableWidth valueBound := by
  unfold
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialAtValuationDirectContext
  unfold
    compactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectResource
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.castContext_payloadLength]
  exact compileExponentialAtValuation_payloadLength_le_fixedPolynomial
    zeroValuation (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth) (by
        simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat) : Nat :=
  let exponentialFormula :=
    compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
      tableWidth valueBound
  let universalFormula :=
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).ballLT
        (shortBinaryNumeralTerm rowCount)
  compactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectResource
      tableWidth valueBound +
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
      exponentialFormula universalFormula

noncomputable def
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    CertifiedPAContextProof ∅
      (compactFormulaTransformAdjacentRowsBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount tableWidth valueBound) := by
  let exponentialProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactFormulaTransformAdjacentRowsBoundedClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound).symm raw

theorem
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound) :
    (compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound
      hgraph).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound := by
  let exponentialProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectResource
        tableWidth valueBound :=
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalResource
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound :=
    compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hgraph.2
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  have hcompiled :
      (compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedContext
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount tableWidth valueBound
        hgraph).payloadLength = raw.payloadLength := by
    unfold
      compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedContext
    rw [CertifiedPAContextProof.cast_payloadLength]
    rfl
  rw [hcompiled]
  unfold
    compactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedResource
  dsimp only [raw] at hraw ⊢
  omega

#print axioms
  compactFormulaTransformAdjacentRowsBoundedFixedCoreDirectBranchProof_payloadLength_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranches_structuralPayloadBound_le_allRowsFinite
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFixedCoreFullyDirectBranchesAllRowsFiniteStructuralEnvelope_le_polynomial
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectUniversalContext_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreExponentialDirectContext_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedFixedCoreAllRowsFiniteDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFixedCoreDirectBounds
