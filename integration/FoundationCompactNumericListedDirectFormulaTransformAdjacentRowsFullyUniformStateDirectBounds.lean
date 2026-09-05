import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFullyUniformStatePublicDirectCompiler

/-!
# Uniform-state direct bounds for all formula-transform adjacent rows

Each actual row is compiled through the `14 + 14 + 9` witness chain.  The
finite universal is aggregated only over `Fin rowCount`; no coordinate-value
enumeration occurs.  The remaining per-row transform-step public-finite
resource stays explicit in the leaf sum.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectBounds

open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFullyUniformStatePublicDirectCompiler
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
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      rowIndex : Nat)
    (hrowIndexBound : rowIndex <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
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
  have hzero : adjacentRowsBranchValuation rowIndex 0 <= numericBound := by
    simpa [adjacentRowsBranchValuation, zeroValuation] using hrowIndexBound
  let raw :=
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound numericBound bitBound
      hindexVariables hzero hvalueBound hwidthValue htokenCount hstateCount
      hareaNumeric hareaBit htokenTableSize hstateBoundarySize hnumericSize
      hnumericBit hbitPositive hcurrent
  exact castValuationContextProof
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).symm raw

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicBranchPayloadResource
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      rowIndex : Nat) : Nat :=
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelope
    (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
    stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
    witnessFinish witnessCount valueBound numericBound bitBound

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchPayloadResource
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      rowIndex : Nat)
    (_hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicBranchPayloadResource
    tokenTable width tokenCount stateBoundary stateCount mode witnessStart
    witnessFinish witnessCount valueBound numericBound bitBound rowIndex

theorem
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      rowIndex : Nat)
    (hrowIndexBound : rowIndex <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound numericBound bitBound rowIndex
      hrowIndexBound hvalueBound hwidthValue htokenCount hstateCount
      hareaNumeric hareaBit htokenTableSize hstateBoundarySize hnumericSize
      hnumericBit hbitPositive hrow).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound numericBound bitBound rowIndex
      hrow := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchPayloadResource
  rw [castValuationContextProof_payloadLength_eq]
  exact
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph_payloadLength_le
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound numericBound bitBound (by simp)
      (by
        simpa [adjacentRowsBranchValuation, zeroValuation] using hrowIndexBound)
      hvalueBound hwidthValue htokenCount hstateCount hareaNumeric hareaBit
      htokenTableSize hstateBoundarySize hnumericSize hnumericBit hbitPositive _

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicLeafPayloadResourceSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat) : Nat :=
  ∑ rowIndex : Fin rowCount,
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound numericBound bitBound rowIndex

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (_hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicLeafPayloadResourceSum
    tokenTable width tokenCount stateBoundary stateCount rowCount mode
    witnessStart witnessFinish witnessCount valueBound numericBound bitBound

theorem
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof_le_leafSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      rowIndex : Nat)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound numericBound bitBound rowIndex
      ((Nat.le_of_lt hrowIndex).trans hrowCount) hvalueBound hwidthValue
      htokenCount hstateCount hareaNumeric hareaBit htokenTableSize
      hstateBoundarySize hnumericSize hnumericBit hbitPositive
      (hrows rowIndex hrowIndex)).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrows := by
  let finiteIndex : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hleaf :=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound numericBound bitBound rowIndex
      ((Nat.le_of_lt hrowIndex).trans hrowCount) hvalueBound hwidthValue
      htokenCount hstateCount hareaNumeric hareaBit htokenTableSize
      hstateBoundarySize hnumericSize hnumericBit hbitPositive
      (hrows rowIndex hrowIndex)
  have hmember :
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound numericBound bitBound
          finiteIndex (hrows finiteIndex finiteIndex.isLt) <=
        compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound numericBound
          bitBound hrows := by
    unfold
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin rowCount) _ => Nat.zero_le
        (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode
          witnessStart witnessFinish witnessCount valueBound numericBound
          bitBound candidate (hrows candidate candidate.isLt)))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hmember
  exact hleaf.trans hmember

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
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
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound numericBound bitBound rowIndex
        ((Nat.le_of_lt hrowIndex).trans hrowCount) hvalueBound hwidthValue
        htokenCount hstateCount hareaNumeric hareaBit htokenTableSize
        hstateBoundarySize hnumericSize hnumericBit hbitPositive
        (hrows rowIndex hrowIndex))

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound) ∅
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound bitBound)
    rowCount

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (_hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicBranchesStructuralEnvelope
    tokenTable width tokenCount stateBoundary stateCount rowCount mode
    witnessStart witnessFinish witnessCount valueBound numericBound bitBound

theorem
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches_structuralPayloadBound_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hrows).structuralPayloadBound rowCount <=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrows := by
  have hbodyVariables :
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound bitBound
        hrows)
    rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound numericBound bitBound rowIndex
        ((Nat.le_of_lt hrowIndex).trans hrowCount) hvalueBound hwidthValue
        htokenCount hstateCount hareaNumeric hareaBit htokenTableSize
        hstateBoundarySize hnumericSize hnumericBit hbitPositive
        (hrows rowIndex hrowIndex))
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof_le_leafSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound
        bitBound rowIndex hrowCount hvalueBound hwidthValue htokenCount
        hstateCount hareaNumeric hareaBit htokenTableSize hstateBoundarySize
        hnumericSize hnumericBit hbitPositive hrows hrowIndex)

theorem
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound
        bitBound hrows <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)
        (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound numericBound
          bitBound hrows) := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrows)
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound bitBound
        hrows)
    (fun _ => Nat.le_refl _)

private noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBoundEquality
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
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
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
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hrows
  let boundEquality :=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBoundEquality
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
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicUniversalResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat) : Nat :=
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
      (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound
        bitBound))

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (_hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicUniversalResource
    tokenTable width tokenCount stateBoundary stateCount rowCount mode
    witnessStart witnessFinish witnessCount valueBound numericBound bitBound

theorem
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalResource_eq_public
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalResource
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound bitBound
        hrows =
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicUniversalResource
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound bitBound :=
  rfl

theorem
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound :
      Nat)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hrows).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicUniversalResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound := by
  let body := compactFormulaTransformAdjacentRowsBoundedUniversalBody
    tokenTable width tokenCount stateBoundary stateCount mode witnessStart
    witnessFinish witnessCount valueBound
  let branches :=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hrows
  let boundEquality :=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBoundEquality
      rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
    boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial rowCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial rowCount := by
    simpa only [boundEquality,
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound rowCount <=
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound
        bitBound hrows :=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches_structuralPayloadBound_le
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hrows
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
    (Rewriting.free body)
    (compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrows)
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
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

#print axioms
  compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchProof_payloadLength_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranches_structuralPayloadBound_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectBounds
