import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeExplicitUniformResource
import integration.FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerBounds

/-! # Bounded universal with an explicit row-independent branch resource -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalExplicitUniformResource

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeExplicitUniformResource

noncomputable def
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBoundEquality
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

def compactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat) : Nat :=
  let body :=
    compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
    (closedShortBoundEqualityPayloadPolynomial rowCount)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
      (Rewriting.free body)
      (compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchesStructuralEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound))

noncomputable def
    compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :
    CertifiedPAContextProof ∅
      ((compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound).ballLT (shortBinaryNumeralTerm rowCount)) := by
  let body :=
    compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound
  let branches :=
    compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hrows
  let boundEquality :=
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBoundEquality
      rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm rowCount)) body) =
        body.ballLT (shortBinaryNumeralTerm rowCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

theorem
    compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :
    (compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hrows).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
  let body :=
    compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound
  let branches :=
    compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hrows
  let boundEquality :=
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBoundEquality
      rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial rowCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial rowCount := by
    simpa only [boundEquality,
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound rowCount <=
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchesStructuralEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
    exact
      compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches_structuralPayloadBound_le
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound hrows
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
    (Rewriting.free body)
    (compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchesStructuralEnvelope
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound)
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
    compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

#print axioms
  compactSequentFormulaStepRowsBoundedDirectExplicitUniformBoundEquality
#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext
#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalExplicitUniformResource
