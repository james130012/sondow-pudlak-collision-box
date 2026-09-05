import integration.FoundationCompactNumericListedDirectNatListListRowsDirectBranchTreeUniformBound
import integration.FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerBounds

/-! # Direct bounded universal for additive natural-list-list rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListListRowsDirectUniversalUniformBound

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
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsDirectBranchTreeUniformBound

noncomputable def compactAdditiveNatListListRowsDirectUniformBoundEquality
    (count : Nat) :
    CertifiedPAContextProof
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 count) =
        !!(Rew.free (Rew.bShift (shortBinaryNumeralTerm count)))” :
        ValuationFormula) := by
  let raw := compileClosedShortBoundEquality count
  have hformula :
      (“!!(iteratedSuccessorTerm 0 count) =
        !!(shortBinaryNumeralTerm count)” : ValuationFormula) =
      (“!!(iteratedSuccessorTerm 0 count) =
        !!(Rew.free (Rew.bShift (shortBinaryNumeralTerm count)))” :
        ValuationFormula) := by
    simp
  exact CertifiedPAContextProof.castContext (by simp)
    (CertifiedPAContextProof.cast hformula raw)

def compactAdditiveNatListListRowsDirectUniformUniversalResource
    (tokenTable width tokenCount boundaryTable count numericBound
      bitBound : Nat) : Nat :=
  let body := compactAdditiveNatListListRowsBody tokenTable width tokenCount
    boundaryTable
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ count
    (Rew.bShift (shortBinaryNumeralTerm count)) body
    (closedShortBoundEqualityPayloadPolynomial count)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ count
      (Rewriting.free body)
      (compactAdditiveNatListListRowsDirectUniformBranchesStructuralEnvelope
        tokenTable width tokenCount boundaryTable count numericBound bitBound))

noncomputable def compileCompactAdditiveNatListListRowsDirectUniformUniversal
    (tokenTable width tokenCount boundaryTable count numericBound
      bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactAdditiveNatListListRowsBody tokenTable width tokenCount
        boundaryTable).ballLT (shortBinaryNumeralTerm count)) := by
  let body := compactAdditiveNatListListRowsBody tokenTable width tokenCount
    boundaryTable
  let branches := compactAdditiveNatListListRowsFullyDirectUniformBranches
    tokenTable width tokenCount boundaryTable count numericBound bitBound hrows
    hcount hwidth htokenCount htableSize hboundarySize hnumericSize
  let boundEquality :=
    compactAdditiveNatListListRowsDirectUniformBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        body.ballLT (shortBinaryNumeralTerm count)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

theorem compileCompactAdditiveNatListListRowsDirectUniformUniversal_payloadLength_le
    (tokenTable width tokenCount boundaryTable count numericBound
      bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveNatListListRowsDirectUniformUniversal tokenTable
      width tokenCount boundaryTable count numericBound bitBound hrows hcount
      hwidth htokenCount htableSize hboundarySize hnumericSize).payloadLength <=
      compactAdditiveNatListListRowsDirectUniformUniversalResource tokenTable
        width tokenCount boundaryTable count numericBound bitBound := by
  let body := compactAdditiveNatListListRowsBody tokenTable width tokenCount
    boundaryTable
  let branches := compactAdditiveNatListListRowsFullyDirectUniformBranches
    tokenTable width tokenCount boundaryTable count numericBound bitBound hrows
    hcount hwidth htokenCount htableSize hboundarySize hnumericSize
  let boundEquality :=
    compactAdditiveNatListListRowsDirectUniformBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial count
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial count := by
    simpa only [boundEquality,
      compactAdditiveNatListListRowsDirectUniformBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound count <=
      compactAdditiveNatListListRowsDirectUniformBranchesStructuralEnvelope
        tokenTable width tokenCount boundaryTable count numericBound
        bitBound := by
    exact
      compactAdditiveNatListListRowsFullyDirectUniformBranches_structuralPayloadBound_le
        tokenTable width tokenCount boundaryTable count numericBound bitBound
        hrows hcount hwidth htokenCount htableSize hboundarySize hnumericSize
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (compactAdditiveNatListListRowsDirectUniformBranchesStructuralEnvelope
      tokenTable width tokenCount boundaryTable count numericBound bitBound)
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
      (Gamma := ∅) count (Rew.bShift (shortBinaryNumeralTerm count)) body
      boundEquality branches
  have henvelope :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) count (Rew.bShift (shortBinaryNumeralTerm count)) body
      boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial count) branchResource hbound
      hbranches
  unfold compileCompactAdditiveNatListListRowsDirectUniformUniversal
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

#print axioms compactAdditiveNatListListRowsDirectUniformBoundEquality
#print axioms compileCompactAdditiveNatListListRowsDirectUniformUniversal
#print axioms
  compileCompactAdditiveNatListListRowsDirectUniformUniversal_payloadLength_le

end FoundationCompactNumericListedDirectNatListListRowsDirectUniversalUniformBound
