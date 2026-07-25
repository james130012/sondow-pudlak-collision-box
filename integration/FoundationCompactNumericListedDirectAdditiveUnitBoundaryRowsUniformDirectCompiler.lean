import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectUniformContextBounds

/-!
# Uniform direct compiler for additive unit-boundary rows

Every row branch is compiled with one context and terminal resource depending
only on the shared numerical and bit-width bounds.  The finite universal branch
tree therefore uses a constant leaf resource rather than a proof-dependent sum.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity02
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectCompiler
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectUniformContextBounds

private abbrev unitZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation

def compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
    (tokenCount boundaryTable numericBound bitBound : Nat) : Nat :=
  let body := compactAdditiveUnitBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let contextCodeBound :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    unitBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
    tokenCount bodyCodeBound terminalResource

noncomputable def compactAdditiveUnitBoundaryRowsUniformBranchDirectBound
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound
      (extendValuation index unitZeroValuation)
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound) := by
  let valuation := extendValuation index unitZeroValuation
  let body := compactAdditiveUnitBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let values := compactAdditiveUnitBoundaryRowsDirectValues data
  let contextCodeBound :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    unitBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  let terminalCertificate :=
    compactAdditiveUnitBoundaryRowsDirectTerminalCertificate
      tokenCount boundaryTable index data
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data :=
    compactAdditiveUnitBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
      tokenCount boundaryTable index data
  have hterminalUniform :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        terminalResource :=
    hterminalStructural.trans
      (compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
        tokenCount boundaryTable index numericBound bitBound data htokenCount
        hindexSuccessor htableSize hnumericSize)
  have hterminal : terminalCertificate.compile.payloadLength <=
      terminalResource :=
    (compile_payloadLength_le_structuralPayloadBound
      terminalCertificate).trans hterminalUniform
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext body.freeVariables valuation) <= contextCodeBound :=
    compactAdditiveUnitBoundaryRowsBranchTerminal_contextCodeSum_le
      tokenCount boundaryTable index numericBound (by omega)
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm tokenCount) 2 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveUnitBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity02
      contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveUnitBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable) :=
    (compactAdditiveUnitBoundaryRowsBody_free_alignment
      tokenCount boundaryTable).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope,
    valuation, body, contextCodeBound, bodyCodeBound, terminalResource]
    using hcoordinates.2

noncomputable def compileCompactAdditiveUnitBoundaryRowsUniformBranchDirect
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactAdditiveUnitBoundaryRowsBody
            tokenCount boundaryTable)).freeVariables
        (extendValuation index unitZeroValuation))
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)) :=
  (compactAdditiveUnitBoundaryRowsUniformBranchDirectBound tokenCount
    boundaryTable index numericBound bitBound data htokenCount
    hindexSuccessor htableSize hnumericSize).proof

theorem compileCompactAdditiveUnitBoundaryRowsUniformBranchDirect_payloadLength_le
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsUniformBranchDirect tokenCount
      boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound :=
  (compactAdditiveUnitBoundaryRowsUniformBranchDirectBound tokenCount
    boundaryTable index numericBound bitBound data htokenCount
    hindexSuccessor htableSize hnumericSize).payloadLength_le

noncomputable def compactAdditiveUnitBoundaryRowsUniformDirectBranches
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable))
      count := by
  have hbodyVariables :
      (compactAdditiveUnitBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveUnitBoundaryRowsBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables count
    (fun index hindex =>
      compileCompactAdditiveUnitBoundaryRowsUniformBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)

def compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope unitZeroValuation count
    (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable) ∅
    (fun _ =>
      compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    count

theorem
    compactAdditiveUnitBoundaryRowsUniformDirectBranches_structuralPayloadBound_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveUnitBoundaryRowsUniformDirectBranches tokenCount count
      boundaryTable numericBound bitBound rows htokenCount hcount htableSize
      hnumericSize).structuralPayloadBound count <=
      compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound := by
  have hbodyVariables :
      (compactAdditiveUnitBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveUnitBoundaryRowsBody_freeVariables_eq_empty]
  unfold compactAdditiveUnitBoundaryRowsUniformDirectBranches
    compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables count
    (fun _ =>
      compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    count
    (fun index hindex =>
      compileCompactAdditiveUnitBoundaryRowsUniformBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)
    (fun index hindex =>
      compileCompactAdditiveUnitBoundaryRowsUniformBranchDirect_payloadLength_le
        tokenCount boundaryTable index numericBound bitBound
        (rows ⟨index, hindex⟩) htokenCount (by omega) htableSize
        hnumericSize)

theorem
    compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
    (tokenCount count boundaryTable numericBound bitBound : Nat) :
    compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial count
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)
        (compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
          tokenCount boundaryTable numericBound bitBound) := by
  unfold compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
      tokenCount boundaryTable numericBound bitBound)
    (fun _ =>
      compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    (fun _ => Nat.le_refl _)

noncomputable def
    compileCompactAdditiveUnitBoundaryRowsUniformDirectUniversalContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactAdditiveUnitBoundaryRowsBody
        tokenCount boundaryTable).ballLT
          (shortBinaryNumeralTerm count)) := by
  let body := compactAdditiveUnitBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveUnitBoundaryRowsUniformDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveUnitBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        body.ballLT (shortBinaryNumeralTerm count)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

def compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ count
    (Rew.bShift (shortBinaryNumeralTerm count))
    (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)
    (closedShortBoundEqualityPayloadPolynomial count)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ count
      (Rewriting.free
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound))

theorem
    compileCompactAdditiveUnitBoundaryRowsUniformDirectUniversalContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsUniformDirectUniversalContext
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
        count boundaryTable numericBound bitBound := by
  let body := compactAdditiveUnitBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveUnitBoundaryRowsUniformDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveUnitBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial count
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial count := by
    simpa only [boundEquality,
      compactAdditiveUnitBoundaryRowsDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound count <=
      compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound :=
    compactAdditiveUnitBoundaryRowsUniformDirectBranches_structuralPayloadBound_le
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
      tokenCount count boundaryTable numericBound bitBound)
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
      (Gamma := ∅) count
      (Rew.bShift (shortBinaryNumeralTerm count)) body
      boundEquality branches
  have henvelope :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) count
      (Rew.bShift (shortBinaryNumeralTerm count)) body
      boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial count)
      branchResource hbound hbranches
  unfold compileCompactAdditiveUnitBoundaryRowsUniformDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

noncomputable def
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable) := by
  let direct :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectUniversalContext
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize
  exact CertifiedPAContextProof.cast
    (compactAdditiveUnitBoundaryRowsClosedFormula_alignment
      tokenCount count boundaryTable).symm direct

theorem compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
    (tokenCount count boundaryTable : Nat) :
    (compactAdditiveUnitBoundaryRowsClosedFormula
      tokenCount count boundaryTable).freeVariables = ∅ := by
  unfold compactAdditiveUnitBoundaryRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable

theorem
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveUnitBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContext
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
        count boundaryTable numericBound bitBound := by
  unfold compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact
    compileCompactAdditiveUnitBoundaryRowsUniformDirectUniversalContext_payloadLength_le
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize

noncomputable def
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable) :=
  compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContext tokenCount
    count boundaryTable numericBound bitBound
    (compactAdditiveUnitBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

theorem
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount count boundaryTable numericBound bitBound hrows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
        count boundaryTable numericBound bitBound :=
  compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContext_payloadLength_le
    tokenCount count boundaryTable numericBound bitBound
    (compactAdditiveUnitBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

#print axioms compactAdditiveUnitBoundaryRowsUniformBranchDirectBound
#print axioms
  compileCompactAdditiveUnitBoundaryRowsUniformBranchDirect_payloadLength_le
#print axioms
  compactAdditiveUnitBoundaryRowsUniformDirectBranches_structuralPayloadBound_le
#print axioms
  compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compileCompactAdditiveUnitBoundaryRowsUniformDirectUniversalContext_payloadLength_le
#print axioms compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
