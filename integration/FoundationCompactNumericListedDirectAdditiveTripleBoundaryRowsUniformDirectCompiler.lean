import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsDirectUniformContextBounds

/-!
# Uniform direct compiler for additive triple-boundary rows

Every row branch is compiled with one context and terminal resource depending
only on the shared numerical and bit-width bounds.  The finite universal branch
tree therefore uses a constant leaf resource rather than a proof-dependent sum.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler

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
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsDirectUniformContextBounds

private abbrev tripleZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation

def compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
    (tokenCount boundaryTable numericBound bitBound : Nat) : Nat :=
  let body := compactAdditiveTripleBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let contextCodeBound :=
    tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    tripleBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
    tokenCount bodyCodeBound terminalResource

noncomputable def compactAdditiveTripleBoundaryRowsUniformBranchDirectBound
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound
      (extendValuation index tripleZeroValuation)
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound) := by
  let valuation := extendValuation index tripleZeroValuation
  let body := compactAdditiveTripleBoundaryRowsBranchTerminal
    tokenCount boundaryTable
  let values := compactAdditiveTripleBoundaryRowsDirectValues data
  let contextCodeBound :=
    tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    tripleBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  let terminalCertificate :=
    compactAdditiveTripleBoundaryRowsDirectTerminalCertificate
      tokenCount boundaryTable index data
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data :=
    compactAdditiveTripleBoundaryRowsDirectTerminalCertificate_structuralPayloadBound_le
      tokenCount boundaryTable index data
  have hterminalUniform :
      hybridFormulaStructuralPayloadBound terminalCertificate <=
        terminalResource :=
    hterminalStructural.trans
      (compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
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
    compactAdditiveTripleBoundaryRowsBranchTerminal_contextCodeSum_le
      tokenCount boundaryTable index numericBound (by omega)
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm tokenCount) 2 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveTripleBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity02
      contextCodeBound tokenCount bodyCodeBound body values
      (compactAdditiveTripleBoundaryRowsDirectValues_le data) hbody hcontext
      terminalResource terminalCertificate.compile hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable) :=
    (compactAdditiveTripleBoundaryRowsBody_free_alignment
      tokenCount boundaryTable).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope,
    valuation, body, contextCodeBound, bodyCodeBound, terminalResource]
    using hcoordinates.2

noncomputable def compileCompactAdditiveTripleBoundaryRowsUniformBranchDirect
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactAdditiveTripleBoundaryRowsBody
            tokenCount boundaryTable)).freeVariables
        (extendValuation index tripleZeroValuation))
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)) :=
  (compactAdditiveTripleBoundaryRowsUniformBranchDirectBound tokenCount
    boundaryTable index numericBound bitBound data htokenCount
    hindexSuccessor htableSize hnumericSize).proof

theorem compileCompactAdditiveTripleBoundaryRowsUniformBranchDirect_payloadLength_le
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsUniformBranchDirect tokenCount
      boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound :=
  (compactAdditiveTripleBoundaryRowsUniformBranchDirectBound tokenCount
    boundaryTable index numericBound bitBound data htokenCount
    hindexSuccessor htableSize hnumericSize).payloadLength_le

noncomputable def compactAdditiveTripleBoundaryRowsUniformDirectBranches
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable))
      count := by
  have hbodyVariables :
      (compactAdditiveTripleBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveTripleBoundaryRowsBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables count
    (fun index hindex =>
      compileCompactAdditiveTripleBoundaryRowsUniformBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)

def compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope tripleZeroValuation count
    (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable) ∅
    (fun _ =>
      compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    count

theorem
    compactAdditiveTripleBoundaryRowsUniformDirectBranches_structuralPayloadBound_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveTripleBoundaryRowsUniformDirectBranches tokenCount count
      boundaryTable numericBound bitBound rows htokenCount hcount htableSize
      hnumericSize).structuralPayloadBound count <=
      compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound := by
  have hbodyVariables :
      (compactAdditiveTripleBoundaryRowsBody
        tokenCount boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveTripleBoundaryRowsBody_freeVariables_eq_empty]
  unfold compactAdditiveTripleBoundaryRowsUniformDirectBranches
    compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables count
    (fun _ =>
      compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    count
    (fun index hindex =>
      compileCompactAdditiveTripleBoundaryRowsUniformBranchDirect tokenCount
        boundaryTable index numericBound bitBound (rows ⟨index, hindex⟩)
        htokenCount (by omega) htableSize hnumericSize)
    (fun index hindex =>
      compileCompactAdditiveTripleBoundaryRowsUniformBranchDirect_payloadLength_le
        tokenCount boundaryTable index numericBound bitBound
        (rows ⟨index, hindex⟩) htokenCount (by omega) htableSize
        hnumericSize)

theorem
    compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
    (tokenCount count boundaryTable numericBound bitBound : Nat) :
    compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial count
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)
        (compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
          tokenCount boundaryTable numericBound bitBound) := by
  unfold compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
      tokenCount boundaryTable numericBound bitBound)
    (fun _ =>
      compactAdditiveTripleBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound)
    (fun _ => Nat.le_refl _)

noncomputable def
    compileCompactAdditiveTripleBoundaryRowsUniformDirectUniversalContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactAdditiveTripleBoundaryRowsBody
        tokenCount boundaryTable).ballLT
          (shortBinaryNumeralTerm count)) := by
  let body := compactAdditiveTripleBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveTripleBoundaryRowsUniformDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveTripleBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        body.ballLT (shortBinaryNumeralTerm count)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

def compactAdditiveTripleBoundaryRowsUniformDirectUniversalResource
    (tokenCount count boundaryTable numericBound bitBound : Nat) : Nat :=
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ count
    (Rew.bShift (shortBinaryNumeralTerm count))
    (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)
    (closedShortBoundEqualityPayloadPolynomial count)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ count
      (Rewriting.free
        (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable))
      (compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound))

theorem
    compileCompactAdditiveTripleBoundaryRowsUniformDirectUniversalContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsUniformDirectUniversalContext
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsUniformDirectUniversalResource tokenCount
        count boundaryTable numericBound bitBound := by
  let body := compactAdditiveTripleBoundaryRowsBody
    tokenCount boundaryTable
  let branches := compactAdditiveTripleBoundaryRowsUniformDirectBranches
    tokenCount count boundaryTable numericBound bitBound rows htokenCount
    hcount htableSize hnumericSize
  let boundEquality := compactAdditiveTripleBoundaryRowsDirectBoundEquality count
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) count
    (Rew.bShift (shortBinaryNumeralTerm count)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial count
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial count := by
    simpa only [boundEquality,
      compactAdditiveTripleBoundaryRowsDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound count <=
      compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound :=
    compactAdditiveTripleBoundaryRowsUniformDirectBranches_structuralPayloadBound_le
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    (Rewriting.free body)
    (compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope
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
  unfold compileCompactAdditiveTripleBoundaryRowsUniformDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

noncomputable def
    compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContext
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveTripleBoundaryRowsClosedFormula
        tokenCount count boundaryTable) := by
  let direct :=
    compileCompactAdditiveTripleBoundaryRowsUniformDirectUniversalContext
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize
  exact CertifiedPAContextProof.cast
    (compactAdditiveTripleBoundaryRowsClosedFormula_alignment
      tokenCount count boundaryTable).symm direct

theorem compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
    (tokenCount count boundaryTable : Nat) :
    (compactAdditiveTripleBoundaryRowsClosedFormula
      tokenCount count boundaryTable).freeVariables = ∅ := by
  unfold compactAdditiveTripleBoundaryRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable

theorem
    compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContext_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData
        tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContext
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsUniformDirectUniversalResource tokenCount
        count boundaryTable numericBound bitBound := by
  unfold compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact
    compileCompactAdditiveTripleBoundaryRowsUniformDirectUniversalContext_payloadLength_le
      tokenCount count boundaryTable numericBound bitBound rows htokenCount
      hcount htableSize hnumericSize

noncomputable def
    compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveTripleBoundaryRowsClosedFormula
        tokenCount count boundaryTable) :=
  compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContext tokenCount
    count boundaryTable numericBound bitBound
    (compactAdditiveTripleBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

theorem
    compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount count boundaryTable numericBound bitBound hrows htokenCount
      hcount htableSize hnumericSize).payloadLength <=
      compactAdditiveTripleBoundaryRowsUniformDirectUniversalResource tokenCount
        count boundaryTable numericBound bitBound :=
  compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContext_payloadLength_le
    tokenCount count boundaryTable numericBound bitBound
    (compactAdditiveTripleBoundaryRowDataOfGraph
      tokenCount count boundaryTable hrows)
    htokenCount hcount htableSize hnumericSize

#print axioms compactAdditiveTripleBoundaryRowsUniformBranchDirectBound
#print axioms
  compileCompactAdditiveTripleBoundaryRowsUniformBranchDirect_payloadLength_le
#print axioms
  compactAdditiveTripleBoundaryRowsUniformDirectBranches_structuralPayloadBound_le
#print axioms
  compactAdditiveTripleBoundaryRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
#print axioms
  compileCompactAdditiveTripleBoundaryRowsUniformDirectUniversalContext_payloadLength_le
#print axioms compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
