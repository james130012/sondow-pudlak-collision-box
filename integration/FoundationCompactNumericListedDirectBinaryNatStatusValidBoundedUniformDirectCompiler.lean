import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectCompiler

/-!
# Uniform direct compiler for bounded binary-Nat status validity

The status terminal selects the actual running, failed, or completed branch.
The completed branch uses the fully uniform direct structured-list and
unit-boundary compilers.  Its hidden body-start witness is absorbed into a
public finite resource envelope before the three branches are joined.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity04
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectCompiler

local notation "completedZeroValuation" =>
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

def compactBinaryNatCompletedStatusDirectNumericBound
    (tokenCount : Nat) : Nat :=
  (tokenCount + 1) * tokenCount

def compactBinaryNatCompletedStatusDirectBitBound
    (tokenCount : Nat) : Nat :=
  compactBinaryNatStatusValidBoundedCanonicalCoordinateScale tokenCount

def compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : ValuationFormula :=
  compactBinaryNatRunningStatusSliceClosedFormula
      tokenTable width tokenCount start finish ⋎
    (compactBinaryNatFailedStatusSliceClosedFormula
        tokenTable width tokenCount start finish ⋎
      compactBinaryNatCompletedStatusUniformDirectFormula tokenTable width
        tokenCount start finish outputStart outputBoundary outputBoundarySize
        outputCount)

def compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let completedFormula := compactBinaryNatCompletedStatusUniformDirectFormula
    tokenTable width tokenCount start finish outputStart outputBoundary
    outputBoundarySize outputCount
  let numericBound := compactBinaryNatCompletedStatusDirectNumericBound tokenCount
  let bitBound := compactBinaryNatCompletedStatusDirectBitBound tokenCount
  let runningResource := transparentHybridDisjunctionLeftPayloadEnvelope
    completedZeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
      tokenTable width tokenCount start finish)
  let failedResource := transparentHybridDisjunctionRightPayloadEnvelope
    completedZeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (transparentHybridDisjunctionLeftPayloadEnvelope completedZeroValuation
      failedFormula completedFormula
      (compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
        tokenTable width tokenCount start finish))
  let completedResource := transparentHybridDisjunctionRightPayloadEnvelope
    completedZeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (transparentHybridDisjunctionRightPayloadEnvelope completedZeroValuation
      failedFormula completedFormula
      (compactBinaryNatCompletedStatusFullyUniformDirectPublicPayloadEnvelope tokenTable
        width tokenCount start finish outputStart outputBoundary
        outputBoundarySize outputCount numericBound bitBound))
  runningResource + failedResource + completedResource

noncomputable def
    compactBinaryNatStatusValidBoundedUniformDirectTerminalBoundOfCanonicalBundle
    (tokenTable width tokenCount start finish valueBound : Nat)
    (bundle : CompactBinaryNatStatusValidBoundedCanonicalDataBundle
      tokenTable width tokenCount start finish valueBound) :
    ExplicitDirectFormulaBound completedZeroValuation
      (compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
        tokenTable width tokenCount start finish bundle.data.outputStart
        bundle.data.outputBoundary bundle.data.outputBoundarySize
        bundle.data.outputCount)
      (compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
        tokenTable width tokenCount start finish bundle.data.outputStart
        bundle.data.outputBoundary bundle.data.outputBoundarySize
        bundle.data.outputCount) := by
  let data := bundle.data
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let completedFormula := compactBinaryNatCompletedStatusUniformDirectFormula
    tokenTable width tokenCount start finish data.outputStart
    data.outputBoundary data.outputBoundarySize data.outputCount
  let numericBound :=
    compactBinaryNatCompletedStatusDirectNumericBound tokenCount
  let bitBound := compactBinaryNatCompletedStatusDirectBitBound tokenCount
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · let runningCertificate :=
      compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount start finish hrunning
    let runningProof := runningCertificate.compile
    let direct := compileDirectDisjunctionLeft
      (right := failedFormula ⋎ completedFormula) runningProof
    have hrunningProof : runningProof.payloadLength <=
        compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
          tokenTable width tokenCount start finish :=
      (compile_payloadLength_le_structuralPayloadBound runningCertificate).trans
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount start finish hrunning)
    have hdirect := compileDirectDisjunctionLeft_payloadLength_le
      (right := failedFormula ⋎ completedFormula) runningProof _ hrunningProof
    refine { proof := direct, payloadLength_le := ?_ }
    exact hdirect.trans (by
      unfold
        compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
      dsimp only [data, runningFormula, failedFormula, completedFormula,
        numericBound, bitBound]
      omega)
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · let failedCertificate :=
        compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hfailed
      let failedProof := failedCertificate.compile
      let inner := compileDirectDisjunctionLeft
        (right := completedFormula) failedProof
      let direct := compileDirectDisjunctionRight
        (left := runningFormula) inner
      have hfailedProof : failedProof.payloadLength <=
          compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
            tokenTable width tokenCount start finish :=
        (compile_payloadLength_le_structuralPayloadBound failedCertificate).trans
          (compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
            tokenTable width tokenCount start finish hfailed)
      have hinner := compileDirectDisjunctionLeft_payloadLength_le
        (right := completedFormula) failedProof _ hfailedProof
      have hdirect := compileDirectDisjunctionRight_payloadLength_le
        (left := runningFormula) inner _ hinner
      refine { proof := direct, payloadLength_le := ?_ }
      exact hdirect.trans (by
        unfold
          compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
        dsimp only [data, runningFormula, failedFormula, completedFormula,
          numericBound, bitBound]
        omega)
    · let hcompleted := compactBinaryNatCompletedStatusValidRows_of_data
        data hrunning hfailed
      have htokenCount : tokenCount <= numericBound := by
        unfold numericBound compactBinaryNatCompletedStatusDirectNumericBound
        rw [Nat.add_mul]
        simp
      have houtputCount : data.outputCount <= numericBound :=
        bundle.outputCount_le_tokenCount.trans htokenCount
      have htableSize : Nat.size data.outputBoundary <= bitBound := by
        unfold bitBound compactBinaryNatCompletedStatusDirectBitBound
          compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
        exact bundle.outputBoundary_size_le_area.trans (by omega)
      have hnumericSize : Nat.size numericBound <= bitBound := by
        unfold numericBound bitBound
          compactBinaryNatCompletedStatusDirectNumericBound
          compactBinaryNatCompletedStatusDirectBitBound
          compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
        omega
      let completedProof :=
        compileCompactBinaryNatCompletedStatusFullyUniformDirect tokenTable width
          tokenCount start finish data.outputStart data.outputBoundary
          data.outputBoundarySize data.outputCount numericBound bitBound
          hcompleted htokenCount houtputCount htableSize hnumericSize
      let completedResource :=
        compactBinaryNatCompletedStatusFullyUniformDirectPublicPayloadEnvelope tokenTable
          width tokenCount start finish data.outputStart data.outputBoundary
          data.outputBoundarySize data.outputCount numericBound bitBound
      have hcompletedProof : completedProof.payloadLength <= completedResource :=
        compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le_public
          tokenTable width tokenCount start finish data.outputStart
          data.outputBoundary data.outputBoundarySize data.outputCount
          numericBound bitBound hcompleted htokenCount houtputCount htableSize
          hnumericSize
      let inner := compileDirectDisjunctionRight
        (left := failedFormula) completedProof
      let direct := compileDirectDisjunctionRight
        (left := runningFormula) inner
      have hinner := compileDirectDisjunctionRight_payloadLength_le
        (left := failedFormula) completedProof completedResource hcompletedProof
      have hdirect := compileDirectDisjunctionRight_payloadLength_le
        (left := runningFormula) inner _ hinner
      refine { proof := direct, payloadLength_le := ?_ }
      exact hdirect.trans (by
        unfold
          compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
        dsimp only [data, runningFormula, failedFormula, completedFormula,
          numericBound, bitBound, completedResource]
        omega)

noncomputable def
    compileCompactBinaryNatStatusValidBoundedUniformDirectTerminalOfCanonicalBundle
    (tokenTable width tokenCount start finish valueBound : Nat)
    (bundle : CompactBinaryNatStatusValidBoundedCanonicalDataBundle
      tokenTable width tokenCount start finish valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
          tokenTable width tokenCount start finish bundle.data.outputStart
          bundle.data.outputBoundary bundle.data.outputBoundarySize
          bundle.data.outputCount).freeVariables
        completedZeroValuation)
      (compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
        tokenTable width tokenCount start finish bundle.data.outputStart
        bundle.data.outputBoundary bundle.data.outputBoundarySize
        bundle.data.outputCount) :=
  (compactBinaryNatStatusValidBoundedUniformDirectTerminalBoundOfCanonicalBundle
    tokenTable width tokenCount start finish valueBound bundle).proof

theorem
    compileCompactBinaryNatStatusValidBoundedUniformDirectTerminalOfCanonicalBundle_payloadLength_le
    (tokenTable width tokenCount start finish valueBound : Nat)
    (bundle : CompactBinaryNatStatusValidBoundedCanonicalDataBundle
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedUniformDirectTerminalOfCanonicalBundle
      tokenTable width tokenCount start finish valueBound bundle).payloadLength <=
      compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
        tokenTable width tokenCount start finish bundle.data.outputStart
        bundle.data.outputBoundary bundle.data.outputBoundarySize
        bundle.data.outputCount :=
  (compactBinaryNatStatusValidBoundedUniformDirectTerminalBoundOfCanonicalBundle
    tokenTable width tokenCount start finish valueBound bundle).payloadLength_le

noncomputable def
    compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  let bundle :=
    compactBinaryNatStatusValidBoundedCanonicalDataBundleOfGraph tokenTable
      width tokenCount start finish valueBound hgraph
  explicitBoundedWitnessDirectPublicPayloadEnvelope 4
    (compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish)
    valueBound
    (compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
      tokenTable width tokenCount start finish)
    (compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
      tokenTable width tokenCount start finish bundle.data.outputStart
      bundle.data.outputBoundary bundle.data.outputBoundarySize
      bundle.data.outputCount)

noncomputable def
    compactBinaryNatStatusValidBoundedUniformDirectBoundOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    ExplicitDirectFormulaBound completedZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph) := by
  let bundle :=
    compactBinaryNatStatusValidBoundedCanonicalDataBundleOfGraph tokenTable
      width tokenCount start finish valueBound hgraph
  let data := bundle.data
  let values := compactBinaryNatStatusValidBoundedValues data
  let rawBody := compactBinaryNatStatusValidBoundedRawTerminal
    tokenTable width tokenCount start finish
  let terminalFormula :=
    compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula tokenTable
      width tokenCount start finish data.outputStart data.outputBoundary
      data.outputBoundarySize data.outputCount
  let contextCodeBound :=
    compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish
  let bodyCodeBound := compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
    tokenTable width tokenCount start finish
  let terminalResource :=
    compactBinaryNatStatusValidBoundedUniformDirectTerminalEnvelopeOfValues
      tokenTable width tokenCount start finish data.outputStart
      data.outputBoundary data.outputBoundarySize data.outputCount
  let terminalRaw :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectTerminalOfCanonicalBundle
      tokenTable width tokenCount start finish valueBound bundle
  have hvalueTerms :
      (fun index : Fin 4 => shortBinaryNumeralTerm (values index)) =
        ![shortBinaryNumeralTerm data.outputCount,
          shortBinaryNumeralTerm data.outputBoundarySize,
          shortBinaryNumeralTerm data.outputBoundary,
          shortBinaryNumeralTerm data.outputStart] := by
    funext index
    fin_cases index <;> rfl
  have hterminalFormula : terminalFormula =
      rawBody ⇜ fun index => shortBinaryNumeralTerm (values index) := by
    rw [hvalueTerms]
    simpa only [terminalFormula,
      compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula,
      compactBinaryNatCompletedStatusUniformDirectFormula,
      rawBody, data, values] using
      (compactBinaryNatStatusValidBoundedRawTerminal_alignment tokenTable
        width tokenCount start finish data.outputStart data.outputBoundary
        data.outputBoundarySize data.outputCount).symm
  let terminalProof :=
    castValuationContextProof hterminalFormula terminalRaw
  have hterminalRaw : terminalRaw.payloadLength <= terminalResource :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectTerminalOfCanonicalBundle_payloadLength_le
      tokenTable width tokenCount start finish valueBound bundle
  have hterminal : terminalProof.payloadLength <= terminalResource := by
    dsimp only [terminalProof]
    rw [castValuationContextProof_payloadLength_eq]
    exact hterminalRaw
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables completedZeroValuation) <=
        contextCodeBound := Nat.le_refl _
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 4 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody values
      (compactBinaryNatStatusValidBoundedValues_le data)
      hbody hcontext terminalResource terminalProof hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity04
      contextCodeBound valueBound bodyCodeBound rawBody values
      (compactBinaryNatStatusValidBoundedValues_le data)
      hbody hcontext terminalResource terminalProof hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound :=
    (compactBinaryNatStatusValidBoundedClosedFormula_alignment
      tokenTable width tokenCount start finish valueBound).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph,
    bundle, data, rawBody, values, contextCodeBound, bodyCodeBound,
    terminalResource] using hcoordinates.2

noncomputable def
    compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount start finish valueBound).freeVariables
        valuation)
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound) := by
  let direct := compactBinaryNatStatusValidBoundedUniformDirectBoundOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          completedZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext direct.proof

theorem
    compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
      hgraph).payloadLength <=
      compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let direct := compactBinaryNatStatusValidBoundedUniformDirectBoundOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          completedZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  change (CertifiedPAContextProof.castContext hcontext direct.proof).payloadLength
    <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact direct.payloadLength_le

#print axioms
  compactBinaryNatStatusValidBoundedUniformDirectTerminalBoundOfCanonicalBundle
#print axioms
  compileCompactBinaryNatStatusValidBoundedUniformDirectTerminalOfCanonicalBundle
#print axioms
  compileCompactBinaryNatStatusValidBoundedUniformDirectTerminalOfCanonicalBundle_payloadLength_le
#print axioms compactBinaryNatStatusValidBoundedUniformDirectBoundOfGraph
#print axioms
  compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectCompiler
