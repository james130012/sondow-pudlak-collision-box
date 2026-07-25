import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler

/-!
# Branch-sensitive direct compiler for bounded binary-Nat status validity

The public-finite status envelope sums over every four-tuple below
`valueBound`.  That is useful for removing proof dependence, but it cannot be
used for a bit-length polynomial when `valueBound = 2 ^ tableWidth`.

This compiler instead retains the real running/failed/completed branch selected
by the checked graph.  Its terminal resource contains no generated proof
payload and does not enumerate the numerical witness range.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity04
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler

local notation "statusZeroValuation" =>
  FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate.zeroValuation

structure CompactBinaryNatStatusValidBoundedCanonicalDataBundle
    (tokenTable width tokenCount start finish valueBound : Nat) where
  data : CompactBinaryNatStatusValidBoundedData
    tokenTable width tokenCount start finish valueBound
  outputStart_le_tokenCount : data.outputStart <= tokenCount
  outputCount_le_tokenCount : data.outputCount <= tokenCount
  outputBoundary_size_le_area :
    Nat.size data.outputBoundary <= (tokenCount + 1) * tokenCount
  outputBoundarySize_le_area :
    data.outputBoundarySize <= (tokenCount + 1) * tokenCount

def compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
    (tokenCount : Nat) : Nat :=
  (tokenCount + 1) * tokenCount +
    Nat.size ((tokenCount + 1) * tokenCount) + Nat.size tokenCount + 1

theorem
    compactBinaryNatStatusValidBoundedCanonicalDataBundle_values_size_le_coordinateScale
    (tokenTable width tokenCount start finish valueBound : Nat)
    (bundle : CompactBinaryNatStatusValidBoundedCanonicalDataBundle
      tokenTable width tokenCount start finish valueBound)
    (index : Fin 4) :
    Nat.size (compactBinaryNatStatusValidBoundedValues bundle.data index) <=
      compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
        tokenCount := by
  have houtputStartSize : Nat.size bundle.data.outputStart <=
      Nat.size tokenCount :=
    Nat.size_le_size bundle.outputStart_le_tokenCount
  have houtputCountSize : Nat.size bundle.data.outputCount <=
      Nat.size tokenCount :=
    Nat.size_le_size bundle.outputCount_le_tokenCount
  have houtputBoundarySizeSize : Nat.size bundle.data.outputBoundarySize <=
      Nat.size ((tokenCount + 1) * tokenCount) :=
    Nat.size_le_size bundle.outputBoundarySize_le_area
  have htokenSizeScale : Nat.size tokenCount <=
      compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
        tokenCount := by
    unfold compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
    omega
  have hareaSizeScale : Nat.size ((tokenCount + 1) * tokenCount) <=
      compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
        tokenCount := by
    unfold compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
    omega
  have hareaScale : (tokenCount + 1) * tokenCount <=
      compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
        tokenCount := by
    unfold compactBinaryNatStatusValidBoundedCanonicalCoordinateScale
    omega
  fin_cases index
  · change Nat.size bundle.data.outputCount <= _
    exact houtputCountSize.trans htokenSizeScale
  · change Nat.size bundle.data.outputBoundarySize <= _
    exact houtputBoundarySizeSize.trans hareaSizeScale
  · change Nat.size bundle.data.outputBoundary <= _
    exact bundle.outputBoundary_size_le_area.trans hareaScale
  · change Nat.size bundle.data.outputStart <= _
    exact houtputStartSize.trans htokenSizeScale

noncomputable def compactBinaryNatStatusValidBoundedCanonicalDataBundleOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CompactBinaryNatStatusValidBoundedCanonicalDataBundle
      tokenTable width tokenCount start finish valueBound := by
  let data := compactBinaryNatStatusValidBoundedDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · let canonicalData : CompactBinaryNatStatusValidBoundedData
        tokenTable width tokenCount start finish valueBound :=
      { outputStart := 0
        outputStart_le_valueBound := Nat.zero_le _
        outputBoundary := 0
        outputBoundary_le_valueBound := Nat.zero_le _
        outputBoundarySize := 0
        outputBoundarySize_le_valueBound := Nat.zero_le _
        outputCount := 0
        outputCount_le_valueBound := Nat.zero_le _
        rows := Or.inl hrunning }
    exact
      { data := canonicalData
        outputStart_le_tokenCount := by simp [canonicalData]
        outputCount_le_tokenCount := by simp [canonicalData]
        outputBoundary_size_le_area := by simp [canonicalData]
        outputBoundarySize_le_area := by simp [canonicalData] }
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · let canonicalData : CompactBinaryNatStatusValidBoundedData
          tokenTable width tokenCount start finish valueBound :=
        { outputStart := 0
          outputStart_le_valueBound := Nat.zero_le _
          outputBoundary := 0
          outputBoundary_le_valueBound := Nat.zero_le _
          outputBoundarySize := 0
          outputBoundarySize_le_valueBound := Nat.zero_le _
          outputCount := 0
          outputCount_le_valueBound := Nat.zero_le _
          rows := Or.inr (Or.inl hfailed) }
      exact
        { data := canonicalData
          outputStart_le_tokenCount := by simp [canonicalData]
          outputCount_le_tokenCount := by simp [canonicalData]
          outputBoundary_size_le_area := by simp [canonicalData]
          outputBoundarySize_le_area := by simp [canonicalData] }
    · have hcompleted := compactBinaryNatCompletedStatusValidRows_of_data
        data hrunning hfailed
      let canonicalData : CompactBinaryNatStatusValidBoundedData
          tokenTable width tokenCount start finish valueBound :=
        { outputStart := data.outputStart
          outputStart_le_valueBound := data.outputStart_le_valueBound
          outputBoundary := data.outputBoundary
          outputBoundary_le_valueBound := data.outputBoundary_le_valueBound
          outputBoundarySize := data.outputBoundarySize
          outputBoundarySize_le_valueBound :=
            data.outputBoundarySize_le_valueBound
          outputCount := data.outputCount
          outputCount_le_valueBound := data.outputCount_le_valueBound
          rows := Or.inr (Or.inr hcompleted) }
      rcases hcompleted with
        ⟨hprefix, hlayout, hunit, hsizeEq, hsizeBound⟩
      simp only [compactBinaryNatStatusValidityWitnessOf] at hprefix hlayout hunit hsizeEq hsizeBound
      have houtputStart : data.outputStart <= tokenCount := by
        rcases hprefix with
          ⟨innerStart, _hinnerStart, _houterCell, hinnerCell⟩
        have hinnerLt := hinnerCell.1
        have houtputEq := hinnerCell.2.1
        omega
      have hfinishEq : finish =
          data.outputStart + 1 + data.outputCount :=
        CompactAdditiveStructuredListLayout.finish_eq_start_add_count
          hlayout hunit
      have hfinishBound : finish <= tokenCount := by
        rcases hlayout with
          ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
        exact hboundary.2.1
      have houtputCount : data.outputCount <= tokenCount := by omega
      have houtputArea :
          (data.outputCount + 1) * tokenCount <=
            (tokenCount + 1) * tokenCount :=
        Nat.mul_le_mul_right tokenCount
          (Nat.add_le_add_right houtputCount 1)
      have hboundarySize :
          Nat.size data.outputBoundary <=
            (tokenCount + 1) * tokenCount := by
        rw [← hsizeEq]
        exact hsizeBound.trans houtputArea
      exact
        { data := canonicalData
          outputStart_le_tokenCount := by
            simpa only [canonicalData] using houtputStart
          outputCount_le_tokenCount := by
            simpa only [canonicalData] using houtputCount
          outputBoundary_size_le_area := by
            simpa only [canonicalData] using hboundarySize
          outputBoundarySize_le_area := by
            simpa only [canonicalData] using hsizeBound.trans houtputArea }

noncomputable def compactBinaryNatStatusValidBoundedCanonicalDataOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound :=
  (compactBinaryNatStatusValidBoundedCanonicalDataBundleOfGraph
    tokenTable width tokenCount start finish valueBound hgraph).data

noncomputable def
    compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
    tokenTable width tokenCount start finish valueBound
    (compactBinaryNatStatusValidBoundedCanonicalDataOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def
    compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 4
    (compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish)
    valueBound
    (compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
      tokenTable width tokenCount start finish)
    (compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    ExplicitDirectFormulaBound statusZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph) := by
  let canonicalData := compactBinaryNatStatusValidBoundedCanonicalDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  let data := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData
    tokenTable width tokenCount start finish valueBound canonicalData
  let rawBody := compactBinaryNatStatusValidBoundedRawTerminal
    tokenTable width tokenCount start finish
  let contextCodeBound :=
    compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish
  let bodyCodeBound := compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
    tokenTable width tokenCount start finish
  let terminalResource :=
    compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound data.terminal <= terminalResource := by
    simpa only [terminalResource,
      compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph]
      using
        compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_transparent
          tokenTable width tokenCount start finish valueBound canonicalData
  have hterminal : data.terminal.compile.payloadLength <= terminalResource :=
    (compile_payloadLength_le_structuralPayloadBound data.terminal).trans
      hterminalStructural
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables statusZeroValuation) <=
        contextCodeBound :=
    Nat.le_refl _
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 4 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody data.values data.values_le
      hbody hcontext terminalResource data.terminal.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity04
      contextCodeBound valueBound bodyCodeBound rawBody data.values
      data.values_le hbody hcontext terminalResource data.terminal.compile
      hterminal
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
  exact hcoordinates.2

noncomputable def
    compactBinaryNatStatusValidBoundedCanonicalAllBranchesTerminalResourceOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  let data := compactBinaryNatStatusValidBoundedCanonicalDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
    tokenTable width tokenCount start finish data.outputStart
    data.outputBoundary data.outputBoundarySize data.outputCount

noncomputable def
    compactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectPayloadEnvelopeOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 4
    (compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish)
    valueBound
    (compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
      tokenTable width tokenCount start finish)
    (compactBinaryNatStatusValidBoundedCanonicalAllBranchesTerminalResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def
    compactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectBoundOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    ExplicitDirectFormulaBound statusZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph) := by
  let canonicalData := compactBinaryNatStatusValidBoundedCanonicalDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  let data := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData
    tokenTable width tokenCount start finish valueBound canonicalData
  let rawBody := compactBinaryNatStatusValidBoundedRawTerminal
    tokenTable width tokenCount start finish
  let contextCodeBound :=
    compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish
  let bodyCodeBound := compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
    tokenTable width tokenCount start finish
  let terminalResource :=
    compactBinaryNatStatusValidBoundedCanonicalAllBranchesTerminalResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph
  have hterminalTransparent :
      hybridFormulaStructuralPayloadBound data.terminal <=
        compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
          tokenTable width tokenCount start finish valueBound
          canonicalData := by
    simpa only [data] using
      compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_transparent
        tokenTable width tokenCount start finish valueBound canonicalData
  have hterminalAllBranches :
      compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
          tokenTable width tokenCount start finish valueBound canonicalData <=
        terminalResource := by
    simpa only [terminalResource,
      compactBinaryNatStatusValidBoundedCanonicalAllBranchesTerminalResourceOfGraph,
      canonicalData] using
      compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData_le_allBranches
        tokenTable width tokenCount start finish valueBound canonicalData
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound data.terminal <= terminalResource :=
    hterminalTransparent.trans hterminalAllBranches
  have hterminal : data.terminal.compile.payloadLength <= terminalResource :=
    (compile_payloadLength_le_structuralPayloadBound data.terminal).trans
      hterminalStructural
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables statusZeroValuation) <=
        contextCodeBound :=
    Nat.le_refl _
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 4 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody data.values data.values_le
      hbody hcontext terminalResource data.terminal.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity04
      contextCodeBound valueBound bodyCodeBound rawBody data.values
      data.values_le hbody hcontext terminalResource data.terminal.compile
      hterminal
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
  exact hcoordinates.2

noncomputable def
    compileCompactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectAtValuationOfGraph
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
  let direct :=
    compactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectBoundOfGraph
      tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          statusZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext direct.proof

theorem
    compileCompactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
        hgraph).payloadLength <=
      compactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let direct :=
    compactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectBoundOfGraph
      tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          statusZeroValuation =
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

noncomputable def
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph
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
  let direct := compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          statusZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext direct.proof

theorem
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
        hgraph).payloadLength <=
      compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let direct := compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          statusZeroValuation =
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
  compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
#print axioms
  compactBinaryNatStatusValidBoundedCanonicalDataBundle_values_size_le_coordinateScale
#print axioms
  compactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectBoundOfGraph
#print axioms
  compileCompactBinaryNatStatusValidBoundedCanonicalAllBranchesDirectAtValuationOfGraph_payloadLength_le
#print axioms
  compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler
