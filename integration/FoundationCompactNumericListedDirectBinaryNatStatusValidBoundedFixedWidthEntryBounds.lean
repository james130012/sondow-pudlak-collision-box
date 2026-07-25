import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds

/-!
# Fixed-width-entry bounds for bounded binary-Nat status validity

The completed status branch contains a structured-list layout and a table of
unit boundary rows.  This layer rebuilds that actual branch with the complete
fixed-width-entry endpoints, then carries the result through the three status
alternatives and the four bounded witnesses.  The core graph-dependent bounds
do not enumerate `valueBound`.  The later `PublicFinite` declarations are only
logical completeness fallbacks; their four range sums are not admissible as
the final bit-width-polynomial route.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedFixedWidthEntryBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity04
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

local notation "statusZeroValuation" =>
  FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate.zeroValuation

noncomputable def
    compactBinaryNatCompletedStatusFixedWidthEntryStructuralPayloadEnvelope
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : Nat :=
  let prefixFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount start outputStart
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount outputCount outputBoundary
  let sizeFormula := compactNatSizeClosedFormula
    outputBoundarySize outputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let prefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart
  let layoutResource :=
    compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitResource :=
    compactAdditiveUnitBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
      tokenCount outputCount outputBoundary
  let sizeResource := compactNatSizeStructuralPayloadPolynomial
    outputBoundarySize outputBoundary
  let areaResource := completedAreaStructuralPayloadPolynomial
    tokenCount outputCount outputBoundarySize
  let sizeAreaResource := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation sizeFormula areaFormula sizeResource areaResource
  let unitTailResource := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation unitFormula (sizeFormula ⋏ areaFormula)
    unitResource sizeAreaResource
  let layoutTailResource := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation layoutFormula
    (unitFormula ⋏ (sizeFormula ⋏ areaFormula))
    layoutResource unitTailResource
  hybridConjunctionStructuralPayloadEnvelope statusZeroValuation prefixFormula
    (layoutFormula ⋏ (unitFormula ⋏ (sizeFormula ⋏ areaFormula)))
    prefixResource layoutTailResource

theorem
    compactBinaryNatCompletedStatusExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf
          outputStart outputBoundary outputBoundarySize outputCount)) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatCompletedStatusExplicitHybridCertificate
          tokenTable width tokenCount start finish outputStart outputBoundary
            outputBoundarySize outputCount hcompleted) <=
      compactBinaryNatCompletedStatusFixedWidthEntryStructuralPayloadEnvelope
        tokenTable width tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount := by
  let prefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hcompleted.1
  let layoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      hcompleted.2.1
  let unitCertificate :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount outputCount outputBoundary hcompleted.2.2.1
  let sizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    outputBoundarySize outputBoundary hcompleted.2.2.2.1
  let areaCertificate := completedAreaCertificate
    tokenCount outputCount outputBoundarySize hcompleted.2.2.2.2
  have hprefix :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount start outputStart hcompleted.1
  have hlayout :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_fixedWidthEntry
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      hcompleted.2.1
  have hunitTransparent :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount outputCount outputBoundary hcompleted.2.2.1
  have hunit := hunitTransparent.trans
    (compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_fixedWidthEntry
      tokenCount outputCount outputBoundary hcompleted.2.2.1)
  have hsize :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      outputBoundarySize outputBoundary hcompleted.2.2.2.1
  have harea := completedAreaCertificate_structuralPayloadBound_le_public
    tokenCount outputCount outputBoundarySize hcompleted.2.2.2.2
  have hsizeArea := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := statusZeroValuation)
    sizeCertificate areaCertificate _ _ hsize harea
  have hunitTail := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := statusZeroValuation)
    unitCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sizeCertificate areaCertificate) _ _ hunit hsizeArea
  have hlayoutTail := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := statusZeroValuation)
    layoutCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      unitCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        sizeCertificate areaCertificate)) _ _ hlayout hunitTail
  have hcompletedBound := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := statusZeroValuation)
    prefixCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      layoutCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        unitCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          sizeCertificate areaCertificate))) _ _ hprefix hlayoutTail
  simpa only [compactBinaryNatCompletedStatusExplicitHybridCertificate,
    compactBinaryNatCompletedStatusFixedWidthEntryStructuralPayloadEnvelope,
    prefixCertificate, layoutCertificate, unitCertificate,
    sizeCertificate, areaCertificate] using hcompletedBound

noncomputable def
    compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let completedFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
        tokenTable width tokenCount start outputStart ⋏
      (compactAdditiveStructuredListLayoutClosedFormula
          tokenTable width tokenCount outputStart outputCount finish
            outputBoundary ⋏
        (compactAdditiveUnitBoundaryRowsClosedFormula
            tokenCount outputCount outputBoundary ⋏
          (compactNatSizeClosedFormula outputBoundarySize outputBoundary ⋏
            “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
              (!!(shortBinaryNumeralTerm outputCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)”)))
  let runningResource := hybridDisjunctionLeftStructuralPayloadEnvelope
    statusZeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
      tokenTable width tokenCount start finish)
  let failedResource := hybridDisjunctionRightStructuralPayloadEnvelope
    statusZeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (hybridDisjunctionLeftStructuralPayloadEnvelope statusZeroValuation
      failedFormula completedFormula
      (compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
        tokenTable width tokenCount start finish))
  let completedResource := hybridDisjunctionRightStructuralPayloadEnvelope
    statusZeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (hybridDisjunctionRightStructuralPayloadEnvelope statusZeroValuation
      failedFormula completedFormula
      (compactBinaryNatCompletedStatusFixedWidthEntryStructuralPayloadEnvelope
        tokenTable width tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount))
  runningResource + failedResource + completedResource

theorem
    compactBinaryNatStatusValidBoundedTerminalPartsOfData_structuralPayloadBound_le_allBranchesFixedWidthEntry
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatStatusValidBoundedTerminalPartsOfData
          tokenTable width tokenCount start finish valueBound data) <=
      compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
        tokenTable width tokenCount start finish data.outputStart
          data.outputBoundary data.outputBoundarySize data.outputCount := by
  classical
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let completedFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
        tokenTable width tokenCount start data.outputStart ⋏
      (compactAdditiveStructuredListLayoutClosedFormula
          tokenTable width tokenCount data.outputStart data.outputCount finish
            data.outputBoundary ⋏
        (compactAdditiveUnitBoundaryRowsClosedFormula
            tokenCount data.outputCount data.outputBoundary ⋏
          (compactNatSizeClosedFormula
              data.outputBoundarySize data.outputBoundary ⋏
            “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
              (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)”)))
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · let runningCertificate :=
      compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount start finish hrunning
    have hrunningBound :=
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenTable width tokenCount start finish hrunning
    have houter := hybridDisjunctionLeftStructuralPayloadBound_le_envelope
      (valuation := statusZeroValuation) (right := failedFormula ⋎ completedFormula)
      runningCertificate _ hrunningBound
    have hactual :
        hybridFormulaStructuralPayloadBound
            (compactBinaryNatStatusValidBoundedTerminalPartsOfData
              tokenTable width tokenCount start finish valueBound data) <=
          hybridDisjunctionLeftStructuralPayloadEnvelope statusZeroValuation
            runningFormula (failedFormula ⋎ completedFormula)
            (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
              tokenTable width tokenCount start finish) := by
      simpa only [compactBinaryNatStatusValidBoundedTerminalPartsOfData,
        hrunning, dite_true, runningCertificate, runningFormula,
        failedFormula, completedFormula] using houter
    exact hactual.trans (by
      unfold
        compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
      dsimp only [runningFormula, failedFormula, completedFormula]
      omega)
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · let failedCertificate :=
        compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hfailed
      have hfailedBound :=
        compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount start finish hfailed
      have hinner := hybridDisjunctionLeftStructuralPayloadBound_le_envelope
        (valuation := statusZeroValuation) (right := completedFormula)
        failedCertificate _ hfailedBound
      have houter := hybridDisjunctionRightStructuralPayloadBound_le_envelope
        (valuation := statusZeroValuation) (left := runningFormula)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := completedFormula) failedCertificate) _ hinner
      have hactual :
          hybridFormulaStructuralPayloadBound
              (compactBinaryNatStatusValidBoundedTerminalPartsOfData
                tokenTable width tokenCount start finish valueBound data) <=
            hybridDisjunctionRightStructuralPayloadEnvelope
              statusZeroValuation runningFormula
              (failedFormula ⋎ completedFormula)
              (hybridDisjunctionLeftStructuralPayloadEnvelope
                statusZeroValuation failedFormula completedFormula
                (compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
                  tokenTable width tokenCount start finish)) := by
        simpa only [compactBinaryNatStatusValidBoundedTerminalPartsOfData,
          hrunning, hfailed, dite_false, dite_true, failedCertificate,
          runningFormula, failedFormula, completedFormula] using houter
      exact hactual.trans (by
        unfold
          compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
        dsimp only [runningFormula, failedFormula, completedFormula]
        omega)
    · let hcompleted := compactBinaryNatCompletedStatusValidRows_of_data
        data hrunning hfailed
      let completedCertificate :=
        compactBinaryNatCompletedStatusExplicitHybridCertificate
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize data.outputCount
              hcompleted
      have hcompletedBound :=
        compactBinaryNatCompletedStatusExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize data.outputCount
              hcompleted
      have hinner := hybridDisjunctionRightStructuralPayloadBound_le_envelope
        (valuation := statusZeroValuation) (left := failedFormula)
        completedCertificate _ hcompletedBound
      have houter := hybridDisjunctionRightStructuralPayloadBound_le_envelope
        (valuation := statusZeroValuation) (left := runningFormula)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := failedFormula) completedCertificate) _ hinner
      have hactual :
          hybridFormulaStructuralPayloadBound
              (compactBinaryNatStatusValidBoundedTerminalPartsOfData
                tokenTable width tokenCount start finish valueBound data) <=
            hybridDisjunctionRightStructuralPayloadEnvelope
              statusZeroValuation runningFormula
              (failedFormula ⋎ completedFormula)
              (hybridDisjunctionRightStructuralPayloadEnvelope
                statusZeroValuation failedFormula completedFormula
                (compactBinaryNatCompletedStatusFixedWidthEntryStructuralPayloadEnvelope
                  tokenTable width tokenCount start finish data.outputStart
                    data.outputBoundary data.outputBoundarySize
                    data.outputCount)) := by
        simpa only [compactBinaryNatStatusValidBoundedTerminalPartsOfData,
          hrunning, hfailed, dite_false, completedCertificate, hcompleted,
          runningFormula, failedFormula, completedFormula] using houter
      exact hactual.trans (by
        unfold
          compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
        dsimp only [runningFormula, failedFormula, completedFormula]
        omega)

noncomputable def
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  let data := compactBinaryNatStatusValidBoundedCanonicalDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
    tokenTable width tokenCount start finish data.outputStart
      data.outputBoundary data.outputBoundarySize data.outputCount

def
    compactBinaryNatStatusValidBoundedTerminalFixedWidthEntryPublicFiniteEnvelope
    (tokenTable width tokenCount start finish valueBound : Nat) : Nat :=
  (Finset.range (valueBound + 1)).sum fun outputStart =>
    (Finset.range (valueBound + 1)).sum fun outputBoundary =>
      (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
        (Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
            tokenTable width tokenCount start finish outputStart outputBoundary
              outputBoundarySize outputCount

theorem
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph_le_publicFinite
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph
        tokenTable width tokenCount start finish valueBound hgraph <=
      compactBinaryNatStatusValidBoundedTerminalFixedWidthEntryPublicFiniteEnvelope
        tokenTable width tokenCount start finish valueBound := by
  let data := compactBinaryNatStatusValidBoundedCanonicalDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcount :
      compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize data.outputCount <=
        (Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
            tokenTable width tokenCount start finish data.outputStart
              data.outputBoundary data.outputBoundarySize outputCount := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize candidate))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputCount_le_valueBound))
  have hsize :
      ((Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
            tokenTable width tokenCount start finish data.outputStart
              data.outputBoundary data.outputBoundarySize outputCount) <=
        (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
          (Finset.range (valueBound + 1)).sum fun outputCount =>
            compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
              tokenTable width tokenCount start finish data.outputStart
                data.outputBoundary outputBoundarySize outputCount := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
            tokenTable width tokenCount start finish data.outputStart
              data.outputBoundary candidate outputCount))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputBoundarySize_le_valueBound))
  have hboundary :
      ((Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
          (Finset.range (valueBound + 1)).sum fun outputCount =>
            compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
              tokenTable width tokenCount start finish data.outputStart
                data.outputBoundary outputBoundarySize outputCount) <=
        (Finset.range (valueBound + 1)).sum fun outputBoundary =>
          (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
            (Finset.range (valueBound + 1)).sum fun outputCount =>
              compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
                tokenTable width tokenCount start finish data.outputStart
                  outputBoundary outputBoundarySize outputCount := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
          (Finset.range (valueBound + 1)).sum fun outputCount =>
            compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
              tokenTable width tokenCount start finish data.outputStart
                candidate outputBoundarySize outputCount))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputBoundary_le_valueBound))
  have hstart :
      ((Finset.range (valueBound + 1)).sum fun outputBoundary =>
          (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
            (Finset.range (valueBound + 1)).sum fun outputCount =>
              compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
                tokenTable width tokenCount start finish data.outputStart
                  outputBoundary outputBoundarySize outputCount) <=
        compactBinaryNatStatusValidBoundedTerminalFixedWidthEntryPublicFiniteEnvelope
          tokenTable width tokenCount start finish valueBound := by
    unfold
      compactBinaryNatStatusValidBoundedTerminalFixedWidthEntryPublicFiniteEnvelope
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (valueBound + 1)).sum fun outputBoundary =>
          (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
            (Finset.range (valueBound + 1)).sum fun outputCount =>
              compactBinaryNatStatusValidBoundedTerminalAllBranchesFixedWidthEntryEnvelopeOfValues
                tokenTable width tokenCount start finish candidate
                  outputBoundary outputBoundarySize outputCount))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputStart_le_valueBound))
  unfold
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph
  dsimp only [data]
  exact hcount.trans (hsize.trans (hboundary.trans hstart))

noncomputable def
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectPayloadEnvelopeOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 4
    (compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish)
    valueBound
    (compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
      tokenTable width tokenCount start finish)
    (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectBoundOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    ExplicitDirectFormulaBound statusZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectPayloadEnvelopeOfGraph
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
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound data.terminal <= terminalResource := by
    have hparts :=
      compactBinaryNatStatusValidBoundedTerminalPartsOfData_structuralPayloadBound_le_allBranchesFixedWidthEntry
        tokenTable width tokenCount start finish valueBound canonicalData
    simpa only [data,
      compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData,
      hybridFormulaStructuralPayloadBound, terminalResource,
      compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph,
      canonicalData] using hparts
  have hterminal : data.terminal.compile.payloadLength <= terminalResource :=
    (compile_payloadLength_le_structuralPayloadBound data.terminal).trans
      hterminalStructural
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables statusZeroValuation) <=
        contextCodeBound := Nat.le_refl _
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
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectAtValuationOfGraph
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
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectBoundOfGraph
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
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
        hgraph).payloadLength <=
      compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let direct :=
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectBoundOfGraph
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

def
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
    (tokenTable width tokenCount start finish valueBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 4
    (compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish)
    valueBound
    (compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
      tokenTable width tokenCount start finish)
    (compactBinaryNatStatusValidBoundedTerminalFixedWidthEntryPublicFiniteEnvelope
      tokenTable width tokenCount start finish valueBound)

noncomputable def
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectBoundOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    ExplicitDirectFormulaBound statusZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
        tokenTable width tokenCount start finish valueBound) := by
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
  let graphTerminalResource :=
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph
  let terminalResource :=
    compactBinaryNatStatusValidBoundedTerminalFixedWidthEntryPublicFiniteEnvelope
      tokenTable width tokenCount start finish valueBound
  have hterminalStructuralGraph :
      hybridFormulaStructuralPayloadBound data.terminal <=
        graphTerminalResource := by
    have hparts :=
      compactBinaryNatStatusValidBoundedTerminalPartsOfData_structuralPayloadBound_le_allBranchesFixedWidthEntry
        tokenTable width tokenCount start finish valueBound canonicalData
    simpa only [data,
      compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData,
      hybridFormulaStructuralPayloadBound, graphTerminalResource,
      compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph,
      canonicalData] using hparts
  have hgraphTerminal : graphTerminalResource <= terminalResource := by
    simpa only [graphTerminalResource, terminalResource] using
      (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryTerminalResourceOfGraph_le_publicFinite
        tokenTable width tokenCount start finish valueBound hgraph)
  have hterminal : data.terminal.compile.payloadLength <= terminalResource :=
    (compile_payloadLength_le_structuralPayloadBound data.terminal).trans
      (hterminalStructuralGraph.trans hgraphTerminal)
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables statusZeroValuation) <=
        contextCodeBound := Nat.le_refl _
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
  simpa only [
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope,
    contextCodeBound, bodyCodeBound, terminalResource] using hcoordinates.2

noncomputable def
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph
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
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectBoundOfGraph
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
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
        hgraph).payloadLength <=
      compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
        tokenTable width tokenCount start finish valueBound := by
  let direct :=
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectBoundOfGraph
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
  compactBinaryNatCompletedStatusExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
#print axioms
  compactBinaryNatStatusValidBoundedTerminalPartsOfData_structuralPayloadBound_le_allBranchesFixedWidthEntry
#print axioms
  compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectBoundOfGraph
#print axioms
  compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryDirectAtValuationOfGraph_payloadLength_le
#print axioms
  compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedFixedWidthEntryBounds
