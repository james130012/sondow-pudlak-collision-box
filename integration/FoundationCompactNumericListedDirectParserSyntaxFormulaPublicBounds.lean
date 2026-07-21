import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaSelectedPublicBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for the complete syntax-formula transition

The running-status, task-uncons, and checked branch certificates are charged
independently before the original 26-coordinate formula is restored.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaSelectedPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds

private abbrev formulaZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation

private abbrev fixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private theorem fixedNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm
  unfold
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

noncomputable def
    compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let unconsFormula :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let branchFormula := compactUnifiedParserSyntaxFormulaBranchExplicitFormula
    tokenTable width tokenCount current next binderArity witness
  let unconsResource :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 1
      binderArity 0 (fixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) hgraph.2.1
  let branchResource :=
    compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData tokenTable
      width tokenCount current next binderArity witness data
  let tailResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation unconsFormula branchFormula unconsResource
    branchResource
  transparentHybridConjunctionPayloadEnvelope formulaZeroValuation
    runningFormula (unconsFormula ⋏ branchFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount current.tasksFinish current.finish)
    tailResource

def compactUnifiedParserSyntaxFormulaExplicitPartsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let unconsFormula :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let branchFormula := compactUnifiedParserSyntaxFormulaBranchExplicitFormula
    tokenTable width tokenCount current next binderArity witness
  let unconsResource :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 1
      binderArity 0 (fixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
  let branchResource :=
    compactUnifiedParserSyntaxFormulaBranchPublicFinitePayloadEnvelope
      tokenTable width tokenCount current next binderArity witness
  let tailResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation unconsFormula branchFormula unconsResource
    branchResource
  transparentHybridConjunctionPayloadEnvelope formulaZeroValuation
    runningFormula (unconsFormula ⋏ branchFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount current.tasksFinish current.finish)
    tailResource

theorem
    compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData
        tokenTable width tokenCount current next binderArity witness hgraph
        data <=
      compactUnifiedParserSyntaxFormulaExplicitPartsPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next binderArity witness := by
  unfold compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData
    compactUnifiedParserSyntaxFormulaExplicitPartsPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize 1
        binderArity 0 (fixedNumeralTerm 1)
        (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) hgraph.2.1)
      (compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData_le_publicFinite
        tokenTable width tokenCount current next binderArity witness data))

theorem
    compactUnifiedParserSyntaxFormulaExplicitParts_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tasksFinish current.finish
            hgraph.1)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tasksBoundary
              current.tasksCount witness.tailBoundary witness.tailCount
              witness.tailBoundarySize 1 binderArity 0 (fixedNumeralTerm 1)
              (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
              (fun valuation => by simp)
              (fun valuation => by
                simp [termValue_shortBinaryNumeralTerm])
              (fun valuation => by simp) hgraph.2.1)
            (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
              tokenTable width tokenCount current next binderArity witness
              data))) <=
      compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData
        tokenTable width tokenCount current next binderArity witness hgraph
        data := by
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hgraph.1
  let unconsCertificate :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 1
      binderArity 0 (fixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
      (fun valuation => by simp)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp) hgraph.2.1
  let branchCertificate :=
    compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
      tokenTable width tokenCount current next binderArity witness data
  have hrunning :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tasksFinish current.finish hgraph.1
  have hheadKindClosed : (fixedNumeralTerm 1).freeVariables = ∅ :=
    fixedNumeralTerm_freeVariables_eq_empty 1
  have hheadBinderArityClosed :
      (shortBinaryNumeralTerm binderArity).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty binderArity
  have hheadRepeatCountClosed : (fixedNumeralTerm 0).freeVariables = ∅ :=
    fixedNumeralTerm_freeVariables_eq_empty 0
  have hheadKindValue : forall valuation,
      termValue valuation (fixedNumeralTerm 1) = 1 := by
    intro valuation
    simp
  have hheadBinderArityValue : forall valuation,
      termValue valuation (shortBinaryNumeralTerm binderArity) = binderArity := by
    intro valuation
    simp [termValue_shortBinaryNumeralTerm]
  have hheadRepeatCountValue : forall valuation,
      termValue valuation (fixedNumeralTerm 0) = 0 := by
    intro valuation
    simp
  have huncons :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 1
      binderArity 0 (fixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
      hheadKindClosed hheadBinderArityClosed hheadRepeatCountClosed
      hheadKindValue hheadBinderArityValue hheadRepeatCountValue hgraph.2.1
  have hbranch :=
    compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next binderArity witness data
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      unconsCertificate branchCertificate
  have htail := transparentHybridConjunctionPayloadBound_le unconsCertificate
    branchCertificate _ _ huncons hbranch
  let partsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate tailCertificate
  have hparts := transparentHybridConjunctionPayloadBound_le runningCertificate
    tailCertificate _ _ hrunning htail
  unfold
    compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData
  change hybridFormulaStructuralPayloadBound partsCertificate <= _
  exact hparts

noncomputable def compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) : Nat :=
  compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData
    tokenTable width tokenCount current next binderArity witness hgraph
    (compactSyntaxFormulaCheckedBranchDataOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph)

def compactUnifiedParserSyntaxFormulaPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Nat :=
  compactUnifiedParserSyntaxFormulaExplicitPartsPublicFinitePayloadEnvelope
    tokenTable width tokenCount current next binderArity witness

theorem compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hgraph <=
      compactUnifiedParserSyntaxFormulaPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity witness := by
  unfold compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope
    compactUnifiedParserSyntaxFormulaPublicFinitePayloadEnvelope
  exact
    compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData_le_publicFinite
      tokenTable width tokenCount current next binderArity witness hgraph
      (compactSyntaxFormulaCheckedBranchDataOfGraph tokenTable width tokenCount
        current next binderArity witness hgraph)

theorem
    compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    @hybridFormulaStructuralPayloadBound formulaZeroValuation
        (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
          tokenCount current next binderArity witness)
        (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next binderArity witness hgraph) <=
      compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hgraph := by
  let data := compactSyntaxFormulaCheckedBranchDataOfGraph tokenTable width
    tokenCount current next binderArity witness hgraph
  have hparts :=
    compactUnifiedParserSyntaxFormulaExplicitParts_structuralPayloadBound_le_public
      tokenTable width tokenCount current next binderArity witness hgraph data
  unfold compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish hgraph.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize 1
          binderArity 0 (fixedNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
          (fun valuation => by simp)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => by simp) hgraph.2.1)
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness data))) <=
    compactUnifiedParserSyntaxFormulaExplicitPartsPayloadEnvelopeFromData
      tokenTable width tokenCount current next binderArity witness hgraph data
  exact hparts

theorem
    compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness) :
    @hybridFormulaStructuralPayloadBound formulaZeroValuation
        (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
          tokenCount current next binderArity witness)
        (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next binderArity witness hgraph) <=
      compactUnifiedParserSyntaxFormulaPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity witness := by
  exact
    (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next binderArity witness hgraph).trans
    (compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next binderArity witness hgraph)

#print axioms
  compactUnifiedParserSyntaxFormulaExplicitParts_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectParserSyntaxFormulaPublicBounds
