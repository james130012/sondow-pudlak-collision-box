import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds

/-!
# Public structural resource for the invalid syntax-task branch

The three invalid-kind inequalities are compiled as negative equality atoms.
They are combined with the running status, exact task-list uncons, and the
already public term-failure rows.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds

private abbrev invalidZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate.zeroValuation

private abbrev binaryStatusZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

private abbrev unconsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation

private theorem fixedNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

def compactUnifiedParserSyntaxInvalidFixedNePayloadPolynomial
    (value expected : Nat) : Nat :=
  compileNegativeRelationPayloadPolynomial invalidZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]

theorem fixedNeCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (hne : value ≠ expected) :
    hybridFormulaStructuralPayloadBound
        (fixedNeCertificate value expected hne) ≤
      compactUnifiedParserSyntaxInvalidFixedNePayloadPolynomial value
        expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (fixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compileNegativeRelationPayloadResource_le_publicPolynomial
    invalidZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
    hleft hright
  change compileNegativeRelationPayloadResource invalidZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] ≤ _
  exact hpublic

noncomputable def
    compactUnifiedParserSyntaxInvalidFromGraphDataPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (_hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize witness.kind
      witness.binderArity witness.repeatCount)
    (_hzero : witness.kind ≠ 0)
    (_hone : witness.kind ≠ 1)
    (_htwo : witness.kind ≠ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let unconsFormula :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula tokenTable
      width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      witness.kind witness.binderArity witness.repeatCount
  let zeroFormula := fixedNeFormula witness.kind 0
  let oneFormula := fixedNeFormula witness.kind 1
  let twoFormula := fixedNeFormula witness.kind 2
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let twoFailureResource := transparentHybridConjunctionPayloadEnvelope
    invalidZeroValuation twoFormula failureFormula
    (compactUnifiedParserSyntaxInvalidFixedNePayloadPolynomial witness.kind 2)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  let oneTailResource := transparentHybridConjunctionPayloadEnvelope
    invalidZeroValuation oneFormula (twoFormula ⋏ failureFormula)
    (compactUnifiedParserSyntaxInvalidFixedNePayloadPolynomial witness.kind 1)
    twoFailureResource
  let zeroTailResource := transparentHybridConjunctionPayloadEnvelope
    invalidZeroValuation zeroFormula
    (oneFormula ⋏ (twoFormula ⋏ failureFormula))
    (compactUnifiedParserSyntaxInvalidFixedNePayloadPolynomial witness.kind 0)
    oneTailResource
  let unconsTailResource := transparentHybridConjunctionPayloadEnvelope
    unconsZeroValuation unconsFormula
    (zeroFormula ⋏ (oneFormula ⋏ (twoFormula ⋏ failureFormula)))
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedGraphPayloadEnvelope
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      witness.kind witness.binderArity witness.repeatCount huncons)
    zeroTailResource
  transparentHybridConjunctionPayloadEnvelope binaryStatusZeroValuation
    runningFormula
    (unconsFormula ⋏
      (zeroFormula ⋏ (oneFormula ⋏ (twoFormula ⋏ failureFormula))))
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount current.tasksFinish current.finish)
    unconsTailResource

noncomputable def compactUnifiedParserSyntaxInvalidGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current next witness) : Nat :=
  compactUnifiedParserSyntaxInvalidFromGraphDataPayloadEnvelope tokenTable
    width tokenCount current next witness hgraph.1 hgraph.2.1 hgraph.2.2.1
    hgraph.2.2.2.1 hgraph.2.2.2.2.1 hgraph.2.2.2.2.2

theorem
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize witness.kind
      witness.binderArity witness.repeatCount)
    (hzero : witness.kind ≠ 0)
    (hone : witness.kind ≠ 1)
    (htwo : witness.kind ≠ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateFromGraphData
          tokenTable width tokenCount current next witness hrunning huncons
          hzero hone htwo hfailure) ≤
      compactUnifiedParserSyntaxInvalidFromGraphDataPayloadEnvelope tokenTable
        width tokenCount current next witness hrunning huncons hzero hone htwo
        hfailure := by
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hrunning
  let unconsCertificate :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      witness.kind witness.binderArity witness.repeatCount huncons
  let zeroCertificate := fixedNeCertificate witness.kind 0 hzero
  let oneCertificate := fixedNeCertificate witness.kind 1 hone
  let twoCertificate := fixedNeCertificate witness.kind 2 htwo
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  have hrunningResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tasksFinish current.finish hrunning
  have hunconsResource :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      witness.kind witness.binderArity witness.repeatCount huncons
  have hzeroResource := fixedNeCertificate_structuralPayloadBound_le_public
    witness.kind 0 hzero
  have honeResource := fixedNeCertificate_structuralPayloadBound_le_public
    witness.kind 1 hone
  have htwoResource := fixedNeCertificate_structuralPayloadBound_le_public
    witness.kind 2 htwo
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let twoFailure := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    twoCertificate failureCertificate
  have htwoFailure := transparentHybridConjunctionPayloadBound_le
    twoCertificate failureCertificate _ _ htwoResource hfailureResource
  let oneTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    oneCertificate twoFailure
  have honeTail := transparentHybridConjunctionPayloadBound_le
    oneCertificate twoFailure _ _ honeResource htwoFailure
  let zeroTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    zeroCertificate oneTail
  have hzeroTail := transparentHybridConjunctionPayloadBound_le
    zeroCertificate oneTail _ _ hzeroResource honeTail
  let unconsTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    unconsCertificate zeroTail
  have hunconsTail := transparentHybridConjunctionPayloadBound_le
    unconsCertificate zeroTail _ _ hunconsResource hzeroTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    runningCertificate unconsTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    runningCertificate unconsTail _ _ hrunningResource hunconsTail
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxInvalidClosedFormula_alignment tokenTable
          width tokenCount current next witness).symm parts) ≤ _
  unfold compactUnifiedParserSyntaxInvalidFromGraphDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, runningCertificate,
    unconsCertificate, zeroCertificate, oneCertificate, twoCertificate,
    failureCertificate, twoFailure, oneTail, zeroTail, unconsTail, parts]
    using hparts

theorem
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current next witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness hgraph) ≤
      compactUnifiedParserSyntaxInvalidGraphPayloadEnvelope tokenTable width
        tokenCount current next witness hgraph := by
  simpa only [
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph,
    compactUnifiedParserSyntaxInvalidGraphPayloadEnvelope] using
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness hgraph.1 hgraph.2.1
      hgraph.2.2.1 hgraph.2.2.2.1 hgraph.2.2.2.2.1
      hgraph.2.2.2.2.2

#print axioms fixedNeCertificate_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxInvalidExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
