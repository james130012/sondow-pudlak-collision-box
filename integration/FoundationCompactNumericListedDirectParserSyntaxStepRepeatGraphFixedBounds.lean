import integration.FoundationCompactNumericListedDirectParserSyntaxStepRepeatSelectedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactListedProofHonestWeight

/-! # Fully fixed selected Repeat graph endpoint inside SyntaxStep -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxStepRepeatGraphFixedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatZeroBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFullGraphFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFullSelectedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepRepeatSelectedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
open FoundationCompactListedProofHonestWeight
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate stepZeroValuation formula

def syntaxStepRepeatGraphSelectedResource
    (tokenCount numericBound bitBound : Nat) : Nat :=
  max
    (repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
      (repeatSelectedBranchPayloadEnvelope bitBound
        (repeatZeroBranchPayloadEnvelope numericBound bitBound)))
    (repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
      (repeatSelectedBranchPayloadEnvelope bitBound
        (repeatPositiveBranchPayloadEnvelope numericBound bitBound)))

noncomputable def compactUnifiedParserSyntaxStepCertificateFromRepeatGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next witness.slot0 witness.slot1 witness.repeat) :
    HybridCertificate
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness) := by
  let branchData :=
    compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
      next witness.slot0 witness.slot1 witness.repeat hgraph.2.2.2.2
  rcases branchData with ⟨hrepeatZero, hsame⟩ |
    ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
  ·
    let branchCertificate :=
      repeatZeroOriginalBranchCertificate tokenTable width tokenCount next
        witness.slot0 witness.slot1 witness.repeat hrepeatZero hsame
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current next
        witness.slot0 witness.slot1 witness.repeat hgraph.1 hgraph.2.1
        hgraph.2.2.1 hgraph.2.2.2.1 branchCertificate
    exact compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate
      tokenTable width tokenCount current next witness selected
  ·
    let branchCertificate :=
      repeatPositiveOriginalBranchCertificate tokenTable width tokenCount next
        witness.slot0 witness.slot1 witness.repeat hrepeatSuccessor hdrop
        htaskZero htaskOne
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current next
        witness.slot0 witness.slot1 witness.repeat hgraph.1 hgraph.2.1
        hgraph.2.2.1 hgraph.2.2.2.1 branchCertificate
    exact compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate
      tokenTable width tokenCount current next witness selected

theorem
    compactUnifiedParserSyntaxStepCertificateFromRepeatGraph_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next witness.slot0 witness.slot1 witness.repeat)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next witness.slot0 witness.slot1 witness.repeat
          coordinate) <= bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcurrentTasksFinishValue : current.tasksFinish <= numericBound)
    (hnextTasksFinishValue : next.tasksFinish <= numericBound)
    (hcurrentTokensCountValue : current.tokensCount <= numericBound)
    (hcurrentTasksCountValue : current.tasksCount <= numericBound)
    (hnextTasksCountValue : next.tasksCount <= numericBound)
    (htailCountValue : witness.repeat.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentTasksFinishSize : Nat.size current.tasksFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound)
    (hnextTokensBoundarySize : Nat.size next.tokensBoundary <= bitBound)
    (hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound)
    (hnextTasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (hnextTasksCountSize : Nat.size next.tasksCount <= bitBound)
    (htailBoundarySize : Nat.size witness.repeat.tailBoundary <= bitBound)
    (hbinderSize : Nat.size witness.slot0 <= bitBound)
    (hrepeatSize : Nat.size witness.slot1 <= bitBound)
    (hdecrementedSize :
      Nat.size witness.repeat.decrementedCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCertificateFromRepeatGraph tokenTable
          width tokenCount current next witness hgraph) <=
      syntaxStepRepeatSelectedPayloadEnvelope
        (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
          current next witness.done)
        (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current next witness.empty)
        (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
          tokenCount current next witness.slot0 witness.slot1 witness.repeat)
        (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
          current next witness.slot0 witness.term)
        (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
          tokenCount current next witness.slot0 witness.formula)
        (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
          tokenCount current next witness.invalid)
        (syntaxStepRepeatGraphSelectedResource tokenCount numericBound
          bitBound) := by
  let branchData :=
    compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
      next witness.slot0 witness.slot1 witness.repeat hgraph.2.2.2.2
  rcases hbranch : branchData with ⟨hrepeatZero, hsame⟩ |
    ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
  ·
    let branchCertificate :=
      repeatZeroOriginalBranchCertificate tokenTable width tokenCount next
        witness.slot0 witness.slot1 witness.repeat hrepeatZero hsame
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current next
        witness.slot0 witness.slot1 witness.repeat hgraph.1 hgraph.2.1
        hgraph.2.2.1 hgraph.2.2.2.1 branchCertificate
    have hselectedRaw :=
      repeatZeroFullGraphCertificate_structuralPayloadBound_le_fixed tokenTable
        width tokenCount current next witness.slot0 witness.slot1
        witness.repeat numericBound bitBound hgraph.1 hgraph.2.1
        hgraph.2.2.1 hgraph.2.2.2.1 hrepeatZero hsame hsize hwidthValue
        htokenCountValue hcurrentTasksFinishValue hnextTasksFinishValue
        hcurrentTokensCountValue hcurrentTasksCountValue htailCountValue
        htableSize hwidthSize htokenCountSize hcurrentTasksFinishSize
        hcurrentFinishSize hnextTasksFinishSize hnextFinishSize
        hcurrentTokensBoundarySize hnextTokensBoundarySize
        hcurrentTasksBoundarySize hnextTasksBoundarySize htailBoundarySize
        hbinderSize hrepeatSize hnumericSize
    have hselected :
        hybridFormulaStructuralPayloadBound selected <=
          syntaxStepRepeatGraphSelectedResource tokenCount numericBound
            bitBound :=
      hselectedRaw.trans (Nat.le_max_left _ _)
    have hpath :=
      compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate_structuralPayloadBound_le
        tokenTable width tokenCount current next witness selected
        (syntaxStepRepeatGraphSelectedResource tokenCount numericBound bitBound)
        hselected
    unfold compactUnifiedParserSyntaxStepCertificateFromRepeatGraph
    dsimp only [branchData] at hbranch
    rw [hbranch]
    simpa only [branchCertificate, selected] using hpath
  ·
    let branchCertificate :=
      repeatPositiveOriginalBranchCertificate tokenTable width tokenCount next
        witness.slot0 witness.slot1 witness.repeat hrepeatSuccessor hdrop
        htaskZero htaskOne
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current next
        witness.slot0 witness.slot1 witness.repeat hgraph.1 hgraph.2.1
        hgraph.2.2.1 hgraph.2.2.2.1 branchCertificate
    have hselectedRaw :=
      repeatPositiveFullGraphCertificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount current next witness.slot0 witness.slot1
        witness.repeat numericBound bitBound hgraph.1 hgraph.2.1
        hgraph.2.2.1 hgraph.2.2.2.1 hrepeatSuccessor hdrop htaskZero
        htaskOne hsize hwidthValue htokenCountValue
        hcurrentTasksFinishValue hnextTasksFinishValue
        hcurrentTokensCountValue hcurrentTasksCountValue hnextTasksCountValue
        htailCountValue htableSize hwidthSize htokenCountSize
        hcurrentTasksFinishSize hcurrentFinishSize hnextTasksFinishSize
        hnextFinishSize hcurrentTokensBoundarySize hnextTokensBoundarySize
        hcurrentTasksBoundarySize hnextTasksBoundarySize hnextTasksCountSize
        htailBoundarySize hbinderSize hrepeatSize hdecrementedSize hnumericSize
    have hselected :
        hybridFormulaStructuralPayloadBound selected <=
          syntaxStepRepeatGraphSelectedResource tokenCount numericBound
            bitBound :=
      hselectedRaw.trans (Nat.le_max_right _ _)
    have hpath :=
      compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate_structuralPayloadBound_le
        tokenTable width tokenCount current next witness selected
        (syntaxStepRepeatGraphSelectedResource tokenCount numericBound bitBound)
        hselected
    unfold compactUnifiedParserSyntaxStepCertificateFromRepeatGraph
    dsimp only [branchData] at hbranch
    rw [hbranch]
    simpa only [branchCertificate, selected] using hpath

#print axioms
  compactUnifiedParserSyntaxStepCertificateFromRepeatGraph_structuralPayloadBound_le_fixed

theorem
    compactUnifiedParserSyntaxStepCertificateFromRepeatGraph_structuralPayloadBound_le_closedFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next witness.slot0 witness.slot1 witness.repeat)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next witness.slot0 witness.slot1 witness.repeat
          coordinate) <= bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcurrentTasksFinishValue : current.tasksFinish <= numericBound)
    (hnextTasksFinishValue : next.tasksFinish <= numericBound)
    (hcurrentTokensCountValue : current.tokensCount <= numericBound)
    (hcurrentTasksCountValue : current.tasksCount <= numericBound)
    (hnextTasksCountValue : next.tasksCount <= numericBound)
    (htailCountValue : witness.repeat.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentTasksFinishSize : Nat.size current.tasksFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound)
    (hnextTokensBoundarySize : Nat.size next.tokensBoundary <= bitBound)
    (hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound)
    (hnextTasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (hnextTasksCountSize : Nat.size next.tasksCount <= bitBound)
    (htailBoundarySize : Nat.size witness.repeat.tailBoundary <= bitBound)
    (hbinderSize : Nat.size witness.slot0 <= bitBound)
    (hrepeatSize : Nat.size witness.slot1 <= bitBound)
    (hdecrementedSize :
      Nat.size witness.repeat.decrementedCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hstepSize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCertificateFromRepeatGraph tokenTable
          width tokenCount current next witness hgraph) <=
      sixRightDisjunctionPathTwoPayloadEnvelope
        (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
        (syntaxStepRepeatGraphSelectedResource tokenCount numericBound
          bitBound) := by
  have hselected :=
    compactUnifiedParserSyntaxStepCertificateFromRepeatGraph_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph hsize hwidthValue htokenCountValue hcurrentTasksFinishValue
      hnextTasksFinishValue hcurrentTokensCountValue hcurrentTasksCountValue
      hnextTasksCountValue htailCountValue htableSize hwidthSize htokenCountSize
      hcurrentTasksFinishSize hcurrentFinishSize hnextTasksFinishSize
      hnextFinishSize hcurrentTokensBoundarySize hnextTokensBoundarySize
      hcurrentTasksBoundarySize hnextTasksBoundarySize hnextTasksCountSize
      htailBoundarySize hbinderSize hrepeatSize hdecrementedSize hnumericSize
  have hclosed :=
    compactUnifiedParserSyntaxStepExplicitFormula_freeVariables_eq_empty
      tokenTable width tokenCount current next witness
  have hcode :=
    compactUnifiedParserSyntaxStepExplicitFormula_code_length_le_fixed tokenTable
      width tokenCount current next witness bitBound hstepSize
  have hpositive :
      1 <= compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)).trans hcode
  exact hselected.trans
    (sixRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral
      stepZeroValuation
      (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount current
        next witness.done)
      (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount current
        next witness.empty)
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.slot1 witness.repeat)
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.term)
      (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.formula)
      (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount
        current next witness.invalid)
      (syntaxStepRepeatGraphSelectedResource tokenCount numericBound bitBound)
      (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
      hpositive hclosed hcode)

end FoundationCompactNumericListedDirectParserSyntaxStepRepeatGraphFixedBounds
