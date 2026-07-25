import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFullAssemblyFixedBounds

/-! # Fully fixed common graph components for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatFullGraphFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFullAssemblyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

def repeatFullGraphPayloadEnvelope
    (tokenCount numericBound bitBound branchResource : Nat) : Nat :=
  repeatFiveAssemblyPayloadEnvelope bitBound
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (parserSyntaxRepeatUnconsFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)
    branchResource

theorem repeatGraphComponentsCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (branchCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness))
    (branchResource numericBound bitBound : Nat)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <= branchResource)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcurrentTasksFinishValue : current.tasksFinish <= numericBound)
    (hnextTasksFinishValue : next.tasksFinish <= numericBound)
    (hcurrentTokensCountValue : current.tokensCount <= numericBound)
    (hcurrentTasksCountValue : current.tasksCount <= numericBound)
    (htailCountValue : witness.tailCount <= numericBound)
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
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tasksFinish current.finish
            hcurrent)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
              tokenTable width tokenCount next.tasksFinish next.finish hnext)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount next.tokensBoundary next.tokensCount htokens)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (parserSyntaxRepeatUnconsGraphCertificate tokenTable width
                  tokenCount current.tasksBoundary current.tasksCount
                  witness.tailBoundary witness.tailCount
                  witness.tailBoundarySize binderArity repeatCount huncons)
                branchCertificate)))) <=
      repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
        branchResource := by
  let currentCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tasksFinish current.finish hcurrent
  let nextCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph tokenTable
      width tokenCount next.tasksFinish next.finish hnext
  let tokensCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  let unconsCertificate :=
    parserSyntaxRepeatUnconsGraphCertificate tokenTable width tokenCount
      current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize binderArity repeatCount huncons
  have hcurrentResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount current.tasksFinish current.finish numericBound
      bitBound hwidthValue hcurrentTasksFinishValue htableSize hwidthSize
      htokenCountSize hcurrentTasksFinishSize hcurrentFinishSize hcurrent
  have hnextResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount next.tasksFinish next.finish numericBound
      bitBound hwidthValue hnextTasksFinishValue htableSize hwidthSize
      htokenCountSize hnextTasksFinishSize hnextFinishSize hnext
  have htokensTransparent :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  have htokensFixed :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount numericBound bitBound htokens
      hwidthValue htokenCountValue hcurrentTokensCountValue htableSize
      hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize
  have htokensResource :
      hybridFormulaStructuralPayloadBound tokensCertificate <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    htokensTransparent.trans htokensFixed
  have hunconsResource :=
    parserSyntaxRepeatUnconsGraphCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize binderArity
      repeatCount numericBound bitBound huncons hwidthValue htokenCountValue
      hcurrentTasksCountValue htailCountValue htableSize
      hcurrentTasksBoundarySize htailBoundarySize hbinderSize hrepeatSize
      hnumericSize
  have hassembly :=
    repeatFiveCertificate_structuralPayloadBound_le_fixed tokenTable width
      tokenCount current next binderArity repeatCount witness currentCertificate
      nextCertificate tokensCertificate unconsCertificate branchCertificate
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (parserSyntaxRepeatUnconsFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      branchResource bitBound hcurrentResource hnextResource htokensResource
      hunconsResource hbranch hsize
  unfold repeatFullGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        currentCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          nextCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tokensCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              unconsCertificate branchCertificate)))) <=
    repeatFiveAssemblyPayloadEnvelope bitBound
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (parserSyntaxRepeatUnconsFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      branchResource
  exact hassembly

#print axioms
  repeatGraphComponentsCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatFullGraphFixedBounds
