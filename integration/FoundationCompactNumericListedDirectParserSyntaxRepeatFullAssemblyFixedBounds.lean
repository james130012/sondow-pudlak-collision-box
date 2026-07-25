import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatBranchFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

/-! # Fully fixed five-component assembly for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatFullAssemblyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaEnvironmentAlignment
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatBranchFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

def repeatFiveAssemblyPayloadEnvelope
    (bitBound currentResource nextResource tokensResource unconsResource
      branchResource : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound + 1)
    currentResource nextResource tokensResource unconsResource branchResource

theorem repeatFiveCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (currentCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount current.tasksFinish current.finish))
    (nextCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount next.tasksFinish next.finish))
    (tokensCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
          current.tokensBoundary current.tokensCount next.tokensBoundary
          next.tokensCount))
    (unconsCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize
          binderArity repeatCount (fixedNumeralTerm 2)))
    (branchCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness))
    (currentResource nextResource tokensResource unconsResource branchResource
      bitBound : Nat)
    (hcurrent :
      hybridFormulaStructuralPayloadBound currentCertificate <= currentResource)
    (hnext :
      hybridFormulaStructuralPayloadBound nextCertificate <= nextResource)
    (htokens :
      hybridFormulaStructuralPayloadBound tokensCertificate <= tokensResource)
    (huncons :
      hybridFormulaStructuralPayloadBound unconsCertificate <= unconsResource)
    (hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <= branchResource)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          currentCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            nextCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              tokensCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                unconsCertificate branchCertificate)))) <=
      repeatFiveAssemblyPayloadEnvelope bitBound currentResource nextResource
        tokensResource unconsResource branchResource := by
  let formula1 :=
    compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      current.tasksFinish current.finish
  let formula2 :=
    compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      next.tasksFinish next.finish
  let formula3 :=
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount
  let formula4 :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      binderArity repeatCount (fixedNumeralTerm 2)
  let formula5 :=
    compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
      tokenCount next binderArity repeatCount witness
  let pair45 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      unconsCertificate branchCertificate
  let tail345 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensCertificate pair45
  let tail2345 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      nextCertificate tail345
  have h45 := transparentHybridConjunctionPayloadBound_le unconsCertificate
    branchCertificate unconsResource branchResource huncons hbranch
  have h345 := transparentHybridConjunctionPayloadBound_le tokensCertificate
    pair45 tokensResource
    (transparentHybridConjunctionPayloadEnvelope repeatZeroValuation formula4
      formula5 unconsResource branchResource) htokens h45
  have h2345 := transparentHybridConjunctionPayloadBound_le nextCertificate
    tail345 nextResource
    (transparentHybridConjunctionPayloadEnvelope repeatZeroValuation formula3
      (formula4 ⋏ formula5) tokensResource
      (transparentHybridConjunctionPayloadEnvelope repeatZeroValuation formula4
        formula5 unconsResource branchResource)) hnext h345
  have hparts := transparentHybridConjunctionPayloadBound_le currentCertificate
    tail2345 currentResource
    (transparentHybridConjunctionPayloadEnvelope repeatZeroValuation formula2
      (formula3 ⋏ (formula4 ⋏ formula5)) nextResource
      (transparentHybridConjunctionPayloadEnvelope repeatZeroValuation formula3
        (formula4 ⋏ formula5) tokensResource
        (transparentHybridConjunctionPayloadEnvelope repeatZeroValuation formula4
          formula5 unconsResource branchResource))) hcurrent h2345
  have hclosed :
      (formula1 ⋏ (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))).freeVariables =
        ∅ := by
    dsimp only [formula1, formula2, formula3, formula4, formula5]
    change
      (compactUnifiedParserSyntaxRepeatExplicitFormula tokenTable width
        tokenCount current next binderArity repeatCount witness).freeVariables =
        ∅
    rw [← compactUnifiedParserSyntaxRepeatClosedFormula_alignment tokenTable
      width tokenCount current next binderArity repeatCount witness]
    exact compactUnifiedParserSyntaxRepeatClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount current next binderArity repeatCount witness
  have hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))))).length <=
        compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound := by
    dsimp only [formula1, formula2, formula3, formula4, formula5]
    exact
      compactUnifiedParserSyntaxRepeatExplicitFormula_code_length_le_fixed
        tokenTable width tokenCount current next binderArity repeatCount witness
        bitBound hsize
  have hcode' :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))))).length <=
        compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound +
          1 :=
    hcode.trans (Nat.le_add_right _ _)
  have hassembly :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral
      repeatZeroValuation formula1 formula2 formula3 formula4 formula5
      currentResource nextResource tokensResource unconsResource branchResource
      (compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound + 1)
      (by omega) hclosed hcode'
  unfold repeatFiveAssemblyPayloadEnvelope
  simpa only [formula1, formula2, formula3, formula4, formula5, pair45,
    tail345, tail2345] using hparts.trans hassembly

#print axioms repeatFiveCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatFullAssemblyFixedBounds
