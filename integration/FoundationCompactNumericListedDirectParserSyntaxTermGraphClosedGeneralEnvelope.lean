import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphFormulaFacts
import integration.FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
import integration.FoundationCompactListedProofHonestWeight

/-! # Closed-general envelope for the complete syntax-term graph formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphClosedGeneralEnvelope

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactListedProofHonestWeight
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphFormulaFacts
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

theorem syntaxTermGraphTransparentEnvelope_le_closedGeneral
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    transparentHybridConjunctionPayloadEnvelope termZeroValuation
        (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount current.tasksFinish current.finish)
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
            tokenTable width tokenCount current.tasksBoundary current.tasksCount
            witness.tailBoundary witness.tailCount witness.tailBoundarySize
            (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
            (fixedNumeralTerm 0) ⋏
          compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
            tokenCount current next binderArity witness)
        (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound)
        (transparentHybridConjunctionPayloadEnvelope termZeroValuation
          (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
            tokenTable width tokenCount current.tasksBoundary current.tasksCount
            witness.tailBoundary witness.tailCount witness.tailBoundarySize
            (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
            (fixedNumeralTerm 0))
          (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
            tokenCount current next binderArity witness)
          (unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
            bitBound)
          (syntaxTermAllBranchesFullyFixedPayloadEnvelope tokenCount numericBound
            bitBound)) <=
      hybridThreeConjunctionGeneralPayloadEnvelope
        (compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound)
        (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound)
        (unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound)
        (syntaxTermAllBranchesFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound) := by
  have hclosed :=
    compactUnifiedParserSyntaxTermExplicitFormula_freeVariables_eq_empty
      tokenTable width tokenCount current next binderArity witness
  have hcode :=
    compactUnifiedParserSyntaxTermExplicitFormula_code_length_le_graph
      tokenTable width tokenCount current next binderArity witness bitBound hsize
  have hpositive :
      1 <= compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial
        bitBound :=
    (one_le_binaryFormulaCode_length
      (compactUnifiedParserSyntaxTermExplicitFormula tokenTable width tokenCount
        current next binderArity witness)).trans hcode
  simpa only [compactUnifiedParserSyntaxTermExplicitFormula] using
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      termZeroValuation
      (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
        current.tasksFinish current.finish)
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
        tokenTable width tokenCount current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
        (fixedNumeralTerm 0))
      (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness)
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)
      (syntaxTermAllBranchesFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound)
      (compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound)
      hpositive hclosed hcode

end FoundationCompactNumericListedDirectParserSyntaxTermGraphClosedGeneralEnvelope
