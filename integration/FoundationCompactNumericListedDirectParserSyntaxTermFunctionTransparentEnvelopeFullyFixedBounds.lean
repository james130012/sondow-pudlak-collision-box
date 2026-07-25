import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
import integration.FoundationCompactListedProofHonestWeight

/-!
# Fixed envelope for the function syntax-term transition

This file isolates the formula-code and connective-assembly estimate from the
construction of the three checked branch certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionTransparentEnvelopeFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactListedProofHonestWeight
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds

theorem syntaxTermFunctionPartsTransparentEnvelope_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity numericBound bitBound :
      Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (htailCountSize : Nat.size tailCount <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound) :
    syntaxTermFunctionPartsTransparentEnvelope tokenTable width tokenCount
        current next tailBoundary tailCount binderArity functionArity
        numericBound bitBound <=
      syntaxTermFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount 3
  let tasksFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount (fixedNumeralTerm 2)
      (FoundationCompactPABinaryNumeralAddition.shortBinaryNumeralTerm
        binderArity)
      (FoundationCompactPABinaryNumeralAddition.shortBinaryNumeralTerm
        functionArity)
  have hformulaAlignment :
      runningFormula ⋏ (tokensFormula ⋏ tasksFormula) =
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity functionArity := by
    simpa only [runningFormula, tokensFormula, tasksFormula,
      compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitFormula] using
        (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity functionArity).symm
  have hclosed :
      (runningFormula ⋏ (tokensFormula ⋏ tasksFormula)).freeVariables =
        ∅ := by
    rw [hformulaAlignment]
    exact
      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next tailBoundary tailCount
        binderArity functionArity
  have hfullCode :=
    syntaxTermFunctionClosedFormula_code_length_le_fixed tokenTable width
      tokenCount current next tailBoundary tailCount binderArity functionArity
      bitBound htokenTableSize hwidthSize htokenCountSize hcurrentSize
      hnextSize htailBoundarySize htailCountSize hbinderSize hfunctionSize
  have hcode :
      (binaryFormulaCode
        (runningFormula ⋏ (tokensFormula ⋏ tasksFormula))).length <=
          syntaxTermFunctionAssemblySyntaxEnvelope tokenCount
            numericBound bitBound := by
    rw [hformulaAlignment]
    simpa only [syntaxTermFunctionAssemblySyntaxEnvelope] using hfullCode
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation
      runningFormula tokensFormula tasksFormula
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound)
      (syntaxTermFunctionAssemblySyntaxEnvelope tokenCount numericBound
        bitBound)
      (by
        exact
          (one_le_binaryFormulaCode_length
            (runningFormula ⋏ (tokensFormula ⋏ tasksFormula))).trans hcode)
      hclosed hcode
  unfold syntaxTermFunctionPartsTransparentEnvelope
  unfold syntaxTermFunctionFullyFixedPayloadEnvelope
  simpa only [runningFormula, tokensFormula, tasksFormula] using hassembly

#print axioms syntaxTermFunctionPartsTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionTransparentEnvelopeFullyFixedBounds
