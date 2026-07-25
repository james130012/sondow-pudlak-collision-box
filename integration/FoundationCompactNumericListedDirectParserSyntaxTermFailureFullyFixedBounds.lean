import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed syntax-term failure certificate

The original twenty-one-coordinate failure certificate is rebuilt from its
real failed-status, unchanged-token-list, and unchanged-task-list leaves.  All
three leaf resources and both conjunction assemblies are charged to public
numeric and bit-width coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds

private def failureZeroValuation : Nat -> Nat := fun _ => 0

def syntaxTermFailureFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (syntaxTermFailureClosedFormulaCodePolynomial numericBound bitBound)
    (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next tailBoundary tailCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          hgraph) <=
      syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound := by
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let tasksFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
    next.tasksCount
  let failedCertificate :=
    compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hgraph.1
  let tokensCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount hgraph.2.1
  let tasksCertificate :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount hgraph.2.2
  have hnextTasksFinish : next.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (3 : Fin 8)
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (1 : Fin 8)
  have hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (3 : Fin 8)
  have hcurrentTokensCount : current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hnextTokensBoundarySize :
      Nat.size next.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (4 : Fin 8)
  have hnextTasksBoundarySize :
      Nat.size next.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (6 : Fin 8)
  rcases hgraph.1 with ⟨innerStart, hinnerLe, hfirst, hsecond⟩
  have hinnerEq : innerStart = next.tasksFinish + 1 := hfirst.2.1
  have hinnerBound : next.tasksFinish + 1 <= numericBound := by
    rw [← hinnerEq]
    exact hinnerLe.trans htokenCount
  have hinnerSize : Nat.size (next.tasksFinish + 1) <= bitBound :=
    (Nat.size_le_size hinnerBound).trans hnumericSize
  have hfailedResource :
      hybridFormulaStructuralPayloadBound failedCertificate <=
        binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
          bitBound := by
    dsimp only [failedCertificate]
    exact
      compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount next.tasksFinish next.finish numericBound
        bitBound hwidth hnextTasksFinish hinnerBound htokenTableSize hwidthSize
        htokenCountSize hnextTasksFinishSize hnextFinishSize hinnerSize
        hbitPositive hgraph.1
  have htokensPublic :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount hgraph.2.1
  have htokensEnvelope :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount numericBound bitBound hgraph.2.1
      hwidth htokenCount hcurrentTokensCount htokenTableSize
      hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize
  have htokensResource :
      hybridFormulaStructuralPayloadBound tokensCertificate <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound := by
    dsimp only [tokensCertificate]
    exact htokensPublic.trans htokensEnvelope
  have htasksPublic :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount hgraph.2.2
  have htasksEnvelope :=
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount numericBound bitBound hgraph.2.2 hwidth htokenCount
      htailCount htokenTableSize htailBoundarySize hnextTasksBoundarySize
      hnumericSize
  have htasksResource :
      hybridFormulaStructuralPayloadBound tasksCertificate <=
        taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [tasksCertificate]
    exact htasksPublic.trans htasksEnvelope
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensCertificate tasksCertificate
  have htail :=
    transparentHybridConjunctionPayloadBound_le tokensCertificate
      tasksCertificate _ _ htokensResource htasksResource
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      failedCertificate tailCertificate
  have hparts :=
    transparentHybridConjunctionPayloadBound_le failedCertificate
      tailCertificate _ _ hfailedResource htail
  have hclosed :
      (failedFormula ⋏ (tokensFormula ⋏ tasksFormula)).freeVariables = ∅ := by
    have hraw :=
      syntaxTermFailureClosedFormula_freeVariables_eq_empty tokenTable
      width tokenCount current next tailBoundary tailCount
    rw [compactUnifiedParserSyntaxTermFailureClosedFormula_alignment] at hraw
    simpa only [compactUnifiedParserSyntaxTermFailureExplicitFormula,
      failedFormula, tokensFormula, tasksFormula] using hraw
  have hcode :
      (binaryFormulaCode
        (failedFormula ⋏ (tokensFormula ⋏ tasksFormula))).length <=
          syntaxTermFailureClosedFormulaCodePolynomial numericBound
            bitBound := by
    have hraw :=
      syntaxTermFailureClosedFormula_code_length_le_fixed tokenTable width
      tokenCount current next tailBoundary tailCount numericBound bitBound
      hgraph hwidth htokenCount htailCount hcurrentValue
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize hnumericSize
    rw [compactUnifiedParserSyntaxTermFailureClosedFormula_alignment] at hraw
    simpa only [compactUnifiedParserSyntaxTermFailureExplicitFormula,
      failedFormula, tokensFormula, tasksFormula] using hraw
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      failureZeroValuation failedFormula tokensFormula tasksFormula
      (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
        bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (syntaxTermFailureClosedFormulaCodePolynomial numericBound bitBound)
      (by
        unfold syntaxTermFailureClosedFormulaCodePolynomial
        omega)
      hclosed hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxTermFailureClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary
          tailCount).symm parts) <= _
  unfold syntaxTermFailureFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, failedFormula,
    tokensFormula, tasksFormula, failedCertificate, tokensCertificate,
    tasksCertificate, tailCertificate, parts, failureZeroValuation] using
      hparts.trans hassembly

#print axioms
  compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
