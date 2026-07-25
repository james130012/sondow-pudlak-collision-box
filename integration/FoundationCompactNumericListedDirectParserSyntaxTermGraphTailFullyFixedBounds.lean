import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphUnconsResourceFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphBranchResourceFullyFixedBounds

/-! # Fully fixed tail conjunction of the complete syntax-term graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphTailFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermGraphUnconsResourceFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphBranchResourceFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

theorem
    syntaxTermFullyFixedGraphTailCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
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
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness
        bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
      (syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) <=
      transparentHybridConjunctionPayloadEnvelope termZeroValuation
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
          bitBound) := by
  let unconsCertificate :=
    syntaxTermFullyFixedGraphUnconsCertificate tokenTable width tokenCount
      current next binderArity witness hgraph
  let branchCertificate :=
    syntaxTermFullyFixedGraphBranchCertificate tokenTable width tokenCount
      current next binderArity witness hgraph
  have huncons :=
    syntaxTermFullyFixedGraphUnconsCertificate_structuralPayloadBound_le
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness hgraph hwidth htokenCount hcurrentValue htokenTableSize
      hcurrentSize hwitness hnumericSize
  have hbranch :=
    syntaxTermFullyFixedGraphBranchCertificate_structuralPayloadBound_le
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      hbinderSize hwitness hnumericSize hbitPositive
  have halign :=
    syntaxTermFullyFixedGraphTailCertificate_structuralPayload_eq tokenTable
      width tokenCount current next binderArity witness hgraph
  have hassembly :=
    transparentHybridConjunctionPayloadBound_le unconsCertificate
      branchCertificate _ _ huncons hbranch
  calc
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          unconsCertificate branchCertificate) := halign
    _ <= _ := hassembly

end FoundationCompactNumericListedDirectParserSyntaxTermGraphTailFullyFixedBounds
