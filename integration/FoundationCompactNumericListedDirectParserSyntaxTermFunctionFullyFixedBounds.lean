import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsFullyFixedBounds

/-!
# Fully fixed function syntax-term transition

The public checked certificate is the cast of the independently bounded
three-branch certificate to the project's canonical closed formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionBranchCertificates
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsFullyFixedBounds

theorem
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity numericBound bitBound :
      Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity
      functionArity)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity functionArity hgraph) <=
      syntaxTermFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  have hparts :=
    syntaxTermFunctionPartsCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity functionArity numericBound bitBound hgraph hwidth
      htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
      hnextSize htailBoundarySize hbinderSize hfunctionSize hnumericSize
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity functionArity).symm
        (syntaxTermFunctionPartsCertificate tokenTable width tokenCount
          next.tasksFinish next.finish current.tokensBoundary
          current.tokensCount next.tokensBoundary next.tokensCount
          tailBoundary tailCount next.tasksBoundary next.tasksCount binderArity
          functionArity hgraph.1 hgraph.2.1 hgraph.2.2)) <= _
  simp only [hybridFormulaStructuralPayloadBound]
  convert hparts using 1
  congr 1

#print axioms
  compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionFullyFixedBounds
