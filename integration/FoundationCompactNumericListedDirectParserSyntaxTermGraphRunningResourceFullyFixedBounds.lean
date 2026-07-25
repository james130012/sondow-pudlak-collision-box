import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds

/-! # Fully fixed running-status leaf of the syntax-term graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphRunningResourceFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds

theorem
    syntaxTermFullyFixedGraphRunningCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness)
    (hwidth : width <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphRunningCertificate tokenTable width
          tokenCount current next binderArity witness hgraph) <=
      compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound := by
  have hcurrentTasksFinish : current.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (3 : Fin 8)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (1 : Fin 8)
  have hcurrentTasksFinishSize :
      Nat.size current.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (3 : Fin 8)
  rw [syntaxTermFullyFixedGraphRunningCertificate_structuralPayload_eq]
  exact
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount current.tasksFinish current.finish
      numericBound bitBound hwidth hcurrentTasksFinish htokenTableSize
      hwidthSize htokenCountSize hcurrentTasksFinishSize hcurrentFinishSize
      hgraph.1

end FoundationCompactNumericListedDirectParserSyntaxTermGraphRunningResourceFullyFixedBounds
