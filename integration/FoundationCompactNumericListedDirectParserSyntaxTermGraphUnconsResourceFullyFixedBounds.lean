import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBounds

/-! # Fully fixed task-uncons leaf of the syntax-term graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphUnconsResourceFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBounds

theorem
    syntaxTermFullyFixedGraphUnconsCertificate_structuralPayloadBound_le
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
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness
        bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphUnconsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) <=
      unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hcurrentTasksCount : current.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (7 : Fin 8)
  have hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (6 : Fin 8)
  have htailBoundarySize :
      Nat.size witness.tailBoundary <= bitBound := by
    simpa [compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (0 : Fin 6)
  have htailCount : witness.tailCount <= numericBound := by
    have hdrop := hgraph.2.1.2.1
    have hcount := hdrop.2.1
    omega
  rw [syntaxTermFullyFixedGraphUnconsCertificate_structuralPayload_eq]
  exact
    unconsRowsWithSizeCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 0
      binderArity 0 numericBound bitBound hgraph.2.1 hwidth htokenCount
      hcurrentTasksCount htailCount htokenTableSize
      hcurrentTasksBoundarySize htailBoundarySize hnumericSize

end FoundationCompactNumericListedDirectParserSyntaxTermGraphUnconsResourceFullyFixedBounds
