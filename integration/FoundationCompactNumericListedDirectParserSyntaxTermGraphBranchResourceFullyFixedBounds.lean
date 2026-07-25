import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate

/-! # Fully fixed eight-way branch leaf of the syntax-term graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphBranchResourceFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate

theorem
    syntaxTermFullyFixedGraphBranchCertificate_structuralPayloadBound_le
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
        (syntaxTermFullyFixedGraphBranchCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) <=
      syntaxTermAllBranchesFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  have htailCount : witness.tailCount <= numericBound := by
    have hdrop := hgraph.2.1.2.1
    have hcount := hdrop.2.1
    have hcurrentTasksCount : current.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hcurrentValue (7 : Fin 8)
    omega
  have htailBoundarySize :
      Nat.size witness.tailBoundary <= bitBound := by
    simpa [compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (0 : Fin 6)
  have htagSize : Nat.size witness.tag <= bitBound := by
    simpa [compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (3 : Fin 6)
  have hargumentSize : Nat.size witness.argument <= bitBound := by
    simpa [compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (4 : Fin 6)
  have hfunctionCodeSize : Nat.size witness.functionCode <= bitBound := by
    simpa [compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (5 : Fin 6)
  have hsize :=
    compactUnifiedParserSyntaxTermFormulaEnvironment_size_le tokenTable width
      tokenCount current next binderArity witness bitBound htokenTableSize
      hwidthSize htokenCountSize hcurrentSize hnextSize hbinderSize hwitness
  rw [syntaxTermFullyFixedGraphBranchCertificate_structuralPayload_eq]
  exact
    syntaxTermFullyFixedBranchCertificateFromData_structuralPayloadBound_le
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness
      (syntaxTermFullyFixedGraphBranchData tokenTable width tokenCount current
        next binderArity witness hgraph)
      hwidth htokenCount htailCount hcurrentValue hnextValue htokenTableSize
      hcurrentSize hnextSize htailBoundarySize htagSize hargumentSize
      hfunctionCodeSize hbinderSize hnumericSize hbitPositive hsize

end FoundationCompactNumericListedDirectParserSyntaxTermGraphBranchResourceFullyFixedBounds
