import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

/-! # Bounds for the seventeen final endpoint coordinates -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFinalValueBounds

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

theorem compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues_le
    (valueBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hstart : witness.finalCoordinates.start <= valueBound)
    (hfinish : witness.finalCoordinates.finish <= valueBound)
    (hparserFinish : witness.finalCoordinates.parserFinish <= valueBound)
    (hparserTokensFinish :
      witness.finalCoordinates.parserTokensFinish <= valueBound)
    (hparserTasksFinish :
      witness.finalCoordinates.parserTasksFinish <= valueBound)
    (hparserTokensBoundary :
      witness.finalCoordinates.parserTokensBoundary <= valueBound)
    (hparserTokensCount :
      witness.finalCoordinates.parserTokensCount <= valueBound)
    (hparserTasksBoundary :
      witness.finalCoordinates.parserTasksBoundary <= valueBound)
    (hparserTasksCount :
      witness.finalCoordinates.parserTasksCount <= valueBound)
    (houtputBoundary : witness.finalCoordinates.outputBoundary <= valueBound)
    (houtputCount : witness.finalCoordinates.outputCount <= valueBound)
    (hparserTokensBoundarySize :
      witness.finalSizeWitness.parserTokensBoundarySize <= valueBound)
    (hparserTasksBoundarySize :
      witness.finalSizeWitness.parserTasksBoundarySize <= valueBound)
    (houtputBoundarySize :
      witness.finalSizeWitness.outputBoundarySize <= valueBound)
    (hparserOutputStart : witness.finalParserOutputStart <= valueBound)
    (hparserOutputBoundary : witness.finalParserOutputBoundary <= valueBound)
    (hparserOutputBoundarySize :
      witness.finalParserOutputBoundarySize <= valueBound) :
    forall coordinate,
      compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues
        witness coordinate <= valueBound := by
  intro coordinate
  fin_cases coordinate <;>
    simp [compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues]
  all_goals assumption

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues_le

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFinalValueBounds
