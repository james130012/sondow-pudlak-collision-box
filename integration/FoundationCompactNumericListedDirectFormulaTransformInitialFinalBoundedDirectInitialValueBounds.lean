import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

/-! # Bounds for the fourteen initial endpoint coordinates -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectInitialValueBounds

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

theorem compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues_le
    (valueBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hstart : witness.initialCoordinates.start <= valueBound)
    (hfinish : witness.initialCoordinates.finish <= valueBound)
    (hparserFinish : witness.initialCoordinates.parserFinish <= valueBound)
    (hparserTokensFinish :
      witness.initialCoordinates.parserTokensFinish <= valueBound)
    (hparserTasksFinish :
      witness.initialCoordinates.parserTasksFinish <= valueBound)
    (hparserTokensBoundary :
      witness.initialCoordinates.parserTokensBoundary <= valueBound)
    (hparserTokensCount :
      witness.initialCoordinates.parserTokensCount <= valueBound)
    (hparserTasksBoundary :
      witness.initialCoordinates.parserTasksBoundary <= valueBound)
    (hparserTasksCount :
      witness.initialCoordinates.parserTasksCount <= valueBound)
    (houtputBoundary :
      witness.initialCoordinates.outputBoundary <= valueBound)
    (houtputCount : witness.initialCoordinates.outputCount <= valueBound)
    (hparserTokensBoundarySize :
      witness.initialSizeWitness.parserTokensBoundarySize <= valueBound)
    (hparserTasksBoundarySize :
      witness.initialSizeWitness.parserTasksBoundarySize <= valueBound)
    (houtputBoundarySize :
      witness.initialSizeWitness.outputBoundarySize <= valueBound) :
    forall coordinate,
      compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues
        witness coordinate <= valueBound := by
  intro coordinate
  fin_cases coordinate <;>
    simp [compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues]
  all_goals assumption

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues_le

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectInitialValueBounds
