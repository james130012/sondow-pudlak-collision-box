import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectParserClosedSuccessStepFormula

/-!
# Adjacent-row formula for successful closed-formula parsing

The existing adjacent syntax row already binds two exact state rows and all
seven step-witness slots.  This layer conjoins the closed-success safety
condition on those very same values, so no detached safety witness can be used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedSuccessBridge
open FoundationCompactNumericListedDirectParserClosedSuccessStepFormula

def CompactParserClosedSuccessAdjacentStepRowGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : Prop :=
  CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row ∧
    CompactUnifiedParserClosedSuccessStepRows
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        row.stepWitness

def compactParserClosedSuccessAdjacentStepRowDef :
    𝚺₀.Semisentence 33 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount index
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      currentTokensBoundarySize currentTasksBoundarySize
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      nextTokensBoundarySize nextTasksBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6.
    !(compactParserSyntaxAdjacentStepRowDef)
      tokenTable width tokenCount stateBoundary stateCount index
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      currentTokensBoundarySize currentTasksBoundarySize
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      nextTokensBoundarySize nextTasksBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∧
    !(compactUnifiedParserClosedSuccessStepRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6”

@[simp] theorem compactParserClosedSuccessAdjacentStepRowDef_spec
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserClosedSuccessAdjacentStepRowDef.val.Evalb
        (compactParserSyntaxAdjacentStepRowEnvironment
          tokenTable width tokenCount stateBoundary stateCount index row) ↔
      CompactParserClosedSuccessAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount index row := by
  let env := compactParserSyntaxAdjacentStepRowEnvironment
    tokenTable width tokenCount stateBoundary stateCount index row
  change compactParserClosedSuccessAdjacentStepRowDef.val.Evalb env ↔ _
  have hfullEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18, #19,
          #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30, #31,
          #32]) = env := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #6, #7, #8, #9, #10, #11, #12, #13,
          #16, #17, #18, #19, #20, #21, #22, #23,
          #26, #27, #28, #29, #30, #31, #32]) =
        compactUnifiedParserSyntaxStepFormulaEnvironment
          tokenTable width tokenCount row.currentCoordinates
            row.nextCoordinates row.stepWitness := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hadjacentSpec : compactParserSyntaxAdjacentStepRowDef.val.Evalb env ↔
      CompactParserSyntaxAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount index row := by
    exact compactParserSyntaxAdjacentStepRowDef_spec
      tokenTable width tokenCount stateBoundary stateCount index row
  have hclosedSpec : compactUnifiedParserClosedSuccessStepRowsDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #6, #7, #8, #9, #10, #11, #12, #13,
            #16, #17, #18, #19, #20, #21, #22, #23,
            #26, #27, #28, #29, #30, #31, #32]) ↔
      CompactUnifiedParserClosedSuccessStepRows
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
          row.stepWitness := by
    rw [hstepEnv]
    exact compactUnifiedParserClosedSuccessStepRowsDef_spec
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        row.stepWitness
  simp [compactParserClosedSuccessAdjacentStepRowDef,
    CompactParserClosedSuccessAdjacentStepRowGraph,
    hfullEnv, hadjacentSpec, hclosedSpec]

theorem compactParserClosedSuccessAdjacentStepRowDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedSuccessAdjacentStepRowDef.val := by
  simp [compactParserClosedSuccessAdjacentStepRowDef]

theorem CompactParserSyntaxAdjacentStepRowGraph.toClosedSuccess
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {row : CompactParserSyntaxAdjacentStepRow}
    {current : CompactUnifiedParserState}
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row)
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount row.currentCoordinates current)
    (hsafe : CompactClosedSyntaxStepSafe current) :
    CompactParserClosedSuccessAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row := by
  refine ⟨hgraph, hgraph.2.2, ?_⟩
  intro hterm
  exact CompactUnifiedParserSyntaxTermRows.guard_of_safe
    hcurrent hterm hsafe

#print axioms compactParserClosedSuccessAdjacentStepRowDef_spec
#print axioms compactParserClosedSuccessAdjacentStepRowDef_sigmaZero
#print axioms CompactParserSyntaxAdjacentStepRowGraph.toClosedSuccess

end FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepFormula
