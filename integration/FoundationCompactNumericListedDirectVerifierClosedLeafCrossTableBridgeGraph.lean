import integration.FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierValueLayouts

/-!
# Cross-table bridge for a closed verifier leaf

The parser table and the closed-rule table are deliberately independent.  This
bounded graph identifies the root context and first-formula slices bit for bit.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierClosedLeafCrossTableBridgeGraph

open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality

def CompactNumericVerifierClosedLeafCrossTableBridgeGraph
    (proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish : Nat) : Prop :=
  CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleFormulaStart ruleFormulaFinish

def compactNumericVerifierClosedLeafCrossTableBridgeGraphDef :
    𝚺₀.Semisentence 14 := .mkSigma
  “proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish.
    !(compactFixedWidthCrossTableSlicesEqDef)
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      proofTable proofWidth proofTokenCount proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleFormulaStart ruleFormulaFinish”

def compactNumericVerifierClosedLeafCrossTableBridgeGraphEnvironment
    (proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish : Nat) : Fin 14 → Nat :=
  ![proofTable, proofWidth, proofTokenCount, proofGammaStart, proofGammaFinish,
    proofFormulaStart, proofFormulaFinish,
    ruleTable, ruleWidth, ruleTokenCount, ruleGammaStart, ruleGammaFinish,
    ruleFormulaStart, ruleFormulaFinish]

@[simp] theorem compactNumericVerifierClosedLeafCrossTableBridgeGraphDef_spec
    (proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish : Nat) :
    compactNumericVerifierClosedLeafCrossTableBridgeGraphDef.val.Evalb
        (compactNumericVerifierClosedLeafCrossTableBridgeGraphEnvironment
          proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
          proofFormulaStart proofFormulaFinish
          ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
          ruleFormulaStart ruleFormulaFinish) ↔
      CompactNumericVerifierClosedLeafCrossTableBridgeGraph
        proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
        proofFormulaStart proofFormulaFinish
        ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
        ruleFormulaStart ruleFormulaFinish := by
  let env := compactNumericVerifierClosedLeafCrossTableBridgeGraphEnvironment
    proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
    proofFormulaStart proofFormulaFinish
    ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
    ruleFormulaStart ruleFormulaFinish
  change compactNumericVerifierClosedLeafCrossTableBridgeGraphDef.val.Evalb env ↔ _
  have hgammaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #3, #4,
          #7, #8, #9, #10, #11]) =
        ![proofTable, proofWidth, proofTokenCount, proofGammaStart,
          proofGammaFinish, ruleTable, ruleWidth, ruleTokenCount,
          ruleGammaStart, ruleGammaFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #5, #6,
          #7, #8, #9, #12, #13]) =
        ![proofTable, proofWidth, proofTokenCount, proofFormulaStart,
          proofFormulaFinish, ruleTable, ruleWidth, ruleTokenCount,
          ruleFormulaStart, ruleFormulaFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierClosedLeafCrossTableBridgeGraphDef,
    CompactNumericVerifierClosedLeafCrossTableBridgeGraph,
    hgammaEnv, hformulaEnv, env]

theorem compactNumericVerifierClosedLeafCrossTableBridgeGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierClosedLeafCrossTableBridgeGraphDef.val := by
  simp [compactNumericVerifierClosedLeafCrossTableBridgeGraphDef]

theorem CompactNumericVerifierClosedLeafCrossTableBridgeGraph.sound
    {proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish : Nat}
    {proofGamma ruleGamma : List (List Nat)} {proofFormula ruleFormula : List Nat}
    (hgraph : CompactNumericVerifierClosedLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish)
    (hproofGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish proofGamma)
    (hruleGamma : CompactAdditiveNatListListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish ruleGamma)
    (hproofFormula : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofFormulaStart proofFormulaFinish proofFormula)
    (hruleFormula : CompactAdditiveNatListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleFormulaStart ruleFormulaFinish ruleFormula) :
    ruleGamma = proofGamma ∧ ruleFormula = proofFormula := by
  exact ⟨FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality.CompactFixedWidthCrossTableSlicesEq.natListListValues_eq
      hgraph.1 hproofGamma hruleGamma,
    hgraph.2.natListValues_eq hproofFormula hruleFormula⟩

theorem CompactNumericVerifierClosedLeafCrossTableBridgeGraph.of_layouts
    {proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish : Nat}
    {Gamma : List (List Nat)} {formula : List Nat}
    (hproofGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish Gamma)
    (hruleGamma : CompactAdditiveNatListListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish Gamma)
    (hproofFormula : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofFormulaStart proofFormulaFinish formula)
    (hruleFormula : CompactAdditiveNatListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleFormulaStart ruleFormulaFinish formula) :
    CompactNumericVerifierClosedLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofFormulaStart proofFormulaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish :=
  ⟨CompactFixedWidthCrossTableSlicesEq.of_natListListLayouts hproofGamma hruleGamma,
    CompactFixedWidthCrossTableSlicesEq.of_natListLayouts hproofFormula hruleFormula⟩

#print axioms compactNumericVerifierClosedLeafCrossTableBridgeGraphDef_spec
#print axioms compactNumericVerifierClosedLeafCrossTableBridgeGraphDef_sigmaZero
#print axioms CompactNumericVerifierClosedLeafCrossTableBridgeGraph.sound
#print axioms CompactNumericVerifierClosedLeafCrossTableBridgeGraph.of_layouts

end FoundationCompactNumericListedDirectVerifierClosedLeafCrossTableBridgeGraph
