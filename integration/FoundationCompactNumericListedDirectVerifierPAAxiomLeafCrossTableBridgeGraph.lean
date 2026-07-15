import integration.FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierValueLayouts

/-!
# Cross-table bridge for a PA-axiom verifier leaf

The parser tables and the canonical PA-rule table are independent.  This
bounded graph identifies the root context, candidate sentence, and decoded
PA-certificate slices bit for bit.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafCrossTableBridgeGraph

open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality

def CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph
    (proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish :
      Nat) : Prop :=
  CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount
        proofCandidateStart proofCandidateFinish
      ruleTable ruleWidth ruleTokenCount
        ruleCandidateStart ruleCandidateFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      certificateTable certificateWidth certificateTokenCount
        certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleAxiomStart ruleAxiomFinish

def compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef :
    𝚺₀.Semisentence 21 := .mkSigma
  “proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish.
    !(compactFixedWidthCrossTableSlicesEqDef)
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      proofTable proofWidth proofTokenCount
        proofCandidateStart proofCandidateFinish
      ruleTable ruleWidth ruleTokenCount
        ruleCandidateStart ruleCandidateFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      certificateTable certificateWidth certificateTokenCount
        certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleAxiomStart ruleAxiomFinish”

def compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphEnvironment
    (proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish :
      Nat) : Fin 21 → Nat :=
  ![proofTable, proofWidth, proofTokenCount, proofGammaStart, proofGammaFinish,
    proofCandidateStart, proofCandidateFinish,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateAxiomStart, certificateAxiomFinish,
    ruleTable, ruleWidth, ruleTokenCount, ruleGammaStart, ruleGammaFinish,
    ruleCandidateStart, ruleCandidateFinish, ruleAxiomStart, ruleAxiomFinish]

@[simp] theorem compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef_spec
    (proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish :
      Nat) :
    compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef.val.Evalb
        (compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphEnvironment
          proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
          proofCandidateStart proofCandidateFinish
          certificateTable certificateWidth certificateTokenCount
          certificateAxiomStart certificateAxiomFinish
          ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
          ruleCandidateStart ruleCandidateFinish ruleAxiomStart
          ruleAxiomFinish) ↔
      CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph
        proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
        proofCandidateStart proofCandidateFinish
        certificateTable certificateWidth certificateTokenCount
        certificateAxiomStart certificateAxiomFinish
        ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
        ruleCandidateStart ruleCandidateFinish ruleAxiomStart
        ruleAxiomFinish := by
  let env := compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphEnvironment
    proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
    proofCandidateStart proofCandidateFinish
    certificateTable certificateWidth certificateTokenCount
    certificateAxiomStart certificateAxiomFinish
    ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
    ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish
  change compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef.val.Evalb
      env ↔ _
  have hgammaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #3, #4,
          #12, #13, #14, #15, #16]) =
        ![proofTable, proofWidth, proofTokenCount, proofGammaStart,
          proofGammaFinish, ruleTable, ruleWidth, ruleTokenCount,
          ruleGammaStart, ruleGammaFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcandidateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #5, #6,
          #12, #13, #14, #17, #18]) =
        ![proofTable, proofWidth, proofTokenCount, proofCandidateStart,
          proofCandidateFinish, ruleTable, ruleWidth, ruleTokenCount,
          ruleCandidateStart, ruleCandidateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have haxiomEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 21), #8, #9, #10, #11,
          #12, #13, #14, #19, #20]) =
        ![certificateTable, certificateWidth, certificateTokenCount,
          certificateAxiomStart, certificateAxiomFinish,
          ruleTable, ruleWidth, ruleTokenCount, ruleAxiomStart,
          ruleAxiomFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef,
    CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph,
    hgammaEnv, hcandidateEnv, haxiomEnv, env]

theorem compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef.val := by
  simp [compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef]

theorem CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph.sound
    {proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish :
      Nat}
    {proofGamma ruleGamma : List (List Nat)}
    {proofCandidate ruleCandidate certificateAxiom ruleAxiom : List Nat}
    (hgraph : CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish)
    (hproofGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        proofGammaStart proofGammaFinish proofGamma)
    (hruleGamma : CompactAdditiveNatListListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish ruleGamma)
    (hproofCandidate : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        proofCandidateStart proofCandidateFinish proofCandidate)
    (hruleCandidate : CompactAdditiveNatListDirectLayout
      ruleTable ruleWidth ruleTokenCount
        ruleCandidateStart ruleCandidateFinish ruleCandidate)
    (hcertificateAxiom : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateAxiomStart certificateAxiomFinish certificateAxiom)
    (hruleAxiom : CompactAdditiveNatListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleAxiomStart ruleAxiomFinish
        ruleAxiom) :
    ruleGamma = proofGamma ∧ ruleCandidate = proofCandidate ∧
      ruleAxiom = certificateAxiom := by
  exact
    ⟨FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality.CompactFixedWidthCrossTableSlicesEq.natListListValues_eq
        hgraph.1 hproofGamma hruleGamma,
      hgraph.2.1.natListValues_eq hproofCandidate hruleCandidate,
      hgraph.2.2.natListValues_eq hcertificateAxiom hruleAxiom⟩

theorem CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph.of_layouts
    {proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish :
      Nat}
    {Gamma : List (List Nat)} {candidate axiomTokens : List Nat}
    (hproofGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        proofGammaStart proofGammaFinish Gamma)
    (hruleGamma : CompactAdditiveNatListListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish Gamma)
    (hproofCandidate : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        proofCandidateStart proofCandidateFinish candidate)
    (hruleCandidate : CompactAdditiveNatListDirectLayout
      ruleTable ruleWidth ruleTokenCount
        ruleCandidateStart ruleCandidateFinish candidate)
    (hcertificateAxiom : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateAxiomStart certificateAxiomFinish axiomTokens)
    (hruleAxiom : CompactAdditiveNatListDirectLayout
      ruleTable ruleWidth ruleTokenCount ruleAxiomStart ruleAxiomFinish
        axiomTokens) :
    CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount proofGammaStart proofGammaFinish
      proofCandidateStart proofCandidateFinish
      certificateTable certificateWidth certificateTokenCount
      certificateAxiomStart certificateAxiomFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleCandidateStart ruleCandidateFinish ruleAxiomStart ruleAxiomFinish :=
  ⟨CompactFixedWidthCrossTableSlicesEq.of_natListListLayouts
      hproofGamma hruleGamma,
    CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hproofCandidate hruleCandidate,
    CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hcertificateAxiom hruleAxiom⟩

#print axioms compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef_spec
#print axioms compactNumericVerifierPAAxiomLeafCrossTableBridgeGraphDef_sigmaZero
#print axioms CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph.sound
#print axioms CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph.of_layouts

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafCrossTableBridgeGraph
