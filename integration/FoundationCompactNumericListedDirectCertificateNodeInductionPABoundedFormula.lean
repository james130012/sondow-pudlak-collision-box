import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint

/-!
# Bounded formula for induction PA-axiom certificate nodes

The twenty-one local coordinates for tag 22 are bounded by one public endpoint
value.  The complete binder-one formula-parser trace remains inside the same
bounded arithmetic formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula

open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint

def compactCertificateNodeInductionPAEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      axiomBoundary axiomCount axiomBoundarySize
      formulaBoundary formulaCount formulaBoundarySize
      suffixBoundary suffixCount suffixBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat) :
    CompactCertificateNodeInductionPAEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailStart := tailStart
    tailFinish := tailFinish
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    axiomBoundary := axiomBoundary
    axiomCount := axiomCount
    axiomBoundarySize := axiomBoundarySize
    parser :=
      { inputBoundary := formulaBoundary
        inputCount := formulaCount
        inputBoundarySize := formulaBoundarySize
        expectedBoundary := suffixBoundary
        expectedCount := suffixCount
        expectedBoundarySize := suffixBoundarySize
        stateBoundary := stateBoundary
        stateCount := stateCount
        tableWidth := tableWidth
        valueBound := valueBound } }

def CompactCertificateNodeInductionPAEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailStart, tailStart ≤ endpointBound ∧
  ∃ tailFinish, tailFinish ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ axiomBoundary, axiomBoundary ≤ endpointBound ∧
  ∃ axiomCount, axiomCount ≤ endpointBound ∧
  ∃ axiomBoundarySize, axiomBoundarySize ≤ endpointBound ∧
  ∃ formulaBoundary, formulaBoundary ≤ endpointBound ∧
  ∃ formulaCount, formulaCount ≤ endpointBound ∧
  ∃ formulaBoundarySize, formulaBoundarySize ≤ endpointBound ∧
  ∃ suffixBoundary, suffixBoundary ≤ endpointBound ∧
  ∃ suffixCount, suffixCount ≤ endpointBound ∧
  ∃ suffixBoundarySize, suffixBoundarySize ≤ endpointBound ∧
  ∃ stateBoundary, stateBoundary ≤ endpointBound ∧
  ∃ stateCount, stateCount ≤ endpointBound ∧
  ∃ tableWidth, tableWidth ≤ endpointBound ∧
  ∃ valueBound, valueBound ≤ endpointBound ∧
    CompactCertificateNodeInductionPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag
        (compactCertificateNodeInductionPAEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailStart tailFinish tailBoundary tailCount tailBoundarySize
          axiomBoundary axiomCount axiomBoundarySize
          formulaBoundary formulaCount formulaBoundarySize
          suffixBoundary suffixCount suffixBoundarySize
          stateBoundary stateCount tableWidth valueBound)

def compactCertificateNodeInductionPAEndpointBoundedGraphDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ tailStart <⁺ endpointBound,
    ∃ tailFinish <⁺ endpointBound,
    ∃ tailBoundary <⁺ endpointBound,
    ∃ tailCount <⁺ endpointBound,
    ∃ tailBoundarySize <⁺ endpointBound,
    ∃ axiomBoundary <⁺ endpointBound,
    ∃ axiomCount <⁺ endpointBound,
    ∃ axiomBoundarySize <⁺ endpointBound,
    ∃ formulaBoundary <⁺ endpointBound,
    ∃ formulaCount <⁺ endpointBound,
    ∃ formulaBoundarySize <⁺ endpointBound,
    ∃ suffixBoundary <⁺ endpointBound,
    ∃ suffixCount <⁺ endpointBound,
    ∃ suffixBoundarySize <⁺ endpointBound,
    ∃ stateBoundary <⁺ endpointBound,
    ∃ stateCount <⁺ endpointBound,
    ∃ tableWidth <⁺ endpointBound,
    ∃ valueBound <⁺ endpointBound,
      !(compactCertificateNodeInductionPAEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag
        inputBoundary inputCount inputBoundarySize
        tailStart tailFinish tailBoundary tailCount tailBoundarySize
        axiomBoundary axiomCount axiomBoundarySize
        formulaBoundary formulaCount formulaBoundarySize
        suffixBoundary suffixCount suffixBoundarySize
        stateBoundary stateCount tableWidth valueBound”

set_option maxHeartbeats 1500000 in
-- Twenty-one nested witnesses and the embedded parser formula need a local budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeInductionPAEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat) :
    compactCertificateNodeInductionPAEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag, endpointBound] ↔
      CompactCertificateNodeInductionPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag endpointBound := by
  have hrow
      (valueBound tableWidth stateCount stateBoundary
        suffixBoundarySize suffixCount suffixBoundary
        formulaBoundarySize formulaCount formulaBoundary
        axiomBoundarySize axiomCount axiomBoundary
        tailBoundarySize tailCount tailBoundary tailFinish tailStart
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![valueBound, tableWidth, stateCount, stateBoundary,
                suffixBoundarySize, suffixCount, suffixBoundary,
                formulaBoundarySize, formulaCount, formulaBoundary,
                axiomBoundarySize, axiomCount, axiomBoundary,
                tailBoundarySize, tailCount, tailBoundary, tailFinish,
                tailStart, inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                axiomStart, axiomFinish, formulaStart, formulaFinish,
                suffixStart, suffixFinish, certificateTag, endpointBound]
              Empty.elim ∘
            ![(#21 : Semiterm ℒₒᵣ Empty 34), #22, #23, #24, #25,
              #26, #27, #28, #29, #30, #31, #32,
              #20, #19, #18, #17, #16, #15, #14, #13,
              #12, #11, #10, #9, #8, #7, #6, #5, #4,
              #3, #2, #1, #0])
          Empty.elim) compactCertificateNodeInductionPAEndpointGraphDef.val ↔
        CompactCertificateNodeInductionPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag
            (compactCertificateNodeInductionPAEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              tailStart tailFinish tailBoundary tailCount tailBoundarySize
              axiomBoundary axiomCount axiomBoundarySize
              formulaBoundary formulaCount formulaBoundarySize
              suffixBoundary suffixCount suffixBoundarySize
              stateBoundary stateCount tableWidth valueBound) := by
    have henv :
        (Semiterm.val
            ![valueBound, tableWidth, stateCount, stateBoundary,
              suffixBoundarySize, suffixCount, suffixBoundary,
              formulaBoundarySize, formulaCount, formulaBoundary,
              axiomBoundarySize, axiomCount, axiomBoundary,
              tailBoundarySize, tailCount, tailBoundary, tailFinish,
              tailStart, inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              axiomStart, axiomFinish, formulaStart, formulaFinish,
              suffixStart, suffixFinish, certificateTag, endpointBound]
            Empty.elim ∘
          ![(#21 : Semiterm ℒₒᵣ Empty 34), #22, #23, #24, #25,
            #26, #27, #28, #29, #30, #31, #32,
            #20, #19, #18, #17, #16, #15, #14, #13,
            #12, #11, #10, #9, #8, #7, #6, #5, #4,
            #3, #2, #1, #0]) =
          compactCertificateNodeInductionPAEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish certificateTag
              (compactCertificateNodeInductionPAEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailStart tailFinish tailBoundary tailCount tailBoundarySize
                axiomBoundary axiomCount axiomBoundarySize
                formulaBoundary formulaCount formulaBoundarySize
                suffixBoundary suffixCount suffixBoundarySize
                stateBoundary stateCount tableWidth valueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeInductionPAEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag _
  simp [compactCertificateNodeInductionPAEndpointBoundedGraphDef,
    CompactCertificateNodeInductionPAEndpointBoundedGraph, hrow]

theorem compactCertificateNodeInductionPAEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeInductionPAEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodeInductionPAEndpointBoundedGraphDef]

theorem CompactCertificateNodeInductionPAEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat}
    (hbounded : CompactCertificateNodeInductionPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag endpointBound) :
    ∃ coordinates : CompactCertificateNodeInductionPAEndpointCoordinates,
      CompactCertificateNodeInductionPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _hinputBoundary,
      inputCount, _hinputCount,
      inputBoundarySize, _hinputBoundarySize,
      tailStart, _htailStart, tailFinish, _htailFinish,
      tailBoundary, _htailBoundary, tailCount, _htailCount,
      tailBoundarySize, _htailBoundarySize,
      axiomBoundary, _haxiomBoundary, axiomCount, _haxiomCount,
      axiomBoundarySize, _haxiomBoundarySize,
      formulaBoundary, _hformulaBoundary,
      formulaCount, _hformulaCount,
      formulaBoundarySize, _hformulaBoundarySize,
      suffixBoundary, _hsuffixBoundary,
      suffixCount, _hsuffixCount,
      suffixBoundarySize, _hsuffixBoundarySize,
      stateBoundary, _hstateBoundary, stateCount, _hstateCount,
      tableWidth, _htableWidth, valueBound, _hvalueBound, hgraph⟩
  exact ⟨compactCertificateNodeInductionPAEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailStart tailFinish tailBoundary tailCount tailBoundarySize
    axiomBoundary axiomCount axiomBoundarySize
    formulaBoundary formulaCount formulaBoundarySize
    suffixBoundary suffixCount suffixBoundarySize
    stateBoundary stateCount tableWidth valueBound, hgraph⟩

theorem CompactCertificateNodeInductionPAEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeInductionPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeInductionPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag coordinates) :
    ∃ endpointBound,
      CompactCertificateNodeInductionPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailStart +
    coordinates.tailFinish + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize +
    coordinates.axiomBoundary + coordinates.axiomCount +
    coordinates.axiomBoundarySize + coordinates.parser.inputBoundary +
    coordinates.parser.inputCount + coordinates.parser.inputBoundarySize +
    coordinates.parser.expectedBoundary + coordinates.parser.expectedCount +
    coordinates.parser.expectedBoundarySize + coordinates.parser.stateBoundary +
    coordinates.parser.stateCount + coordinates.parser.tableWidth +
    coordinates.parser.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodeInductionPAEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.tailStart, ?_,
      coordinates.tailFinish, ?_, coordinates.tailBoundary, ?_,
      coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
      coordinates.axiomBoundary, ?_, coordinates.axiomCount, ?_,
      coordinates.axiomBoundarySize, ?_,
      coordinates.parser.inputBoundary, ?_, coordinates.parser.inputCount, ?_,
      coordinates.parser.inputBoundarySize, ?_,
      coordinates.parser.expectedBoundary, ?_,
      coordinates.parser.expectedCount, ?_,
      coordinates.parser.expectedBoundarySize, ?_,
      coordinates.parser.stateBoundary, ?_, coordinates.parser.stateCount, ?_,
      coordinates.parser.tableWidth, ?_, coordinates.parser.valueBound, ?_,
      hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodeInductionPAEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat}
    (hbounded : CompactCertificateNodeInductionPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag endpointBound) :
    ∃ input axiomTokens suffix : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, (axiomTokens, suffix)) := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactCertificateNodeInductionPAEndpointBoundedGraph_of_results
    (formulaInput suffix : List Nat)
    (hformula : FoundationCompactSyntaxTokenMachine.compactFormulaTokenParser
      1 formulaInput = some suffix) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactCertificateNodeInductionPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish 1 endpointBound := by
  rcases exists_compactCertificateNodeInductionPAEndpointGraph_of_results
      formulaInput suffix hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, coordinates, hgraph⟩
  rcases CompactCertificateNodeInductionPAEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, endpointBound, hbounded⟩

#print axioms compactCertificateNodeInductionPAEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodeInductionPAEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeInductionPAEndpointBoundedGraph.exists_coordinates
#print axioms CompactCertificateNodeInductionPAEndpointGraph.exists_bounded
#print axioms CompactCertificateNodeInductionPAEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodeInductionPAEndpointBoundedGraph_of_results

end FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula
