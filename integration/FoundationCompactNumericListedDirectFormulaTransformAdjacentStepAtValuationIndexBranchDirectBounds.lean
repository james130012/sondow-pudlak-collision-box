import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryBounds

/-!
# Branch-sensitive direct resource for one formula-transform adjacent row

The current and next state resources are unchanged.  The transform-step child
is charged by the checked semantic branch selected by its graph, rather than
by the envelope containing all six branches.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexBranchDirectBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAClosedHybridContextTransport
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds

private theorem arithmeticAddTerm_eq_func_branch
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables_branch
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticAddTerm_freeVariables_branch
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func_branch]
  exact binaryFunctionTerm_freeVariables_branch Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty_branch :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd_branch
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_branch]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_branch (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) : Nat := by
  rcases hgraph with ⟨_hcurrent, _hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let currentFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
      row.currentSize
  let nextFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula := compactFormulaTransformStepRowsClosedFormula tokenTable
    width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let currentResource :=
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize
  let nextResource :=
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize
  let stepResource := compactFormulaTransformStepRowsGraphPayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount hstep
  let nextStepResource := transparentHybridConjunctionPayloadEnvelope valuation
    nextFormula stepFormula nextResource stepResource
  exact transparentHybridConjunctionPayloadEnvelope valuation currentFormula
    (nextFormula ⋏ stepFormula) currentResource nextStepResource

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchExplicitDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount indexTerm mode witnessStart
        witnessFinish witnessCount row)
      (compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_branch,
      arithmeticOneTerm_freeVariables_eq_empty_branch]
    simpa using hindexVariables
  have hnextAtTerm : CompactFormulaTransformStateAtRows tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, termValue_arithmeticAdd_branch,
      termValue_arithmeticOne_branch] using hnext
  let currentFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
      row.currentSize
  let nextFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula := compactFormulaTransformStepRowsClosedFormula tokenTable
    width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let currentBound :=
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize hindexVariables hcurrent
  let nextBound :=
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize hnextIndexVariables
      hnextAtTerm
  let stepCertificate :=
    compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount row.currentCoordinates row.nextCoordinates mode
      row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
      witnessCount hstep
  have hstepClosed :=
    compactFormulaTransformStepRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
      mode row.stepWitness row.consumedCount row.mappedHead witnessStart
      witnessFinish witnessCount
  let stepProof := compileClosedHybridAtValuation (target := valuation)
    stepCertificate hstepClosed
  let stepResource := compactFormulaTransformStepRowsGraphPayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount hstep
  have hstepResource : stepProof.payloadLength <= stepResource :=
    (compileClosedHybridAtValuation_payloadLength_le_structural
      (target := valuation) stepCertificate hstepClosed).trans
        (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount row.currentCoordinates
          row.nextCoordinates mode row.stepWitness row.consumedCount
          row.mappedHead witnessStart witnessFinish witnessCount hstep)
  let nextStepProof := compileDirectConjunction nextBound.proof stepProof
  have hnextStep := compileDirectConjunction_payloadLength_le nextBound.proof
    stepProof
    (compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize)
    stepResource nextBound.payloadLength_le hstepResource
  let explicitProof := compileDirectConjunction currentBound.proof nextStepProof
  have hexplicit := compileDirectConjunction_payloadLength_le
    currentBound.proof nextStepProof
    (compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize)
    (transparentHybridConjunctionPayloadEnvelope valuation nextFormula
      stepFormula
      (compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        nextIndexTerm row.nextCoordinates row.nextSize)
      stepResource)
    currentBound.payloadLength_le hnextStep
  have hformula :
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitFormula
          tokenTable width tokenCount stateBoundary stateCount indexTerm mode
          witnessStart witnessFinish witnessCount row =
        compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
          width tokenCount stateBoundary stateCount indexTerm mode witnessStart
          witnessFinish witnessCount row :=
    (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm mode
      witnessStart witnessFinish witnessCount row).symm
  let proof := castValuationContextProof hformula explicitProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula explicitProof]
  unfold
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope
  dsimp only [nextIndexTerm, currentFormula, nextFormula, stepFormula,
    currentBound, nextBound, stepCertificate, stepProof, stepResource,
    nextStepProof, explicitProof]
  exact hexplicit

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) : Nat := by
  rcases hgraph with ⟨_hcurrent, _hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let currentFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
      row.currentSize
  let nextFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula := compactFormulaTransformStepRowsClosedFormula tokenTable
    width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let currentResource :=
    compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize
  let nextResource :=
    compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize
  let stepResource := compactFormulaTransformStepRowsGraphPayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount hstep
  let nextStepResource := transparentHybridConjunctionPayloadEnvelope valuation
    nextFormula stepFormula nextResource stepResource
  exact transparentHybridConjunctionPayloadEnvelope valuation currentFormula
    (nextFormula ⋏ stepFormula) currentResource nextStepResource

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreExplicitDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount indexTerm mode witnessStart
        witnessFinish witnessCount row)
      (compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_branch,
      arithmeticOneTerm_freeVariables_eq_empty_branch]
    simpa using hindexVariables
  have hnextAtTerm : CompactFormulaTransformStateAtRows tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, termValue_arithmeticAdd_branch,
      termValue_arithmeticOne_branch] using hnext
  let currentFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
      row.currentSize
  let nextFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula := compactFormulaTransformStepRowsClosedFormula tokenTable
    width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let currentBound :=
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraphFixedCore
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize hindexVariables hcurrent
  let nextBound :=
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraphFixedCore
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize hnextIndexVariables
      hnextAtTerm
  let stepCertificate :=
    compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount row.currentCoordinates row.nextCoordinates mode
      row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
      witnessCount hstep
  have hstepClosed :=
    compactFormulaTransformStepRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
      mode row.stepWitness row.consumedCount row.mappedHead witnessStart
      witnessFinish witnessCount
  let stepProof := compileClosedHybridAtValuation (target := valuation)
    stepCertificate hstepClosed
  let stepResource := compactFormulaTransformStepRowsGraphPayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount hstep
  have hstepResource : stepProof.payloadLength <= stepResource :=
    (compileClosedHybridAtValuation_payloadLength_le_structural
      (target := valuation) stepCertificate hstepClosed).trans
        (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
          tokenTable width tokenCount row.currentCoordinates
          row.nextCoordinates mode row.stepWitness row.consumedCount
          row.mappedHead witnessStart witnessFinish witnessCount hstep)
  let nextStepProof := compileDirectConjunction nextBound.proof stepProof
  have hnextStep := compileDirectConjunction_payloadLength_le nextBound.proof
    stepProof
    (compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize)
    stepResource nextBound.payloadLength_le hstepResource
  let explicitProof := compileDirectConjunction currentBound.proof nextStepProof
  have hexplicit := compileDirectConjunction_payloadLength_le
    currentBound.proof nextStepProof
    (compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize)
    (transparentHybridConjunctionPayloadEnvelope valuation nextFormula
      stepFormula
      (compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        nextIndexTerm row.nextCoordinates row.nextSize)
      stepResource)
    currentBound.payloadLength_le hnextStep
  have hformula :
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitFormula
          tokenTable width tokenCount stateBoundary stateCount indexTerm mode
          witnessStart witnessFinish witnessCount row =
        compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
          width tokenCount stateBoundary stateCount indexTerm mode witnessStart
          witnessFinish witnessCount row :=
    (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm mode
      witnessStart witnessFinish witnessCount row).symm
  let proof := castValuationContextProof hformula explicitProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula explicitProof]
  unfold
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope
  dsimp only [nextIndexTerm, currentFormula, nextFormula, stepFormula,
    currentBound, nextBound, stepCertificate, stepProof, stepResource,
    nextStepProof, explicitProof]
  exact hexplicit

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) : Nat :=
  if hindexVariables : indexTerm.freeVariables ⊆ {0} then
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount row hgraph
  else
    hybridFormulaStructuralPayloadBound
      (compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph)

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let currentFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
      row.currentSize
  let nextFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula := compactFormulaTransformStepRowsClosedFormula tokenTable
    width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let currentResource :=
    compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize
  let nextResource :=
    compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize
  let stepResource := compactFormulaTransformStepRowsPublicFinitePayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let nextStepResource := transparentHybridConjunctionPayloadEnvelope valuation
    nextFormula stepFormula nextResource stepResource
  transparentHybridConjunctionPayloadEnvelope valuation currentFormula
    (nextFormula ⋏ stepFormula) currentResource nextStepResource

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope_le_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph <=
      compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row := by
  rcases hgraph with ⟨_hcurrent, _hnext, hstep⟩
  unfold
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope
    compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
  dsimp only
  apply transparentHybridConjunctionPayloadEnvelope_mono
  · exact Nat.le_refl _
  · apply transparentHybridConjunctionPayloadEnvelope_mono
    · exact Nat.le_refl _
    · exact compactFormulaTransformStepRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        mode row.stepWitness row.consumedCount row.mappedHead witnessStart
        witnessFinish witnessCount hstep

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreExplicitDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount indexTerm mode witnessStart
        witnessFinish witnessCount row)
      (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph) := by
  by_cases hindexVariables : indexTerm.freeVariables ⊆ {0}
  · let direct :=
      compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreExplicitDirectOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hindexVariables hgraph
    refine ⟨direct.proof, ?_⟩
    simpa only [
      compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope,
      dif_pos hindexVariables, direct] using direct.payloadLength_le
  · let certificate :=
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph
    refine ⟨certificate.compile, ?_⟩
    simpa only [
      compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope,
      dif_neg hindexVariables, certificate] using
        (compile_payloadLength_le_structuralPayloadBound certificate)

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope_eq_branch
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph =
      compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph := by
  simp only [
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope,
    dif_pos hindexVariables]

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope_le_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph <=
      compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row := by
  rw [
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope_eq_branch
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount row hgraph hindexVariables]
  exact
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreDirectPayloadEnvelope_le_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount row hgraph

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope_le_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph <=
      compactFormulaTransformAdjacentStepRowAtValuationIndexPublicFiniteDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  unfold
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope
    compactFormulaTransformAdjacentStepRowAtValuationIndexPublicFiniteDirectPayloadEnvelope
  dsimp only
  apply transparentHybridConjunctionPayloadEnvelope_mono
  · exact Nat.le_refl _
  · apply transparentHybridConjunctionPayloadEnvelope_mono
    · exact Nat.le_refl _
    · exact compactFormulaTransformStepRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        mode row.stepWitness row.consumedCount row.mappedHead witnessStart
        witnessFinish witnessCount hstep

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) : Nat :=
  if hindexVariables : indexTerm.freeVariables ⊆ {0} then
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount row hgraph
  else
    hybridFormulaStructuralPayloadBound
      (compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph)

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchExplicitDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount indexTerm mode witnessStart
        witnessFinish witnessCount row)
      (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph) := by
  by_cases hindexVariables : indexTerm.freeVariables ⊆ {0}
  · let direct :=
      compactFormulaTransformAdjacentStepRowAtValuationIndexBranchExplicitDirectOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hindexVariables hgraph
    refine ⟨direct.proof, ?_⟩
    simpa only [
      compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope,
      dif_pos hindexVariables, direct] using direct.payloadLength_le
  · let certificate :=
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph
    refine ⟨certificate.compile, ?_⟩
    simpa only [
      compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope,
      dif_neg hindexVariables, certificate] using
        (compile_payloadLength_le_structuralPayloadBound certificate)

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope_eq_branch
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph =
      compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph := by
  simp only [
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope,
    dif_pos hindexVariables]

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope_le_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph <=
      compactFormulaTransformAdjacentStepRowAtValuationIndexPublicFiniteDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row := by
  rw [
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope_eq_branch
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount row hgraph hindexVariables]
  exact
    compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope_le_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount row hgraph

#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexBranchExplicitDirectOfGraph
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexBranchFixedCoreExplicitDirectOfGraph
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreExplicitDirectOfGraph
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope_le_publicFinite
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexBranchDirectPayloadEnvelope_le_publicFinite
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchExplicitDirectOfGraph
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope_eq_branch
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedBranchDirectPayloadEnvelope_le_publicFinite

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexBranchDirectBounds
