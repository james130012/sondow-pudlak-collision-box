import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAClosedHybridContextTransport
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-!
# Public direct resource for one formula-transform adjacent row

The current state, next state, and six-way transform step are compiled under
the same valuation. The index term is required to use only the row variable;
all three child resources and both conjunction costs remain visible.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds

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
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
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

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func]
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

theorem compactFormulaTransformStepRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount).freeVariables = ∅ := by
  unfold compactFormulaTransformStepRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) : Nat := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextAtTerm : CompactFormulaTransformStateAtRows tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hnext
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
      row.currentCoordinates row.currentSize hcurrent
  let nextResource :=
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize hnextAtTerm
  let stepResource := compactFormulaTransformStepRowsGraphPayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount hstep
  let nextStepResource := transparentHybridConjunctionPayloadEnvelope valuation
    nextFormula stepFormula nextResource stepResource
  exact transparentHybridConjunctionPayloadEnvelope valuation currentFormula
    (nextFormula ⋏ stepFormula) currentResource nextStepResource

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitDirectOfGraph
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
      (compactFormulaTransformAdjacentStepRowAtValuationIndexDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simpa using hindexVariables
  have hnextAtTerm : CompactFormulaTransformStateAtRows tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hnext
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
  have hstepResource : stepProof.payloadLength <=
      compactFormulaTransformStepRowsGraphPayloadEnvelope tokenTable width
        tokenCount row.currentCoordinates row.nextCoordinates mode
        row.stepWitness row.consumedCount row.mappedHead witnessStart
        witnessFinish witnessCount hstep :=
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
      nextIndexTerm row.nextCoordinates row.nextSize hnextAtTerm)
    (compactFormulaTransformStepRowsGraphPayloadEnvelope tokenTable width
      tokenCount row.currentCoordinates row.nextCoordinates mode
      row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
      witnessCount hstep)
    nextBound.payloadLength_le hstepResource
  let explicitProof := compileDirectConjunction currentBound.proof nextStepProof
  have hexplicit := compileDirectConjunction_payloadLength_le
    currentBound.proof nextStepProof
    (compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize hcurrent)
    (transparentHybridConjunctionPayloadEnvelope valuation nextFormula
      stepFormula
      (compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        nextIndexTerm row.nextCoordinates row.nextSize hnextAtTerm)
      (compactFormulaTransformStepRowsGraphPayloadEnvelope tokenTable width
        tokenCount row.currentCoordinates row.nextCoordinates mode
        row.stepWitness row.consumedCount row.mappedHead witnessStart
        witnessFinish witnessCount hstep))
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
    compactFormulaTransformAdjacentStepRowAtValuationIndexDirectPayloadEnvelope
  dsimp only [nextIndexTerm, currentFormula, nextFormula, stepFormula,
    currentBound, nextBound, stepCertificate, stepProof, nextStepProof,
    explicitProof]
  exact hexplicit

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row) : Nat :=
  if _hindexVariables : indexTerm.freeVariables ⊆ {0} then
    compactFormulaTransformAdjacentStepRowAtValuationIndexDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount row hgraph
  else
    hybridFormulaStructuralPayloadBound
      (compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph)

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedExplicitDirectOfGraph
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
      (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph) := by
  by_cases hindexVariables : indexTerm.freeVariables ⊆ {0}
  · let direct :=
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitDirectOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hindexVariables hgraph
    refine ⟨direct.proof, ?_⟩
    simpa only [
      compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope,
      dif_pos hindexVariables, direct] using direct.payloadLength_le
  · let certificate :=
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph
    refine ⟨certificate.compile, ?_⟩
    simpa only [
      compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope,
      dif_neg hindexVariables, certificate] using
        (compile_payloadLength_le_structuralPayloadBound certificate)

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope_eq_public
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph =
      compactFormulaTransformAdjacentStepRowAtValuationIndexDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
        mode witnessStart witnessFinish witnessCount row hgraph := by
  simp only [
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope,
    dif_pos hindexVariables]

#print axioms
  compactFormulaTransformStepRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitDirectOfGraph
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedExplicitDirectOfGraph
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope_eq_public

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds
