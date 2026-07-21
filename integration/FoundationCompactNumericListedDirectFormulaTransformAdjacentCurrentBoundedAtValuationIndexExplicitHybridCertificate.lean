import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-!
# Bounded current transform state at an arbitrary valuation index

The outer fourteen current-state witnesses are installed around the checked
next-state endpoint without closing the row-index valuation term.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

def adjacentCurrentSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    Fin 11 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    rowIndexTerm,
    shortBinaryNumeralTerm mode,
    shortBinaryNumeralTerm witnessStart,
    shortBinaryNumeralTerm witnessFinish,
    shortBinaryNumeralTerm witnessCount,
    shortBinaryNumeralTerm valueBound]

def compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentCurrentBoundedDef.val) ⇜
    adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound

def compactFormulaTransformAdjacentCurrentBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    ArithmeticSemiformula Nat 14 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentNextBoundedDef.val) ⇜
    ![sourceSubstitutionLift 14 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 14 rowIndexTerm,
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm mode),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm witnessStart),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm witnessFinish),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm witnessCount),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm valueBound),
      (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 25 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentNextBoundedDef.val) ⇜
    ![(#14 : ArithmeticSemiterm Nat 25), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 25 :=
  compactFormulaTransformAdjacentNextBoundedDef.val ⇜
    ![(#14 : ArithmeticSemiterm Empty 25), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentCurrentBoundedSourceRawBody :
    ArithmeticSemiformula Nat 11 :=
  sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Nat 11) 14
    compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal

private def compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 11 :=
  sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Empty 11) 14
    compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal

private theorem compactFormulaTransformAdjacentCurrentBoundedDef_eq_emptyRawBody :
    compactFormulaTransformAdjacentCurrentBoundedDef.val =
      compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody := by
  unfold compactFormulaTransformAdjacentCurrentBoundedDef
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody
  unfold sourceBoundedWitnessFormula
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal
  rfl

private theorem compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 25 Nat 25) ▹
        compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal =
      compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal := by
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp [Function.comp_apply]

private theorem compactFormulaTransformAdjacentCurrentBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat) compactFormulaTransformAdjacentCurrentBoundedDef.val =
      compactFormulaTransformAdjacentCurrentBoundedSourceRawBody := by
  rw [compactFormulaTransformAdjacentCurrentBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 11 Nat 11) ▹
      compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody = _
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawBody
  rw [rewriting_sourceBoundedWitnessFormula]
  simp only [rewritingQpow_emb_eq_emb]
  rw [compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal_embedding]
  rfl

private theorem compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    sourceSubstitutionQpow
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound) 14 ▹
      compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal =
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound := by
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal
  unfold compactFormulaTransformAdjacentCurrentBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentCurrentSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar] <;>
      simp [sourceSubstitutionNormalizedBVarResult,
        adjacentCurrentSourceTerms]

def compactFormulaTransformAdjacentCurrentBoundedRawTerminalSourceCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  sourceSubstitutionFormulaCodeEnvelope 14
    (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound)
    compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal

def compactFormulaTransformAdjacentCurrentBoundedRawTerminalSourceCodeEnvelopeOfTermBound
    (termBound : Nat) : Nat :=
  sourceSubstitutionFormulaCodeEnvelopeOfTermBound 14 termBound
    compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal

theorem compactFormulaTransformAdjacentCurrentBoundedRawTerminal_code_length_le_source_of_termBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound termBound : Nat)
    (hterms : forall index,
      (binaryTermCode
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound index)).length <= termBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound)).length <=
      compactFormulaTransformAdjacentCurrentBoundedRawTerminalSourceCodeEnvelopeOfTermBound
        termBound := by
  rw [← compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal_rewriting]
  exact binaryFormulaCode_sourceSubstitutionQpow_length_le_of_termBound 14
    termBound
    (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound)
    compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal hterms

def compactFormulaTransformAdjacentCurrentBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
    (termBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 14 termBound
    (binaryFormulaCode
      compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal).length

theorem compactFormulaTransformAdjacentCurrentBoundedRawTerminal_code_length_le_polynomial_source_of_termBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound termBound : Nat)
    (hterms : forall index,
      (binaryTermCode
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound index)).length <= termBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound)).length <=
      compactFormulaTransformAdjacentCurrentBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
        termBound := by
  rw [← compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal_rewriting]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      14 termBound
      (binaryFormulaCode
        compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal).length
      (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
        valueBound)
      compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal hterms
      le_rfl

theorem compactFormulaTransformAdjacentCurrentBoundedRawTerminal_code_length_le_source
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound)).length <=
      compactFormulaTransformAdjacentCurrentBoundedRawTerminalSourceCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound := by
  rw [← compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal_rewriting]
  exact binaryFormulaCode_sourceSubstitutionQpow_length_le 14
    (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound)
    compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal

@[simp] private theorem compactFormulaTransformAdjacentCurrentBoundedSourceQpow_valueBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound depth : Nat) :
    sourceSubstitutionQpow
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound) depth
        (#(⟨depth + 10, by omega⟩ : Fin (11 + depth)) :
          ArithmeticSemiterm Nat (11 + depth)) =
      sourceSubstitutionLift depth (shortBinaryNumeralTerm valueBound) := by
  simpa [adjacentCurrentSourceTerms] using
    (sourceSubstitutionQpow_shiftedBVar
      (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
        valueBound)
      depth (⟨10, by omega⟩ : Fin 11))

theorem compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 14
        (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound) := by
  unfold compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
  rw [compactFormulaTransformAdjacentCurrentBoundedDef_emb_eq_sourceRawBody]
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawBody
  change Rew.subst
      (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
        valueBound) ▹
      sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Nat 11) 14
        compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal = _
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal_rewriting]
  change sourceBoundedWitnessFormula
      (shortBinaryNumeralTerm valueBound) 14
        (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound) = _
  rfl

structure CompactFormulaTransformAdjacentCurrentStateWitness where
  coordinates : CompactFormulaTransformStateRowCoordinates
  size : CompactFormulaTransformStateCoreSizeWitness

def adjacentCurrentBoundedWitnessValues
    (witness : CompactFormulaTransformAdjacentCurrentStateWitness) :
    Fin 14 -> Nat :=
  ![witness.size.outputBoundarySize,
    witness.size.parserTasksBoundarySize,
    witness.size.parserTokensBoundarySize,
    witness.coordinates.outputCount,
    witness.coordinates.outputBoundary,
    witness.coordinates.parserTasksCount,
    witness.coordinates.parserTasksBoundary,
    witness.coordinates.parserTokensCount,
    witness.coordinates.parserTokensBoundary,
    witness.coordinates.parserTasksFinish,
    witness.coordinates.parserTokensFinish,
    witness.coordinates.parserFinish,
    witness.coordinates.finish,
    witness.coordinates.start]

private theorem substitute_sourceSubstitutionLift
    {depth : Nat} (values : Fin (0 + depth) -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift depth term) = term := by
  induction depth with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ depth inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin (0 + depth) => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (sourceSubstitutionLift (depth + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (sourceSubstitutionLift depth term) := by
                simp [sourceSubstitutionLift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin (0 + depth) => values index.succ)
              (sourceSubstitutionLift depth term) := by rw [hrew]
        _ = term := inductionHypothesis _

private theorem substitute_sourceSubstitutionLift14
    (values : Fin 14 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 14 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 14) values term)

theorem compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (witness : CompactFormulaTransformAdjacentCurrentStateWitness) :
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound ⇜
      (fun index => shortBinaryNumeralTerm
        (adjacentCurrentBoundedWitnessValues witness index)) =
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size := by
  change Rew.subst
      (fun index => shortBinaryNumeralTerm
        (adjacentCurrentBoundedWitnessValues witness index)) ▹
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound = _
  unfold compactFormulaTransformAdjacentCurrentBoundedRawTerminal
  unfold compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentCurrentBoundedWitnessValues,
      adjacentNextSourceTerms, Rew.subst_bvar,
      substitute_sourceSubstitutionLift14]

structure CompactFormulaTransformAdjacentCurrentBoundedWitnessData
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) where
  witness : CompactFormulaTransformAdjacentCurrentStateWitness
  values_le : ∀ index,
    adjacentCurrentBoundedWitnessValues witness index ≤ valueBound
  next : CompactFormulaTransformAdjacentNextBounded
    tokenTable width tokenCount stateBoundary stateCount
    (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
    witnessCount valueBound witness.coordinates witness.size

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    CompactFormulaTransformAdjacentCurrentBoundedWitnessData
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound := by
  have hexists :
      ∃ witness : CompactFormulaTransformAdjacentCurrentStateWitness,
        (∀ index,
          adjacentCurrentBoundedWitnessValues witness index ≤ valueBound) ∧
        CompactFormulaTransformAdjacentNextBounded
          tokenTable width tokenCount stateBoundary stateCount
          (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
          witnessCount valueBound witness.coordinates witness.size := by
    rcases hcurrent with
      ⟨currentStart, hcurrentStart, currentFinish, hcurrentFinish,
        currentParserFinish, hcurrentParserFinish,
        currentParserTokensFinish, hcurrentParserTokensFinish,
        currentParserTasksFinish, hcurrentParserTasksFinish,
        currentParserTokensBoundary, hcurrentParserTokensBoundary,
        currentParserTokensCount, hcurrentParserTokensCount,
        currentParserTasksBoundary, hcurrentParserTasksBoundary,
        currentParserTasksCount, hcurrentParserTasksCount,
        currentOutputBoundary, hcurrentOutputBoundary,
        currentOutputCount, hcurrentOutputCount,
        currentParserTokensBoundarySize, hcurrentParserTokensBoundarySize,
        currentParserTasksBoundarySize, hcurrentParserTasksBoundarySize,
        currentOutputBoundarySize, hcurrentOutputBoundarySize, hinner⟩
    let witness : CompactFormulaTransformAdjacentCurrentStateWitness :=
      { coordinates := compactFormulaTransformStateRowCoordinatesOf
          currentStart currentFinish currentParserFinish
          currentParserTokensFinish currentParserTasksFinish
          currentParserTokensBoundary currentParserTokensCount
          currentParserTasksBoundary currentParserTasksCount
          currentOutputBoundary currentOutputCount
        size :=
          { parserTokensBoundarySize := currentParserTokensBoundarySize
            parserTasksBoundarySize := currentParserTasksBoundarySize
            outputBoundarySize := currentOutputBoundarySize } }
    refine ⟨witness, ?_, ?_⟩
    · intro index
      fin_cases index
      · exact hcurrentOutputBoundarySize
      · exact hcurrentParserTasksBoundarySize
      · exact hcurrentParserTokensBoundarySize
      · exact hcurrentOutputCount
      · exact hcurrentOutputBoundary
      · exact hcurrentParserTasksCount
      · exact hcurrentParserTasksBoundary
      · exact hcurrentParserTokensCount
      · exact hcurrentParserTokensBoundary
      · exact hcurrentParserTasksFinish
      · exact hcurrentParserTokensFinish
      · exact hcurrentParserFinish
      · exact hcurrentFinish
      · exact hcurrentStart
    · simpa [witness] using hinner
  let witness := Classical.choose hexists
  have hwitness := Classical.choose_spec hexists
  exact
    { witness := witness
      values_le := hwitness.1
      next := hwitness.2 }

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridTerminalOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    ExplicitBoundedWitnessHybridTerminal valuation valueBound
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound) := by
  let data :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let values := adjacentCurrentBoundedWitnessValues witness
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values, witness] using data.values_le
  let innerCertificate :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificateOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  let terminal : HybridCertificate valuation
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound witness).symm)
      innerCertificate
  exact
    { values := values
      values_le := hvalues
      terminal := terminal }

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificateOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    HybridCertificate valuation
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound) := by
  let data :=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent
  rw [compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    data.values data.values_le data.terminal

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) : Nat :=
  let data :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let values := adjacentCurrentBoundedWitnessValues witness
  let rawBody :=
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  explicitBoundedWitnessDirectPayloadEnvelope valuation valueBound rawBody values
    innerResource

noncomputable def
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound).freeVariables valuation)
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound) := by
  let data :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let values := adjacentCurrentBoundedWitnessValues witness
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values, witness] using data.values_le
  let rawBody :=
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  let innerProof :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  let terminal := castValuationContextProof
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound witness).symm
    innerProof
  have hterminal : terminal.payloadLength ≤ innerResource := by
    dsimp only [terminal]
    rw [castValuationContextProof_payloadLength_eq]
    exact
      compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph_payloadLength_le
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
        witness.size data.next
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  let rawProof := compileExplicitBoundedWitnessDirectArity14
    valueBound rawBody values hvalues innerResource terminal hterminal
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound :=
    (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound).symm
  exact castValuationContextProof hformula rawProof

theorem
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength ≤
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent := by
  let data :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let values := adjacentCurrentBoundedWitnessValues witness
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values, witness] using data.values_le
  let rawBody :=
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  let innerProof :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  let terminal := castValuationContextProof
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound witness).symm
    innerProof
  have hterminal : terminal.payloadLength ≤ innerResource := by
    dsimp only [terminal]
    rw [castValuationContextProof_payloadLength_eq]
    exact
      compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph_payloadLength_le
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
        witness.size data.next
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  let rawProof := compileExplicitBoundedWitnessDirectArity14
    valueBound rawBody values hvalues innerResource terminal hterminal
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound :=
    (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound).symm
  change (castValuationContextProof hformula rawProof).payloadLength ≤ _
  rw [castValuationContextProof_payloadLength_eq]
  change rawProof.payloadLength ≤
    explicitBoundedWitnessDirectPayloadEnvelope valuation valueBound rawBody
      values innerResource
  exact compileExplicitBoundedWitnessDirectArity14_payloadLength_le
    valueBound rawBody values hvalues innerResource terminal hterminal

#print axioms
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment
#print axioms
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexDirectOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
