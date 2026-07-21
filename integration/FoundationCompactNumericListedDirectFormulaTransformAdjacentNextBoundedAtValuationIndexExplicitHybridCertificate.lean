import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-!
# Bounded next transform state at an arbitrary valuation index

The fourteen next-state witnesses are installed while the row index remains
an arbitrary valuation term.  The terminal is the already checked nine-step
witness formula at that identical term and valuation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
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

def adjacentNextSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 25 -> ValuationTerm :=
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
    shortBinaryNumeralTerm valueBound,
    shortBinaryNumeralTerm currentCoordinates.start,
    shortBinaryNumeralTerm currentCoordinates.finish,
    shortBinaryNumeralTerm currentCoordinates.parserFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTokensFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTasksFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTokensBoundary,
    shortBinaryNumeralTerm currentCoordinates.parserTokensCount,
    shortBinaryNumeralTerm currentCoordinates.parserTasksBoundary,
    shortBinaryNumeralTerm currentCoordinates.parserTasksCount,
    shortBinaryNumeralTerm currentCoordinates.outputBoundary,
    shortBinaryNumeralTerm currentCoordinates.outputCount,
    shortBinaryNumeralTerm currentSize.parserTokensBoundarySize,
    shortBinaryNumeralTerm currentSize.parserTasksBoundarySize,
    shortBinaryNumeralTerm currentSize.outputBoundarySize]

def compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentNextBoundedDef.val) ⇜
    adjacentNextSourceTerms tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize

def compactFormulaTransformAdjacentNextBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    ArithmeticSemiformula Nat 14 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepWitnessBoundedDef.val) ⇜
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
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.start),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.finish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserFinish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTokensFinish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTasksFinish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTokensBoundary),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTokensCount),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTasksBoundary),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTasksCount),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.outputBoundary),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.outputCount),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentSize.parserTokensBoundarySize),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentSize.parserTasksBoundarySize),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentSize.outputBoundarySize),
      (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentNextBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 39 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepWitnessBoundedDef.val) ⇜
    ![(#14 : ArithmeticSemiterm Nat 39), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33, #34, #35, #36, #37, #38,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 39 :=
  compactFormulaTransformAdjacentStepWitnessBoundedDef.val ⇜
    ![(#14 : ArithmeticSemiterm Empty 39), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33, #34, #35, #36, #37, #38,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentNextBoundedSourceRawBody :
    ArithmeticSemiformula Nat 25 :=
  sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Nat 25) 14
    compactFormulaTransformAdjacentNextBoundedSourceRawTerminal

private def compactFormulaTransformAdjacentNextBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 25 :=
  sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Empty 25) 14
    compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal

private theorem compactFormulaTransformAdjacentNextBoundedDef_eq_emptyRawBody :
    compactFormulaTransformAdjacentNextBoundedDef.val =
      compactFormulaTransformAdjacentNextBoundedEmptyRawBody := by
  unfold compactFormulaTransformAdjacentNextBoundedDef
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawBody
  unfold sourceBoundedWitnessFormula
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal
  rfl

private theorem compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 39 Nat 39) ▹
        compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal =
      compactFormulaTransformAdjacentNextBoundedSourceRawTerminal := by
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp [Function.comp_apply]

private theorem compactFormulaTransformAdjacentNextBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat) compactFormulaTransformAdjacentNextBoundedDef.val =
      compactFormulaTransformAdjacentNextBoundedSourceRawBody := by
  rw [compactFormulaTransformAdjacentNextBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 25 Nat 25) ▹
      compactFormulaTransformAdjacentNextBoundedEmptyRawBody = _
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawBody
  rw [rewriting_sourceBoundedWitnessFormula]
  simp only [rewritingQpow_emb_eq_emb]
  rw [compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal_embedding]
  rfl

private theorem compactFormulaTransformAdjacentNextBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    sourceSubstitutionQpow
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize) 14 ▹
      compactFormulaTransformAdjacentNextBoundedSourceRawTerminal =
    compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize := by
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawTerminal
  unfold compactFormulaTransformAdjacentNextBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentNextSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar] <;>
      simp [sourceSubstitutionNormalizedBVarResult, adjacentNextSourceTerms]

def compactFormulaTransformAdjacentNextBoundedRawTerminalSourceCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) : Nat :=
  sourceSubstitutionFormulaCodeEnvelope 14
    (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound currentCoordinates currentSize)
    compactFormulaTransformAdjacentNextBoundedSourceRawTerminal

def compactFormulaTransformAdjacentNextBoundedRawTerminalSourceCodeEnvelopeOfTermBound
    (termBound : Nat) : Nat :=
  sourceSubstitutionFormulaCodeEnvelopeOfTermBound 14 termBound
    compactFormulaTransformAdjacentNextBoundedSourceRawTerminal

theorem compactFormulaTransformAdjacentNextBoundedRawTerminal_code_length_le_source_of_termBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound termBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hterms : forall index,
      (binaryTermCode
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize index)).length <=
        termBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentNextBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates
        currentSize)).length <=
      compactFormulaTransformAdjacentNextBoundedRawTerminalSourceCodeEnvelopeOfTermBound
        termBound := by
  rw [← compactFormulaTransformAdjacentNextBoundedSourceRawTerminal_rewriting]
  exact binaryFormulaCode_sourceSubstitutionQpow_length_le_of_termBound 14
    termBound
    (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound currentCoordinates currentSize)
    compactFormulaTransformAdjacentNextBoundedSourceRawTerminal hterms

def compactFormulaTransformAdjacentNextBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
    (termBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 14 termBound
    (binaryFormulaCode
      compactFormulaTransformAdjacentNextBoundedSourceRawTerminal).length

theorem compactFormulaTransformAdjacentNextBoundedRawTerminal_code_length_le_polynomial_source_of_termBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound termBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hterms : forall index,
      (binaryTermCode
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize index)).length <=
        termBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentNextBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates
        currentSize)).length <=
      compactFormulaTransformAdjacentNextBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
        termBound := by
  rw [← compactFormulaTransformAdjacentNextBoundedSourceRawTerminal_rewriting]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      14 termBound
      (binaryFormulaCode
        compactFormulaTransformAdjacentNextBoundedSourceRawTerminal).length
      (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
        valueBound currentCoordinates currentSize)
      compactFormulaTransformAdjacentNextBoundedSourceRawTerminal hterms
      le_rfl

theorem compactFormulaTransformAdjacentNextBoundedRawTerminal_code_length_le_source
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentNextBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates
        currentSize)).length <=
      compactFormulaTransformAdjacentNextBoundedRawTerminalSourceCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize := by
  rw [← compactFormulaTransformAdjacentNextBoundedSourceRawTerminal_rewriting]
  exact binaryFormulaCode_sourceSubstitutionQpow_length_le 14
    (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound currentCoordinates currentSize)
    compactFormulaTransformAdjacentNextBoundedSourceRawTerminal

@[simp] private theorem compactFormulaTransformAdjacentNextBoundedSourceQpow_valueBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (depth : Nat) :
    sourceSubstitutionQpow
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize) depth
        (#(⟨depth + 10, by omega⟩ : Fin (25 + depth)) :
          ArithmeticSemiterm Nat (25 + depth)) =
      sourceSubstitutionLift depth (shortBinaryNumeralTerm valueBound) := by
  simpa [adjacentNextSourceTerms] using
    (sourceSubstitutionQpow_shiftedBVar
      (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
        valueBound currentCoordinates currentSize)
      depth (⟨10, by omega⟩ : Fin 25))

theorem compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 14
        (compactFormulaTransformAdjacentNextBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize) := by
  unfold compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
  rw [compactFormulaTransformAdjacentNextBoundedDef_emb_eq_sourceRawBody]
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawBody
  change Rew.subst
      (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
        valueBound currentCoordinates currentSize) ▹
      sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Nat 25) 14
        compactFormulaTransformAdjacentNextBoundedSourceRawTerminal = _
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactFormulaTransformAdjacentNextBoundedSourceRawTerminal_rewriting]
  change sourceBoundedWitnessFormula
      (shortBinaryNumeralTerm valueBound) 14
        (compactFormulaTransformAdjacentNextBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize) = _
  rfl

structure CompactFormulaTransformAdjacentNextStateWitness where
  coordinates : CompactFormulaTransformStateRowCoordinates
  size : CompactFormulaTransformStateCoreSizeWitness

def adjacentNextBoundedWitnessValues
    (witness : CompactFormulaTransformAdjacentNextStateWitness) :
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

theorem compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (witness : CompactFormulaTransformAdjacentNextStateWitness) :
    compactFormulaTransformAdjacentNextBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize ⇜
      (fun index => shortBinaryNumeralTerm
        (adjacentNextBoundedWitnessValues witness index)) =
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size := by
  change Rew.subst
      (fun index => shortBinaryNumeralTerm
        (adjacentNextBoundedWitnessValues witness index)) ▹
    compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize = _
  unfold compactFormulaTransformAdjacentNextBoundedRawTerminal
  unfold compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentNextBoundedWitnessValues,
      boundedSourceTerms, Rew.subst_bvar, substitute_sourceSubstitutionLift14]

private theorem compactFormulaTransformAdjacentNextBounded_witness_exists
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    ∃ witness : CompactFormulaTransformAdjacentNextStateWitness,
      (∀ index, adjacentNextBoundedWitnessValues witness index ≤ valueBound) ∧
      CompactFormulaTransformAdjacentStepWitnessBounded
        tokenTable width tokenCount stateBoundary stateCount
        (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
        witnessCount valueBound currentCoordinates currentSize
        witness.coordinates witness.size := by
  rcases hnext with
    ⟨nextStart, hnextStart, nextFinish, hnextFinish,
      nextParserFinish, hnextParserFinish,
      nextParserTokensFinish, hnextParserTokensFinish,
      nextParserTasksFinish, hnextParserTasksFinish,
      nextParserTokensBoundary, hnextParserTokensBoundary,
      nextParserTokensCount, hnextParserTokensCount,
      nextParserTasksBoundary, hnextParserTasksBoundary,
      nextParserTasksCount, hnextParserTasksCount,
      nextOutputBoundary, hnextOutputBoundary,
      nextOutputCount, hnextOutputCount,
      nextParserTokensBoundarySize, hnextParserTokensBoundarySize,
      nextParserTasksBoundarySize, hnextParserTasksBoundarySize,
      nextOutputBoundarySize, hnextOutputBoundarySize, hinner⟩
  let witness : CompactFormulaTransformAdjacentNextStateWitness :=
    { coordinates := compactFormulaTransformStateRowCoordinatesOf
        nextStart nextFinish nextParserFinish nextParserTokensFinish
        nextParserTasksFinish nextParserTokensBoundary nextParserTokensCount
        nextParserTasksBoundary nextParserTasksCount nextOutputBoundary
        nextOutputCount
      size :=
        { parserTokensBoundarySize := nextParserTokensBoundarySize
          parserTasksBoundarySize := nextParserTasksBoundarySize
          outputBoundarySize := nextOutputBoundarySize } }
  refine ⟨witness, ?_, ?_⟩
  · intro index
    fin_cases index
    · exact hnextOutputBoundarySize
    · exact hnextParserTasksBoundarySize
    · exact hnextParserTokensBoundarySize
    · exact hnextOutputCount
    · exact hnextOutputBoundary
    · exact hnextParserTasksCount
    · exact hnextParserTasksBoundary
    · exact hnextParserTokensCount
    · exact hnextParserTokensBoundary
    · exact hnextParserTasksFinish
    · exact hnextParserTokensFinish
    · exact hnextParserFinish
    · exact hnextFinish
    · exact hnextStart
  · simpa [witness] using hinner

noncomputable def compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    CompactFormulaTransformAdjacentNextStateWitness :=
  Classical.choose
    (compactFormulaTransformAdjacentNextBounded_witness_exists
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext)

theorem compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    (∀ index,
      adjacentNextBoundedWitnessValues
        (compactFormulaTransformAdjacentNextBounded_witnessOfGraph
          valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
          mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize hnext) index ≤ valueBound) ∧
    CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).coordinates
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).size :=
  Classical.choose_spec
    (compactFormulaTransformAdjacentNextBounded_witness_exists
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext)

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridTerminalOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    ExplicitBoundedWitnessHybridTerminal valuation valueBound
      (compactFormulaTransformAdjacentNextBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize) := by
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  have hwitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let values := adjacentNextBoundedWitnessValues witness
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values] using hwitness.1
  let innerCertificate :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificateOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  let terminal : HybridCertificate valuation
      (compactFormulaTransformAdjacentNextBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize witness).symm) innerCertificate
  exact
    { values := values
      values_le := hvalues
      terminal := terminal }

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificateOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    HybridCertificate valuation
      (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize) := by
  let data :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext
  rw [compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) data.values data.values_le data.terminal

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) : Nat :=
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let values := adjacentNextBoundedWitnessValues witness
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).2
  explicitBoundedWitnessDirectPayloadEnvelope valuation valueBound
    (compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) values innerResource

noncomputable def
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize).freeVariables valuation)
      (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize) := by
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  have hwitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let values := adjacentNextBoundedWitnessValues witness
  let rawBody := compactFormulaTransformAdjacentNextBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize
  let innerDirect :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength ≤ innerResource := by
    exact
      compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph_payloadLength_le
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize witness.coordinates witness.size hwitness.2
  let rawTerminal := castValuationContextProof
    (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness).symm innerDirect
  have hrawTerminal : rawTerminal.payloadLength ≤ innerResource := by
    change (castValuationContextProof
      (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize witness).symm innerDirect).payloadLength ≤ _
    rw [castValuationContextProof_payloadLength_eq]
    exact hinner
  let rawProof := compileExplicitBoundedWitnessDirectArity14
    valueBound rawBody values hwitness.1 innerResource rawTerminal hrawTerminal
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize :=
    (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize).symm
  exact castValuationContextProof hformula rawProof

theorem
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    (compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext).payloadLength ≤
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext := by
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  have hwitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let values := adjacentNextBoundedWitnessValues witness
  let rawBody := compactFormulaTransformAdjacentNextBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize
  let innerDirect :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength ≤ innerResource := by
    exact
      compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph_payloadLength_le
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize witness.coordinates witness.size hwitness.2
  let rawTerminal := castValuationContextProof
    (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness).symm innerDirect
  have hrawTerminal : rawTerminal.payloadLength ≤ innerResource := by
    change (castValuationContextProof
      (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize witness).symm innerDirect).payloadLength ≤ _
    rw [castValuationContextProof_payloadLength_eq]
    exact hinner
  let rawProof := compileExplicitBoundedWitnessDirectArity14
    valueBound rawBody values hwitness.1 innerResource rawTerminal hrawTerminal
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize :=
    (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize).symm
  change (castValuationContextProof hformula rawProof).payloadLength ≤ _
  rw [castValuationContextProof_payloadLength_eq]
  change rawProof.payloadLength ≤
    explicitBoundedWitnessDirectPayloadEnvelope valuation valueBound rawBody
      values innerResource
  exact compileExplicitBoundedWitnessDirectArity14_payloadLength_le
    valueBound rawBody values hwitness.1 innerResource rawTerminal hrawTerminal

#print axioms
  compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula_alignment
#print axioms
  compactFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
