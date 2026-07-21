import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactPAClosedHybridContextTransport

/-!
# Bounded adjacent-step witnesses at an arbitrary valuation index

The row index remains an arbitrary valuation term while the nine local step
witnesses are installed explicitly.  This is the first bounded layer needed
inside the eventual row-index universal branch.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAClosedHybridContextTransport
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

structure ExplicitAdjacentStepDirectTerminal
    (valuation : Nat -> Nat)
    (valueBound : Nat)
    (body : ArithmeticSemiformula Nat 9) where
  values : Fin 9 -> Nat
  values_le : ∀ index, values index ≤ valueBound
  terminalResource : Nat
  terminal : CertifiedPAContextProof
    (valuationContext
      (body ⇜ fun index =>
        shortBinaryNumeralTerm (values index)).freeVariables valuation)
    (body ⇜ fun index => shortBinaryNumeralTerm (values index))
  terminal_payloadLength_le : terminal.payloadLength ≤ terminalResource

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

def boundedSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 39 -> ValuationTerm :=
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
    shortBinaryNumeralTerm currentSize.outputBoundarySize,
    shortBinaryNumeralTerm nextCoordinates.start,
    shortBinaryNumeralTerm nextCoordinates.finish,
    shortBinaryNumeralTerm nextCoordinates.parserFinish,
    shortBinaryNumeralTerm nextCoordinates.parserTokensFinish,
    shortBinaryNumeralTerm nextCoordinates.parserTasksFinish,
    shortBinaryNumeralTerm nextCoordinates.parserTokensBoundary,
    shortBinaryNumeralTerm nextCoordinates.parserTokensCount,
    shortBinaryNumeralTerm nextCoordinates.parserTasksBoundary,
    shortBinaryNumeralTerm nextCoordinates.parserTasksCount,
    shortBinaryNumeralTerm nextCoordinates.outputBoundary,
    shortBinaryNumeralTerm nextCoordinates.outputCount,
    shortBinaryNumeralTerm nextSize.parserTokensBoundarySize,
    shortBinaryNumeralTerm nextSize.parserTasksBoundarySize,
    shortBinaryNumeralTerm nextSize.outputBoundarySize]

def compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepWitnessBoundedDef.val) ⇜
    boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize

def compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    ArithmeticSemiformula Nat 9 :=
  ((Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepRowDef.val) ⇜
    ![sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 9 rowIndexTerm,
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm mode),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm witnessStart),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm witnessFinish),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm witnessCount),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm currentCoordinates.start),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm currentCoordinates.finish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTokensFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTokensBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTokensCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.outputBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.outputCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentSize.parserTokensBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentSize.parserTasksBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentSize.outputBoundarySize),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm nextCoordinates.start),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm nextCoordinates.finish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTokensFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTasksFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTokensBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTokensCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTasksBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTasksCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.outputBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.outputCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextSize.parserTokensBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextSize.parserTasksBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextSize.outputBoundarySize),
      (#8 : ArithmeticSemiterm Nat 9), #7, #6, #5, #4, #3, #2, #1, #0]) ⋏
  (((Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserFinish),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm valueBound)]) ⋏
    ((Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusValidBoundedDef.val) ⇜
      ![sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenTable),
        sourceSubstitutionLift 9 (shortBinaryNumeralTerm width),
        sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenCount),
        sourceSubstitutionLift 9
          (shortBinaryNumeralTerm nextCoordinates.parserTasksFinish),
        sourceSubstitutionLift 9
          (shortBinaryNumeralTerm nextCoordinates.parserFinish),
        sourceSubstitutionLift 9 (shortBinaryNumeralTerm valueBound)]))

private def compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 48 :=
  ((Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepRowDef.val) ⇜
    ![(#9 : ArithmeticSemiterm Nat 48), #10, #11, #12, #13, #14,
      #15, #16, #17, #18,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33,
      #34, #35, #36, #37, #38, #39, #40, #41, #42, #43, #44,
      #45, #46, #47,
      #8, #7, #6, #5, #4, #3, #2, #1, #0]) ⋏
  (((Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![(#9 : ArithmeticSemiterm Nat 48), #10, #11, #24, #22, #19]) ⋏
    ((Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusValidBoundedDef.val) ⇜
      ![(#9 : ArithmeticSemiterm Nat 48), #10, #11, #38, #36, #19]))

private def compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 48 :=
  (compactFormulaTransformAdjacentStepRowDef.val ⇜
    ![(#9 : ArithmeticSemiterm Empty 48), #10, #11, #12, #13, #14,
      #15, #16, #17, #18,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33,
      #34, #35, #36, #37, #38, #39, #40, #41, #42, #43, #44,
      #45, #46, #47,
      #8, #7, #6, #5, #4, #3, #2, #1, #0]) ⋏
  ((compactBinaryNatStatusValidBoundedDef.val ⇜
    ![(#9 : ArithmeticSemiterm Empty 48), #10, #11, #24, #22, #19]) ⋏
    (compactBinaryNatStatusValidBoundedDef.val ⇜
      ![(#9 : ArithmeticSemiterm Empty 48), #10, #11, #38, #36, #19]))

private def compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody :
    ArithmeticSemiformula Nat 39 :=
  sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Nat 39) 9
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal

private def compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 39 :=
  sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Empty 39) 9
    compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal

private theorem compactFormulaTransformAdjacentStepWitnessBoundedDef_eq_emptyRawBody :
    compactFormulaTransformAdjacentStepWitnessBoundedDef.val =
      compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedDef
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody
  unfold sourceBoundedWitnessFormula
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal
  rfl

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 48 Nat 48) ▹
        compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal =
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;> simp [Function.comp_apply]
  · constructor
    · congr 1
      funext coordinate
      fin_cases coordinate <;> simp [Function.comp_apply]
    · congr 1
      funext coordinate
      fin_cases coordinate <;> simp [Function.comp_apply]

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat)
        compactFormulaTransformAdjacentStepWitnessBoundedDef.val =
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody := by
  rw [compactFormulaTransformAdjacentStepWitnessBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 39 Nat 39) ▹
      compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody = _
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody
  rw [rewriting_sourceBoundedWitnessFormula]
  simp only [rewritingQpow_emb_eq_emb]
  rw [compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal_embedding]
  rfl

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    sourceSubstitutionQpow
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize) 9 ▹
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal =
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal
  unfold compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply, boundedSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar] <;>
      simp [sourceSubstitutionNormalizedBVarResult, boundedSourceTerms]

def compactFormulaTransformAdjacentStepWitnessBoundedRawTerminalSourceCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) : Nat :=
  sourceSubstitutionFormulaCodeEnvelope 9
    (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize)
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal

def compactFormulaTransformAdjacentStepWitnessBoundedRawTerminalSourceCodeEnvelopeOfTermBound
    (termBound : Nat) : Nat :=
  sourceSubstitutionFormulaCodeEnvelopeOfTermBound 9 termBound
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal

theorem compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_code_length_le_source_of_termBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound termBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hterms : forall index,
      (binaryTermCode
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize index)).length
        <= termBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal tokenTable
        width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates currentSize
        nextCoordinates nextSize)).length <=
      compactFormulaTransformAdjacentStepWitnessBoundedRawTerminalSourceCodeEnvelopeOfTermBound
        termBound := by
  rw [←
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal_rewriting]
  exact binaryFormulaCode_sourceSubstitutionQpow_length_le_of_termBound 9
    termBound
    (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize)
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal hterms

def compactFormulaTransformAdjacentStepWitnessBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
    (termBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 9 termBound
    (binaryFormulaCode
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal).length

theorem compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_code_length_le_polynomial_source_of_termBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound termBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hterms : forall index,
      (binaryTermCode
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize index)).length
        <= termBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal tokenTable
        width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates currentSize
        nextCoordinates nextSize)).length <=
      compactFormulaTransformAdjacentStepWitnessBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
        termBound := by
  rw [←
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal_rewriting]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      9 termBound
      (binaryFormulaCode
        compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal).length
      (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize)
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal hterms
      le_rfl

theorem compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_code_length_le_source
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal tokenTable
        width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates currentSize
        nextCoordinates nextSize)).length <=
      compactFormulaTransformAdjacentStepWitnessBoundedRawTerminalSourceCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize := by
  rw [←
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal_rewriting]
  exact binaryFormulaCode_sourceSubstitutionQpow_length_le 9
    (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize)
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal

@[simp] private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedSourceQpow_valueBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (depth : Nat) :
    sourceSubstitutionQpow
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize) depth
        (#(⟨depth + 10, by omega⟩ : Fin (39 + depth)) :
          ArithmeticSemiterm Nat (39 + depth)) =
      sourceSubstitutionLift depth (shortBinaryNumeralTerm valueBound) := by
  simpa [boundedSourceTerms] using
    (sourceSubstitutionQpow_shiftedBVar
      (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize)
      depth (⟨10, by omega⟩ : Fin 39))

theorem
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 9
        (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize) := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
  rw [compactFormulaTransformAdjacentStepWitnessBoundedDef_emb_eq_sourceRawBody]
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody
  change Rew.subst
      (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize) ▹
      sourceBoundedWitnessFormula (#10 : ArithmeticSemiterm Nat 39) 9
        compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal = _
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal_rewriting]
  change sourceBoundedWitnessFormula
      (shortBinaryNumeralTerm valueBound) 9
        (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize) = _
  rfl

def boundedWitnessValues
    (row : CompactFormulaTransformAdjacentStepRow) : Fin 9 -> Nat :=
  ![row.mappedHead, row.consumedCount,
    row.stepWitness.slot6, row.stepWitness.slot5, row.stepWitness.slot4,
    row.stepWitness.slot3, row.stepWitness.slot2, row.stepWitness.slot1,
    row.stepWitness.slot0]

structure ExplicitAdjacentStepDirectTerminalComponents
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) where
  row : CompactFormulaTransformAdjacentStepRow
  row_current_coordinates : row.currentCoordinates = currentCoordinates
  row_current_size : row.currentSize = currentSize
  row_next_coordinates : row.nextCoordinates = nextCoordinates
  row_next_size : row.nextSize = nextSize
  row_graph : CompactFormulaTransformAdjacentStepRowGraph
    tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount row
  current_status : CompactBinaryNatStatusValidBounded
    tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  next_status : CompactBinaryNatStatusValidBounded
    tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound
  values_le : ∀ index, boundedWitnessValues row index ≤ valueBound

private structure CompactFormulaTransformAdjacentStepLocalWitness where
  stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates
  consumedCount : Nat
  mappedHead : Nat

private def compactFormulaTransformAdjacentStepRowOfLocalWitness
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (witness : CompactFormulaTransformAdjacentStepLocalWitness) :
    CompactFormulaTransformAdjacentStepRow :=
  { currentCoordinates := currentCoordinates
    currentSize := currentSize
    nextCoordinates := nextCoordinates
    nextSize := nextSize
    stepWitness := witness.stepWitness
    consumedCount := witness.consumedCount
    mappedHead := witness.mappedHead }

private structure ExplicitAdjacentStepGraphData
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) where
  witness : CompactFormulaTransformAdjacentStepLocalWitness
  values_le : ∀ index,
    boundedWitnessValues
      (compactFormulaTransformAdjacentStepRowOfLocalWitness
        currentCoordinates currentSize nextCoordinates nextSize witness)
      index ≤ valueBound
  row_graph : CompactFormulaTransformAdjacentStepRowGraph
    tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount
      (compactFormulaTransformAdjacentStepRowOfLocalWitness
        currentCoordinates currentSize nextCoordinates nextSize witness)
  current_status : CompactBinaryNatStatusValidBounded
    tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  next_status : CompactBinaryNatStatusValidBounded
    tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound

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

private theorem substitute_sourceSubstitutionLift9
    (values : Fin 9 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 9 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 9) values term)

theorem
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) :
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound
        row.currentCoordinates row.currentSize row.nextCoordinates row.nextSize ⇜
      (fun index => shortBinaryNumeralTerm (boundedWitnessValues row index)) =
    compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount row ⋏
      (compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount
          row.currentCoordinates.parserTasksFinish
          row.currentCoordinates.parserFinish valueBound ⋏
        compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount
          row.nextCoordinates.parserTasksFinish
          row.nextCoordinates.parserFinish valueBound) := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (boundedWitnessValues row index)) ▹
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
      row.currentCoordinates row.currentSize row.nextCoordinates row.nextSize = _
  unfold compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
  unfold compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
  unfold compactBinaryNatStatusValidBoundedClosedFormula
  simp [rewriting_embeddedFormulaSubstitution]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply, boundedWitnessValues, Rew.subst_bvar,
        substitute_sourceSubstitutionLift9]

private theorem compactBinaryNatStatusValidBoundedClosedFormula_freeVariables
    (tokenTable width tokenCount start finish valueBound : Nat) :
    (compactBinaryNatStatusValidBoundedClosedFormula
      tokenTable width tokenCount start finish valueBound).freeVariables = ∅ := by
  unfold compactBinaryNatStatusValidBoundedClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private noncomputable def explicitAdjacentStepGraphDataOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    ExplicitAdjacentStepGraphData valuation tokenTable width tokenCount
      stateBoundary stateCount rowIndexTerm mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize := by
  have hexists :
      ∃ witness : CompactFormulaTransformAdjacentStepLocalWitness,
        (∀ index,
          boundedWitnessValues
            (compactFormulaTransformAdjacentStepRowOfLocalWitness
              currentCoordinates currentSize nextCoordinates nextSize witness)
            index ≤ valueBound) ∧
        CompactFormulaTransformAdjacentStepRowGraph
          tokenTable width tokenCount stateBoundary stateCount
            (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
            witnessCount
            (compactFormulaTransformAdjacentStepRowOfLocalWitness
              currentCoordinates currentSize nextCoordinates nextSize witness) ∧
        CompactBinaryNatStatusValidBounded tokenTable width tokenCount
          currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
            valueBound ∧
        CompactBinaryNatStatusValidBounded tokenTable width tokenCount
          nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
            valueBound := by
    rcases hbounded with
      ⟨slot0, hslot0, slot1, hslot1, slot2, hslot2, slot3, hslot3,
        slot4, hslot4, slot5, hslot5, slot6, hslot6,
        consumedCount, hconsumedCount, mappedHead, hmappedHead,
        hrow, hcurrentStatus, hnextStatus⟩
    let witness : CompactFormulaTransformAdjacentStepLocalWitness :=
      { stepWitness :=
          { slot0 := slot0
            slot1 := slot1
            slot2 := slot2
            slot3 := slot3
            slot4 := slot4
            slot5 := slot5
            slot6 := slot6 }
        consumedCount := consumedCount
        mappedHead := mappedHead }
    refine ⟨witness, ?_, ?_, hcurrentStatus, hnextStatus⟩
    · intro index
      fin_cases index
      · exact hmappedHead
      · exact hconsumedCount
      · exact hslot6
      · exact hslot5
      · exact hslot4
      · exact hslot3
      · exact hslot2
      · exact hslot1
      · exact hslot0
    · simpa [witness, compactFormulaTransformAdjacentStepRowOfLocalWitness]
        using hrow
  let witness := Classical.choose hexists
  have hdata := Classical.choose_spec hexists
  exact
    { witness := witness
      values_le := hdata.1
      row_graph := hdata.2.1
      current_status := hdata.2.2.1
      next_status := hdata.2.2.2 }

noncomputable def explicitAdjacentStepDirectTerminalComponentsOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    ExplicitAdjacentStepDirectTerminalComponents valuation tokenTable width
      tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound currentCoordinates currentSize
      nextCoordinates nextSize := by
  let data := explicitAdjacentStepGraphDataOfGraph valuation tokenTable width
    tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
    witnessFinish witnessCount valueBound currentCoordinates currentSize
    nextCoordinates nextSize hbounded
  let row := compactFormulaTransformAdjacentStepRowOfLocalWitness
    currentCoordinates currentSize nextCoordinates nextSize data.witness
  exact
    { row := row
      row_current_coordinates := rfl
      row_current_size := rfl
      row_next_coordinates := rfl
      row_next_size := rfl
      row_graph := data.row_graph
      current_status := data.current_status
      next_status := data.next_status
      values_le := data.values_le }

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridTerminalOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    ExplicitBoundedWitnessHybridTerminal valuation valueBound
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) := by
  have hexists :
      ∃ witness : CompactFormulaTransformAdjacentStepLocalWitness,
        (∀ index,
          boundedWitnessValues
            (compactFormulaTransformAdjacentStepRowOfLocalWitness
              currentCoordinates currentSize nextCoordinates nextSize witness)
            index ≤ valueBound) ∧
        CompactFormulaTransformAdjacentStepRowGraph
          tokenTable width tokenCount stateBoundary stateCount
            (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
            witnessCount
            (compactFormulaTransformAdjacentStepRowOfLocalWitness
              currentCoordinates currentSize nextCoordinates nextSize witness) ∧
        CompactBinaryNatStatusValidBounded tokenTable width tokenCount
          currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
            valueBound ∧
        CompactBinaryNatStatusValidBounded tokenTable width tokenCount
          nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
            valueBound := by
    rcases hbounded with
      ⟨slot0, hslot0, slot1, hslot1, slot2, hslot2, slot3, hslot3,
        slot4, hslot4, slot5, hslot5, slot6, hslot6,
        consumedCount, hconsumedCount, mappedHead, hmappedHead,
        hrow, hcurrentStatus, hnextStatus⟩
    let witness : CompactFormulaTransformAdjacentStepLocalWitness :=
      { stepWitness :=
          { slot0 := slot0
            slot1 := slot1
            slot2 := slot2
            slot3 := slot3
            slot4 := slot4
            slot5 := slot5
            slot6 := slot6 }
        consumedCount := consumedCount
        mappedHead := mappedHead }
    refine ⟨witness, ?_, ?_, hcurrentStatus, hnextStatus⟩
    · intro index
      fin_cases index
      · exact hmappedHead
      · exact hconsumedCount
      · exact hslot6
      · exact hslot5
      · exact hslot4
      · exact hslot3
      · exact hslot2
      · exact hslot1
      · exact hslot0
    · simpa [witness, compactFormulaTransformAdjacentStepRowOfLocalWitness]
        using hrow
  let witness := Classical.choose hexists
  have hrowData := Classical.choose_spec hexists
  let row := compactFormulaTransformAdjacentStepRowOfLocalWitness
    currentCoordinates currentSize nextCoordinates nextSize witness
  let values := boundedWitnessValues row
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values, row] using hrowData.1
  let currentStatusAtZero :=
    compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound hrowData.2.2.1
  let currentStatusAtValuation := revalueClosedHybridCertificate
    currentStatusAtZero
    (compactBinaryNatStatusValidBoundedClosedFormula_freeVariables
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound) valuation
  let nextStatusAtZero :=
    compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound hrowData.2.2.2
  let nextStatusAtValuation := revalueClosedHybridCertificate
    nextStatusAtZero
    (compactBinaryNatStatusValidBoundedClosedFormula_freeVariables
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound) valuation
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitHybridCertificateOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount row
        hrowData.2.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        currentStatusAtValuation nextStatusAtValuation)
  let terminal : HybridCertificate valuation
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values, row,
        compactFormulaTransformAdjacentStepRowOfLocalWitness]
      exact
        (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound row).symm)
      terminalParts
  exact
    { values := values
      values_le := hvalues
      terminal := terminal }

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hrowGraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount
        (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
        witnessCount row) : Nat :=
  let rowFormula :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount row
  let currentFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount currentCoordinates.parserTasksFinish
    currentCoordinates.parserFinish valueBound
  let nextFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount nextCoordinates.parserTasksFinish
    nextCoordinates.parserFinish valueBound
  let innerFormula := currentFormula ⋏ nextFormula
  let terminalFormula := rowFormula ⋏ innerFormula
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount row
      hrowGraph
  let currentResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  let nextResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound
  (rowResource + weakeningFullAssemblyCost
      (insert rowFormula
        (valuationContext terminalFormula.freeVariables valuation))) +
    (((currentResource + weakeningFullAssemblyCost
          (insert currentFormula
            (valuationContext innerFormula.freeVariables valuation))) +
        (nextResource + weakeningFullAssemblyCost
          (insert nextFormula
            (valuationContext innerFormula.freeVariables valuation))) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (valuationContext innerFormula.freeVariables valuation)
          currentFormula nextFormula) +
      weakeningFullAssemblyCost
        (insert innerFormula
          (valuationContext terminalFormula.freeVariables valuation))) +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      (valuationContext terminalFormula.freeVariables valuation)
      rowFormula innerFormula

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResourceOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) : Nat :=
  let components := explicitAdjacentStepDirectTerminalComponentsOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize hbounded
  compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    nextCoordinates components.row components.row_graph

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    ExplicitAdjacentStepDirectTerminal valuation valueBound
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) := by
  let graphData := explicitAdjacentStepGraphDataOfGraph valuation tokenTable
    width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
    witnessFinish witnessCount valueBound currentCoordinates currentSize
    nextCoordinates nextSize hbounded
  let witness := graphData.witness
  let row := compactFormulaTransformAdjacentStepRowOfLocalWitness
    currentCoordinates currentSize nextCoordinates nextSize witness
  let values := boundedWitnessValues row
  have hvalues : ∀ index, values index ≤ valueBound := graphData.values_le
  have hrowGraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount row := graphData.row_graph
  have hcurrentStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound := graphData.current_status
  have hnextStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound := graphData.next_status
  let rowFormula :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount row
  let currentFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount currentCoordinates.parserTasksFinish
    currentCoordinates.parserFinish valueBound
  let nextFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount nextCoordinates.parserTasksFinish
    nextCoordinates.parserFinish valueBound
  let innerFormula := currentFormula ⋏ nextFormula
  let terminalFormula := rowFormula ⋏ innerFormula
  let rowBound :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedExplicitDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount row hrowGraph
  let rowProof := rowBound.proof
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount row hrowGraph
  have hrowPayload : rowProof.payloadLength ≤ rowResource := by
    exact rowBound.payloadLength_le
  let currentProof :=
    compileCompactBinaryNatStatusValidBoundedPublicDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
        currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
        valueBound hcurrentStatus
  let currentResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  have hcurrentPayload : currentProof.payloadLength ≤ currentResource := by
    exact
      compileCompactBinaryNatStatusValidBoundedPublicDirectAtValuationOfGraph_payloadLength_le
        valuation tokenTable width tokenCount
          currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
          valueBound hcurrentStatus
  let nextProof :=
    compileCompactBinaryNatStatusValidBoundedPublicDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
        nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
        valueBound hnextStatus
  let nextResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound
  have hnextPayload : nextProof.payloadLength ≤ nextResource := by
    exact
      compileCompactBinaryNatStatusValidBoundedPublicDirectAtValuationOfGraph_payloadLength_le
        valuation tokenTable width tokenCount
          nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
          valueBound hnextStatus
  have hcurrentVariables : currentFormula.freeVariables ⊆
      innerFormula.freeVariables := by
    simp [innerFormula]
  have hnextVariables : nextFormula.freeVariables ⊆
      innerFormula.freeVariables := by
    simp [innerFormula]
  let currentAtInner := CertifiedPAContextProof.weakenContext currentProof
    (valuationContext_mono valuation hcurrentVariables)
  let nextAtInner := CertifiedPAContextProof.weakenContext nextProof
    (valuationContext_mono valuation hnextVariables)
  have hcurrentAtInner : currentAtInner.payloadLength ≤
      currentResource + weakeningFullAssemblyCost
        (insert currentFormula
          (valuationContext innerFormula.freeVariables valuation)) := by
    exact (CertifiedPAContextProof.weakenContext_payloadLength_le currentProof
      (valuationContext_mono valuation hcurrentVariables)).trans
        (Nat.add_le_add_right hcurrentPayload _)
  have hnextAtInner : nextAtInner.payloadLength ≤
      nextResource + weakeningFullAssemblyCost
        (insert nextFormula
          (valuationContext innerFormula.freeVariables valuation)) := by
    exact (CertifiedPAContextProof.weakenContext_payloadLength_le nextProof
      (valuationContext_mono valuation hnextVariables)).trans
        (Nat.add_le_add_right hnextPayload _)
  let innerProof := CertifiedPAContextProof.conjunction
    currentAtInner nextAtInner
  have hinnerRaw := CertifiedPAContextProof.conjunction_payloadLength_le
    currentAtInner nextAtInner
  have hinner : innerProof.payloadLength ≤
      (currentResource + weakeningFullAssemblyCost
        (insert currentFormula
          (valuationContext innerFormula.freeVariables valuation))) +
      (nextResource + weakeningFullAssemblyCost
        (insert nextFormula
          (valuationContext innerFormula.freeVariables valuation))) +
      CertifiedPAContextProof.conjunctionFullAssemblyCost
        (valuationContext innerFormula.freeVariables valuation)
        currentFormula nextFormula := by
    calc
      innerProof.payloadLength ≤
          currentAtInner.payloadLength + nextAtInner.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost
              (valuationContext innerFormula.freeVariables valuation)
              currentFormula nextFormula := by
        simpa only [innerProof] using hinnerRaw
      _ ≤
          (currentResource + weakeningFullAssemblyCost
            (insert currentFormula
              (valuationContext innerFormula.freeVariables valuation))) +
          (nextResource + weakeningFullAssemblyCost
            (insert nextFormula
              (valuationContext innerFormula.freeVariables valuation))) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            (valuationContext innerFormula.freeVariables valuation)
            currentFormula nextFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add hcurrentAtInner hnextAtInner) _
  have hrowVariables : rowFormula.freeVariables ⊆
      terminalFormula.freeVariables := by
    simp [terminalFormula]
  have hinnerVariables : innerFormula.freeVariables ⊆
      terminalFormula.freeVariables := by
    simp [terminalFormula]
  let rowAtTerminal := CertifiedPAContextProof.weakenContext rowProof
    (valuationContext_mono valuation hrowVariables)
  let innerAtTerminal := CertifiedPAContextProof.weakenContext innerProof
    (valuationContext_mono valuation hinnerVariables)
  have hrowAtTerminal : rowAtTerminal.payloadLength ≤
      rowResource + weakeningFullAssemblyCost
        (insert rowFormula
          (valuationContext terminalFormula.freeVariables valuation)) := by
    exact (CertifiedPAContextProof.weakenContext_payloadLength_le rowProof
      (valuationContext_mono valuation hrowVariables)).trans
        (Nat.add_le_add_right hrowPayload _)
  have hinnerAtTerminal : innerAtTerminal.payloadLength ≤
      ((currentResource + weakeningFullAssemblyCost
          (insert currentFormula
            (valuationContext innerFormula.freeVariables valuation))) +
        (nextResource + weakeningFullAssemblyCost
          (insert nextFormula
            (valuationContext innerFormula.freeVariables valuation))) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (valuationContext innerFormula.freeVariables valuation)
          currentFormula nextFormula) +
      weakeningFullAssemblyCost
        (insert innerFormula
          (valuationContext terminalFormula.freeVariables valuation)) := by
    exact (CertifiedPAContextProof.weakenContext_payloadLength_le innerProof
      (valuationContext_mono valuation hinnerVariables)).trans
        (Nat.add_le_add_right hinner _)
  let outerProof := CertifiedPAContextProof.conjunction
    rowAtTerminal innerAtTerminal
  let terminalResource :=
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResourceOfGraph
      valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded
  have houterRaw := CertifiedPAContextProof.conjunction_payloadLength_le
    rowAtTerminal innerAtTerminal
  have houter : outerProof.payloadLength ≤ terminalResource := by
    calc
      outerProof.payloadLength ≤
          rowAtTerminal.payloadLength + innerAtTerminal.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost
              (valuationContext terminalFormula.freeVariables valuation)
              rowFormula innerFormula := by
        simpa only [outerProof] using houterRaw
      _ ≤
          (rowResource + weakeningFullAssemblyCost
            (insert rowFormula
              (valuationContext terminalFormula.freeVariables valuation))) +
          (((currentResource + weakeningFullAssemblyCost
                (insert currentFormula
                  (valuationContext innerFormula.freeVariables valuation))) +
              (nextResource + weakeningFullAssemblyCost
                (insert nextFormula
                  (valuationContext innerFormula.freeVariables valuation))) +
              CertifiedPAContextProof.conjunctionFullAssemblyCost
                (valuationContext innerFormula.freeVariables valuation)
                currentFormula nextFormula) +
            weakeningFullAssemblyCost
              (insert innerFormula
                (valuationContext terminalFormula.freeVariables valuation))) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            (valuationContext terminalFormula.freeVariables valuation)
            rowFormula innerFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add hrowAtTerminal hinnerAtTerminal) _
      _ = terminalResource := by
        rfl
  let rawBody := compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize
  have hformula :
      rawBody ⇜ (fun index => shortBinaryNumeralTerm (values index)) =
        terminalFormula := by
    simpa [rawBody, terminalFormula, innerFormula, rowFormula,
      currentFormula, nextFormula, values, row,
      compactFormulaTransformAdjacentStepRowOfLocalWitness] using
        (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound row)
  let terminal := castValuationContextProof hformula.symm outerProof
  have hterminal : terminal.payloadLength ≤ terminalResource := by
    change (castValuationContextProof hformula.symm outerProof).payloadLength ≤ _
    rw [castValuationContextProof_payloadLength_eq]
    exact houter
  exact
    { values := values
      values_le := hvalues
      terminalResource := terminalResource
      terminal := by simpa only [rawBody] using terminal
      terminal_payloadLength_le := by
        simpa only [rawBody] using hterminal }

theorem
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_eq
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize
      hbounded).terminalResource =
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResourceOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded := by
  rfl

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificateOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    HybridCertificate valuation
      (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) := by
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  rw [
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize)
    data.values data.values_le data.terminal

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) : Nat :=
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  explicitBoundedWitnessDirectPayloadEnvelope valuation valueBound
    (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize)
    data.values data.terminalResource

noncomputable def
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize).freeVariables valuation)
      (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) := by
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  let rawBody :=
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 9 rawBody
  let terminal := data.terminal
  let terminalResource := data.terminalResource
  let rawProof := compileExplicitBoundedWitnessDirectArity9
    valueBound rawBody data.values data.values_le terminalResource terminal
      data.terminal_payloadLength_le
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize :=
    (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize).symm
  exact castValuationContextProof hformula rawProof

theorem
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    (compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded).payloadLength ≤
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded := by
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  let rawBody :=
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 9 rawBody
  let terminal := data.terminal
  let terminalResource := data.terminalResource
  let rawProof := compileExplicitBoundedWitnessDirectArity9
    valueBound rawBody data.values data.values_le terminalResource terminal
      data.terminal_payloadLength_le
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize :=
    (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize).symm
  change (castValuationContextProof hformula rawProof).payloadLength ≤ _
  rw [castValuationContextProof_payloadLength_eq]
  change rawProof.payloadLength ≤
    explicitBoundedWitnessDirectPayloadEnvelope valuation valueBound rawBody
      data.values terminalResource
  exact compileExplicitBoundedWitnessDirectArity9_payloadLength_le
    valueBound rawBody data.values data.values_le terminalResource terminal
      data.terminal_payloadLength_le

#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula_alignment
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificateOfGraph
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
