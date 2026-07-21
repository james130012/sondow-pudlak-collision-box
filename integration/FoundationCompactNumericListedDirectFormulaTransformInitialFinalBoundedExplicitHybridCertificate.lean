import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit bounded certificate for formula-transform endpoints

All thirty-one endpoint coordinates are installed below the original shared
value bound.  The terminal is the exact seven-conjunct initial/final certificate
on those same coordinates, not a semantic truth conversion.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

private def initialFinalSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm fuel,
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedOutputBoundary,
    shortBinaryNumeralTerm expectedOutputCount,
    shortBinaryNumeralTerm expectedSuffixBoundary,
    shortBinaryNumeralTerm expectedSuffixCount,
    shortBinaryNumeralTerm binderArity,
    shortBinaryNumeralTerm valueBound]

def compactFormulaTransformInitialFinalBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformInitialFinalBoundedDef.val) ⇜
    initialFinalSourceTerms tokenTable width tokenCount stateBoundary stateCount
      fuel inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound

private def compactFormulaTransformInitialFinalBoundedEmptyRawTerms :
    Fin 44 -> ArithmeticSemiterm Empty 45 :=
  ![(#31 : ArithmeticSemiterm Empty 45), #32, #33, #34, #35, #36,
      #37, #38, #39, #40, #41, #42, #43,
      #30, #29, #28, #27, #26, #25, #24, #23, #22, #21, #20, #19,
      #18, #17, #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6,
      #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformInitialFinalBoundedSourceRawTerms :
    Fin 44 -> ArithmeticSemiterm Nat 45 :=
  ![(#31 : ArithmeticSemiterm Nat 45), #32, #33, #34, #35, #36,
      #37, #38, #39, #40, #41, #42, #43,
      #30, #29, #28, #27, #26, #25, #24, #23, #22, #21, #20, #19,
      #18, #17, #16, #15, #14, #13, #12, #11, #10, #9, #8, #7, #6,
      #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformInitialFinalBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 45 :=
  compactFormulaTransformInitialFinalRowsDef.val ⇜
    compactFormulaTransformInitialFinalBoundedEmptyRawTerms

private def compactFormulaTransformInitialFinalBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 45 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformInitialFinalRowsDef.val) ⇜
    compactFormulaTransformInitialFinalBoundedSourceRawTerms

private def compactFormulaTransformInitialFinalBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 14 :=
  sourceBoundedWitnessFormula (#13 : ArithmeticSemiterm Empty 14) 31
    compactFormulaTransformInitialFinalBoundedEmptyRawTerminal

private def compactFormulaTransformInitialFinalBoundedSourceRawBody :
    ArithmeticSemiformula Nat 14 :=
  sourceBoundedWitnessFormula (#13 : ArithmeticSemiterm Nat 14) 31
    compactFormulaTransformInitialFinalBoundedSourceRawTerminal

private theorem compactFormulaTransformInitialFinalBoundedDef_eq_emptyRawBody :
    compactFormulaTransformInitialFinalBoundedDef.val =
      compactFormulaTransformInitialFinalBoundedEmptyRawBody := by
  unfold compactFormulaTransformInitialFinalBoundedDef
  unfold compactFormulaTransformInitialFinalBoundedEmptyRawBody
  unfold compactFormulaTransformInitialFinalBoundedEmptyRawTerminal
  unfold sourceBoundedWitnessFormula sourceSubstitutionLift
  rfl

private theorem
    compactFormulaTransformInitialFinalBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 45 Nat 45) ▹
        compactFormulaTransformInitialFinalBoundedEmptyRawTerminal =
      compactFormulaTransformInitialFinalBoundedSourceRawTerminal := by
  unfold compactFormulaTransformInitialFinalBoundedEmptyRawTerminal
  unfold compactFormulaTransformInitialFinalBoundedSourceRawTerminal
  have hrewriting :
      (Rew.emb : Rew ℒₒᵣ Empty 45 Nat 45).comp
          (Rew.subst
            compactFormulaTransformInitialFinalBoundedEmptyRawTerms) =
        (Rew.subst
          compactFormulaTransformInitialFinalBoundedSourceRawTerms).comp
          (Rew.emb : Rew ℒₒᵣ Empty 44 Nat 44) := by
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app,
          compactFormulaTransformInitialFinalBoundedEmptyRawTerms,
          compactFormulaTransformInitialFinalBoundedSourceRawTerms]
    · intro coordinate
      exact Empty.elim coordinate
  calc
    (Rew.emb : Rew ℒₒᵣ Empty 45 Nat 45) ▹
        (compactFormulaTransformInitialFinalRowsDef.val ⇜
          compactFormulaTransformInitialFinalBoundedEmptyRawTerms) =
      ((Rew.emb : Rew ℒₒᵣ Empty 45 Nat 45).comp
        (Rew.subst
          compactFormulaTransformInitialFinalBoundedEmptyRawTerms)) ▹
        compactFormulaTransformInitialFinalRowsDef.val := by
          rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst
          compactFormulaTransformInitialFinalBoundedSourceRawTerms).comp
        (Rew.emb : Rew ℒₒᵣ Empty 44 Nat 44)) ▹
          compactFormulaTransformInitialFinalRowsDef.val := by rw [hrewriting]
    _ = (Rewriting.emb (ξ := Nat)
          compactFormulaTransformInitialFinalRowsDef.val) ⇜
        compactFormulaTransformInitialFinalBoundedSourceRawTerms := by
          rw [TransitiveRewriting.comp_app]

private theorem compactFormulaTransformInitialFinalBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat)
        compactFormulaTransformInitialFinalBoundedDef.val =
      compactFormulaTransformInitialFinalBoundedSourceRawBody := by
  rw [compactFormulaTransformInitialFinalBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) ▹
      compactFormulaTransformInitialFinalBoundedEmptyRawBody = _
  unfold compactFormulaTransformInitialFinalBoundedEmptyRawBody
  unfold compactFormulaTransformInitialFinalBoundedSourceRawBody
  rw [rewriting_sourceBoundedWitnessFormula]
  rw [rewritingQpow_emb_eq_emb]
  rw [compactFormulaTransformInitialFinalBoundedEmptyRawTerminal_embedding]
  rfl

private def compactFormulaTransformInitialFinalBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    ArithmeticSemiformula Nat 31 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformInitialFinalRowsDef.val) ⇜
    ![sourceSubstitutionLift 31 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm fuel),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm inputBoundary),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm inputCount),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedOutputBoundary),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedOutputCount),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedSuffixBoundary),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedSuffixCount),
      sourceSubstitutionLift 31 (shortBinaryNumeralTerm binderArity),
      (#30 : ArithmeticSemiterm Nat 31), #29, #28, #27, #26, #25, #24,
      #23, #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12,
      #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private theorem compactFormulaTransformInitialFinalBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    sourceSubstitutionQpow
        (initialFinalSourceTerms tokenTable width tokenCount stateBoundary
          stateCount fuel inputBoundary inputCount expectedOutputBoundary
          expectedOutputCount expectedSuffixBoundary expectedSuffixCount
          binderArity valueBound) 31 ▹
      compactFormulaTransformInitialFinalBoundedSourceRawTerminal =
    compactFormulaTransformInitialFinalBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity := by
  unfold compactFormulaTransformInitialFinalBoundedSourceRawTerminal
  unfold compactFormulaTransformInitialFinalBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, initialFinalSourceTerms,
      compactFormulaTransformInitialFinalBoundedSourceRawTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

theorem compactFormulaTransformInitialFinalBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    compactFormulaTransformInitialFinalBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 31
        (compactFormulaTransformInitialFinalBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity) := by
  unfold compactFormulaTransformInitialFinalBoundedClosedFormula
  rw [compactFormulaTransformInitialFinalBoundedDef_emb_eq_sourceRawBody]
  change Rew.subst
      (initialFinalSourceTerms tokenTable width tokenCount stateBoundary
        stateCount fuel inputBoundary inputCount expectedOutputBoundary
        expectedOutputCount expectedSuffixBoundary expectedSuffixCount
        binderArity valueBound) ▹
      compactFormulaTransformInitialFinalBoundedSourceRawBody = _
  unfold compactFormulaTransformInitialFinalBoundedSourceRawBody
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactFormulaTransformInitialFinalBoundedSourceRawTerminal_rewriting]
  simp [initialFinalSourceTerms, Rew.subst_bvar]
  rfl

private def boundedWitnessValues
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    Fin 31 -> Nat :=
  ![witness.finalParserOutputBoundarySize,
    witness.finalParserOutputBoundary,
    witness.finalParserOutputStart,
    witness.finalSizeWitness.outputBoundarySize,
    witness.finalSizeWitness.parserTasksBoundarySize,
    witness.finalSizeWitness.parserTokensBoundarySize,
    witness.finalCoordinates.outputCount,
    witness.finalCoordinates.outputBoundary,
    witness.finalCoordinates.parserTasksCount,
    witness.finalCoordinates.parserTasksBoundary,
    witness.finalCoordinates.parserTokensCount,
    witness.finalCoordinates.parserTokensBoundary,
    witness.finalCoordinates.parserTasksFinish,
    witness.finalCoordinates.parserTokensFinish,
    witness.finalCoordinates.parserFinish,
    witness.finalCoordinates.finish,
    witness.finalCoordinates.start,
    witness.initialSizeWitness.outputBoundarySize,
    witness.initialSizeWitness.parserTasksBoundarySize,
    witness.initialSizeWitness.parserTokensBoundarySize,
    witness.initialCoordinates.outputCount,
    witness.initialCoordinates.outputBoundary,
    witness.initialCoordinates.parserTasksCount,
    witness.initialCoordinates.parserTasksBoundary,
    witness.initialCoordinates.parserTokensCount,
    witness.initialCoordinates.parserTokensBoundary,
    witness.initialCoordinates.parserTasksFinish,
    witness.initialCoordinates.parserTokensFinish,
    witness.initialCoordinates.parserFinish,
    witness.initialCoordinates.finish,
    witness.initialCoordinates.start]

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

private theorem substitute_sourceSubstitutionLift31
    (values : Fin 31 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 31 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 31) values term)

private theorem compactFormulaTransformInitialFinalBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialFinalBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity ⇜
      (fun index => shortBinaryNumeralTerm
        (boundedWitnessValues witness index)) =
    compactFormulaTransformInitialFinalRowsClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (boundedWitnessValues witness index)) ▹
    compactFormulaTransformInitialFinalBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity = _
  unfold compactFormulaTransformInitialFinalBoundedRawTerminal
  unfold compactFormulaTransformInitialFinalRowsClosedFormula
  rw [rewriting_embeddedFormulaSubstitution]
  unfold boundedWitnessValues
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, Rew.subst_bvar]
  all_goals
    rw [substitute_sourceSubstitutionLift31]

noncomputable def
    compactFormulaTransformInitialFinalBoundedExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :
    HybridCertificate
      (compactFormulaTransformInitialFinalBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound) := by
  have hexists :
      ∃ witness : CompactFormulaTransformInitialFinalWitnessCoordinates,
        (∀ index, boundedWitnessValues witness index ≤ valueBound) ∧
        CompactFormulaTransformInitialFinalRows
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity witness := by
    rcases hbounded with
      ⟨initialStart, hinitialStart,
        initialFinish, hinitialFinish,
        initialParserFinish, hinitialParserFinish,
        initialParserTokensFinish, hinitialParserTokensFinish,
        initialParserTasksFinish, hinitialParserTasksFinish,
        initialParserTokensBoundary, hinitialParserTokensBoundary,
        initialParserTokensCount, hinitialParserTokensCount,
        initialParserTasksBoundary, hinitialParserTasksBoundary,
        initialParserTasksCount, hinitialParserTasksCount,
        initialOutputBoundary, hinitialOutputBoundary,
        initialOutputCount, hinitialOutputCount,
        initialParserTokensBoundarySize, hinitialParserTokensBoundarySize,
        initialParserTasksBoundarySize, hinitialParserTasksBoundarySize,
        initialOutputBoundarySize, hinitialOutputBoundarySize,
        finalStart, hfinalStart,
        finalFinish, hfinalFinish,
        finalParserFinish, hfinalParserFinish,
        finalParserTokensFinish, hfinalParserTokensFinish,
        finalParserTasksFinish, hfinalParserTasksFinish,
        finalParserTokensBoundary, hfinalParserTokensBoundary,
        finalParserTokensCount, hfinalParserTokensCount,
        finalParserTasksBoundary, hfinalParserTasksBoundary,
        finalParserTasksCount, hfinalParserTasksCount,
        finalOutputBoundary, hfinalOutputBoundary,
        finalOutputCount, hfinalOutputCount,
        finalParserTokensBoundarySize, hfinalParserTokensBoundarySize,
        finalParserTasksBoundarySize, hfinalParserTasksBoundarySize,
        finalOutputBoundarySize, hfinalOutputBoundarySize,
        finalParserOutputStart, hfinalParserOutputStart,
        finalParserOutputBoundary, hfinalParserOutputBoundary,
        finalParserOutputBoundarySize, hfinalParserOutputBoundarySize,
        hrelation⟩
    let witness := compactFormulaTransformInitialFinalWitnessOfValues
      initialStart initialFinish initialParserFinish
      initialParserTokensFinish initialParserTasksFinish
      initialParserTokensBoundary initialParserTokensCount
      initialParserTasksBoundary initialParserTasksCount
      initialOutputBoundary initialOutputCount
      initialParserTokensBoundarySize initialParserTasksBoundarySize
      initialOutputBoundarySize
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      finalParserTokensBoundarySize finalParserTasksBoundarySize
      finalOutputBoundarySize finalParserOutputStart
      finalParserOutputBoundary finalParserOutputBoundarySize
    refine ⟨witness, ?_, ?_⟩
    · intro index
      fin_cases index
      · exact hfinalParserOutputBoundarySize
      · exact hfinalParserOutputBoundary
      · exact hfinalParserOutputStart
      · exact hfinalOutputBoundarySize
      · exact hfinalParserTasksBoundarySize
      · exact hfinalParserTokensBoundarySize
      · exact hfinalOutputCount
      · exact hfinalOutputBoundary
      · exact hfinalParserTasksCount
      · exact hfinalParserTasksBoundary
      · exact hfinalParserTokensCount
      · exact hfinalParserTokensBoundary
      · exact hfinalParserTasksFinish
      · exact hfinalParserTokensFinish
      · exact hfinalParserFinish
      · exact hfinalFinish
      · exact hfinalStart
      · exact hinitialOutputBoundarySize
      · exact hinitialParserTasksBoundarySize
      · exact hinitialParserTokensBoundarySize
      · exact hinitialOutputCount
      · exact hinitialOutputBoundary
      · exact hinitialParserTasksCount
      · exact hinitialParserTasksBoundary
      · exact hinitialParserTokensCount
      · exact hinitialParserTokensBoundary
      · exact hinitialParserTasksFinish
      · exact hinitialParserTokensFinish
      · exact hinitialParserFinish
      · exact hinitialFinish
      · exact hinitialStart
    · simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
        compactFormulaTransformStateRowCoordinatesOf] using hrelation
  let witness := Classical.choose hexists
  have hwitness := Classical.choose_spec hexists
  let values := boundedWitnessValues witness
  let endpointCertificate :=
    compactFormulaTransformInitialFinalRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness hwitness.2
  let terminal : HybridCertificate
      (compactFormulaTransformInitialFinalBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactFormulaTransformInitialFinalBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity witness).symm)
      endpointCertificate
  rw [compactFormulaTransformInitialFinalBoundedClosedFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactFormulaTransformInitialFinalBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity)
    values (by simpa [values] using hwitness.1) terminal

noncomputable def
    compileCompactFormulaTransformInitialFinalBoundedExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformInitialFinalBoundedClosedFormula
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity
          valueBound).freeVariables zeroValuation)
      (compactFormulaTransformInitialFinalBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :=
  (compactFormulaTransformInitialFinalBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount fuel
    inputBoundary inputCount expectedOutputBoundary expectedOutputCount
    expectedSuffixBoundary expectedSuffixCount binderArity valueBound
    hbounded).compile

noncomputable def
    compactFormulaTransformInitialFinalBoundedExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformInitialFinalBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
      hbounded)

theorem
    compileCompactFormulaTransformInitialFinalBoundedExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound) :
    (compileCompactFormulaTransformInitialFinalBoundedExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
      hbounded).payloadLength ≤
    compactFormulaTransformInitialFinalBoundedExplicitStructuralResource
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
      hbounded := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformInitialFinalBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
      hbounded)

#print axioms compactFormulaTransformInitialFinalBoundedClosedFormula_alignment
#print axioms
  compactFormulaTransformInitialFinalBoundedExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformInitialFinalBoundedExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate
