import integration.FoundationCompactNumericListedDirectParserInitialFinalFormula
import integration.FoundationCompactNumericListedDirectTraceNatListRowLayouts
import integration.FoundationCompactNumericListedDirectTraceParserStateLayouts

/-!
# Installation of parser initial/final formulas into the complete trace

The proof parser starts on the certified input, the formula parser starts on
the formula input, and the certificate parser starts on the exact list produced
by the proof parser.  Certificate and formula final outputs are both empty.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserInitialFinalInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectTraceParserStateLayouts
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectTraceNatListRowLayouts

private theorem getI_eq_of_parserTraceState?_eq_some
    {states : List CompactUnifiedParserState} {index : Nat}
    {state : CompactUnifiedParserState}
    (hstate : compactParserTraceState? states index = some state) :
    states.getI index = state := by
  unfold compactParserTraceState? at hstate
  rw [List.getI_eq_getElem?_getD]
  rw [hstate]
  rfl

private theorem compactSyntaxParserStateOutput_eq_some_iff
    (state : CompactUnifiedParserState) (output : List Nat) :
    compactSyntaxParserStateOutput state = some output ↔
      state.2.2 = some (some output) := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | none => simp [compactSyntaxParserStateOutput]
  | some inner =>
      cases inner <;> simp [compactSyntaxParserStateOutput]

theorem compactParserOutputLocalTraceValid_initial_final
    {step : CompactUnifiedParserState → CompactUnifiedParserState}
    {fuel taskKind taskBinderArity taskRepeatCount : Nat}
    {input expected : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid step fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    states.length = fuel + 1 ∧
      states.getI 0 =
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) ∧
      (states.getI fuel).2.2 = some (some expected) := by
  rcases hvalid with ⟨hlocal, houtput⟩
  have hinitial :=
    getI_eq_of_parserTraceState?_eq_some hlocal.2.1
  have hfinalOption :=
    compactParserLocalTraceValid_stateAt hlocal (Nat.le_refl fuel)
  have hfinal := getI_eq_of_parserTraceState?_eq_some hfinalOption
  rw [hfinalOption] at houtput
  have hfinalOutput : compactSyntaxParserStateOutput
      (compactParserStateAt step
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) fuel) =
      some expected := by
    simpa [compactParserStateOutputOption] using houtput
  have hfinalStatus :=
    (compactSyntaxParserStateOutput_eq_some_iff _ _).mp hfinalOutput
  refine ⟨hlocal.1, hinitial, ?_⟩
  rw [hfinal]
  exact hfinalStatus

theorem compactParserOutputLocalTraceValid_initial_final_formula
    {step : CompactUnifiedParserState → CompactUnifiedParserState}
    {tokenTable width tokenCount stateBoundary fuel
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount :
      Nat}
    {input expected : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid step fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected) :
    ∃ witness,
      compactUnifiedParserInitialFinalRowsDef.val.Evalb
        (compactUnifiedParserInitialFinalRowsEnvironment
          tokenTable width tokenCount stateBoundary states.length fuel
          inputBoundary input.length expectedBoundary expected.length
          taskKind taskBinderArity taskRepeatCount witness) := by
  apply (exists_compactUnifiedParserInitialFinalFormula_iff
    rfl hrows hinput hexpected).mpr
  exact compactParserOutputLocalTraceValid_initial_final hvalid

def CompactNumericParserInitialFinalFormulaRows
    (trace : CompactNumericListedDirectTrace)
    (certifiedBoundary formulaBoundary
      proofStateBoundary certificateStateBoundary formulaStateBoundary
      certificateInputBoundary : Nat)
    (proofWitness certificateWitness formulaWitness :
      CompactParserInitialFinalWitnessCoordinates) : Prop :=
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let boundaries := compactAdditiveComponentBoundaries components
  let certifiedTokens := compactNumericDirectTraceCertifiedTokens trace
  let formulaTokens := compactNumericDirectTraceFormulaTokens trace
  let certificateTokens := (compactNumericDirectTraceParts trace).2.1
  let proofStates := compactNumericDirectTraceProofParserTrace trace
  let certificateStates := compactNumericDirectTraceCertificateParserTrace trace
  let formulaStates := compactNumericDirectTraceFormulaParserTrace trace
  CompactNatListComponentRowLayout tokenTable width tokens.length
      (boundaries.getI 0) (boundaries.getI 1)
      certifiedBoundary certifiedTokens ∧
    CompactNatListComponentRowLayout tokenTable width tokens.length
      (boundaries.getI 2) (boundaries.getI 3)
      formulaBoundary formulaTokens ∧
    CompactUnifiedParserStateListComponentLayout tokenTable width tokens.length
      (boundaries.getI 4) (boundaries.getI 5)
      proofStateBoundary proofStates ∧
    CompactUnifiedParserStateListComponentLayout tokenTable width tokens.length
      (boundaries.getI 5) (boundaries.getI 6)
      certificateStateBoundary certificateStates ∧
    CompactUnifiedParserStateListComponentLayout tokenTable width tokens.length
      (boundaries.getI 6) (boundaries.getI 7)
      formulaStateBoundary formulaStates ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokens.length
        certificateInputBoundary certificateTokens ∧
    compactUnifiedParserInitialFinalRowsDef.val.Evalb
      (compactUnifiedParserInitialFinalRowsEnvironment
        tokenTable width tokens.length proofStateBoundary proofStates.length
        (compactProofParserFuelBound certifiedTokens)
        certifiedBoundary certifiedTokens.length
        certificateInputBoundary certificateTokens.length
        3 0 0 proofWitness) ∧
    compactUnifiedParserInitialFinalRowsDef.val.Evalb
      (compactUnifiedParserInitialFinalRowsEnvironment
        tokenTable width tokens.length certificateStateBoundary
        certificateStates.length
        (compactCertificateParserFuelBound certificateTokens)
        certificateInputBoundary certificateTokens.length 0 0
        8 0 0 certificateWitness) ∧
    compactUnifiedParserInitialFinalRowsDef.val.Evalb
      (compactUnifiedParserInitialFinalRowsEnvironment
        tokenTable width tokens.length formulaStateBoundary formulaStates.length
        (compactSyntaxRunFuelBound formulaTokens)
        formulaBoundary formulaTokens.length 0 0
        1 0 0 formulaWitness)

theorem compactNumericListedDirectTrace_parser_initial_final_formulas
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    ∃ certifiedBoundary formulaBoundary
        proofStateBoundary certificateStateBoundary formulaStateBoundary
        certificateInputBoundary proofWitness certificateWitness formulaWitness,
      CompactNumericParserInitialFinalFormulaRows trace
        certifiedBoundary formulaBoundary
        proofStateBoundary certificateStateBoundary formulaStateBoundary
        certificateInputBoundary proofWitness certificateWitness formulaWitness := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let boundaries := compactAdditiveComponentBoundaries components
  let certifiedTokens := compactNumericDirectTraceCertifiedTokens trace
  let formulaTokens := compactNumericDirectTraceFormulaTokens trace
  let certificateTokens := (compactNumericDirectTraceParts trace).2.1
  let proofStates := compactNumericDirectTraceProofParserTrace trace
  let certificateStates := compactNumericDirectTraceCertificateParserTrace trace
  let formulaStates := compactNumericDirectTraceFormulaParserTrace trace
  rcases compactNumericListedDirectTrace_three_natList_row_layouts trace with
    ⟨certifiedBoundary, formulaBoundary, _formulaValueBoundary,
      hcertifiedRows, hformulaRows, _hformulaValueRows⟩
  rcases compactNumericListedDirectTrace_parser_state_layouts trace with
    ⟨proofStateBoundary, certificateStateBoundary, formulaStateBoundary,
      hproofStateRows, hcertificateStateRows, hformulaStateRows⟩
  have hfull := hvalid
  unfold CompactNumericListedDirectTraceValid at hfull
  have hproofValid : CompactProofTokenParserDirectTraceValid
      certifiedTokens certificateTokens proofStates := hfull.2.2.1
  have hcertificateValid : CompactCertificateTokenParserDirectTraceValid
      certificateTokens [] certificateStates := hfull.2.2.2.1
  have hformulaValid : CompactFormulaTokenParserDirectTraceValid
      0 formulaTokens [] formulaStates := hfull.2.2.2.2.1
  have hproofLocal : CompactParserOutputLocalTraceValid compactProofParserStep
      (compactProofParserFuelBound certifiedTokens)
      (certifiedTokens, [(3, 0, 0)], none)
      (some certificateTokens) proofStates := by
    simpa [CompactProofTokenParserDirectTraceValid,
      compactProofParserInitialState, compactProofTask] using hproofValid
  have hcertificateLocal : CompactParserOutputLocalTraceValid
      compactCertificateParserStep
      (compactCertificateParserFuelBound certificateTokens)
      (certificateTokens, [(8, 0, 0)], none)
      (some []) certificateStates := by
    simpa [CompactCertificateTokenParserDirectTraceValid,
      compactCertificateParserInitialState,
      compactStructuralCertificateTask] using hcertificateValid
  have hformulaLocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound formulaTokens)
      (formulaTokens, [(1, 0, 0)], none)
      (some []) formulaStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hformulaValid
  have hcertificateFacts :=
    compactParserOutputLocalTraceValid_initial_final hcertificateLocal
  have hcertificateZero : 0 < certificateStates.length := by
    omega
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hcertificateStateRows.2.1 hcertificateZero with
    ⟨certificateInitialCoordinates, _certificateInitialSize,
      _hcertificateInitialAt, hcertificateInitialFixed⟩
  let certificateInputBoundary :=
    certificateInitialCoordinates.tokensBoundary
  have hcertificateInitialTokens :
      (certificateStates.getI 0).1 = certificateTokens :=
    congrArg Prod.fst hcertificateFacts.2.1
  have hcertificateInitialTokensExpanded :
      ((compactNumericDirectTraceCertificateParserTrace trace).getI 0).1 =
        (compactNumericDirectTraceParts trace).2.1 := by
    simpa only [certificateStates, certificateTokens] using
      hcertificateInitialTokens
  have hcertificateInitialRows := hcertificateInitialFixed.tokensRows
  rw [hcertificateInitialTokensExpanded] at hcertificateInitialRows
  have hcertificateInputRows :
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokens.length
          certificateInputBoundary certificateTokens := by
    simpa only [tokenTable, width, tokens, certificateInputBoundary,
      certificateTokens] using hcertificateInitialRows
  have hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokens.length 0
        ([] : List Nat) := by
    intro index hindex
    simp at hindex
  have hproofFormula :=
    compactParserOutputLocalTraceValid_initial_final_formula
      hproofLocal hproofStateRows.2.1 hcertifiedRows.2.1
        hcertificateInputRows
  have hcertificateFormula :=
    compactParserOutputLocalTraceValid_initial_final_formula
      hcertificateLocal hcertificateStateRows.2.1
        hcertificateInputRows hemptyRows
  have hformulaFormula :=
    compactParserOutputLocalTraceValid_initial_final_formula
      hformulaLocal hformulaStateRows.2.1 hformulaRows.2.1 hemptyRows
  rcases hproofFormula with ⟨proofWitness, hproofFormula⟩
  rcases hcertificateFormula with
    ⟨certificateWitness, hcertificateFormula⟩
  rcases hformulaFormula with ⟨formulaWitness, hformulaFormula⟩
  refine ⟨certifiedBoundary, formulaBoundary,
    proofStateBoundary, certificateStateBoundary, formulaStateBoundary,
    certificateInputBoundary, proofWitness, certificateWitness, formulaWitness,
    ?_⟩
  exact ⟨hcertifiedRows, hformulaRows,
    hproofStateRows, hcertificateStateRows, hformulaStateRows,
    hcertificateInputRows,
    hproofFormula, hcertificateFormula, hformulaFormula⟩

#print axioms compactParserOutputLocalTraceValid_initial_final
#print axioms compactParserOutputLocalTraceValid_initial_final_formula
#print axioms compactNumericListedDirectTrace_parser_initial_final_formulas

end FoundationCompactNumericListedDirectParserInitialFinalInstallation
