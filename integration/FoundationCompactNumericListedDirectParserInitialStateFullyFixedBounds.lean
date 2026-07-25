import integration.FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserInitialTaskAtRowsShortFixedBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-!
# Fully fixed parser initial-state certificate

The four original initial-state leaves are rebuilt with exact short-binary
syntax and bounded by one public numeric/bit envelope.  The resulting theorem
contains no graph-dependent payload term.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserInitialTaskAtRowsShortFixedBounds

private def initialZeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate initialZeroValuation formula

private theorem binaryFormulaCode_and_left_le_initial
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_initial
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem conjunction_left_closed_of_closed_initial
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

private theorem conjunction_right_closed_of_closed_initial
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def parserInitialTaskCountOneCertificate
    (value : Nat) (hvalue : value = 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm value) = 1” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    initialZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, (‘1’ : ValuationTerm)] (by
      change termValue initialZeroValuation (shortBinaryNumeralTerm value) =
        termValue initialZeroValuation (‘1’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticOne] using hvalue)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

def parserInitialTaskCountTermCodeEnvelope (bitBound : Nat) : Nat :=
  max (binaryNumeralTermCodeEnvelope bitBound)
    (binaryTermCode (‘1’ : ValuationTerm)).length

def parserInitialTaskCountPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (parserInitialTaskCountTermCodeEnvelope bitBound)

theorem parserInitialTaskCountOneCertificate_structuralPayloadBound_le_fixed
    (value numericBound bitBound : Nat)
    (hvalue : value = 1)
    (hvalueSize : Nat.size value <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (parserInitialTaskCountOneCertificate value hvalue) <=
      parserInitialTaskCountPayloadEnvelope numericBound bitBound := by
  let first := shortBinaryNumeralTerm value
  let second : ValuationTerm := ‘1’
  let args : Fin 2 -> ValuationTerm := ![first, second]
  have hfirstVariables : first.freeVariables ⊆ {0} := by
    rw [show first.freeVariables = ∅ by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty value]
    simp
  have hsecondVariables : second.freeVariables ⊆ {0} := by
    simp [second]
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      initialZeroValuation Language.Eq.eq args hfirstVariables
        hsecondVariables
  have hfirstCode : (binaryTermCode first).length <=
      parserInitialTaskCountTermCodeEnvelope bitBound := by
    unfold parserInitialTaskCountTermCodeEnvelope
    exact
      (binaryNumeralTerm_code_length_le_envelope value bitBound
        hvalueSize).trans (Nat.le_max_left _ _)
  have hsecondCode : (binaryTermCode second).length <=
      parserInitialTaskCountTermCodeEnvelope bitBound := by
    unfold parserInitialTaskCountTermCodeEnvelope
    dsimp only [second]
    exact Nat.le_max_right _ _
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed initialZeroValuation
      Language.Eq.eq args numericBound
      (parserInitialTaskCountTermCodeEnvelope bitBound) hfirstVariables
      hsecondVariables (by simp [initialZeroValuation]) hfirstCode hsecondCode
  simpa only [parserInitialTaskCountOneCertificate,
    hybridFormulaStructuralPayloadBound, args, first, second,
    parserInitialTaskCountPayloadEnvelope] using hpublic.trans hfixed

def parserInitialStateClosedTerms
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount :
      Nat) : Fin 16 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm coordinates.start,
    shortBinaryNumeralTerm coordinates.finish,
    shortBinaryNumeralTerm coordinates.tokensFinish,
    shortBinaryNumeralTerm coordinates.tasksFinish,
    shortBinaryNumeralTerm coordinates.tokensBoundary,
    shortBinaryNumeralTerm coordinates.tokensCount,
    shortBinaryNumeralTerm coordinates.tasksBoundary,
    shortBinaryNumeralTerm coordinates.tasksCount,
    shortBinaryNumeralTerm sourceBoundary,
    shortBinaryNumeralTerm sourceCount,
    shortBinaryNumeralTerm taskKind,
    shortBinaryNumeralTerm taskBinderArity,
    shortBinaryNumeralTerm taskRepeatCount]

def parserInitialStateFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserInitialStateRowsDef.val)).length

def parserInitialStateSyntaxResource (bitBound : Nat) : Nat :=
  parserInitialStateFormulaCodeEnvelope bitBound + 1

theorem compactUnifiedParserInitialStateRowsClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount
      bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hfinishSize : Nat.size coordinates.finish <= bitBound)
    (htokensFinishSize : Nat.size coordinates.tokensFinish <= bitBound)
    (htasksFinishSize : Nat.size coordinates.tasksFinish <= bitBound)
    (htokensBoundarySize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htokensCountSize : Nat.size coordinates.tokensCount <= bitBound)
    (htasksBoundarySize : Nat.size coordinates.tasksBoundary <= bitBound)
    (htasksCountSize : Nat.size coordinates.tasksCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htaskKindSize : Nat.size taskKind <= bitBound)
    (htaskBinderAritySize : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount)).length <=
      parserInitialStateSyntaxResource bitBound := by
  let terms := parserInitialStateClosedTerms tokenTable width tokenCount
    coordinates sourceBoundary sourceCount taskKind taskBinderArity
    taskRepeatCount
  let source : ArithmeticSemiformula Nat 16 :=
    Rewriting.emb (ξ := Nat) compactUnifiedParserInitialStateRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
        htokenTableSize
    · exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
        htokenCountSize
    · exact binaryNumeralTerm_code_length_le_envelope coordinates.start bitBound
        hstartSize
    · exact binaryNumeralTerm_code_length_le_envelope coordinates.finish bitBound
        hfinishSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tokensFinish bitBound htokensFinishSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tasksFinish bitBound htasksFinishSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tokensBoundary bitBound htokensBoundarySize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tokensCount bitBound htokensCountSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tasksBoundary bitBound htasksBoundarySize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tasksCount bitBound htasksCountSize
    · exact binaryNumeralTerm_code_length_le_envelope sourceBoundary bitBound
        hsourceBoundarySize
    · exact binaryNumeralTerm_code_length_le_envelope sourceCount bitBound
        hsourceCountSize
    · exact binaryNumeralTerm_code_length_le_envelope taskKind bitBound
        htaskKindSize
    · exact binaryNumeralTerm_code_length_le_envelope taskBinderArity bitBound
        htaskBinderAritySize
    · exact binaryNumeralTerm_code_length_le_envelope taskRepeatCount bitBound
        htaskRepeatCountSize
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  have hraw' := hraw.trans (Nat.le_succ _)
  unfold compactUnifiedParserInitialStateRowsClosedFormula
    parserInitialStateSyntaxResource parserInitialStateFormulaCodeEnvelope
  simpa only [sourceSubstitutionQpow, terms, source,
    parserInitialStateClosedTerms] using hraw'

theorem compactUnifiedParserInitialStateRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount :
      Nat) :
    (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
      tokenCount coordinates sourceBoundary sourceCount taskKind
        taskBinderArity taskRepeatCount).freeVariables = ∅ := by
  unfold compactUnifiedParserInitialStateRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

noncomputable def compactUnifiedParserInitialStateRowsFixedCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount :
      Nat)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates sourceBoundary sourceCount taskKind taskBinderArity
        taskRepeatCount) :
    HybridCertificate
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount) := by
  rcases hgraph with ⟨hsame, htaskCount, htask, hrunning⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount
        coordinates.tokensBoundary coordinates.tokensCount hsame)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (parserInitialTaskCountOneCertificate coordinates.tasksCount htaskCount)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (parserInitialTaskAtRowsExactCertificateOfGraph tokenTable width
          tokenCount coordinates.tasksBoundary coordinates.tasksCount taskKind
          taskBinderArity taskRepeatCount htask)
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates.tasksFinish
            coordinates.finish hrunning)))
  exact .cast
    (compactUnifiedParserInitialStateRowsClosedFormula_alignment tokenTable
      width tokenCount coordinates sourceBoundary sourceCount taskKind
        taskBinderArity taskRepeatCount).symm parts

def parserInitialStateFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (parserInitialStateSyntaxResource bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (hybridThreeConjunctionGeneralPayloadEnvelope
      (parserInitialStateSyntaxResource bitBound)
      (parserInitialTaskCountPayloadEnvelope numericBound bitBound)
      (parserInitialTaskAtRowsFullPayloadEnvelope numericBound bitBound)
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound))

theorem
    compactUnifiedParserInitialStateRowsFixedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount
      numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates sourceBoundary sourceCount taskKind taskBinderArity
        taskRepeatCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hsourceCountValue : sourceCount <= numericBound)
    (htasksCountValue : coordinates.tasksCount <= numericBound)
    (htasksFinishValue : coordinates.tasksFinish <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hfinishSize : Nat.size coordinates.finish <= bitBound)
    (htokensFinishSize : Nat.size coordinates.tokensFinish <= bitBound)
    (htasksFinishSize : Nat.size coordinates.tasksFinish <= bitBound)
    (htokensBoundarySize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htokensCountSize : Nat.size coordinates.tokensCount <= bitBound)
    (htasksBoundarySize : Nat.size coordinates.tasksBoundary <= bitBound)
    (htasksCountSize : Nat.size coordinates.tasksCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htaskKindSize : Nat.size taskKind <= bitBound)
    (htaskBinderAritySize : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound)
    (hnumericBoundSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserInitialStateRowsFixedCertificateOfGraph tokenTable
          width tokenCount coordinates sourceBoundary sourceCount taskKind
          taskBinderArity taskRepeatCount hgraph) <=
      parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound := by
  rcases hgraph with ⟨hsame, htaskCount, htask, hrunning⟩
  let sameFormula :=
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      sourceBoundary sourceCount coordinates.tokensBoundary
        coordinates.tokensCount
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm coordinates.tasksCount) = 1”
  let taskFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount coordinates.tasksBoundary coordinates.tasksCount taskKind
      taskBinderArity taskRepeatCount (‘0’ : ValuationTerm)
  let runningFormula :=
    compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      coordinates.tasksFinish coordinates.finish
  let sameCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount
        coordinates.tokensBoundary coordinates.tokensCount hsame
  let countCertificate :=
    parserInitialTaskCountOneCertificate coordinates.tasksCount htaskCount
  let taskCertificate :=
    parserInitialTaskAtRowsExactCertificateOfGraph tokenTable width tokenCount
      coordinates.tasksBoundary coordinates.tasksCount taskKind taskBinderArity
      taskRepeatCount htask
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates.tasksFinish coordinates.finish
        hrunning
  let sameResource :=
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let countResource :=
    parserInitialTaskCountPayloadEnvelope numericBound bitBound
  let taskResource :=
    parserInitialTaskAtRowsFullPayloadEnvelope numericBound bitBound
  let runningResource :=
    compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound
  let syntaxResource := parserInitialStateSyntaxResource bitBound
  have hsameResource :
      hybridFormulaStructuralPayloadBound sameCertificate <= sameResource := by
    exact
      (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount sourceBoundary sourceCount
        coordinates.tokensBoundary coordinates.tokensCount hsame).trans
      (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount
        coordinates.tokensBoundary coordinates.tokensCount numericBound
        bitBound hsame hwidthValue htokenCountValue hsourceCountValue
        htokenTableSize hsourceBoundarySize htokensBoundarySize
        hnumericBoundSize)
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= countResource := by
    exact
      parserInitialTaskCountOneCertificate_structuralPayloadBound_le_fixed
        coordinates.tasksCount numericBound bitBound htaskCount
        htasksCountSize
  have htaskResource :
      hybridFormulaStructuralPayloadBound taskCertificate <= taskResource := by
    exact
      parserInitialTaskAtRowsExactCertificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount coordinates.tasksBoundary
        coordinates.tasksCount taskKind taskBinderArity taskRepeatCount
        numericBound bitBound htask hwidthValue htokenCountValue
        htasksCountValue htokenTableSize hwidthSize htokenCountSize
        htasksBoundarySize htasksCountSize htaskKindSize
        htaskBinderAritySize htaskRepeatCountSize
  have hrunningResource :
      hybridFormulaStructuralPayloadBound runningCertificate <=
        runningResource := by
    exact
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount coordinates.tasksFinish coordinates.finish
        numericBound bitBound hwidthValue htasksFinishValue htokenTableSize
        hwidthSize htokenCountSize htasksFinishSize hfinishSize hrunning
  have hfullCode :
      (binaryFormulaCode
        (sameFormula ⋏
          (countFormula ⋏ (taskFormula ⋏ runningFormula)))).length <=
        syntaxResource := by
    have hcode :=
      compactUnifiedParserInitialStateRowsClosedFormula_code_length_le_fixed
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
        taskKind taskBinderArity taskRepeatCount bitBound htokenTableSize
        hwidthSize htokenCountSize hstartSize hfinishSize htokensFinishSize
        htasksFinishSize htokensBoundarySize htokensCountSize
        htasksBoundarySize htasksCountSize hsourceBoundarySize
        hsourceCountSize htaskKindSize htaskBinderAritySize
        htaskRepeatCountSize
    rw [compactUnifiedParserInitialStateRowsClosedFormula_alignment] at hcode
    simpa only [compactUnifiedParserInitialStateRowsExplicitFormula,
      sameFormula, countFormula, taskFormula, runningFormula] using hcode
  have hfullClosed :
      (sameFormula ⋏
        (countFormula ⋏ (taskFormula ⋏ runningFormula))).freeVariables = ∅ := by
    have hclosed :=
      compactUnifiedParserInitialStateRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
        taskKind taskBinderArity taskRepeatCount
    rw [compactUnifiedParserInitialStateRowsClosedFormula_alignment] at hclosed
    simpa only [compactUnifiedParserInitialStateRowsExplicitFormula,
      sameFormula, countFormula, taskFormula, runningFormula] using hclosed
  let innerFormula := countFormula ⋏ (taskFormula ⋏ runningFormula)
  have hsameClosed : sameFormula.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_initial sameFormula innerFormula (by
      simpa only [innerFormula] using hfullClosed)
  have hinnerClosed : innerFormula.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_initial sameFormula innerFormula (by
      simpa only [innerFormula] using hfullClosed)
  have hsameCode :
      (binaryFormulaCode sameFormula).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_initial sameFormula innerFormula).trans
      (by simpa only [innerFormula] using hfullCode)
  have hinnerCode :
      (binaryFormulaCode innerFormula).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_initial sameFormula innerFormula).trans
      (by simpa only [innerFormula] using hfullCode)
  have htaskRunning :
      hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            taskCertificate runningCertificate) <=
        transparentHybridConjunctionPayloadEnvelope initialZeroValuation
          taskFormula runningFormula taskResource runningResource := by
    exact
      transparentHybridConjunctionPayloadBound_le
        (valuation := initialZeroValuation) taskCertificate
        runningCertificate taskResource runningResource htaskResource
        hrunningResource
  let taskRunningCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction taskCertificate
      runningCertificate
  have htaskRunningCertificate :
      hybridFormulaStructuralPayloadBound taskRunningCertificate <=
        transparentHybridConjunctionPayloadEnvelope initialZeroValuation
          taskFormula runningFormula taskResource runningResource := by
    dsimp only [taskRunningCertificate]
    exact htaskRunning
  have hcountTail :=
    transparentHybridConjunctionPayloadBound_le countCertificate
      taskRunningCertificate countResource
      (transparentHybridConjunctionPayloadEnvelope initialZeroValuation
        taskFormula runningFormula taskResource runningResource)
      hcountResource htaskRunningCertificate
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      taskRunningCertificate
  have hinnerFixed :
      hybridFormulaStructuralPayloadBound innerCertificate <=
        hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
          countResource taskResource runningResource := by
    have hclosedGeneral :=
      transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
        initialZeroValuation countFormula taskFormula runningFormula
        countResource taskResource runningResource syntaxResource
        (by simp [syntaxResource, parserInitialStateSyntaxResource])
        (by simpa only [innerFormula] using hinnerClosed)
        (by simpa only [innerFormula] using hinnerCode)
    have hcountTail' :
        hybridFormulaStructuralPayloadBound innerCertificate <=
          transparentHybridConjunctionPayloadEnvelope initialZeroValuation
            countFormula (taskFormula ⋏ runningFormula) countResource
            (transparentHybridConjunctionPayloadEnvelope initialZeroValuation
              taskFormula runningFormula taskResource runningResource) := by
      simpa only [innerCertificate, taskRunningCertificate, countFormula,
        taskFormula, runningFormula] using hcountTail
    exact hcountTail'.trans hclosedGeneral
  have houter :=
    transparentHybridConjunctionPayloadBound_le sameCertificate
      innerCertificate sameResource
      (hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
        countResource taskResource runningResource)
      hsameResource hinnerFixed
  have houterFixed :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      initialZeroValuation sameFormula innerFormula sameResource
      (hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
        countResource taskResource runningResource)
      syntaxResource
      (by simp [syntaxResource, parserInitialStateSyntaxResource])
      hsameClosed hinnerClosed hsameCode hinnerCode
      (by simpa only [innerFormula] using hfullCode)
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast _
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          sameCertificate innerCertificate)) <= _
  unfold parserInitialStateFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, sameFormula, countFormula,
    taskFormula, runningFormula, sameCertificate, countCertificate,
    taskCertificate, runningCertificate, sameResource, countResource,
    taskResource, runningResource, syntaxResource, innerFormula,
    taskRunningCertificate, innerCertificate] using houter.trans houterFixed

#print axioms
  compactUnifiedParserInitialStateRowsClosedFormula_code_length_le_fixed
#print axioms
  compactUnifiedParserInitialStateRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compactUnifiedParserInitialStateRowsFixedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
