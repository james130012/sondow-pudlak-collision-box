import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalSyntaxFixedBounds
import integration.FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds

/-!
# Fully fixed payload for one syntax-task same-rows terminal

Four fixed-width entry leaves and the already fixed syntax-task row leaf are
assembled over the single open row-index variable.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalPayloadFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalSyntaxFixedBounds

private abbrev taskSameRowsZeroValuationPayload : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def taskSameRowsLeftEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (&0 : ValuationTerm) numericBound bitBound))

def taskSameRowsRightEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (‘&0 + 1’ : ValuationTerm) numericBound bitBound))

def taskSameRowsTerminalContextCodePolynomial (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def taskSameRowsTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    taskSameRowsLeftEntryFixedPayloadPolynomial numericBound bitBound
  let rightResource :=
    taskSameRowsRightEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
      (taskSameRowsRowTermCodePolynomial bitBound)
  taskSameRowsTerminalContextCodePolynomial numericBound +
    8 * (leftResource + rightResource + rowResource +
      (binaryNatCode 4).length + 1) + 1

def taskSameRowsTerminalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (taskSameRowsTerminalAssemblySyntaxPolynomial numericBound bitBound)
    (taskSameRowsLeftEntryFixedPayloadPolynomial numericBound bitBound)
    (taskSameRowsRightEntryFixedPayloadPolynomial numericBound bitBound)
    (taskSameRowsLeftEntryFixedPayloadPolynomial numericBound bitBound)
    (taskSameRowsRightEntryFixedPayloadPolynomial numericBound bitBound)
    (taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
      (taskSameRowsRowTermCodePolynomial bitBound))

theorem entry_payload_and_code_le_taskSameRowsFixed
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value) :
    let resource :=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
            numericBound bitBound))
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value) <= resource ∧
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value))).length <= resource := by
  let resource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
        (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
          numericBound bitBound))
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hentry)
  have hresource :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm table)
            (shortBinaryNumeralTerm width) indexTerm
            (shortBinaryNumeralTerm value) <= resource := by
    dsimp only [resource]
    exact
      compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
        valuation table width value indexTerm numericBound bitBound hwidth
        hindexValue hvaluation htableSize hwidthSize hindexSize hvalueSize
        hindexVariables
  have hpayload : hybridFormulaStructuralPayloadBound certificate <=
      resource := by
    dsimp only [certificate, resource]
    exact
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        valuation table width value indexTerm numericBound bitBound hwidth
        hindexValue hvaluation htableSize hwidthSize hindexSize hvalueSize
        hindexVariables hentry
  have hcodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  have hcode :
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value))).length <= resource := by
    simpa only [certificate] using hcodeRaw.trans hpayload
  exact ⟨hresource, hcode⟩

theorem taskRowFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft
      targetRight : Nat) :
    ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
        shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceLeft,
        shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm targetLeft,
        shortBinaryNumeralTerm targetRight]).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data <=
      taskSameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound := by
  let valuation := extendValuation index taskSameRowsZeroValuationPayload
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
  let sourceLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
    (shortBinaryNumeralTerm data.sourceLeft)
  let sourceRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) nextIndexTerm
    (shortBinaryNumeralTerm data.sourceRight)
  let targetLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
    (shortBinaryNumeralTerm data.targetLeft)
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) nextIndexTerm
    (shortBinaryNumeralTerm data.targetRight)
  let rowFormula :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
        shortBinaryNumeralTerm tokenCount,
        shortBinaryNumeralTerm data.sourceLeft,
        shortBinaryNumeralTerm data.sourceRight,
        shortBinaryNumeralTerm data.targetLeft,
        shortBinaryNumeralTerm data.targetRight]
  let leftResource :=
    taskSameRowsLeftEntryFixedPayloadPolynomial numericBound bitBound
  let rightResource :=
    taskSameRowsRightEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
      (taskSameRowsRowTermCodePolynomial bitBound)
  let syntaxResource :=
    taskSameRowsTerminalAssemblySyntaxPolynomial numericBound bitBound
  have hindex : index <= numericBound := by omega
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size hindex).trans hnumericSize
  have hindexSuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size hindexSuccessor).trans hnumericSize
  have hsourceLeftSize : Nat.size data.sourceLeft <= bitBound :=
    (Nat.size_le_size (data.sourceLeft_le.trans htokenCount)).trans
      hnumericSize
  have hsourceRightSize : Nat.size data.sourceRight <= bitBound :=
    (Nat.size_le_size (data.sourceRight_le.trans htokenCount)).trans
      hnumericSize
  have htargetLeftSize : Nat.size data.targetLeft <= bitBound :=
    (Nat.size_le_size (data.targetLeft_le.trans htokenCount)).trans
      hnumericSize
  have htargetRightSize : Nat.size data.targetRight <= bitBound :=
    (Nat.size_le_size (data.targetRight_le.trans htokenCount)).trans
      hnumericSize
  have hsourceIndexValue : termValue valuation sourceIndexTerm = index := by
    simp [valuation, sourceIndexTerm, taskSameRowsZeroValuationPayload]
  have hnextIndexValue : termValue valuation nextIndexTerm = index + 1 := by
    simp [valuation, nextIndexTerm, taskSameRowsZeroValuationPayload,
      termValue_arithmeticAdd, termValue_arithmeticOne]
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hsourceIndexVariables : sourceIndexTerm.freeVariables ⊆ {0} := by
    simp [sourceIndexTerm]
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_eq_union]
    rw [arithmeticOneTerm_freeVariables_eq_empty]
    simp
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation sourceBoundary
      tokenCount data.sourceLeft sourceIndexTerm numericBound bitBound
      htokenCount (by simpa only [hsourceIndexValue] using hindex) hvaluation
      hsourceBoundarySize htokenCountSize
      (by simpa only [hsourceIndexValue] using hindexSize) hsourceLeftSize
      hsourceIndexVariables (by
        simpa only [hsourceIndexValue] using data.sourceLeft_entry) with
    ⟨hsourceLeftResource, hsourceLeftCode⟩
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation sourceBoundary
      tokenCount data.sourceRight nextIndexTerm numericBound bitBound
      htokenCount (by simpa only [hnextIndexValue] using hindexSuccessor)
      hvaluation hsourceBoundarySize htokenCountSize
      (by simpa only [hnextIndexValue] using hindexSuccessorSize)
      hsourceRightSize hnextIndexVariables (by
        simpa only [hnextIndexValue] using data.sourceRight_entry) with
    ⟨hsourceRightResource, hsourceRightCode⟩
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation targetBoundary
      tokenCount data.targetLeft sourceIndexTerm numericBound bitBound
      htokenCount (by simpa only [hsourceIndexValue] using hindex) hvaluation
      htargetBoundarySize htokenCountSize
      (by simpa only [hsourceIndexValue] using hindexSize) htargetLeftSize
      hsourceIndexVariables (by
        simpa only [hsourceIndexValue] using data.targetLeft_entry) with
    ⟨htargetLeftResource, htargetLeftCode⟩
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation targetBoundary
      tokenCount data.targetRight nextIndexTerm numericBound bitBound
      htokenCount (by simpa only [hnextIndexValue] using hindexSuccessor)
      hvaluation htargetBoundarySize htokenCountSize
      (by simpa only [hnextIndexValue] using hindexSuccessorSize)
      htargetRightSize hnextIndexVariables (by
        simpa only [hnextIndexValue] using data.targetRight_entry) with
    ⟨htargetRightResource, htargetRightCode⟩
  have hsourceLeftResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
            (shortBinaryNumeralTerm data.sourceLeft) <= leftResource := by
    simpa only [leftResource, taskSameRowsLeftEntryFixedPayloadPolynomial,
      sourceIndexTerm] using hsourceLeftResource
  have hsourceLeftCodeFixed :
      (binaryFormulaCode sourceLeftFormula).length <= leftResource := by
    simpa only [sourceLeftFormula, leftResource,
      taskSameRowsLeftEntryFixedPayloadPolynomial, sourceIndexTerm] using
      hsourceLeftCode
  have hsourceRightResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) nextIndexTerm
            (shortBinaryNumeralTerm data.sourceRight) <= rightResource := by
    simpa only [rightResource, taskSameRowsRightEntryFixedPayloadPolynomial,
      nextIndexTerm] using hsourceRightResource
  have hsourceRightCodeFixed :
      (binaryFormulaCode sourceRightFormula).length <= rightResource := by
    simpa only [sourceRightFormula, rightResource,
      taskSameRowsRightEntryFixedPayloadPolynomial, nextIndexTerm] using
      hsourceRightCode
  have htargetLeftResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
            (shortBinaryNumeralTerm data.targetLeft) <= leftResource := by
    simpa only [leftResource, taskSameRowsLeftEntryFixedPayloadPolynomial,
      sourceIndexTerm] using htargetLeftResource
  have htargetLeftCodeFixed :
      (binaryFormulaCode targetLeftFormula).length <= leftResource := by
    simpa only [targetLeftFormula, leftResource,
      taskSameRowsLeftEntryFixedPayloadPolynomial, sourceIndexTerm] using
      htargetLeftCode
  have htargetRightResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) nextIndexTerm
            (shortBinaryNumeralTerm data.targetRight) <= rightResource := by
    simpa only [rightResource, taskSameRowsRightEntryFixedPayloadPolynomial,
      nextIndexTerm] using htargetRightResource
  have htargetRightCodeFixed :
      (binaryFormulaCode targetRightFormula).length <= rightResource := by
    simpa only [targetRightFormula, rightResource,
      taskSameRowsRightEntryFixedPayloadPolynomial, nextIndexTerm] using
      htargetRightCode
  have hrowResource :
      compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation
          tokenTable width tokenCount data.sourceLeft data.sourceRight
          data.targetLeft data.targetRight <= rowResource := by
    dsimp only [rowResource]
    exact
      compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope_le_fullyFixed
        valuation tokenTable width tokenCount data.sourceLeft data.sourceRight
        data.targetLeft data.targetRight numericBound bitBound data.row_eq
        hwidth htokenCount htokenTableSize hnumericSize
  have hrowCode : (binaryFormulaCode rowFormula).length <= rowResource := by
    dsimp only [rowFormula, rowResource]
    exact compactAdditiveSyntaxTaskRowEqFormula_code_length_le_fullyFixed
      valuation tokenTable width tokenCount data.sourceLeft data.sourceRight
      data.targetLeft data.targetRight numericBound bitBound data.row_eq
      hwidth htokenCount htokenTableSize hnumericSize
  have hsourceLeftVariables : sourceLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceLeftFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hsourceIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hsourceRightVariables : sourceRightFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceRightFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hnextIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetLeftVariables : targetLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [targetLeftFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hsourceIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetRightVariables : targetRightFormula.freeVariables ⊆ {0} := by
    dsimp only [targetRightFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hnextIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hrowVariables : rowFormula.freeVariables ⊆ {0} := by
    rw [show rowFormula.freeVariables = ∅ by
      dsimp only [rowFormula]
      exact taskRowFormula_freeVariables_eq_empty _ _ _ _ _ _ _]
    simp
  have htotalVariables :
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula)))).freeVariables ⊆ {0} := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hsourceLeftVariables
      (Finset.union_subset hsourceRightVariables
        (Finset.union_subset htargetLeftVariables
          (Finset.union_subset htargetRightVariables hrowVariables)))
  have htail4CodeRaw :=
    binaryFormulaCode_and_length_le_local targetRightFormula rowFormula
  have htail3CodeRaw :=
    binaryFormulaCode_and_length_le_local targetLeftFormula
      (targetRightFormula ⋏ rowFormula)
  have htail2CodeRaw :=
    binaryFormulaCode_and_length_le_local sourceRightFormula
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
  have htotalCodeRaw :=
    binaryFormulaCode_and_length_le_local sourceLeftFormula
      (sourceRightFormula ⋏
        (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
  have htotalCode :
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        syntaxResource := by
    simp only [syntaxResource, taskSameRowsTerminalAssemblySyntaxPolynomial]
    omega
  have hpositive : 1 <= syntaxResource := by
    simp only [syntaxResource, taskSameRowsTerminalAssemblySyntaxPolynomial]
    omega
  have hcontext :
      taskSameRowsTerminalContextCodePolynomial numericBound <=
        syntaxResource := by
    simp only [syntaxResource, taskSameRowsTerminalAssemblySyntaxPolynomial]
    omega
  have hgeneral :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_singletonGeneral
      valuation sourceLeftFormula sourceRightFormula targetLeftFormula
      targetRightFormula rowFormula
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
          (shortBinaryNumeralTerm data.sourceLeft))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) nextIndexTerm
          (shortBinaryNumeralTerm data.sourceRight))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
          (shortBinaryNumeralTerm data.targetLeft))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) nextIndexTerm
          (shortBinaryNumeralTerm data.targetRight))
      (compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation
        tokenTable width tokenCount data.sourceLeft data.sourceRight
        data.targetLeft data.targetRight)
      syntaxResource numericBound hpositive hvaluation htotalVariables
      htotalCode (by
        simpa only [taskSameRowsTerminalContextCodePolynomial] using hcontext)
  have hmono :
      hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm sourceBoundary)
              (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
              (shortBinaryNumeralTerm data.sourceLeft))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm sourceBoundary)
              (shortBinaryNumeralTerm tokenCount) nextIndexTerm
              (shortBinaryNumeralTerm data.sourceRight))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
              (shortBinaryNumeralTerm data.targetLeft))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) nextIndexTerm
              (shortBinaryNumeralTerm data.targetRight))
          (compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation
            tokenTable width tokenCount data.sourceLeft data.sourceRight
            data.targetLeft data.targetRight) <=
        taskSameRowsTerminalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold taskSameRowsTerminalFullyFixedPayloadPolynomial
      hybridFiveConjunctionGeneralPayloadEnvelope
      hybridConjunctionGeneralPayloadEnvelope
    simp only [syntaxResource]
    omega
  unfold compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope
  dsimp only [valuation, sourceIndexTerm, nextIndexTerm, sourceLeftFormula,
    sourceRightFormula, targetLeftFormula, targetRightFormula, rowFormula]
  exact hgeneral.trans hmono

#print axioms entry_payload_and_code_le_taskSameRowsFixed
#print axioms taskRowFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalPayloadFixedBounds
