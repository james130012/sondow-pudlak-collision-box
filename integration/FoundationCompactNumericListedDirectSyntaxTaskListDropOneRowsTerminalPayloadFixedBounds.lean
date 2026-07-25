import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalPayloadFixedBounds

/-!
# Fully fixed payload for one syntax-task drop-one terminal

Four fixed-width entries at `1+i`, `2+i`, `i`, and `i+1`, together with the
checked task-row equality, are assembled over the single open row variable.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalPayloadFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalPayloadFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalSyntaxFixedBounds

private abbrev dropOneZeroValuation : Nat -> Nat :=
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

private theorem fixedNumeralOne_value (valuation : Nat -> Nat) :
    termValue valuation (fixedNumeralTerm 1) = 1 := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  simp

private theorem fixedNumeralOne_freeVariables_eq_empty :
    (fixedNumeralTerm 1).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

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
    · exact Finset.mem_biUnion.mpr
        ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticOne_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def taskDropOneSourceLeftEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let indexTerm : ValuationTerm := ‘!!(fixedNumeralTerm 1) + &0’
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
        numericBound bitBound))

def taskDropOneSourceRightEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let indexTerm : ValuationTerm := ‘(!!(fixedNumeralTerm 1) + &0) + 1’
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
        numericBound bitBound))

def taskDropOneTargetLeftEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (&0 : ValuationTerm) numericBound bitBound))

def taskDropOneTargetRightEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (‘&0 + 1’ : ValuationTerm) numericBound bitBound))

def taskDropOneTerminalContextCodePolynomial (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def taskDropOneTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  taskDropOneSourceLeftEntryFixedPayloadPolynomial numericBound bitBound +
    taskDropOneSourceRightEntryFixedPayloadPolynomial numericBound bitBound +
    taskDropOneTargetLeftEntryFixedPayloadPolynomial numericBound bitBound +
    taskDropOneTargetRightEntryFixedPayloadPolynomial numericBound bitBound +
    taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
      (taskSameRowsRowTermCodePolynomial bitBound) +
    taskDropOneTerminalContextCodePolynomial numericBound +
    4 * (binaryNatCode 4).length + 1

def taskDropOneTerminalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (taskDropOneTerminalAssemblySyntaxPolynomial numericBound bitBound)
    (taskDropOneSourceLeftEntryFixedPayloadPolynomial numericBound bitBound)
    (taskDropOneSourceRightEntryFixedPayloadPolynomial numericBound bitBound)
    (taskDropOneTargetLeftEntryFixedPayloadPolynomial numericBound bitBound)
    (taskDropOneTargetRightEntryFixedPayloadPolynomial numericBound bitBound)
    (taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
      (taskSameRowsRowTermCodePolynomial bitBound))

theorem
    compactAdditiveSyntaxTaskListDropOneRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveSyntaxTaskListDropRowData tokenTable width
      tokenCount sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceNextIndex : 1 + index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary 1 index
        data <=
      taskDropOneTerminalFullyFixedPayloadPolynomial numericBound bitBound := by
  let valuation := extendValuation index dropOneZeroValuation
  let sourceIndexTerm : ValuationTerm := ‘!!(fixedNumeralTerm 1) + &0’
  let sourceNextTerm : ValuationTerm :=
    ‘(!!(fixedNumeralTerm 1) + &0) + 1’
  let targetIndexTerm : ValuationTerm := &0
  let targetNextTerm : ValuationTerm := ‘&0 + 1’
  let sourceLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
    (shortBinaryNumeralTerm data.sourceLeft)
  let sourceRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) sourceNextTerm
    (shortBinaryNumeralTerm data.sourceRight)
  let targetLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) targetIndexTerm
    (shortBinaryNumeralTerm data.targetLeft)
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) targetNextTerm
    (shortBinaryNumeralTerm data.targetRight)
  let rowFormula :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
        shortBinaryNumeralTerm tokenCount,
        shortBinaryNumeralTerm data.sourceLeft,
        shortBinaryNumeralTerm data.sourceRight,
        shortBinaryNumeralTerm data.targetLeft,
        shortBinaryNumeralTerm data.targetRight]
  let sourceLeftResource :=
    taskDropOneSourceLeftEntryFixedPayloadPolynomial numericBound bitBound
  let sourceRightResource :=
    taskDropOneSourceRightEntryFixedPayloadPolynomial numericBound bitBound
  let targetLeftResource :=
    taskDropOneTargetLeftEntryFixedPayloadPolynomial numericBound bitBound
  let targetRightResource :=
    taskDropOneTargetRightEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
      (taskSameRowsRowTermCodePolynomial bitBound)
  let syntaxResource :=
    taskDropOneTerminalAssemblySyntaxPolynomial numericBound bitBound
  have hindex : index <= numericBound := by omega
  have hsourceIndex : 1 + index <= numericBound := by omega
  have htargetNext : index + 1 <= numericBound := by omega
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size hindex).trans hnumericSize
  have hsourceIndexSize : Nat.size (1 + index) <= bitBound :=
    (Nat.size_le_size hsourceIndex).trans hnumericSize
  have hsourceNextSize : Nat.size (1 + index + 1) <= bitBound :=
    (Nat.size_le_size hsourceNextIndex).trans hnumericSize
  have htargetNextSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size htargetNext).trans hnumericSize
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
  have hsourceIndexValue :
      termValue valuation sourceIndexTerm = 1 + index := by
    simp only [valuation, sourceIndexTerm, termValue_arithmeticAdd,
      fixedNumeralOne_value]
    simp [dropOneZeroValuation]
  have hsourceNextValue :
      termValue valuation sourceNextTerm = 1 + index + 1 := by
    simp only [valuation, sourceNextTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne, fixedNumeralOne_value]
    simp [dropOneZeroValuation]
  have htargetIndexValue :
      termValue valuation targetIndexTerm = index := by
    simp [valuation, targetIndexTerm, dropOneZeroValuation]
  have htargetNextValue :
      termValue valuation targetNextTerm = index + 1 := by
    simp only [valuation, targetNextTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne]
    simp [dropOneZeroValuation]
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hsourceIndexVariables : sourceIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [sourceIndexTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      fixedNumeralOne_freeVariables_eq_empty]
    simp
  have hsourceNextVariables : sourceNextTerm.freeVariables ⊆ {0} := by
    dsimp only [sourceNextTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      fixedNumeralOne_freeVariables_eq_empty,
      arithmeticOne_freeVariables_eq_empty]
    simp
  have htargetIndexVariables : targetIndexTerm.freeVariables ⊆ {0} := by
    simp [targetIndexTerm]
  have htargetNextVariables : targetNextTerm.freeVariables ⊆ {0} := by
    dsimp only [targetNextTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      arithmeticOne_freeVariables_eq_empty]
    simp
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation sourceBoundary
      tokenCount data.sourceLeft sourceIndexTerm numericBound bitBound
      htokenCount (by simpa only [hsourceIndexValue] using hsourceIndex)
      hvaluation hsourceBoundarySize htokenCountSize
      (by simpa only [hsourceIndexValue] using hsourceIndexSize)
      hsourceLeftSize hsourceIndexVariables (by
        simpa only [hsourceIndexValue] using data.sourceLeft_entry) with
    ⟨hsourceLeftResource, hsourceLeftCode⟩
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation sourceBoundary
      tokenCount data.sourceRight sourceNextTerm numericBound bitBound
      htokenCount (by
        simpa only [hsourceNextValue] using hsourceNextIndex)
      hvaluation hsourceBoundarySize htokenCountSize
      (by simpa only [hsourceNextValue] using hsourceNextSize)
      hsourceRightSize hsourceNextVariables (by
        simpa only [hsourceNextValue] using data.sourceRight_entry) with
    ⟨hsourceRightResource, hsourceRightCode⟩
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation targetBoundary
      tokenCount data.targetLeft targetIndexTerm numericBound bitBound
      htokenCount (by simpa only [htargetIndexValue] using hindex)
      hvaluation htargetBoundarySize htokenCountSize
      (by simpa only [htargetIndexValue] using hindexSize)
      htargetLeftSize htargetIndexVariables (by
        simpa only [htargetIndexValue] using data.targetLeft_entry) with
    ⟨htargetLeftResource, htargetLeftCode⟩
  rcases entry_payload_and_code_le_taskSameRowsFixed valuation targetBoundary
      tokenCount data.targetRight targetNextTerm numericBound bitBound
      htokenCount (by simpa only [htargetNextValue] using htargetNext)
      hvaluation htargetBoundarySize htokenCountSize
      (by simpa only [htargetNextValue] using htargetNextSize)
      htargetRightSize htargetNextVariables (by
        simpa only [htargetNextValue] using data.targetRight_entry) with
    ⟨htargetRightResource, htargetRightCode⟩
  have hsourceLeftResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
            (shortBinaryNumeralTerm data.sourceLeft) <=
        sourceLeftResource := by
    simpa only [sourceLeftResource,
      taskDropOneSourceLeftEntryFixedPayloadPolynomial, sourceIndexTerm] using
      hsourceLeftResource
  have hsourceLeftCodeFixed :
      (binaryFormulaCode sourceLeftFormula).length <= sourceLeftResource := by
    simpa only [sourceLeftFormula, sourceLeftResource,
      taskDropOneSourceLeftEntryFixedPayloadPolynomial, sourceIndexTerm] using
      hsourceLeftCode
  have hsourceRightResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) sourceNextTerm
            (shortBinaryNumeralTerm data.sourceRight) <=
        sourceRightResource := by
    simpa only [sourceRightResource,
      taskDropOneSourceRightEntryFixedPayloadPolynomial, sourceNextTerm] using
      hsourceRightResource
  have hsourceRightCodeFixed :
      (binaryFormulaCode sourceRightFormula).length <=
        sourceRightResource := by
    simpa only [sourceRightFormula, sourceRightResource,
      taskDropOneSourceRightEntryFixedPayloadPolynomial, sourceNextTerm] using
      hsourceRightCode
  have htargetLeftResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) targetIndexTerm
            (shortBinaryNumeralTerm data.targetLeft) <=
        targetLeftResource := by
    simpa only [targetLeftResource,
      taskDropOneTargetLeftEntryFixedPayloadPolynomial, targetIndexTerm] using
      htargetLeftResource
  have htargetLeftCodeFixed :
      (binaryFormulaCode targetLeftFormula).length <=
        targetLeftResource := by
    simpa only [targetLeftFormula, targetLeftResource,
      taskDropOneTargetLeftEntryFixedPayloadPolynomial, targetIndexTerm] using
      htargetLeftCode
  have htargetRightResourceFixed :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) targetNextTerm
            (shortBinaryNumeralTerm data.targetRight) <=
        targetRightResource := by
    simpa only [targetRightResource,
      taskDropOneTargetRightEntryFixedPayloadPolynomial, targetNextTerm] using
      htargetRightResource
  have htargetRightCodeFixed :
      (binaryFormulaCode targetRightFormula).length <=
        targetRightResource := by
    simpa only [targetRightFormula, targetRightResource,
      taskDropOneTargetRightEntryFixedPayloadPolynomial, targetNextTerm] using
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
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _) hsourceIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hsourceRightVariables : sourceRightFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceRightFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _) hsourceNextVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetLeftVariables : targetLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [targetLeftFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _) htargetIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetRightVariables : targetRightFormula.freeVariables ⊆ {0} := by
    dsimp only [targetRightFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _) htargetNextVariables
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
    dsimp only [syntaxResource, sourceLeftResource, sourceRightResource,
      targetLeftResource, targetRightResource, rowResource]
    unfold taskDropOneTerminalAssemblySyntaxPolynomial
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold taskDropOneTerminalAssemblySyntaxPolynomial
    omega
  have hcontext :
      taskDropOneTerminalContextCodePolynomial numericBound <=
        syntaxResource := by
    dsimp only [syntaxResource]
    unfold taskDropOneTerminalAssemblySyntaxPolynomial
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
          (shortBinaryNumeralTerm tokenCount) sourceNextTerm
          (shortBinaryNumeralTerm data.sourceRight))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) targetIndexTerm
          (shortBinaryNumeralTerm data.targetLeft))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) targetNextTerm
          (shortBinaryNumeralTerm data.targetRight))
      (compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation
        tokenTable width tokenCount data.sourceLeft data.sourceRight
        data.targetLeft data.targetRight)
      syntaxResource numericBound hpositive hvaluation htotalVariables
      htotalCode (by
        simpa only [taskDropOneTerminalContextCodePolynomial] using hcontext)
  have hmono :
      hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm sourceBoundary)
              (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
              (shortBinaryNumeralTerm data.sourceLeft))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm sourceBoundary)
              (shortBinaryNumeralTerm tokenCount) sourceNextTerm
              (shortBinaryNumeralTerm data.sourceRight))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) targetIndexTerm
              (shortBinaryNumeralTerm data.targetLeft))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) targetNextTerm
              (shortBinaryNumeralTerm data.targetRight))
          (compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation
            tokenTable width tokenCount data.sourceLeft data.sourceRight
            data.targetLeft data.targetRight) <=
        taskDropOneTerminalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold taskDropOneTerminalFullyFixedPayloadPolynomial
      hybridFiveConjunctionGeneralPayloadEnvelope
      hybridConjunctionGeneralPayloadEnvelope
    dsimp only [syntaxResource, sourceLeftResource, sourceRightResource,
      targetLeftResource, targetRightResource, rowResource]
    omega
  unfold
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
  dsimp only [valuation, sourceIndexTerm, sourceNextTerm, targetIndexTerm,
    targetNextTerm, sourceLeftFormula, sourceRightFormula, targetLeftFormula,
    targetRightFormula, rowFormula]
  exact hgeneral.trans hmono

#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsTerminalStructuralPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalPayloadFixedBounds
