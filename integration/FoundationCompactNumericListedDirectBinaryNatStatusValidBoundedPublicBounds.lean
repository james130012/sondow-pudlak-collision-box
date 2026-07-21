import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatSizePublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds

/-!
# Public structural resources for bounded binary-Nat status validity

This file starts the public resource closure of the completed-status branch.
The area inequality is reduced to the two checked positive atomic branches of
the native `<=` disjunction and charges both possible assemblies explicitly.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusCases

local notation "zeroValuation" =>
  FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate.zeroValuation

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
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
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticMulTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Mul.mul left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (left right : ValuationTerm) :
    termValue zeroValuation ‘!!left + !!right’ =
      termValue zeroValuation left + termValue zeroValuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add zeroValuation ![left, right]

private theorem termValue_arithmeticMul
    (left right : ValuationTerm) :
    termValue zeroValuation ‘!!left * !!right’ =
      termValue zeroValuation left * termValue zeroValuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul zeroValuation ![left, right]

private theorem termValue_arithmeticOne :
    termValue zeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one zeroValuation ![]

def valuationLeStructuralPayloadPolynomial
    (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables zeroValuation
  compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      zeroValuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_public
    (leftTerm rightTerm : ValuationTerm)
    (hleft : leftTerm.freeVariables = ∅)
    (hright : rightTerm.freeVariables = ∅)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (valuationLeCertificate leftTerm rightTerm hle) ≤
      valuationLeStructuralPayloadPolynomial leftTerm rightTerm := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change leftTerm.freeVariables ⊆ {0}
    rw [hleft]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [hright]
    simp
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      zeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      zeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm
  · simp only [valuationLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold valuationLeStructuralPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    omega
  · simp only [valuationLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold valuationLeStructuralPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    omega

def completedAreaStructuralPayloadPolynomial
    (tokenCount outputCount outputBoundarySize : Nat) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  valuationLeStructuralPayloadPolynomial
    (shortBinaryNumeralTerm outputBoundarySize) rightTerm

theorem completedAreaCertificate_structuralPayloadBound_le_public
    (tokenCount outputCount outputBoundarySize : Nat)
    (hbound : outputBoundarySize ≤ (outputCount + 1) * tokenCount) :
    hybridFormulaStructuralPayloadBound
        (completedAreaCertificate tokenCount outputCount outputBoundarySize
          hbound) ≤
      completedAreaStructuralPayloadPolynomial
        tokenCount outputCount outputBoundarySize := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  have hleft :
      (shortBinaryNumeralTerm outputBoundarySize).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty outputBoundarySize
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticMulTerm_freeVariables, arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hle : termValue zeroValuation
      (shortBinaryNumeralTerm outputBoundarySize) ≤
      termValue zeroValuation rightTerm := by
    simpa [rightTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticMul,
      termValue_arithmeticOne]
      using hbound
  have hpublic := valuationLeCertificate_structuralPayloadBound_le_public
    (shortBinaryNumeralTerm outputBoundarySize) rightTerm hleft hright hle
  change hybridFormulaStructuralPayloadBound
      (valuationLeCertificate
        (shortBinaryNumeralTerm outputBoundarySize) rightTerm hle) ≤ _
  unfold completedAreaStructuralPayloadPolynomial
  dsimp only [rightTerm] at hpublic ⊢
  exact hpublic

noncomputable def compactBinaryNatCompletedStatusStructuralPayloadEnvelope
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : Nat :=
  let prefixFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount start outputStart
  let layoutFormula :=
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.compactAdditiveStructuredListLayoutClosedFormula
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitFormula :=
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsClosedFormula
      tokenCount outputCount outputBoundary
  let sizeFormula :=
    FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.compactNatSizeClosedFormula
      outputBoundarySize outputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let prefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart
  let layoutResource :=
    compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitResource :=
    compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope
      tokenCount outputCount outputBoundary
  let sizeResource := compactNatSizeStructuralPayloadPolynomial
    outputBoundarySize outputBoundary
  let areaResource := completedAreaStructuralPayloadPolynomial
    tokenCount outputCount outputBoundarySize
  let sizeAreaResource := hybridConjunctionStructuralPayloadEnvelope
    zeroValuation sizeFormula areaFormula sizeResource areaResource
  let unitTailResource := hybridConjunctionStructuralPayloadEnvelope
    zeroValuation unitFormula (sizeFormula ⋏ areaFormula)
    unitResource sizeAreaResource
  let layoutTailResource := hybridConjunctionStructuralPayloadEnvelope
    zeroValuation layoutFormula
    (unitFormula ⋏ (sizeFormula ⋏ areaFormula))
    layoutResource unitTailResource
  hybridConjunctionStructuralPayloadEnvelope zeroValuation prefixFormula
    (layoutFormula ⋏ (unitFormula ⋏ (sizeFormula ⋏ areaFormula)))
    prefixResource layoutTailResource

theorem
    compactBinaryNatCompletedStatusExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf
          outputStart outputBoundary outputBoundarySize outputCount)) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatCompletedStatusExplicitHybridCertificate
          tokenTable width tokenCount start finish outputStart outputBoundary
            outputBoundarySize outputCount hcompleted) <=
      compactBinaryNatCompletedStatusStructuralPayloadEnvelope
        tokenTable width tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount := by
  let prefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hcompleted.1
  let layoutCertificate :=
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
        hcompleted.2.1
  let unitCertificate :=
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount outputCount outputBoundary hcompleted.2.2.1
  let sizeCertificate :=
    FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.compactNatSizeExplicitHybridCertificateOfEq
      outputBoundarySize outputBoundary hcompleted.2.2.2.1
  let areaCertificate := completedAreaCertificate
    tokenCount outputCount outputBoundarySize hcompleted.2.2.2.2
  have hprefix :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount start outputStart hcompleted.1
  have hlayout :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
        hcompleted.2.1
  have hunitTransparent :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount outputCount outputBoundary hcompleted.2.2.1
  have hunitPublic :=
    compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_publicFinite
      tokenCount outputCount outputBoundary hcompleted.2.2.1
  have hunit := hunitTransparent.trans hunitPublic
  have hsize :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      outputBoundarySize outputBoundary hcompleted.2.2.2.1
  have harea := completedAreaCertificate_structuralPayloadBound_le_public
    tokenCount outputCount outputBoundarySize hcompleted.2.2.2.2
  have hsizeArea := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := zeroValuation) sizeCertificate areaCertificate _ _
    hsize harea
  have hunitTail := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := zeroValuation) unitCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sizeCertificate areaCertificate) _ _ hunit hsizeArea
  have hlayoutTail := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := zeroValuation) layoutCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      unitCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        sizeCertificate areaCertificate)) _ _ hlayout hunitTail
  have hcompletedBound := hybridConjunctionStructuralPayloadBound_le_envelope
    (valuation := zeroValuation) prefixCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      layoutCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        unitCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          sizeCertificate areaCertificate))) _ _ hprefix hlayoutTail
  simpa only [compactBinaryNatCompletedStatusExplicitHybridCertificate,
    compactBinaryNatCompletedStatusStructuralPayloadEnvelope,
    prefixCertificate, layoutCertificate, unitCertificate,
    sizeCertificate, areaCertificate] using hcompletedBound

def hybridDisjunctionLeftStructuralPayloadEnvelope
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource : Nat) : Nat :=
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  leftResource + weakeningFullAssemblyCost (insert left Gamma) +
    disjunctionFullAssemblyCost Gamma left right

theorem hybridDisjunctionLeftStructuralPayloadBound_le_envelope
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (leftResource : Nat)
    (hleft : hybridFormulaStructuralPayloadBound leftCertificate <=
      leftResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := right) leftCertificate) <=
      hybridDisjunctionLeftStructuralPayloadEnvelope
        valuation left right leftResource := by
  simp only [hybridFormulaStructuralPayloadBound]
  unfold hybridDisjunctionLeftStructuralPayloadEnvelope
  dsimp only
  omega

def hybridDisjunctionRightStructuralPayloadEnvelope
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (rightResource : Nat) : Nat :=
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  rightResource + weakeningFullAssemblyCost (insert right Gamma) +
    disjunctionFullAssemblyCost Gamma left right

theorem hybridDisjunctionRightStructuralPayloadBound_le_envelope
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (rightResource : Nat)
    (hright : hybridFormulaStructuralPayloadBound rightCertificate <=
      rightResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := left) rightCertificate) <=
      hybridDisjunctionRightStructuralPayloadEnvelope
        valuation left right rightResource := by
  simp only [hybridFormulaStructuralPayloadBound]
  unfold hybridDisjunctionRightStructuralPayloadEnvelope
  dsimp only
  omega

noncomputable def
    compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) : Nat := by
  classical
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let completedFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
        tokenTable width tokenCount start data.outputStart ⋏
      (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.compactAdditiveStructuredListLayoutClosedFormula
          tokenTable width tokenCount data.outputStart data.outputCount finish
            data.outputBoundary ⋏
        (FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsClosedFormula
            tokenCount data.outputCount data.outputBoundary ⋏
          (FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.compactNatSizeClosedFormula
              data.outputBoundarySize data.outputBoundary ⋏
            “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
              (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)”)))
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · exact hybridDisjunctionLeftStructuralPayloadEnvelope zeroValuation
      runningFormula (failedFormula ⋎ completedFormula)
      (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
        tokenTable width tokenCount start finish)
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · exact hybridDisjunctionRightStructuralPayloadEnvelope zeroValuation
        runningFormula (failedFormula ⋎ completedFormula)
        (hybridDisjunctionLeftStructuralPayloadEnvelope zeroValuation
          failedFormula completedFormula
          (compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
            tokenTable width tokenCount start finish))
    · exact hybridDisjunctionRightStructuralPayloadEnvelope zeroValuation
        runningFormula (failedFormula ⋎ completedFormula)
        (hybridDisjunctionRightStructuralPayloadEnvelope zeroValuation
          failedFormula completedFormula
          (compactBinaryNatCompletedStatusStructuralPayloadEnvelope
            tokenTable width tokenCount start finish data.outputStart
              data.outputBoundary data.outputBoundarySize data.outputCount))

theorem
    compactBinaryNatStatusValidBoundedTerminalPartsOfData_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatStatusValidBoundedTerminalPartsOfData
          tokenTable width tokenCount start finish valueBound data) <=
      compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
        tokenTable width tokenCount start finish valueBound data := by
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · let runningCertificate :=
      compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount start finish hrunning
    have hrunningBound :=
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenTable width tokenCount start finish hrunning
    have houter := hybridDisjunctionLeftStructuralPayloadBound_le_envelope
      (valuation := zeroValuation)
      (right :=
        compactBinaryNatFailedStatusSliceClosedFormula
            tokenTable width tokenCount start finish ⋎
          (compactBinaryNatCompletedStatusPrefixClosedFormula
              tokenTable width tokenCount start data.outputStart ⋏
            (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.compactAdditiveStructuredListLayoutClosedFormula
                tokenTable width tokenCount data.outputStart data.outputCount
                  finish data.outputBoundary ⋏
              (FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsClosedFormula
                  tokenCount data.outputCount data.outputBoundary ⋏
                (FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.compactNatSizeClosedFormula
                    data.outputBoundarySize data.outputBoundary ⋏
                  “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”)))))
      runningCertificate _ hrunningBound
    simpa [compactBinaryNatStatusValidBoundedTerminalPartsOfData,
      compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData,
      hrunning, runningCertificate] using houter
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · let failedCertificate :=
        compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hfailed
      have hfailedBound :=
        compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount start finish hfailed
      have hinner := hybridDisjunctionLeftStructuralPayloadBound_le_envelope
        (valuation := zeroValuation)
        (right :=
          compactBinaryNatCompletedStatusPrefixClosedFormula
              tokenTable width tokenCount start data.outputStart ⋏
            (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.compactAdditiveStructuredListLayoutClosedFormula
                tokenTable width tokenCount data.outputStart data.outputCount
                  finish data.outputBoundary ⋏
              (FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsClosedFormula
                  tokenCount data.outputCount data.outputBoundary ⋏
                (FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.compactNatSizeClosedFormula
                    data.outputBoundarySize data.outputBoundary ⋏
                  “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”))))
        failedCertificate _ hfailedBound
      have houter := hybridDisjunctionRightStructuralPayloadBound_le_envelope
        (valuation := zeroValuation)
        (left := compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount start finish)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            compactBinaryNatCompletedStatusPrefixClosedFormula
                tokenTable width tokenCount start data.outputStart ⋏
              (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.compactAdditiveStructuredListLayoutClosedFormula
                  tokenTable width tokenCount data.outputStart data.outputCount
                    finish data.outputBoundary ⋏
                (FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsClosedFormula
                    tokenCount data.outputCount data.outputBoundary ⋏
                  (FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.compactNatSizeClosedFormula
                      data.outputBoundarySize data.outputBoundary ⋏
                    “!!(shortBinaryNumeralTerm data.outputBoundarySize) ≤
                      (!!(shortBinaryNumeralTerm data.outputCount) + 1) *
                        !!(shortBinaryNumeralTerm tokenCount)”))))
          failedCertificate) _ hinner
      simpa [compactBinaryNatStatusValidBoundedTerminalPartsOfData,
        compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData,
        hrunning, hfailed, failedCertificate] using houter
    · let hcompleted := compactBinaryNatCompletedStatusValidRows_of_data
        data hrunning hfailed
      let completedCertificate :=
        compactBinaryNatCompletedStatusExplicitHybridCertificate
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize data.outputCount
              hcompleted
      have hcompletedBound :=
        compactBinaryNatCompletedStatusExplicitHybridCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize data.outputCount
              hcompleted
      have hinner := hybridDisjunctionRightStructuralPayloadBound_le_envelope
        (valuation := zeroValuation)
        (left := compactBinaryNatFailedStatusSliceClosedFormula
          tokenTable width tokenCount start finish)
        completedCertificate _ hcompletedBound
      have houter := hybridDisjunctionRightStructuralPayloadBound_le_envelope
        (valuation := zeroValuation)
        (left := compactBinaryNatRunningStatusSliceClosedFormula
          tokenTable width tokenCount start finish)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := compactBinaryNatFailedStatusSliceClosedFormula
            tokenTable width tokenCount start finish)
          completedCertificate) _ hinner
      simpa [compactBinaryNatStatusValidBoundedTerminalPartsOfData,
        compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData,
        hrunning, hfailed, hcompleted, completedCertificate] using houter

/-! ## Removing status-data and branch dependence by a finite public envelope -/

def compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let completedFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
        tokenTable width tokenCount start outputStart ⋏
      (FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.compactAdditiveStructuredListLayoutClosedFormula
          tokenTable width tokenCount outputStart outputCount finish
            outputBoundary ⋏
        (FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.compactAdditiveUnitBoundaryRowsClosedFormula
            tokenCount outputCount outputBoundary ⋏
          (FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.compactNatSizeClosedFormula
              outputBoundarySize outputBoundary ⋏
            “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
              (!!(shortBinaryNumeralTerm outputCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)”)))
  let runningResource := hybridDisjunctionLeftStructuralPayloadEnvelope
    zeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
      tokenTable width tokenCount start finish)
  let failedResource := hybridDisjunctionRightStructuralPayloadEnvelope
    zeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (hybridDisjunctionLeftStructuralPayloadEnvelope zeroValuation
      failedFormula completedFormula
      (compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
        tokenTable width tokenCount start finish))
  let completedResource := hybridDisjunctionRightStructuralPayloadEnvelope
    zeroValuation runningFormula (failedFormula ⋎ completedFormula)
    (hybridDisjunctionRightStructuralPayloadEnvelope zeroValuation
      failedFormula completedFormula
      (compactBinaryNatCompletedStatusStructuralPayloadEnvelope
        tokenTable width tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount))
  runningResource + failedResource + completedResource

theorem
    compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData_le_allBranches
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
        tokenTable width tokenCount start finish valueBound data <=
      compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
        tokenTable width tokenCount start finish data.outputStart
          data.outputBoundary data.outputBoundarySize data.outputCount := by
  classical
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · simp only [
      compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData,
      compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues,
      hrunning, dite_true]
    omega
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · simp only [
        compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData,
        compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues,
        hrunning, hfailed, dite_false, dite_true]
      omega
    · simp only [
        compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData,
        compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues,
        hrunning, hfailed, dite_false]
      omega

def compactBinaryNatStatusValidBoundedTerminalPublicFiniteEnvelope
    (tokenTable width tokenCount start finish valueBound : Nat) : Nat :=
  (Finset.range (valueBound + 1)).sum fun outputStart =>
    (Finset.range (valueBound + 1)).sum fun outputBoundary =>
      (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
        (Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
            tokenTable width tokenCount start finish outputStart outputBoundary
              outputBoundarySize outputCount

theorem
    compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData_le_publicFinite
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
        tokenTable width tokenCount start finish valueBound data <=
      compactBinaryNatStatusValidBoundedTerminalPublicFiniteEnvelope
        tokenTable width tokenCount start finish valueBound := by
  have hbranch :=
    compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData_le_allBranches
      tokenTable width tokenCount start finish valueBound data
  have hcount :
      compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize data.outputCount <=
        (Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
            tokenTable width tokenCount start finish data.outputStart
              data.outputBoundary data.outputBoundarySize outputCount := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
          tokenTable width tokenCount start finish data.outputStart
            data.outputBoundary data.outputBoundarySize candidate))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputCount_le_valueBound))
  have hsize :
      ((Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
            tokenTable width tokenCount start finish data.outputStart
              data.outputBoundary data.outputBoundarySize outputCount) <=
        (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
          (Finset.range (valueBound + 1)).sum fun outputCount =>
            compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
              tokenTable width tokenCount start finish data.outputStart
                data.outputBoundary outputBoundarySize outputCount := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (valueBound + 1)).sum fun outputCount =>
          compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
            tokenTable width tokenCount start finish data.outputStart
              data.outputBoundary candidate outputCount))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputBoundarySize_le_valueBound))
  have hboundary :
      ((Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
          (Finset.range (valueBound + 1)).sum fun outputCount =>
            compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
              tokenTable width tokenCount start finish data.outputStart
                data.outputBoundary outputBoundarySize outputCount) <=
        (Finset.range (valueBound + 1)).sum fun outputBoundary =>
          (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
            (Finset.range (valueBound + 1)).sum fun outputCount =>
              compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
                tokenTable width tokenCount start finish data.outputStart
                  outputBoundary outputBoundarySize outputCount := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
          (Finset.range (valueBound + 1)).sum fun outputCount =>
            compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
              tokenTable width tokenCount start finish data.outputStart
                candidate outputBoundarySize outputCount))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputBoundary_le_valueBound))
  have hstart :
      ((Finset.range (valueBound + 1)).sum fun outputBoundary =>
          (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
            (Finset.range (valueBound + 1)).sum fun outputCount =>
              compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
                tokenTable width tokenCount start finish data.outputStart
                  outputBoundary outputBoundarySize outputCount) <=
        compactBinaryNatStatusValidBoundedTerminalPublicFiniteEnvelope
          tokenTable width tokenCount start finish valueBound := by
    unfold compactBinaryNatStatusValidBoundedTerminalPublicFiniteEnvelope
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (valueBound + 1)).sum fun outputBoundary =>
          (Finset.range (valueBound + 1)).sum fun outputBoundarySize =>
            (Finset.range (valueBound + 1)).sum fun outputCount =>
              compactBinaryNatStatusValidBoundedTerminalAllBranchesEnvelopeOfValues
                tokenTable width tokenCount start finish candidate
                  outputBoundary outputBoundarySize outputCount))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.outputStart_le_valueBound))
  exact hbranch.trans (hcount.trans (hsize.trans (hboundary.trans hstart)))

theorem
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData
          tokenTable width tokenCount start finish valueBound data).terminal <=
      compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
        tokenTable width tokenCount start finish valueBound data := by
  have hparts :=
    compactBinaryNatStatusValidBoundedTerminalPartsOfData_structuralPayloadBound_le_transparent
      tokenTable width tokenCount start finish valueBound data
  simpa only [
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData,
    hybridFormulaStructuralPayloadBound] using hparts

theorem
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph_terminal_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
          tokenTable width tokenCount start finish valueBound hgraph).terminal <=
      compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
        tokenTable width tokenCount start finish valueBound
        (compactBinaryNatStatusValidBoundedDataOfGraph
          tokenTable width tokenCount start finish valueBound hgraph) := by
  exact
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_transparent
      tokenTable width tokenCount start finish valueBound
      (compactBinaryNatStatusValidBoundedDataOfGraph
        tokenTable width tokenCount start finish valueBound hgraph)

theorem
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount start finish valueBound : Nat)
    (data : CompactBinaryNatStatusValidBoundedData
      tokenTable width tokenCount start finish valueBound) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData
          tokenTable width tokenCount start finish valueBound data).terminal <=
      compactBinaryNatStatusValidBoundedTerminalPublicFiniteEnvelope
        tokenTable width tokenCount start finish valueBound := by
  exact
    (compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_transparent
      tokenTable width tokenCount start finish valueBound data).trans
    (compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData_le_publicFinite
      tokenTable width tokenCount start finish valueBound data)

theorem
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph_terminal_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
          tokenTable width tokenCount start finish valueBound hgraph).terminal <=
      compactBinaryNatStatusValidBoundedTerminalPublicFiniteEnvelope
        tokenTable width tokenCount start finish valueBound := by
  exact
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount start finish valueBound
      (compactBinaryNatStatusValidBoundedDataOfGraph
        tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def
    compactBinaryNatStatusValidBoundedStructuralPayloadEnvelopeOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  let data := compactBinaryNatStatusValidBoundedDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  explicitBoundedWitnessHybridStructuralPayloadEnvelope zeroValuation
    valueBound
    (compactBinaryNatStatusValidBoundedRawTerminal
      tokenTable width tokenCount start finish)
    (compactBinaryNatStatusValidBoundedValues data)
    (compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
      tokenTable width tokenCount start finish valueBound data)

theorem
    compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish valueBound hgraph) <=
      compactBinaryNatStatusValidBoundedStructuralPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let data := compactBinaryNatStatusValidBoundedDataOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  let terminal := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData
    tokenTable width tokenCount start finish valueBound data
  have hterminal :=
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData_terminal_structuralPayloadBound_le_transparent
      tokenTable width tokenCount start finish valueBound data
  have hbuild :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      valueBound
      (compactBinaryNatStatusValidBoundedRawTerminal
        tokenTable width tokenCount start finish)
      terminal.values terminal.values_le terminal.terminal
      (compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
        tokenTable width tokenCount start finish valueBound data)
      hterminal
  simpa only [
    compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph,
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph,
    compactBinaryNatStatusValidBoundedStructuralPayloadEnvelopeOfGraph,
    compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfData,
    compactBinaryNatStatusValidBoundedValues, data, terminal,
    hybridFormulaStructuralPayloadBound] using hbuild

#print axioms valuationLeCertificate_structuralPayloadBound_le_public
#print axioms completedAreaCertificate_structuralPayloadBound_le_public
#print axioms
  compactBinaryNatCompletedStatusExplicitHybridCertificate_structuralPayloadBound_le_public
#print axioms
  compactBinaryNatStatusValidBoundedTerminalPartsOfData_structuralPayloadBound_le_transparent
#print axioms
  compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph_terminal_structuralPayloadBound_le_transparent
#print axioms
  compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds
