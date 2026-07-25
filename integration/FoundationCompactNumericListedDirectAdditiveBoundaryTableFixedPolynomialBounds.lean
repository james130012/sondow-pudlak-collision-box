import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds

/-!
# Fixed polynomial bounds for additive boundary-table rows

This layer removes the concrete left and right row witnesses from the
boundary-table terminal resource.  Both fixed-width entries and the strict
order atom are bounded at one public numeric/bit-width coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveBoundaryTableFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds

private abbrev boundaryLayoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private theorem boundaryArithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
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

private theorem boundaryArithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem boundaryHybridConjunctionEnvelope_mono
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    {leftSmall leftLarge rightSmall rightLarge : Nat}
    (hleft : leftSmall <= leftLarge)
    (hright : rightSmall <= rightLarge) :
    hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftSmall rightSmall <=
      hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftLarge rightLarge := by
  unfold hybridConjunctionStructuralPayloadEnvelope
  dsimp only
  omega

def boundaryRowLtBitWidthUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (binaryNumeralTermCodeEnvelope bitBound)

theorem boundaryRowClosedLtStructuralPayloadResource_le_bitWidthUniform
    (valuation : Nat -> Nat) (left right numericBound bitBound : Nat)
    (hvaluation : valuation 0 <= numericBound)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    boundaryRowClosedLtStructuralPayloadResource valuation left right <=
      boundaryRowLtBitWidthUniformPayloadPolynomial numericBound bitBound := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hleftCode : (binaryTermCode leftTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hrightCode : (binaryTermCode rightTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hrightSize
  have hleftVariables : leftTerm.freeVariables ⊆ {0} := by
    rw [show leftTerm.freeVariables = ∅ by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty left]
    simp
  have hrightVariables : rightTerm.freeVariables ⊆ {0} := by
    rw [show rightTerm.freeVariables = ∅ by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty right]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    valuation Language.ORing.Rel.lt args hleftVariables hrightVariables
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed valuation
    Language.ORing.Rel.lt args numericBound
      (binaryNumeralTermCodeEnvelope bitBound) hleftVariables hrightVariables
      hvaluation hleftCode hrightCode
  simpa only [boundaryRowClosedLtStructuralPayloadResource,
    boundaryRowLtBitWidthUniformPayloadPolynomial, args, leftTerm, rightTerm]
    using hpublic.trans hfixed

def boundaryRowTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let ltResource :=
    boundaryRowLtBitWidthUniformPayloadPolynomial numericBound bitBound
  let contextResource :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let conjunctionTag := (binaryNatCode 4).length
  contextResource + 4 *
    (leftResource + rightResource + ltResource + conjunctionTag + 1) + 1

def boundaryRowTerminalFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let ltResource :=
    boundaryRowLtBitWidthUniformPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    boundaryRowTerminalAssemblySyntaxPolynomial numericBound bitBound
  leftResource + rightResource + ltResource +
    6 * generalContextAssemblyEnvelope syntaxResource

private theorem boundaryValuationContextFormulaCodeSum_le_singleton
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound := by
  have hcard : formula.freeVariables.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall index, index ∈ formula.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact hvaluation
  have htermCodes : forall index, index ∈ formula.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact le_rfl
  have hraw :=
    FoundationCompactPAValuationTermCompilerPublicBounds.valuationContext_formulaCodeSum_le_uniform
      formula.freeVariables valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  simpa only [
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
    unitBoundaryTerminalContextFormulaCodeSumEnvelope] using hraw

def boundaryRowTerminalEntryBitWidthUniformEnvelope
    (tokenCount boundaryTable index left right numericBound bitBound : Nat) :
    Nat :=
  let valuation := extendValuation index boundaryLayoutZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm rightIndexTerm rightValueTerm
  let ltFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm left) <
      !!(shortBinaryNumeralTerm right)”
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let ltResource :=
    boundaryRowLtBitWidthUniformPayloadPolynomial numericBound bitBound
  let innerResource := hybridConjunctionStructuralPayloadEnvelope valuation
    rightFormula ltFormula rightResource ltResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ ltFormula) leftResource innerResource

theorem boundaryRowTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
    (tokenCount boundaryTable index left right numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hindexSuccessorSize : Nat.size (index + 1) <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    boundaryRowTerminalStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      boundaryRowTerminalEntryBitWidthUniformEnvelope tokenCount boundaryTable
        index left right numericBound bitBound := by
  let valuation := extendValuation index boundaryLayoutZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  have hindex : index <= numericBound := by omega
  have hzeroValuation : boundaryLayoutZeroValuation =
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation := by
    funext coordinate
    simp [boundaryLayoutZeroValuation,
      FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation,
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
  have hleftIndexEvaluation :
      termValue valuation leftIndexTerm = index := by
    change termValue (extendValuation index boundaryLayoutZeroValuation)
      (&0 : ValuationTerm) = index
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZero_under_extendValuation index
  have hrightIndexEvaluation :
      termValue valuation rightIndexTerm = index + 1 := by
    change termValue (extendValuation index boundaryLayoutZeroValuation)
      (‘&0 + 1’ : ValuationTerm) = index + 1
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZeroAddOne_under_extendValuation index
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hleftIndexValue : termValue valuation leftIndexTerm <= numericBound := by
    simpa only [hleftIndexEvaluation] using hindex
  have hrightIndexValue :
      termValue valuation rightIndexTerm <= numericBound := by
    simpa only [hrightIndexEvaluation] using hindexSuccessor
  have hleftIndexSize :
      Nat.size (termValue valuation leftIndexTerm) <= bitBound := by
    simpa only [hleftIndexEvaluation] using hindexSize
  have hrightIndexSize :
      Nat.size (termValue valuation rightIndexTerm) <= bitBound := by
    simpa only [hrightIndexEvaluation] using hindexSuccessorSize
  have hleftIndexVariables : leftIndexTerm.freeVariables ⊆ {0} := by
    simp [leftIndexTerm]
  have hrightIndexVariables : rightIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [rightIndexTerm]
    rw [boundaryArithmeticAddTerm_freeVariables,
      boundaryArithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hleftResource :=
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
      valuation boundaryTable tokenCount left leftIndexTerm numericBound
      bitBound htokenCount hleftIndexValue hvaluation htableSize
      htokenCountSize hleftIndexSize hleftSize hleftIndexVariables
  have hrightResource :=
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
      valuation boundaryTable tokenCount right rightIndexTerm numericBound
      bitBound htokenCount hrightIndexValue hvaluation htableSize
      htokenCountSize hrightIndexSize hrightSize hrightIndexVariables
  have hltResource :=
    boundaryRowClosedLtStructuralPayloadResource_le_bitWidthUniform valuation
      left right numericBound bitBound hvaluation hleftSize hrightSize
  unfold boundaryRowTerminalStructuralPayloadEnvelopeOfValues
    boundaryRowTerminalEntryBitWidthUniformEnvelope
  dsimp only [valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm]
  exact boundaryHybridConjunctionEnvelope_mono _ _ _ hleftResource
    (boundaryHybridConjunctionEnvelope_mono _ _ _ hrightResource hltResource)

theorem boundaryRowTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    boundaryRowTerminalEntryBitWidthUniformEnvelope tokenCount boundaryTable
        index data.left data.right numericBound bitBound <=
      boundaryRowTerminalFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let valuation := extendValuation index boundaryLayoutZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm data.left
  let rightValueTerm := shortBinaryNumeralTerm data.right
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm leftIndexTerm leftValueTerm
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm rightIndexTerm rightValueTerm
  let ltFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm data.left) <
      !!(shortBinaryNumeralTerm data.right)”
  let innerFormula := rightFormula ⋏ ltFormula
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let ltResource :=
    boundaryRowLtBitWidthUniformPayloadPolynomial numericBound bitBound
  let contextResource :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let syntaxResource :=
    boundaryRowTerminalAssemblySyntaxPolynomial numericBound bitBound
  let innerResource := hybridConjunctionStructuralPayloadEnvelope valuation
    rightFormula ltFormula rightResource ltResource
  have hindex : index <= numericBound := by omega
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size hindex).trans hnumericSize
  have hindexSuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size hindexSuccessor).trans hnumericSize
  have hleftSize : Nat.size data.left <= bitBound :=
    (Nat.size_le_size (data.left_le.trans htokenCount)).trans hnumericSize
  have hrightSize : Nat.size data.right <= bitBound :=
    (Nat.size_le_size (data.right_le.trans htokenCount)).trans hnumericSize
  have hzeroValuation : boundaryLayoutZeroValuation =
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation := by
    funext coordinate
    simp [boundaryLayoutZeroValuation,
      FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation,
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
  have hleftIndexEvaluation :
      termValue valuation leftIndexTerm = index := by
    change termValue (extendValuation index boundaryLayoutZeroValuation)
      (&0 : ValuationTerm) = index
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZero_under_extendValuation index
  have hrightIndexEvaluation :
      termValue valuation rightIndexTerm = index + 1 := by
    change termValue (extendValuation index boundaryLayoutZeroValuation)
      (‘&0 + 1’ : ValuationTerm) = index + 1
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZeroAddOne_under_extendValuation index
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hleftIndexValue : termValue valuation leftIndexTerm <= numericBound := by
    simpa only [hleftIndexEvaluation] using hindex
  have hrightIndexValue :
      termValue valuation rightIndexTerm <= numericBound := by
    simpa only [hrightIndexEvaluation] using hindexSuccessor
  have hleftIndexSize :
      Nat.size (termValue valuation leftIndexTerm) <= bitBound := by
    simpa only [hleftIndexEvaluation] using hindexSize
  have hrightIndexSize :
      Nat.size (termValue valuation rightIndexTerm) <= bitBound := by
    simpa only [hrightIndexEvaluation] using hindexSuccessorSize
  have hleftIndexVariables : leftIndexTerm.freeVariables ⊆ {0} := by
    simp [leftIndexTerm]
  have hrightIndexVariables : rightIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [rightIndexTerm]
    rw [boundaryArithmeticAddTerm_freeVariables,
      boundaryArithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hleftEntry : CompactFixedWidthEntry boundaryTable tokenCount
      (termValue valuation leftIndexTerm) data.left := by
    simpa only [hleftIndexEvaluation] using data.left_entry
  have hrightEntry : CompactFixedWidthEntry boundaryTable tokenCount
      (termValue valuation rightIndexTerm) data.right := by
    simpa only [hrightIndexEvaluation] using data.right_entry
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm leftIndexTerm leftValueTerm (by
        simpa only [tableTerm, widthTerm, leftValueTerm,
          termValue_shortBinaryNumeralTerm] using hleftEntry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm rightIndexTerm rightValueTerm (by
        simpa only [tableTerm, widthTerm, rightValueTerm,
          termValue_shortBinaryNumeralTerm] using hrightEntry)
  let ltCertificate := closedLtCertificate valuation data.left data.right
    data.left_lt_right
  have hleftPayload : hybridFormulaStructuralPayloadBound leftCertificate <=
      leftResource := by
    dsimp only [leftCertificate, leftResource, tableTerm, widthTerm,
      leftValueTerm]
    exact
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        valuation boundaryTable tokenCount data.left leftIndexTerm numericBound
        bitBound htokenCount hleftIndexValue hvaluation htableSize
        htokenCountSize hleftIndexSize hleftSize hleftIndexVariables hleftEntry
  have hrightPayload : hybridFormulaStructuralPayloadBound rightCertificate <=
      rightResource := by
    dsimp only [rightCertificate, rightResource, tableTerm, widthTerm,
      rightValueTerm]
    exact
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        valuation boundaryTable tokenCount data.right rightIndexTerm numericBound
        bitBound htokenCount hrightIndexValue hvaluation htableSize
        htokenCountSize hrightIndexSize hrightSize hrightIndexVariables
        hrightEntry
  have hltPayload : hybridFormulaStructuralPayloadBound ltCertificate <=
      ltResource :=
    (closedLtCertificate_structuralPayloadBound_le_transparent valuation
      data.left data.right data.left_lt_right).trans
      (boundaryRowClosedLtStructuralPayloadResource_le_bitWidthUniform
        valuation data.left data.right numericBound bitBound hvaluation
        hleftSize hrightSize)
  have hleftCode : (binaryFormulaCode leftFormula).length <= leftResource := by
    have hraw :=
      FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        leftCertificate
    simpa only [leftCertificate, leftFormula, tableTerm, widthTerm,
      leftIndexTerm, leftValueTerm] using hraw.trans hleftPayload
  have hrightCode : (binaryFormulaCode rightFormula).length <= rightResource := by
    have hraw :=
      FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        rightCertificate
    simpa only [rightCertificate, rightFormula, tableTerm, widthTerm,
      rightIndexTerm, rightValueTerm] using hraw.trans hrightPayload
  have hltCode : (binaryFormulaCode ltFormula).length <= ltResource := by
    have hraw :=
      FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        ltCertificate
    simpa only [ltCertificate, ltFormula] using hraw.trans hltPayload
  have htableVariables : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hwidthVariables : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftValueVariables : leftValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.left
  have hrightValueVariables : rightValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.right
  have hleftVariables : leftFormula.freeVariables ⊆ {0} :=
    compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm leftIndexTerm leftValueTerm htableVariables
      hwidthVariables hleftIndexVariables hleftValueVariables
  have hrightVariables : rightFormula.freeVariables ⊆ {0} :=
    compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm rightIndexTerm rightValueTerm htableVariables
      hwidthVariables hrightIndexVariables hrightValueVariables
  have hltVariables : ltFormula.freeVariables ⊆ {0} := by
    have hclosed : ltFormula.freeVariables = ∅ := by
      dsimp only [ltFormula]
      simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hinnerVariables : innerFormula.freeVariables ⊆ {0} := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hrightVariables hltVariables
  have houterVariables : (leftFormula ⋏ innerFormula).freeVariables ⊆
      {0} := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hleftVariables hinnerVariables
  have hinnerContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext innerFormula.freeVariables valuation) <=
        contextResource := by
    simpa only [contextResource] using
      boundaryValuationContextFormulaCodeSum_le_singleton valuation
        innerFormula numericBound hinnerVariables hvaluation
  have houterContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (leftFormula ⋏ innerFormula).freeVariables
            valuation) <= contextResource := by
    simpa only [contextResource] using
      boundaryValuationContextFormulaCodeSum_le_singleton valuation
        (leftFormula ⋏ innerFormula) numericBound houterVariables hvaluation
  have hinnerCodeRaw := binaryFormulaCode_and_length_le_local
    rightFormula ltFormula
  have hinnerCode : (binaryFormulaCode innerFormula).length <=
      rightResource + ltResource + (binaryNatCode 4).length := by
    dsimp only [innerFormula] at hinnerCodeRaw ⊢
    omega
  have houterCodeRaw := binaryFormulaCode_and_length_le_local
    leftFormula innerFormula
  have houterCode : (binaryFormulaCode (leftFormula ⋏ innerFormula)).length <=
      leftResource + rightResource + ltResource +
        2 * (binaryNatCode 4).length := by
    omega
  have hsyntaxOne : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold boundaryRowTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hcontextResource_le_syntax : contextResource <= syntaxResource := by
    dsimp only [contextResource, syntaxResource]
    unfold boundaryRowTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hleftResource_le_syntax : leftResource <= syntaxResource := by
    dsimp only [leftResource, syntaxResource]
    unfold boundaryRowTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hrightResource_le_syntax : rightResource <= syntaxResource := by
    dsimp only [rightResource, syntaxResource]
    unfold boundaryRowTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hltResource_le_syntax : ltResource <= syntaxResource := by
    dsimp only [ltResource, syntaxResource]
    unfold boundaryRowTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hinnerCode_le_syntax :
      (binaryFormulaCode innerFormula).length <= syntaxResource :=
    hinnerCode.trans (by
      dsimp only [rightResource, ltResource, syntaxResource]
      unfold boundaryRowTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have houterCode_le_syntax :
      (binaryFormulaCode (leftFormula ⋏ innerFormula)).length <=
        syntaxResource :=
    houterCode.trans (by
      dsimp only [leftResource, rightResource, ltResource, syntaxResource]
      unfold boundaryRowTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have hinnerGeneral : innerResource <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
        ltResource := by
    dsimp only [innerResource]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      rightFormula ltFormula rightResource ltResource syntaxResource
      hsyntaxOne (hinnerContext.trans hcontextResource_le_syntax)
      (hrightCode.trans hrightResource_le_syntax)
      (hltCode.trans hltResource_le_syntax) hinnerCode_le_syntax
  have houterGeneral :
      hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
          innerFormula leftResource innerResource <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
          innerResource :=
    hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      leftFormula innerFormula leftResource innerResource syntaxResource
      hsyntaxOne (houterContext.trans hcontextResource_le_syntax)
      (hleftCode.trans hleftResource_le_syntax) hinnerCode_le_syntax
      houterCode_le_syntax
  change
    hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
        innerFormula leftResource innerResource <=
      boundaryRowTerminalFullyUniformPayloadPolynomial numericBound bitBound
  apply houterGeneral.trans
  unfold hybridConjunctionGeneralPayloadEnvelope at hinnerGeneral
  unfold hybridConjunctionGeneralPayloadEnvelope
    boundaryRowTerminalFullyUniformPayloadPolynomial
  dsimp only [leftResource, rightResource, ltResource, syntaxResource,
    innerResource] at hinnerGeneral ⊢
  omega

theorem boundaryRowTerminalStructuralPayloadEnvelope_le_fullyUniform
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    boundaryRowTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data <=
      boundaryRowTerminalFullyUniformPayloadPolynomial
        numericBound bitBound := by
  have hindex : index <= numericBound := by omega
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size hindex).trans hnumericSize
  have hindexSuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size hindexSuccessor).trans hnumericSize
  have hleftSize : Nat.size data.left <= bitBound :=
    (Nat.size_le_size (data.left_le.trans htokenCount)).trans hnumericSize
  have hrightSize : Nat.size data.right <= bitBound :=
    (Nat.size_le_size (data.right_le.trans htokenCount)).trans hnumericSize
  have hchildren :=
    boundaryRowTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
      tokenCount boundaryTable index data.left data.right numericBound bitBound
      htokenCount hindexSuccessor htableSize htokenCountSize hindexSize
      hindexSuccessorSize hleftSize hrightSize
  have hassembly :=
    boundaryRowTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
      tokenCount boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize
  simpa only [boundaryRowTerminalStructuralPayloadEnvelope,
    boundaryRowTerminalStructuralPayloadEnvelopeOfValues] using
      hchildren.trans hassembly

#print axioms
  boundaryRowClosedLtStructuralPayloadResource_le_bitWidthUniform
#print axioms
  boundaryRowTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
#print axioms
  boundaryRowTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
#print axioms boundaryRowTerminalStructuralPayloadEnvelope_le_fullyUniform

end FoundationCompactNumericListedDirectAdditiveBoundaryTableFixedPolynomialBounds
