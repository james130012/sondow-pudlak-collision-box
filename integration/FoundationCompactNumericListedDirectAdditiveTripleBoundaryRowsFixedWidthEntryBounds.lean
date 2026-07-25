import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fixed-width entry closure for additive triple-boundary rows

This layer replaces the two open-index fixed-width entry resources in every
triple-boundary row by one common scale-only endpoint.  The span-three atom and
the surrounding finite witness/universal structure remain explicit.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsFixedWidthEntryBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds

private abbrev tripleZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_freeVariables_fixedWidthEntry
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
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

private theorem arithmeticOneTerm_freeVariables_fixedWidthEntry :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticThreeTerm_freeVariables_fixedWidthEntry :
    (‘3’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem hybridConjunctionStructuralPayloadEnvelope_mono
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

def compactAdditiveTripleBoundaryRowsFixedWidthEntryScale
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index tripleZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
      leftIndexTerm leftValueTerm +
    fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
      rightIndexTerm rightValueTerm

def compactAdditiveTripleBoundaryRowsTerminalFixedWidthEntryEnvelope
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index tripleZeroValuation
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
  let spanFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm right) =
      !!(shortBinaryNumeralTerm left) + 3”
  let scale := compactAdditiveTripleBoundaryRowsFixedWidthEntryScale
    tokenCount boundaryTable index left right
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let spanResource := tripleBoundarySpanStructuralPayloadResource
    valuation left right
  let rightSpanResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula spanFormula entryResource spanResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ spanFormula) entryResource rightSpanResource

theorem
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
    (tokenCount boundaryTable index left right : Nat) :
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      compactAdditiveTripleBoundaryRowsTerminalFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right := by
  let valuation := extendValuation index tripleZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  let scale := compactAdditiveTripleBoundaryRowsFixedWidthEntryScale
    tokenCount boundaryTable index left right
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftValue : leftValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hrightValue : rightValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty right
  have hleftIndex : leftIndexTerm.freeVariables ⊆ {0} := by
    simp [leftIndexTerm]
  have hrightIndex : rightIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [rightIndexTerm]
    rw [arithmeticAddTerm_freeVariables_fixedWidthEntry,
      arithmeticOneTerm_freeVariables_fixedWidthEntry]
    simp
  have hleftScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          leftIndexTerm leftValueTerm <= scale := by
    dsimp only [scale,
      compactAdditiveTripleBoundaryRowsFixedWidthEntryScale, valuation,
      tableTerm, widthTerm, leftIndexTerm, rightIndexTerm, leftValueTerm,
      rightValueTerm]
    omega
  have hrightScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          rightIndexTerm rightValueTerm <= scale := by
    dsimp only [scale,
      compactAdditiveTripleBoundaryRowsFixedWidthEntryScale, valuation,
      tableTerm, widthTerm, leftIndexTerm, rightIndexTerm, leftValueTerm,
      rightValueTerm]
    omega
  have hleftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm scale
        hleftScale htable hwidth hleftIndex hleftValue
  have hrightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm scale
        hrightScale htable hwidth hrightIndex hrightValue
  unfold
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
    compactAdditiveTripleBoundaryRowsTerminalFixedWidthEntryEnvelope
  dsimp only [valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm, scale]
  exact hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hleftResource
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hrightResource
      le_rfl)

def tripleBoundarySpanTermCodeCeiling (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘3’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def tripleBoundarySpanBitWidthUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (tripleBoundarySpanTermCodeCeiling bitBound)

theorem tripleBoundarySpanStructuralPayloadResource_le_bitWidthUniform
    (valuation : Nat -> Nat) (left right numericBound bitBound : Nat)
    (hvaluation : valuation 0 <= numericBound)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    tripleBoundarySpanStructuralPayloadResource valuation left right <=
      tripleBoundarySpanBitWidthUniformPayloadPolynomial
        numericBound bitBound := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let spanTerm : ValuationTerm := ‘!!leftTerm + 3’
  let args : Fin 2 -> ValuationTerm := ![rightTerm, spanTerm]
  have hleftCode : (binaryTermCode leftTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hrightCode : (binaryTermCode rightTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope right bitBound hrightSize
  have hspanCodeRaw := paAddTerm_code_length_le
    leftTerm (‘3’ : ValuationTerm)
  have hspanCode : (binaryTermCode spanTerm).length <=
      tripleBoundarySpanTermCodeCeiling bitBound := by
    dsimp only [spanTerm]
    change (binaryTermCode
      (paAddTerm leftTerm (‘3’ : ValuationTerm))).length <= _
    exact hspanCodeRaw.trans (by
      unfold tripleBoundarySpanTermCodeCeiling
      omega)
  have hrightCodeCeiling : (binaryTermCode rightTerm).length <=
      tripleBoundarySpanTermCodeCeiling bitBound :=
    hrightCode.trans (by
      unfold tripleBoundarySpanTermCodeCeiling
      omega)
  have hrightVariables : rightTerm.freeVariables ⊆ {0} := by
    rw [show rightTerm.freeVariables = ∅ by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty right]
    simp
  have hspanVariables : spanTerm.freeVariables ⊆ {0} := by
    rw [show spanTerm.freeVariables = ∅ by
      dsimp only [spanTerm]
      rw [arithmeticAddTerm_freeVariables_fixedWidthEntry,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticThreeTerm_freeVariables_fixedWidthEntry]
      simp]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    valuation Language.Eq.eq args hrightVariables hspanVariables
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
    valuation Language.Eq.eq args numericBound
      (tripleBoundarySpanTermCodeCeiling bitBound)
      hrightVariables hspanVariables hvaluation hrightCodeCeiling
      hspanCode
  simpa only [tripleBoundarySpanStructuralPayloadResource,
    tripleBoundarySpanBitWidthUniformPayloadPolynomial, args, rightTerm,
    spanTerm, leftTerm] using hpublic.trans hfixed

def tripleBoundaryLeftEntryBitWidthUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (&0 : ValuationTerm) numericBound bitBound))

def tripleBoundaryRightEntryBitWidthUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (‘&0 + 1’ : ValuationTerm) numericBound bitBound))

def tripleBoundaryTerminalContextFormulaCodeSumEnvelope
    (numericBound : Nat) : Nat :=
  FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
    1 numericBound (binaryTermCode (&0 : ValuationTerm)).length

def tripleBoundaryTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    tripleBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    tripleBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    tripleBoundarySpanBitWidthUniformPayloadPolynomial numericBound bitBound
  let contextResource :=
    tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let conjunctionTag := (binaryNatCode 4).length
  contextResource + 4 *
    (leftResource + rightResource + successorResource + conjunctionTag + 1) + 1

def tripleBoundaryTerminalFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    tripleBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    tripleBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    tripleBoundarySpanBitWidthUniformPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    tripleBoundaryTerminalAssemblySyntaxPolynomial numericBound bitBound
  leftResource + rightResource + successorResource +
    6 * generalContextAssemblyEnvelope syntaxResource

private theorem valuationContextGeneralFormulaCodeSum_le_singleton
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound := by
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
    tripleBoundaryTerminalContextFormulaCodeSumEnvelope] using hraw

/-- The two fixed-width entries are charged by numeric loop bounds and binary
coordinate widths.  The span-three equality remains visible for the next
uniformization layer. -/
def compactAdditiveTripleBoundaryRowsTerminalEntryBitWidthUniformEnvelope
    (tokenCount boundaryTable index left right numericBound bitBound : Nat) :
    Nat :=
  let valuation := extendValuation index tripleZeroValuation
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
  let successorFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm right) =
      !!(shortBinaryNumeralTerm left) + 3”
  let leftResource :=
    tripleBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    tripleBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    tripleBoundarySpanBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightSuccessorResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula successorFormula rightResource successorResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ successorFormula) leftResource rightSuccessorResource

theorem
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
    (tokenCount boundaryTable index left right numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hindexSuccessorSize : Nat.size (index + 1) <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      compactAdditiveTripleBoundaryRowsTerminalEntryBitWidthUniformEnvelope
        tokenCount boundaryTable index left right numericBound bitBound := by
  let valuation := extendValuation index tripleZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  have hindex : index <= numericBound := by omega
  have hzeroValuation : tripleZeroValuation =
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation := by
    funext coordinate
    simp [tripleZeroValuation,
      FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation,
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
  have hleftIndexEvaluation :
      termValue valuation leftIndexTerm = index := by
    change termValue (extendValuation index tripleZeroValuation)
      (&0 : ValuationTerm) = index
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZero_under_extendValuation index
  have hrightIndexEvaluation :
      termValue valuation rightIndexTerm = index + 1 := by
    change termValue (extendValuation index tripleZeroValuation)
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
    rw [arithmeticAddTerm_freeVariables_fixedWidthEntry,
      arithmeticOneTerm_freeVariables_fixedWidthEntry]
    simp
  have hleftResource :=
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
      valuation boundaryTable tokenCount left leftIndexTerm numericBound bitBound
      htokenCount hleftIndexValue hvaluation htableSize htokenCountSize
      hleftIndexSize hleftSize hleftIndexVariables
  have hrightResource :=
    compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
      valuation boundaryTable tokenCount right rightIndexTerm numericBound
      bitBound htokenCount hrightIndexValue hvaluation htableSize
      htokenCountSize hrightIndexSize hrightSize hrightIndexVariables
  have hsuccessorResource :=
    tripleBoundarySpanStructuralPayloadResource_le_bitWidthUniform
      valuation left right numericBound bitBound hvaluation hleftSize hrightSize
  unfold
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
    compactAdditiveTripleBoundaryRowsTerminalEntryBitWidthUniformEnvelope
  dsimp only [valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm]
  exact hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hleftResource
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hrightResource
      hsuccessorResource)

theorem
    compactAdditiveTripleBoundaryRowsTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveTripleBoundaryRowsTerminalEntryBitWidthUniformEnvelope
        tokenCount boundaryTable index data.left data.right
          numericBound bitBound <=
      tripleBoundaryTerminalFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let valuation := extendValuation index tripleZeroValuation
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
  let successorFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm data.right) =
      !!(shortBinaryNumeralTerm data.left) + 3”
  let innerFormula := rightFormula ⋏ successorFormula
  let leftResource :=
    tripleBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    tripleBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    tripleBoundarySpanBitWidthUniformPayloadPolynomial numericBound bitBound
  let contextResource :=
    tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let syntaxResource :=
    tripleBoundaryTerminalAssemblySyntaxPolynomial numericBound bitBound
  let innerResource := hybridConjunctionStructuralPayloadEnvelope valuation
    rightFormula successorFormula rightResource successorResource
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
  have hzeroValuation : tripleZeroValuation =
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation := by
    funext coordinate
    simp [tripleZeroValuation,
      FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation,
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
  have hleftIndexEvaluation :
      termValue valuation leftIndexTerm = index := by
    change termValue (extendValuation index tripleZeroValuation)
      (&0 : ValuationTerm) = index
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZero_under_extendValuation index
  have hrightIndexEvaluation :
      termValue valuation rightIndexTerm = index + 1 := by
    change termValue (extendValuation index tripleZeroValuation)
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
    rw [arithmeticAddTerm_freeVariables_fixedWidthEntry,
      arithmeticOneTerm_freeVariables_fixedWidthEntry]
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
  let successorCertificate := tripleEqualityCertificate valuation
    data.left data.right data.triple
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
  have hsuccessorPayload :
      hybridFormulaStructuralPayloadBound successorCertificate <=
        successorResource :=
    (tripleEqualityCertificate_structuralPayloadBound_le_transparent
      valuation data.left data.right data.triple).trans
      (tripleBoundarySpanStructuralPayloadResource_le_bitWidthUniform
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
  have hsuccessorCode :
      (binaryFormulaCode successorFormula).length <= successorResource := by
    have hraw :=
      FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        successorCertificate
    simpa only [successorCertificate, successorFormula] using
      hraw.trans hsuccessorPayload
  have htableVariables : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hwidthVariables : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftValueVariables : leftValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.left
  have hrightValueVariables : rightValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.right
  have hleftVariables : leftFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm leftIndexTerm leftValueTerm htableVariables
      hwidthVariables hleftIndexVariables hleftValueVariables
  have hrightVariables : rightFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm rightIndexTerm rightValueTerm htableVariables
      hwidthVariables hrightIndexVariables hrightValueVariables
  have hsuccessorVariables : successorFormula.freeVariables ⊆ {0} := by
    have hclosed : successorFormula.freeVariables = ∅ := by
      dsimp only [successorFormula]
      simp [arithmeticAddTerm_freeVariables_fixedWidthEntry,
        arithmeticThreeTerm_freeVariables_fixedWidthEntry,
        shortBinaryNumeralTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hinnerVariables : innerFormula.freeVariables ⊆ {0} := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hrightVariables hsuccessorVariables
  have houterVariables : (leftFormula ⋏ innerFormula).freeVariables ⊆ {0} := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hleftVariables hinnerVariables
  have hinnerContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext innerFormula.freeVariables valuation) <=
        contextResource := by
    simpa only [contextResource] using
      valuationContextGeneralFormulaCodeSum_le_singleton valuation innerFormula
        numericBound hinnerVariables hvaluation
  have houterContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (leftFormula ⋏ innerFormula).freeVariables
            valuation) <= contextResource := by
    simpa only [contextResource] using
      valuationContextGeneralFormulaCodeSum_le_singleton valuation
        (leftFormula ⋏ innerFormula) numericBound houterVariables hvaluation
  have hinnerCodeRaw := binaryFormulaCode_and_length_le_local
    rightFormula successorFormula
  have hinnerCode : (binaryFormulaCode innerFormula).length <=
      rightResource + successorResource + (binaryNatCode 4).length := by
    dsimp only [innerFormula] at hinnerCodeRaw ⊢
    omega
  have houterCodeRaw := binaryFormulaCode_and_length_le_local
    leftFormula innerFormula
  have houterCode : (binaryFormulaCode (leftFormula ⋏ innerFormula)).length <=
      leftResource + rightResource + successorResource +
        2 * (binaryNatCode 4).length := by
    omega
  have hsyntaxOne : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tripleBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hcontextResource_le_syntax : contextResource <= syntaxResource := by
    dsimp only [contextResource, syntaxResource]
    unfold tripleBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hleftResource_le_syntax : leftResource <= syntaxResource := by
    dsimp only [leftResource, syntaxResource]
    unfold tripleBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hrightResource_le_syntax : rightResource <= syntaxResource := by
    dsimp only [rightResource, syntaxResource]
    unfold tripleBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hsuccessorResource_le_syntax : successorResource <= syntaxResource := by
    dsimp only [successorResource, syntaxResource]
    unfold tripleBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hinnerCode_le_syntax :
      (binaryFormulaCode innerFormula).length <= syntaxResource :=
    hinnerCode.trans (by
      dsimp only [rightResource, successorResource, syntaxResource]
      unfold tripleBoundaryTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have houterCode_le_syntax :
      (binaryFormulaCode (leftFormula ⋏ innerFormula)).length <=
        syntaxResource :=
    houterCode.trans (by
      dsimp only [leftResource, rightResource, successorResource,
        syntaxResource]
      unfold tripleBoundaryTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have hinnerGeneral : innerResource <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
        successorResource := by
    dsimp only [innerResource]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      rightFormula successorFormula rightResource successorResource
      syntaxResource hsyntaxOne
      (hinnerContext.trans hcontextResource_le_syntax)
      (hrightCode.trans hrightResource_le_syntax)
      (hsuccessorCode.trans hsuccessorResource_le_syntax)
      hinnerCode_le_syntax
  have houterGeneral :
      hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
          innerFormula leftResource innerResource <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
          innerResource := by
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      leftFormula innerFormula leftResource innerResource syntaxResource
      hsyntaxOne (houterContext.trans hcontextResource_le_syntax)
      (hleftCode.trans hleftResource_le_syntax) hinnerCode_le_syntax
      houterCode_le_syntax
  change
    hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
        innerFormula leftResource innerResource <=
      tripleBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  apply houterGeneral.trans
  unfold hybridConjunctionGeneralPayloadEnvelope at hinnerGeneral
  unfold hybridConjunctionGeneralPayloadEnvelope
    tripleBoundaryTerminalFullyUniformPayloadPolynomial
  dsimp only [leftResource, rightResource, successorResource, syntaxResource,
    innerResource] at hinnerGeneral ⊢
  omega

theorem
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data <=
      tripleBoundaryTerminalFullyUniformPayloadPolynomial
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
  have hentry :=
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
      tokenCount boundaryTable index data.left data.right numericBound bitBound
      htokenCount hindexSuccessor htableSize htokenCountSize hindexSize
      hindexSuccessorSize hleftSize hrightSize
  have hassembly :=
    compactAdditiveTripleBoundaryRowsTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
      tokenCount boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize
  simpa only [
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope,
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues]
    using hentry.trans hassembly

def compactAdditiveTripleBoundaryRowsBranchFixedWidthEntryEnvelope
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index tripleZeroValuation
  let values : Fin 2 -> Nat := ![right, left]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveTripleBoundaryRowsBranchTerminal tokenCount boundaryTable)
    values
    (compactAdditiveTripleBoundaryRowsTerminalFixedWidthEntryEnvelope
      tokenCount boundaryTable index left right)

theorem
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
    (tokenCount boundaryTable index left right : Nat) :
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      compactAdditiveTripleBoundaryRowsBranchFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right := by
  unfold
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelopeOfValues
    compactAdditiveTripleBoundaryRowsBranchFixedWidthEntryEnvelope
  exact explicitBoundedWitnessHybridStructuralPayloadEnvelope_mono _ _ _ _
    (compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
      tokenCount boundaryTable index left right)

def compactAdditiveTripleBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
    (tokenCount boundaryTable index : Nat) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun left =>
    (Finset.range (tokenCount + 1)).sum fun right =>
      compactAdditiveTripleBoundaryRowsBranchFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right

theorem
    compactAdditiveTripleBoundaryRowsPublicFiniteBranchEnvelope_le_fixedWidthEntry
    (tokenCount boundaryTable index : Nat) :
    compactAdditiveTripleBoundaryRowsPublicFiniteBranchEnvelope
        tokenCount boundaryTable index <=
      compactAdditiveTripleBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
        tokenCount boundaryTable index := by
  unfold compactAdditiveTripleBoundaryRowsPublicFiniteBranchEnvelope
    compactAdditiveTripleBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
  exact Finset.sum_le_sum fun left _ =>
    Finset.sum_le_sum fun right _ =>
      compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
        tokenCount boundaryTable index left right

def compactAdditiveTripleBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
    (tokenCount count boundaryTable : Nat) : Nat :=
  ∑ index : Fin count,
    compactAdditiveTripleBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
      tokenCount boundaryTable index

theorem
    compactAdditiveTripleBoundaryRowsPublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveTripleBoundaryRowsPublicFiniteLeafPayloadResourceSum
        tokenCount count boundaryTable <=
      compactAdditiveTripleBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
        tokenCount count boundaryTable := by
  unfold compactAdditiveTripleBoundaryRowsPublicFiniteLeafPayloadResourceSum
    compactAdditiveTripleBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
  exact Finset.sum_le_sum fun index _ =>
    compactAdditiveTripleBoundaryRowsPublicFiniteBranchEnvelope_le_fixedWidthEntry
      tokenCount boundaryTable index

private theorem hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    {small large : Nat} (hresource : small <= large) :
    forall bound,
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body small bound <=
        hybridBranchesUniformStructuralPayloadEnvelope totalBound
          outerVariables valuation body large bound
  | 0 => by rfl
  | bound + 1 => by
      simp only [hybridBranchesUniformStructuralPayloadEnvelope]
      have hinduction :=
        hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf totalBound
          outerVariables valuation body hresource bound
      omega

def compactAdditiveTripleBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
    (tokenCount count boundaryTable : Nat) : Nat :=
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm count)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue tripleZeroValuation (shortBinaryNumeralTerm count)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    tripleZeroValuation body
    (compactAdditiveTripleBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
      tokenCount count boundaryTable)
    bound

theorem
    compactAdditiveTripleBoundaryRowsBranchesPublicFiniteStructuralEnvelope_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveTripleBoundaryRowsBranchesPublicFiniteStructuralEnvelope
        tokenCount count boundaryTable <=
      compactAdditiveTripleBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
        tokenCount count boundaryTable := by
  unfold compactAdditiveTripleBoundaryRowsBranchesPublicFiniteStructuralEnvelope
    compactAdditiveTripleBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
  exact hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (termValue tripleZeroValuation (shortBinaryNumeralTerm count))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count))
      (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)).freeVariables
    tripleZeroValuation
    (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable)
    (compactAdditiveTripleBoundaryRowsPublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
      tokenCount count boundaryTable)
    (termValue tripleZeroValuation (shortBinaryNumeralTerm count))

def compactAdditiveTripleBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
    (tokenCount count boundaryTable : Nat) : Nat :=
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables tripleZeroValuation
  let bound := termValue tripleZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveTripleBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
      tokenCount count boundaryTable)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource tripleZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveTripleBoundaryRowsPublicFiniteStructuralPayloadEnvelope_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveTripleBoundaryRowsPublicFiniteStructuralPayloadEnvelope
        tokenCount count boundaryTable <=
      compactAdditiveTripleBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
        tokenCount count boundaryTable := by
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables tripleZeroValuation
  let bound := termValue tripleZeroValuation boundTerm
  let oldCore :=
    compactAdditiveTripleBoundaryRowsBranchesPublicFiniteStructuralEnvelope
      tokenCount count boundaryTable
  let newCore :=
    compactAdditiveTripleBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
      tokenCount count boundaryTable
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    tripleZeroValuation outerVariables boundTerm
  have hcore : oldCore <= newCore :=
    compactAdditiveTripleBoundaryRowsBranchesPublicFiniteStructuralEnvelope_le_fixedWidthEntry
      tokenCount count boundaryTable
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranch
  simpa only [
    compactAdditiveTripleBoundaryRowsPublicFiniteStructuralPayloadEnvelope,
    compactAdditiveTripleBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

theorem
    compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable) :
    compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope
        tokenCount count boundaryTable hrows <=
      compactAdditiveTripleBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
        tokenCount count boundaryTable :=
  (compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_publicFinite
    tokenCount count boundaryTable hrows).trans
      (compactAdditiveTripleBoundaryRowsPublicFiniteStructuralPayloadEnvelope_le_fixedWidthEntry
        tokenCount count boundaryTable)

#print axioms
  compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
#print axioms
  compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
#print axioms
  tripleBoundarySpanStructuralPayloadResource_le_bitWidthUniform
#print axioms
  compactAdditiveTripleBoundaryRowsTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
#print axioms
  compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
#print axioms
  compactAdditiveTripleBoundaryRowsPublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
#print axioms
  compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fixedWidthEntry

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsFixedWidthEntryBounds
