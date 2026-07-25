import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fixed-width entry closure for additive unit-boundary rows

This layer replaces the two open-index fixed-width entry resources in every
unit-boundary row by one common scale-only endpoint.  The successor atom and
the surrounding finite witness/universal structure remain explicit.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds

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
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds

private abbrev unitZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation

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

def compactAdditiveUnitBoundaryRowsFixedWidthEntryScale
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index unitZeroValuation
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

def compactAdditiveUnitBoundaryRowsTerminalFixedWidthEntryEnvelope
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index unitZeroValuation
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
      !!(shortBinaryNumeralTerm left) + 1”
  let scale := compactAdditiveUnitBoundaryRowsFixedWidthEntryScale
    tokenCount boundaryTable index left right
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let successorResource := unitBoundarySuccessorStructuralPayloadResource
    valuation left right
  let rightSuccessorResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula successorFormula entryResource successorResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ successorFormula) entryResource rightSuccessorResource

theorem
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
    (tokenCount boundaryTable index left right : Nat) :
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      compactAdditiveUnitBoundaryRowsTerminalFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right := by
  let valuation := extendValuation index unitZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  let scale := compactAdditiveUnitBoundaryRowsFixedWidthEntryScale
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
      compactAdditiveUnitBoundaryRowsFixedWidthEntryScale, valuation,
      tableTerm, widthTerm, leftIndexTerm, rightIndexTerm, leftValueTerm,
      rightValueTerm]
    omega
  have hrightScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          rightIndexTerm rightValueTerm <= scale := by
    dsimp only [scale,
      compactAdditiveUnitBoundaryRowsFixedWidthEntryScale, valuation,
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
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
    compactAdditiveUnitBoundaryRowsTerminalFixedWidthEntryEnvelope
  dsimp only [valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm, scale]
  exact hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hleftResource
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hrightResource
      le_rfl)

def unitBoundarySuccessorTermCodeCeiling (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def unitBoundarySuccessorBitWidthUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (unitBoundarySuccessorTermCodeCeiling bitBound)

theorem unitBoundarySuccessorStructuralPayloadResource_le_bitWidthUniform
    (valuation : Nat -> Nat) (left right numericBound bitBound : Nat)
    (hvaluation : valuation 0 <= numericBound)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    unitBoundarySuccessorStructuralPayloadResource valuation left right <=
      unitBoundarySuccessorBitWidthUniformPayloadPolynomial
        numericBound bitBound := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let successorTerm : ValuationTerm := ‘!!leftTerm + 1’
  let args : Fin 2 -> ValuationTerm := ![rightTerm, successorTerm]
  have hleftCode : (binaryTermCode leftTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hrightCode : (binaryTermCode rightTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope right bitBound hrightSize
  have hsuccessorCodeRaw := paAddTerm_code_length_le
    leftTerm (‘1’ : ValuationTerm)
  have hsuccessorCode : (binaryTermCode successorTerm).length <=
      unitBoundarySuccessorTermCodeCeiling bitBound := by
    dsimp only [successorTerm]
    change (binaryTermCode
      (paAddTerm leftTerm (‘1’ : ValuationTerm))).length <= _
    exact hsuccessorCodeRaw.trans (by
      unfold unitBoundarySuccessorTermCodeCeiling
      omega)
  have hrightCodeCeiling : (binaryTermCode rightTerm).length <=
      unitBoundarySuccessorTermCodeCeiling bitBound :=
    hrightCode.trans (by
      unfold unitBoundarySuccessorTermCodeCeiling
      omega)
  have hrightVariables : rightTerm.freeVariables ⊆ {0} := by
    rw [show rightTerm.freeVariables = ∅ by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty right]
    simp
  have hsuccessorVariables : successorTerm.freeVariables ⊆ {0} := by
    rw [show successorTerm.freeVariables = ∅ by
      dsimp only [successorTerm]
      rw [arithmeticAddTerm_freeVariables_fixedWidthEntry,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticOneTerm_freeVariables_fixedWidthEntry]
      simp]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    valuation Language.Eq.eq args hrightVariables hsuccessorVariables
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
    valuation Language.Eq.eq args numericBound
      (unitBoundarySuccessorTermCodeCeiling bitBound)
      hrightVariables hsuccessorVariables hvaluation hrightCodeCeiling
      hsuccessorCode
  simpa only [unitBoundarySuccessorStructuralPayloadResource,
    unitBoundarySuccessorBitWidthUniformPayloadPolynomial, args, rightTerm,
    successorTerm, leftTerm] using hpublic.trans hfixed

def unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (&0 : ValuationTerm) numericBound bitBound))

def unitBoundaryRightEntryBitWidthUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (‘&0 + 1’ : ValuationTerm) numericBound bitBound))

def unitBoundaryTerminalContextFormulaCodeSumEnvelope
    (numericBound : Nat) : Nat :=
  FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
    1 numericBound (binaryTermCode (&0 : ValuationTerm)).length

def unitBoundaryTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    unitBoundarySuccessorBitWidthUniformPayloadPolynomial numericBound bitBound
  let contextResource :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let conjunctionTag := (binaryNatCode 4).length
  contextResource + 4 *
    (leftResource + rightResource + successorResource + conjunctionTag + 1) + 1

def unitBoundaryTerminalFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    unitBoundarySuccessorBitWidthUniformPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    unitBoundaryTerminalAssemblySyntaxPolynomial numericBound bitBound
  leftResource + rightResource + successorResource +
    6 * generalContextAssemblyEnvelope syntaxResource

private theorem valuationContextGeneralFormulaCodeSum_le_singleton
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

/-- The two fixed-width entries are charged by numeric loop bounds and binary
coordinate widths.  The successor equality remains visible for the next
uniformization layer. -/
def compactAdditiveUnitBoundaryRowsTerminalEntryBitWidthUniformEnvelope
    (tokenCount boundaryTable index left right numericBound bitBound : Nat) :
    Nat :=
  let valuation := extendValuation index unitZeroValuation
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
      !!(shortBinaryNumeralTerm left) + 1”
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    unitBoundarySuccessorBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightSuccessorResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula successorFormula rightResource successorResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ successorFormula) leftResource rightSuccessorResource

theorem
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
    (tokenCount boundaryTable index left right numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hindexSuccessorSize : Nat.size (index + 1) <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      compactAdditiveUnitBoundaryRowsTerminalEntryBitWidthUniformEnvelope
        tokenCount boundaryTable index left right numericBound bitBound := by
  let valuation := extendValuation index unitZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  have hindex : index <= numericBound := by omega
  have hzeroValuation : unitZeroValuation =
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation := by
    funext coordinate
    simp [unitZeroValuation,
      FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation,
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
  have hleftIndexEvaluation :
      termValue valuation leftIndexTerm = index := by
    change termValue (extendValuation index unitZeroValuation)
      (&0 : ValuationTerm) = index
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZero_under_extendValuation index
  have hrightIndexEvaluation :
      termValue valuation rightIndexTerm = index + 1 := by
    change termValue (extendValuation index unitZeroValuation)
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
    unitBoundarySuccessorStructuralPayloadResource_le_bitWidthUniform
      valuation left right numericBound bitBound hvaluation hleftSize hrightSize
  unfold
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues
    compactAdditiveUnitBoundaryRowsTerminalEntryBitWidthUniformEnvelope
  dsimp only [valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm]
  exact hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hleftResource
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hrightResource
      hsuccessorResource)

theorem
    compactAdditiveUnitBoundaryRowsTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveUnitBoundaryRowsTerminalEntryBitWidthUniformEnvelope
        tokenCount boundaryTable index data.left data.right
          numericBound bitBound <=
      unitBoundaryTerminalFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let valuation := extendValuation index unitZeroValuation
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
      !!(shortBinaryNumeralTerm data.left) + 1”
  let innerFormula := rightFormula ⋏ successorFormula
  let leftResource :=
    unitBoundaryLeftEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let rightResource :=
    unitBoundaryRightEntryBitWidthUniformPayloadPolynomial numericBound bitBound
  let successorResource :=
    unitBoundarySuccessorBitWidthUniformPayloadPolynomial numericBound bitBound
  let contextResource :=
    unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound
  let syntaxResource :=
    unitBoundaryTerminalAssemblySyntaxPolynomial numericBound bitBound
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
  have hzeroValuation : unitZeroValuation =
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation := by
    funext coordinate
    simp [unitZeroValuation,
      FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation,
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
  have hleftIndexEvaluation :
      termValue valuation leftIndexTerm = index := by
    change termValue (extendValuation index unitZeroValuation)
      (&0 : ValuationTerm) = index
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZero_under_extendValuation index
  have hrightIndexEvaluation :
      termValue valuation rightIndexTerm = index + 1 := by
    change termValue (extendValuation index unitZeroValuation)
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
  let successorCertificate := successorEqualityCertificate valuation
    data.left data.right data.successor
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
    (successorEqualityCertificate_structuralPayloadBound_le_transparent
      valuation data.left data.right data.successor).trans
      (unitBoundarySuccessorStructuralPayloadResource_le_bitWidthUniform
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
        arithmeticOneTerm_freeVariables_fixedWidthEntry,
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
    unfold unitBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hcontextResource_le_syntax : contextResource <= syntaxResource := by
    dsimp only [contextResource, syntaxResource]
    unfold unitBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hleftResource_le_syntax : leftResource <= syntaxResource := by
    dsimp only [leftResource, syntaxResource]
    unfold unitBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hrightResource_le_syntax : rightResource <= syntaxResource := by
    dsimp only [rightResource, syntaxResource]
    unfold unitBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hsuccessorResource_le_syntax : successorResource <= syntaxResource := by
    dsimp only [successorResource, syntaxResource]
    unfold unitBoundaryTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hinnerCode_le_syntax :
      (binaryFormulaCode innerFormula).length <= syntaxResource :=
    hinnerCode.trans (by
      dsimp only [rightResource, successorResource, syntaxResource]
      unfold unitBoundaryTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have houterCode_le_syntax :
      (binaryFormulaCode (leftFormula ⋏ innerFormula)).length <=
        syntaxResource :=
    houterCode.trans (by
      dsimp only [leftResource, rightResource, successorResource,
        syntaxResource]
      unfold unitBoundaryTerminalAssemblySyntaxPolynomial
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
      unitBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound
  apply houterGeneral.trans
  unfold hybridConjunctionGeneralPayloadEnvelope at hinnerGeneral
  unfold hybridConjunctionGeneralPayloadEnvelope
    unitBoundaryTerminalFullyUniformPayloadPolynomial
  dsimp only [leftResource, rightResource, successorResource, syntaxResource,
    innerResource] at hinnerGeneral ⊢
  omega

theorem
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveUnitBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope
        tokenCount boundaryTable index data <=
      unitBoundaryTerminalFullyUniformPayloadPolynomial
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
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
      tokenCount boundaryTable index data.left data.right numericBound bitBound
      htokenCount hindexSuccessor htableSize htokenCountSize hindexSize
      hindexSuccessorSize hleftSize hrightSize
  have hassembly :=
    compactAdditiveUnitBoundaryRowsTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
      tokenCount boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize
  simpa only [
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope,
    compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues]
    using hentry.trans hassembly

def compactAdditiveUnitBoundaryRowsBranchFixedWidthEntryEnvelope
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index unitZeroValuation
  let values : Fin 2 -> Nat := ![right, left]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveUnitBoundaryRowsBranchTerminal tokenCount boundaryTable)
    values
    (compactAdditiveUnitBoundaryRowsTerminalFixedWidthEntryEnvelope
      tokenCount boundaryTable index left right)

theorem
    compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
    (tokenCount boundaryTable index left right : Nat) :
    compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      compactAdditiveUnitBoundaryRowsBranchFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right := by
  unfold
    compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelopeOfValues
    compactAdditiveUnitBoundaryRowsBranchFixedWidthEntryEnvelope
  exact explicitBoundedWitnessHybridStructuralPayloadEnvelope_mono _ _ _ _
    (compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
      tokenCount boundaryTable index left right)

def compactAdditiveUnitBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
    (tokenCount boundaryTable index : Nat) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun left =>
    (Finset.range (tokenCount + 1)).sum fun right =>
      compactAdditiveUnitBoundaryRowsBranchFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right

theorem
    compactAdditiveUnitBoundaryRowsPublicFiniteBranchEnvelope_le_fixedWidthEntry
    (tokenCount boundaryTable index : Nat) :
    compactAdditiveUnitBoundaryRowsPublicFiniteBranchEnvelope
        tokenCount boundaryTable index <=
      compactAdditiveUnitBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
        tokenCount boundaryTable index := by
  unfold compactAdditiveUnitBoundaryRowsPublicFiniteBranchEnvelope
    compactAdditiveUnitBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
  exact Finset.sum_le_sum fun left _ =>
    Finset.sum_le_sum fun right _ =>
      compactAdditiveUnitBoundaryRowsBranchStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
        tokenCount boundaryTable index left right

def compactAdditiveUnitBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
    (tokenCount count boundaryTable : Nat) : Nat :=
  ∑ index : Fin count,
    compactAdditiveUnitBoundaryRowsFixedWidthEntryPublicFiniteBranchEnvelope
      tokenCount boundaryTable index

theorem
    compactAdditiveUnitBoundaryRowsPublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveUnitBoundaryRowsPublicFiniteLeafPayloadResourceSum
        tokenCount count boundaryTable <=
      compactAdditiveUnitBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
        tokenCount count boundaryTable := by
  unfold compactAdditiveUnitBoundaryRowsPublicFiniteLeafPayloadResourceSum
    compactAdditiveUnitBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
  exact Finset.sum_le_sum fun index _ =>
    compactAdditiveUnitBoundaryRowsPublicFiniteBranchEnvelope_le_fixedWidthEntry
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

def compactAdditiveUnitBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
    (tokenCount count boundaryTable : Nat) : Nat :=
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm count)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue unitZeroValuation (shortBinaryNumeralTerm count)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    unitZeroValuation body
    (compactAdditiveUnitBoundaryRowsFixedWidthEntryLeafPayloadResourceSum
      tokenCount count boundaryTable)
    bound

theorem
    compactAdditiveUnitBoundaryRowsBranchesPublicFiniteStructuralEnvelope_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveUnitBoundaryRowsBranchesPublicFiniteStructuralEnvelope
        tokenCount count boundaryTable <=
      compactAdditiveUnitBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
        tokenCount count boundaryTable := by
  unfold compactAdditiveUnitBoundaryRowsBranchesPublicFiniteStructuralEnvelope
    compactAdditiveUnitBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
  exact hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (termValue unitZeroValuation (shortBinaryNumeralTerm count))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count))
      (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)).freeVariables
    unitZeroValuation
    (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable)
    (compactAdditiveUnitBoundaryRowsPublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
      tokenCount count boundaryTable)
    (termValue unitZeroValuation (shortBinaryNumeralTerm count))

def compactAdditiveUnitBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
    (tokenCount count boundaryTable : Nat) : Nat :=
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables unitZeroValuation
  let bound := termValue unitZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveUnitBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
      tokenCount count boundaryTable)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource unitZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope
        tokenCount count boundaryTable <=
      compactAdditiveUnitBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
        tokenCount count boundaryTable := by
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables unitZeroValuation
  let bound := termValue unitZeroValuation boundTerm
  let oldCore :=
    compactAdditiveUnitBoundaryRowsBranchesPublicFiniteStructuralEnvelope
      tokenCount count boundaryTable
  let newCore :=
    compactAdditiveUnitBoundaryRowsFixedWidthEntryBranchesStructuralEnvelope
      tokenCount count boundaryTable
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    unitZeroValuation outerVariables boundTerm
  have hcore : oldCore <= newCore :=
    compactAdditiveUnitBoundaryRowsBranchesPublicFiniteStructuralEnvelope_le_fixedWidthEntry
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
    compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope,
    compactAdditiveUnitBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

theorem
    compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_fixedWidthEntry
    (tokenCount count boundaryTable : Nat)
    (hrows : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable) :
    compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope
        tokenCount count boundaryTable hrows <=
      compactAdditiveUnitBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
        tokenCount count boundaryTable :=
  (compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_publicFinite
    tokenCount count boundaryTable hrows).trans
      (compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope_le_fixedWidthEntry
        tokenCount count boundaryTable)

#print axioms
  compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
#print axioms
  compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelopeOfValues_le_entryBitWidthUniform
#print axioms
  unitBoundarySuccessorStructuralPayloadResource_le_bitWidthUniform
#print axioms
  compactAdditiveUnitBoundaryRowsTerminalEntryBitWidthUniformEnvelope_le_fullyUniform
#print axioms
  compactAdditiveUnitBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
#print axioms
  compactAdditiveUnitBoundaryRowsPublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
#print axioms
  compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_fixedWidthEntry

end FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
