import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds

/-!
# Fixed-width entry closure for additive structured-list layouts

This layer first replaces both open-index entries in every boundary-table row
by a common scale-only endpoint.  It then carries that replacement through the
finite witness sums and the boundary-table universal.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

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

private theorem hybridExistsWitnessStructuralPayloadEnvelope_mono
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat) {small large : Nat} (hresource : small <= large) :
    hybridExistsWitnessStructuralPayloadEnvelope valuation body witness small <=
      hybridExistsWitnessStructuralPayloadEnvelope
        valuation body witness large := by
  unfold hybridExistsWitnessStructuralPayloadEnvelope
  dsimp only
  omega

def boundaryRowFixedWidthEntryScale
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index layoutZeroValuation
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

def boundaryRowTerminalFixedWidthEntryEnvelope
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index layoutZeroValuation
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
  let scale := boundaryRowFixedWidthEntryScale
    tokenCount boundaryTable index left right
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let ltResource := boundaryRowClosedLtStructuralPayloadResource
    valuation left right
  let rightLtResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightFormula ltFormula entryResource ltResource
  hybridConjunctionStructuralPayloadEnvelope valuation leftFormula
    (rightFormula ⋏ ltFormula) entryResource rightLtResource

theorem boundaryRowTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
    (tokenCount boundaryTable index left right : Nat) :
    boundaryRowTerminalStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      boundaryRowTerminalFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right := by
  let valuation := extendValuation index layoutZeroValuation
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm : ValuationTerm := &0
  let rightIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftValueTerm := shortBinaryNumeralTerm left
  let rightValueTerm := shortBinaryNumeralTerm right
  let scale := boundaryRowFixedWidthEntryScale
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
    dsimp only [scale, boundaryRowFixedWidthEntryScale, valuation, tableTerm,
      widthTerm, leftIndexTerm, rightIndexTerm, leftValueTerm, rightValueTerm]
    omega
  have hrightScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          rightIndexTerm rightValueTerm <= scale := by
    dsimp only [scale, boundaryRowFixedWidthEntryScale, valuation, tableTerm,
      widthTerm, leftIndexTerm, rightIndexTerm, leftValueTerm, rightValueTerm]
    omega
  have hleftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm leftIndexTerm leftValueTerm scale
        hleftScale htable hwidth hleftIndex hleftValue
  have hrightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm rightIndexTerm rightValueTerm scale
        hrightScale htable hwidth hrightIndex hrightValue
  unfold boundaryRowTerminalStructuralPayloadEnvelopeOfValues
    boundaryRowTerminalFixedWidthEntryEnvelope
  dsimp only [valuation, tableTerm, widthTerm, leftIndexTerm, rightIndexTerm,
    leftValueTerm, rightValueTerm, scale]
  exact hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hleftResource
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hrightResource
      le_rfl)

def boundaryRowBranchFixedWidthEntryEnvelope
    (tokenCount boundaryTable index left right : Nat) : Nat :=
  let valuation := extendValuation index layoutZeroValuation
  let terminalFormula :=
    compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm left) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (‘&0 + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm right) ⋏
        “!!(shortBinaryNumeralTerm left) <
          !!(shortBinaryNumeralTerm right)”)
  let rightGuardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm right) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let rightGuardedResource := hybridConjunctionStructuralPayloadEnvelope
    valuation rightGuardFormula terminalFormula
    (boundaryRowGuardStructuralPayloadResource
      valuation right tokenCount)
    (boundaryRowTerminalFixedWidthEntryEnvelope
      tokenCount boundaryTable index left right)
  let rightExistsFormula : ValuationFormula :=
    ∃⁰ boundaryRowRightWitnessBody tokenCount boundaryTable left
  let rightExistsResource := hybridExistsWitnessStructuralPayloadEnvelope
    valuation (boundaryRowRightWitnessBody
      tokenCount boundaryTable left) right rightGuardedResource
  let leftGuardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm left) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let leftGuardedResource := hybridConjunctionStructuralPayloadEnvelope
    valuation leftGuardFormula rightExistsFormula
    (boundaryRowGuardStructuralPayloadResource
      valuation left tokenCount)
    rightExistsResource
  hybridExistsWitnessStructuralPayloadEnvelope valuation
    (boundaryRowLeftWitnessBody tokenCount boundaryTable)
    left leftGuardedResource

theorem boundaryRowBranchStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
    (tokenCount boundaryTable index left right : Nat) :
    boundaryRowBranchStructuralPayloadEnvelopeOfValues
        tokenCount boundaryTable index left right <=
      boundaryRowBranchFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right := by
  have hterminal :=
    boundaryRowTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
      tokenCount boundaryTable index left right
  unfold boundaryRowBranchStructuralPayloadEnvelopeOfValues
    boundaryRowBranchFixedWidthEntryEnvelope
  exact hybridExistsWitnessStructuralPayloadEnvelope_mono _ _ _
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
      (hybridExistsWitnessStructuralPayloadEnvelope_mono _ _ _
        (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ le_rfl
          hterminal)))

def boundaryRowFixedWidthEntryPublicFiniteBranchEnvelope
    (tokenCount boundaryTable index : Nat) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun left =>
    (Finset.range (tokenCount + 1)).sum fun right =>
      boundaryRowBranchFixedWidthEntryEnvelope
        tokenCount boundaryTable index left right

theorem boundaryRowPublicFiniteBranchEnvelope_le_fixedWidthEntry
    (tokenCount boundaryTable index : Nat) :
    boundaryRowPublicFiniteBranchEnvelope tokenCount boundaryTable index <=
      boundaryRowFixedWidthEntryPublicFiniteBranchEnvelope
        tokenCount boundaryTable index := by
  unfold boundaryRowPublicFiniteBranchEnvelope
    boundaryRowFixedWidthEntryPublicFiniteBranchEnvelope
  exact Finset.sum_le_sum fun left _ =>
    Finset.sum_le_sum fun right _ =>
      boundaryRowBranchStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
        tokenCount boundaryTable index left right

def boundaryTableFixedWidthEntryLeafPayloadResourceSum
    (tokenCount partCount boundaryTable : Nat) : Nat :=
  ∑ index : Fin partCount,
    boundaryRowFixedWidthEntryPublicFiniteBranchEnvelope
      tokenCount boundaryTable index

theorem boundaryTablePublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
    (tokenCount partCount boundaryTable : Nat) :
    boundaryTablePublicFiniteLeafPayloadResourceSum
        tokenCount partCount boundaryTable <=
      boundaryTableFixedWidthEntryLeafPayloadResourceSum
        tokenCount partCount boundaryTable := by
  unfold boundaryTablePublicFiniteLeafPayloadResourceSum
    boundaryTableFixedWidthEntryLeafPayloadResourceSum
  exact Finset.sum_le_sum fun index _ =>
    boundaryRowPublicFiniteBranchEnvelope_le_fixedWidthEntry
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

def boundaryTableFixedWidthEntryBranchesStructuralEnvelope
    (tokenCount partCount boundaryTable : Nat) : Nat :=
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue layoutZeroValuation boundTerm
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    layoutZeroValuation body
    (boundaryTableFixedWidthEntryLeafPayloadResourceSum
      tokenCount partCount boundaryTable)
    bound

theorem boundaryTableBranchesPublicFiniteStructuralEnvelope_le_fixedWidthEntry
    (tokenCount partCount boundaryTable : Nat) :
    boundaryTableBranchesPublicFiniteStructuralEnvelope
        tokenCount partCount boundaryTable <=
      boundaryTableFixedWidthEntryBranchesStructuralEnvelope
        tokenCount partCount boundaryTable := by
  unfold boundaryTableBranchesPublicFiniteStructuralEnvelope
    boundaryTableFixedWidthEntryBranchesStructuralEnvelope
  exact hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (termValue layoutZeroValuation (shortBinaryNumeralTerm partCount))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm partCount))
      (compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable)).freeVariables
    layoutZeroValuation
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
    (boundaryTablePublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
      tokenCount partCount boundaryTable)
    (termValue layoutZeroValuation (shortBinaryNumeralTerm partCount))

def boundaryTableFixedWidthEntryUniversalStructuralPayloadEnvelope
    (tokenCount partCount boundaryTable : Nat) : Nat :=
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables layoutZeroValuation
  let bound := termValue layoutZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (boundaryTableFixedWidthEntryBranchesStructuralEnvelope
      tokenCount partCount boundaryTable)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource layoutZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope_le_fixedWidthEntry
    (tokenCount partCount boundaryTable : Nat) :
    boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope
        tokenCount partCount boundaryTable <=
      boundaryTableFixedWidthEntryUniversalStructuralPayloadEnvelope
        tokenCount partCount boundaryTable := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := shortBinaryNumeralTerm partCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables layoutZeroValuation
  let bound := termValue layoutZeroValuation boundTerm
  let oldCore := boundaryTableBranchesPublicFiniteStructuralEnvelope
    tokenCount partCount boundaryTable
  let newCore := boundaryTableFixedWidthEntryBranchesStructuralEnvelope
    tokenCount partCount boundaryTable
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    layoutZeroValuation outerVariables boundTerm
  have hcore : oldCore <= newCore :=
    boundaryTableBranchesPublicFiniteStructuralEnvelope_le_fixedWidthEntry
      tokenCount partCount boundaryTable
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranch
  simpa only [boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope,
    boundaryTableFixedWidthEntryUniversalStructuralPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

def compactAdditiveBoundaryTableFixedWidthEntryScale
    (tokenCount partCount start finish boundaryTable : Nat) : Nat :=
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startIndexTerm := unaryNumeralTerm 0
  let finishIndexTerm := shortBinaryNumeralTerm partCount
  let startValueTerm := shortBinaryNumeralTerm start
  let finishValueTerm := shortBinaryNumeralTerm finish
  fixedWidthOpenIndexAtomicCoordinateScale layoutZeroValuation tableTerm
      widthTerm startIndexTerm startValueTerm +
    fixedWidthOpenIndexAtomicCoordinateScale layoutZeroValuation tableTerm
      widthTerm finishIndexTerm finishValueTerm

def compactAdditiveBoundaryTableFixedWidthEntryStructuralPayloadEnvelope
    (tokenCount partCount start finish boundaryTable : Nat) : Nat :=
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount)
    (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody
      tokenCount boundaryTable).ballLT
        (shortBinaryNumeralTerm partCount)
  let startResource := boundaryClosedLeStructuralPayloadEnvelope
    layoutZeroValuation start tokenCount
  let finishResource := boundaryClosedLeStructuralPayloadEnvelope
    layoutZeroValuation finish tokenCount
  let scale := compactAdditiveBoundaryTableFixedWidthEntryScale
    tokenCount partCount start finish boundaryTable
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let universalResource :=
    boundaryTableFixedWidthEntryUniversalStructuralPayloadEnvelope
      tokenCount partCount boundaryTable
  let finishEntryUniversalResource :=
    hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
      finishEntryFormula universalFormula entryResource universalResource
  let startEntryTailResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation startEntryFormula
    (finishEntryFormula ⋏ universalFormula)
    entryResource finishEntryUniversalResource
  let finishTailResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation finishFormula
    (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula))
    finishResource startEntryTailResource
  hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
    startFormula
    (finishFormula ⋏
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula)))
    startResource finishTailResource

theorem
    compactAdditiveBoundaryTableExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
    (tokenCount partCount start finish boundaryTable : Nat)
    (hstartBound : start <= tokenCount)
    (hfinishBound : finish <= tokenCount)
    (hstartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 start)
    (hfinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount partCount finish)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveBoundaryTableExplicitHybridCertificate
          tokenCount partCount start finish boundaryTable
          hstartBound hfinishBound hstartEntry hfinishEntry rows) <=
      compactAdditiveBoundaryTableFixedWidthEntryStructuralPayloadEnvelope
        tokenCount partCount start finish boundaryTable := by
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startIndexTerm := unaryNumeralTerm 0
  let finishIndexTerm := shortBinaryNumeralTerm partCount
  let startValueTerm := shortBinaryNumeralTerm start
  let finishValueTerm := shortBinaryNumeralTerm finish
  let scale := compactAdditiveBoundaryTableFixedWidthEntryScale
    tokenCount partCount start finish boundaryTable
  let startCertificate :=
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLeCertificate
      layoutZeroValuation start tokenCount hstartBound
  let finishCertificate :=
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.closedLeCertificate
      layoutZeroValuation finish tokenCount hfinishBound
  have hstartEntryAtTerms : CompactFixedWidthEntry
      (termValue layoutZeroValuation tableTerm)
      (termValue layoutZeroValuation widthTerm)
      (termValue layoutZeroValuation startIndexTerm)
      (termValue layoutZeroValuation startValueTerm) := by
    simpa only [tableTerm, widthTerm, startIndexTerm, startValueTerm,
      termValue_shortBinaryNumeralTerm, termValue_unaryNumeralTerm] using
      hstartEntry
  have hfinishEntryAtTerms : CompactFixedWidthEntry
      (termValue layoutZeroValuation tableTerm)
      (termValue layoutZeroValuation widthTerm)
      (termValue layoutZeroValuation finishIndexTerm)
      (termValue layoutZeroValuation finishValueTerm) := by
    simpa only [tableTerm, widthTerm, finishIndexTerm, finishValueTerm,
      termValue_shortBinaryNumeralTerm] using hfinishEntry
  let startEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      layoutZeroValuation tableTerm widthTerm startIndexTerm startValueTerm
        hstartEntryAtTerms
  let finishEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      layoutZeroValuation tableTerm widthTerm finishIndexTerm finishValueTerm
        hfinishEntryAtTerms
  let universalCertificate := boundaryTableUniversalCertificate
    tokenCount partCount boundaryTable rows
  have hstart := closedLeCertificate_structuralPayloadBound_le_transparent
    layoutZeroValuation start tokenCount hstartBound
  have hfinish := closedLeCertificate_structuralPayloadBound_le_transparent
    layoutZeroValuation finish tokenCount hfinishBound
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstartIndexEmpty : startIndexTerm.freeVariables = ∅ := by
    simp [startIndexTerm, unaryNumeralTerm,
      LO.FirstOrder.Semiterm.Operator.operator]
  have hfinishIndexEmpty : finishIndexTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty partCount
  have hstartIndex : startIndexTerm.freeVariables ⊆ {0} := by
    rw [hstartIndexEmpty]
    simp
  have hfinishIndex : finishIndexTerm.freeVariables ⊆ {0} := by
    rw [hfinishIndexEmpty]
    simp
  have hstartValue : startValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty start
  have hfinishValue : finishValueTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty finish
  have hstartScale :
      fixedWidthOpenIndexAtomicCoordinateScale layoutZeroValuation tableTerm
          widthTerm startIndexTerm startValueTerm <= scale := by
    dsimp only [scale, compactAdditiveBoundaryTableFixedWidthEntryScale,
      tableTerm, widthTerm, startIndexTerm, finishIndexTerm,
      startValueTerm, finishValueTerm]
    omega
  have hfinishScale :
      fixedWidthOpenIndexAtomicCoordinateScale layoutZeroValuation tableTerm
          widthTerm finishIndexTerm finishValueTerm <= scale := by
    dsimp only [scale, compactAdditiveBoundaryTableFixedWidthEntryScale,
      tableTerm, widthTerm, startIndexTerm, finishIndexTerm,
      startValueTerm, finishValueTerm]
    omega
  have hstartEntryOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      layoutZeroValuation tableTerm widthTerm startIndexTerm startValueTerm
        htable hwidth hstartIndex hstartValue hstartEntryAtTerms
  have hstartEntryFixed :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      layoutZeroValuation tableTerm widthTerm startIndexTerm startValueTerm
        scale hstartScale htable hwidth hstartIndex hstartValue
  have hstartEntryResource := hstartEntryOpen.trans hstartEntryFixed
  have hfinishEntryOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      layoutZeroValuation tableTerm widthTerm finishIndexTerm finishValueTerm
        htable hwidth hfinishIndex hfinishValue hfinishEntryAtTerms
  have hfinishEntryFixed :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      layoutZeroValuation tableTerm widthTerm finishIndexTerm finishValueTerm
        scale hfinishScale htable hwidth hfinishIndex hfinishValue
  have hfinishEntryResource := hfinishEntryOpen.trans hfinishEntryFixed
  have huniversalTransparent :=
    boundaryTableUniversalCertificate_structuralPayloadBound_le_transparent
      tokenCount partCount boundaryTable rows
  have huniversalPublic := huniversalTransparent.trans
    (boundaryTableUniversalStructuralPayloadEnvelope_le_publicFinite
      tokenCount partCount boundaryTable rows)
  have huniversal := huniversalPublic.trans
    (boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope_le_fixedWidthEntry
      tokenCount partCount boundaryTable)
  let finishEntryUniversal :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      finishEntryCertificate universalCertificate
  have hfinishEntryUniversal :=
    hybridConjunctionStructuralPayloadBound_le_envelope
      finishEntryCertificate universalCertificate _ _
      hfinishEntryResource huniversal
  let startEntryTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      startEntryCertificate finishEntryUniversal
  have hstartEntryTail := hybridConjunctionStructuralPayloadBound_le_envelope
    startEntryCertificate finishEntryUniversal _ _
    hstartEntryResource hfinishEntryUniversal
  let finishTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      finishCertificate startEntryTail
  have hfinishTail := hybridConjunctionStructuralPayloadBound_le_envelope
    finishCertificate startEntryTail _ _ hfinish hstartEntryTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    startCertificate finishTail
  have hparts := hybridConjunctionStructuralPayloadBound_le_envelope
    startCertificate finishTail _ _ hstart hfinishTail
  simpa only [compactAdditiveBoundaryTableExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveBoundaryTableFixedWidthEntryStructuralPayloadEnvelope,
    tableTerm, widthTerm, startIndexTerm, finishIndexTerm, startValueTerm,
    finishValueTerm, scale, startCertificate, finishCertificate,
    startEntryCertificate, finishEntryCertificate, universalCertificate,
    finishEntryUniversal, startEntryTail, finishTail, parts] using hparts

def compactAdditiveStructuredListLayoutFixedWidthEntryAtBodyStartEnvelope
    (tokenTable width tokenCount start count finish boundaryTable bodyStart :
      Nat) : Nat :=
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let guardFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm bodyStart) <
      !!(shortBinaryNumeralTerm tokenCount) + 1”
  let headerFormula :=
    FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
      tokenTable width tokenCount start count bodyStart
  let boundaryFormula := compactAdditiveBoundaryTableClosedFormula
    tokenCount count bodyStart finish boundaryTable
  let headerResource :=
    compactAdditiveListHeaderStructuralPayloadPolynomial
      tokenTable width tokenCount start count bodyStart
  let boundaryResource :=
    compactAdditiveBoundaryTableFixedWidthEntryStructuralPayloadEnvelope
      tokenCount count bodyStart finish boundaryTable
  let innerResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation headerFormula boundaryFormula
    headerResource boundaryResource
  let postResource := hybridConjunctionStructuralPayloadEnvelope
    layoutZeroValuation guardFormula (headerFormula ⋏ boundaryFormula)
    (boundaryRowGuardStructuralPayloadResource
      layoutZeroValuation bodyStart tokenCount)
    innerResource
  hybridExistsWitnessStructuralPayloadEnvelope layoutZeroValuation
    witnessBody bodyStart postResource

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
    (tokenTable width tokenCount start count finish boundaryTable bodyStart :
      Nat)
    (hbodyStart : bodyStart <= tokenCount)
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart)
    (hboundaryFinish : finish <= tokenCount)
    (hboundaryStartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 bodyStart)
    (hboundaryFinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount count finish)
    (rows : (index : Fin count) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificate
          tokenTable width tokenCount start count finish boundaryTable
          bodyStart hbodyStart hheader hboundaryFinish
          hboundaryStartEntry hboundaryFinishEntry rows) <=
      compactAdditiveStructuredListLayoutFixedWidthEntryAtBodyStartEnvelope
        tokenTable width tokenCount start count finish boundaryTable
        bodyStart := by
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let guardCertificate := boundedWitnessGuardCertificate
    layoutZeroValuation bodyStart tokenCount hbodyStart
  let headerCertificate :=
    compactAdditiveListHeaderExplicitHybridCertificate
      tokenTable width tokenCount start count bodyStart hheader
  let boundaryCertificate :=
    compactAdditiveBoundaryTableExplicitHybridCertificate
      tokenCount count bodyStart finish boundaryTable
      hbodyStart hboundaryFinish hboundaryStartEntry
      hboundaryFinishEntry rows
  let inner := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    headerCertificate boundaryCertificate
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guardCertificate inner
  have hguard :=
    boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
      layoutZeroValuation bodyStart tokenCount hbodyStart
  have hheaderResource :=
    compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount start count bodyStart hheader
  have hboundaryResource :=
    compactAdditiveBoundaryTableExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
      tokenCount count bodyStart finish boundaryTable
      hbodyStart hboundaryFinish hboundaryStartEntry
      hboundaryFinishEntry rows
  have hinner : hybridFormulaStructuralPayloadBound inner <=
      hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
        (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
          tokenTable width tokenCount start count bodyStart)
        (compactAdditiveBoundaryTableClosedFormula
          tokenCount count bodyStart finish boundaryTable)
        (compactAdditiveListHeaderStructuralPayloadPolynomial
          tokenTable width tokenCount start count bodyStart)
        (compactAdditiveBoundaryTableFixedWidthEntryStructuralPayloadEnvelope
          tokenCount count bodyStart finish boundaryTable) := by
    have hraw := hybridConjunctionStructuralPayloadBound_le_envelope
      headerCertificate boundaryCertificate _ _
      hheaderResource hboundaryResource
    have hzero :
        FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation =
          FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation := by
      funext index
      rfl
    simpa only [inner, headerCertificate, boundaryCertificate,
      layoutZeroValuation, hzero] using hraw
  have hpost := hybridConjunctionStructuralPayloadBound_le_envelope
    guardCertificate inner _ _ hguard hinner
  let installed := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactAdditiveStructuredListLayoutWitnessBody_subst
      tokenTable width tokenCount start count finish boundaryTable
      bodyStart).symm post
  have hinstalled : hybridFormulaStructuralPayloadBound installed <=
      hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
        (“!!(shortBinaryNumeralTerm bodyStart) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” : ValuationFormula)
        (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
            tokenTable width tokenCount start count bodyStart ⋏
          compactAdditiveBoundaryTableClosedFormula
            tokenCount count bodyStart finish boundaryTable)
        (boundaryRowGuardStructuralPayloadResource
          layoutZeroValuation bodyStart tokenCount)
        (hybridConjunctionStructuralPayloadEnvelope layoutZeroValuation
          (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
            tokenTable width tokenCount start count bodyStart)
          (compactAdditiveBoundaryTableClosedFormula
            tokenCount count bodyStart finish boundaryTable)
          (compactAdditiveListHeaderStructuralPayloadPolynomial
            tokenTable width tokenCount start count bodyStart)
          (compactAdditiveBoundaryTableFixedWidthEntryStructuralPayloadEnvelope
            tokenCount count bodyStart finish boundaryTable)) := by
    simpa only [installed, hybridFormulaStructuralPayloadBound,
      post, inner, guardCertificate, headerCertificate,
      boundaryCertificate, layoutZeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation,
      FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation]
      using hpost
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      witnessBody bodyStart installed
  have hdirect := hybridExistsWitnessStructuralPayloadBound_le_envelope
    witnessBody bodyStart installed _ hinstalled
  simpa only [compactAdditiveStructuredListLayoutExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveStructuredListLayoutFixedWidthEntryAtBodyStartEnvelope,
    witnessBody, guardCertificate, headerCertificate, boundaryCertificate,
    inner, post, installed, direct] using hdirect

def compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    Nat :=
  (Finset.range (tokenCount + 1)).sum fun bodyStart =>
    compactAdditiveStructuredListLayoutFixedWidthEntryAtBodyStartEnvelope
      tokenTable width tokenCount start count finish boundaryTable bodyStart

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_fixedWidthEntry
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (data : CompactAdditiveStructuredListLayoutData
      tokenTable width tokenCount start count finish boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData
          tokenTable width tokenCount start count finish boundaryTable data) <=
      compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable := by
  have hatBodyStart :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
      tokenTable width tokenCount start count finish boundaryTable
      data.bodyStart data.bodyStart_le_tokenCount data.header
      data.boundaryFinish_le_tokenCount data.boundaryStartEntry
      data.boundaryFinishEntry data.rows
  have hsum :
      compactAdditiveStructuredListLayoutFixedWidthEntryAtBodyStartEnvelope
          tokenTable width tokenCount start count finish boundaryTable
          data.bodyStart <=
        compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
          tokenTable width tokenCount start count finish boundaryTable := by
    unfold
      compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compactAdditiveStructuredListLayoutFixedWidthEntryAtBodyStartEnvelope
          tokenTable width tokenCount start count finish boundaryTable
          candidate))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le data.bodyStart_le_tokenCount))
  simpa only [
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData] using
      hatBodyStart.trans hsum

theorem
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_fixedWidthEntry
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start count finish boundaryTable
          hlayout) <=
      compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable := by
  exact
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData_structuralPayloadBound_le_fixedWidthEntry
      tokenTable width tokenCount start count finish boundaryTable
      (compactAdditiveStructuredListLayoutDataOfLayout
        tokenTable width tokenCount start count finish boundaryTable hlayout)

#print axioms
  boundaryRowTerminalStructuralPayloadEnvelopeOfValues_le_fixedWidthEntry
#print axioms
  boundaryTablePublicFiniteLeafPayloadResourceSum_le_fixedWidthEntry
#print axioms
  boundaryTablePublicFiniteUniversalStructuralPayloadEnvelope_le_fixedWidthEntry
#print axioms
  compactAdditiveBoundaryTableExplicitHybridCertificate_structuralPayloadBound_le_fixedWidthEntry
#print axioms
  compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_fixedWidthEntry

end FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
