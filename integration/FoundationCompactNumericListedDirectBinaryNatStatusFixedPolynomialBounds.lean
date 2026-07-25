import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds

/-!
# Fixed-polynomial bounds for binary-Nat status certificates

This layer first bounds the seven-leaf failed/completed-prefix terminal by one
resource depending only on common numeric and bit-width coordinates.  The two
fixed-width entries use the open-index endpoint, so no closed/open resource
identification is hidden in definitional reduction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds

private abbrev statusZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

private theorem shortBinaryNumeralTerm_zero_eq_paZero :
    shortBinaryNumeralTerm 0 = (‘0’ : ValuationTerm) := by
  simp [shortBinaryNumeralTerm,
    FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
    FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
    LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]

private theorem termValue_statusZeroValuation_zero :
    termValue statusZeroValuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero statusZeroValuation ![]

private theorem termValue_statusZeroValuation_one :
    termValue statusZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one statusZeroValuation ![]

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

private theorem arithmeticZeroTerm_freeVariables_eq_empty :
    (‘0’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq]

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem paZeroTerm_code_length_le_binaryNumeralEnvelope
    (bitBound : Nat) :
    (binaryTermCode (‘0’ : ValuationTerm)).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
  have hbase : (binaryTermCode (‘0’ : ValuationTerm)).length <=
      binaryNumeralTermCodeEnvelope 0 := by decide
  exact hbase.trans
    (FoundationCompactPAExponentialShortNumeralCompilerBounds.binaryNumeralTermCodeEnvelope_mono_short
      (Nat.zero_le bitBound))

private theorem paOneTerm_code_length_le_binaryNumeralEnvelope
    (bitBound : Nat) (hbitPositive : 1 <= bitBound) :
    (binaryTermCode (‘1’ : ValuationTerm)).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
  have hbase : (binaryTermCode (‘1’ : ValuationTerm)).length <=
      binaryNumeralTermCodeEnvelope 1 := by decide
  exact hbase.trans
    (FoundationCompactPAExponentialShortNumeralCompilerBounds.binaryNumeralTermCodeEnvelope_mono_short
      hbitPositive)

private theorem hybridConjunctionGeneralPayloadEnvelope_mono
    {resource leftSmall leftLarge rightSmall rightLarge : Nat}
    (hleft : leftSmall <= leftLarge)
    (hright : rightSmall <= rightLarge) :
    hybridConjunctionGeneralPayloadEnvelope resource leftSmall rightSmall <=
      hybridConjunctionGeneralPayloadEnvelope resource leftLarge rightLarge := by
  unfold hybridConjunctionGeneralPayloadEnvelope
  omega

def binaryNatStatusSevenLeafSyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let contextCode := additiveTokenCellContextFormulaCodeSumEnvelope numericBound
  let atomicCode := additiveTokenCellAtomicFormulaCodeEnvelope bitBound
  let entryCode := additiveTokenCellEntryFormulaCodeEnvelope bitBound
  let conjunctionTag := (binaryNatCode 4).length
  contextCode + 5 * atomicCode + 2 * entryCode + 6 * conjunctionTag + 1

theorem sevenLeafRightConjunctionFormula_code_length_le_syntaxPolynomial
    (numericBound bitBound : Nat)
    (formula1 formula2 formula3 formula4 formula5 formula6 formula7 :
      ValuationFormula)
    (hcode1 : (binaryFormulaCode formula1).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode2 : (binaryFormulaCode formula2).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode3 : (binaryFormulaCode formula3).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode4 : (binaryFormulaCode formula4).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound)
    (hcode5 : (binaryFormulaCode formula5).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode6 : (binaryFormulaCode formula6).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode7 : (binaryFormulaCode formula7).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound) :
    (binaryFormulaCode
      (formula1 ⋏ (formula2 ⋏ (formula3 ⋏
        (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))))))).length <=
      binaryNatStatusSevenLeafSyntaxPolynomial numericBound bitBound := by
  let formula67 := formula6 ⋏ formula7
  let formula567 := formula5 ⋏ formula67
  let formula4567 := formula4 ⋏ formula567
  let formula34567 := formula3 ⋏ formula4567
  let formula234567 := formula2 ⋏ formula34567
  let atomicCode := additiveTokenCellAtomicFormulaCodeEnvelope bitBound
  let entryCode := additiveTokenCellEntryFormulaCodeEnvelope bitBound
  let conjunctionTag := (binaryNatCode 4).length
  have hcode67Raw := binaryFormulaCode_and_length_le_local formula6 formula7
  have hcode67 : (binaryFormulaCode formula67).length <=
      atomicCode + entryCode + conjunctionTag := by
    dsimp only [formula67, atomicCode, entryCode, conjunctionTag]
      at hcode67Raw ⊢
    omega
  have hcode567Raw := binaryFormulaCode_and_length_le_local formula5 formula67
  have hcode567 : (binaryFormulaCode formula567).length <=
      2 * atomicCode + entryCode + 2 * conjunctionTag := by
    dsimp only [formula567] at hcode567Raw ⊢
    omega
  have hcode4567Raw := binaryFormulaCode_and_length_le_local formula4 formula567
  have hcode4567 : (binaryFormulaCode formula4567).length <=
      2 * atomicCode + 2 * entryCode + 3 * conjunctionTag := by
    dsimp only [formula4567] at hcode4567Raw ⊢
    omega
  have hcode34567Raw := binaryFormulaCode_and_length_le_local formula3 formula4567
  have hcode34567 : (binaryFormulaCode formula34567).length <=
      3 * atomicCode + 2 * entryCode + 4 * conjunctionTag := by
    dsimp only [formula34567] at hcode34567Raw ⊢
    omega
  have hcode234567Raw := binaryFormulaCode_and_length_le_local formula2 formula34567
  have hcode234567 : (binaryFormulaCode formula234567).length <=
      4 * atomicCode + 2 * entryCode + 5 * conjunctionTag := by
    dsimp only [formula234567] at hcode234567Raw ⊢
    omega
  have hcodeAllRaw := binaryFormulaCode_and_length_le_local
    formula1 formula234567
  change (binaryFormulaCode (formula1 ⋏ formula234567)).length <= _
  calc
    (binaryFormulaCode (formula1 ⋏ formula234567)).length <=
        (binaryFormulaCode formula1).length +
          (binaryFormulaCode formula234567).length + conjunctionTag := by
      simpa only [conjunctionTag] using hcodeAllRaw
    _ <= 5 * atomicCode + 2 * entryCode + 6 * conjunctionTag := by omega
    _ <= binaryNatStatusSevenLeafSyntaxPolynomial
        numericBound bitBound := by
      unfold binaryNatStatusSevenLeafSyntaxPolynomial
      dsimp only [atomicCode, entryCode, conjunctionTag]
      omega

def hybridExistsWitnessGeneralPayloadEnvelope
    (syntaxResource bodyResource : Nat) : Nat :=
  bodyResource + 2 * generalContextAssemblyEnvelope syntaxResource

theorem hybridExistsWitnessStructuralPayloadEnvelope_le_general
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat)
    (bodyResource syntaxResource : Nat)
    (hresource : 1 <= syntaxResource)
    (hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext
            (∃⁰ body : ValuationFormula).freeVariables valuation) <=
        syntaxResource)
    (hbody : (binaryFormulaCode body).length <= syntaxResource)
    (hwitness : (binaryTermCode (shortBinaryNumeralTerm witness)).length <=
      syntaxResource)
    (hinstantiated : (binaryFormulaCode
      (body/[shortBinaryNumeralTerm witness])).length <= syntaxResource)
    (hexistential : (binaryFormulaCode
      (∃⁰ body : ValuationFormula)).length <= syntaxResource) :
    hybridExistsWitnessStructuralPayloadEnvelope valuation body witness
        bodyResource <=
      hybridExistsWitnessGeneralPayloadEnvelope syntaxResource bodyResource := by
  let formula : ValuationFormula := ∃⁰ body
  let witnessTerm := shortBinaryNumeralTerm witness
  let instantiated : ValuationFormula := body/[witnessTerm]
  let Gamma := valuationContext formula.freeVariables valuation
  have hinstantiatedTerm : (binaryFormulaCode instantiated).length <=
      syntaxResource := by
    simpa only [instantiated, witnessTerm] using hinstantiated
  have hcontextGamma :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          Gamma <= syntaxResource := by
    simpa only [Gamma, formula] using hcontext
  have hinsertRaw :=
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds.formulaCodeSum_insert_le
      Gamma instantiated
  have hinsert :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (insert instantiated Gamma) <=
        generalContextCoordinate syntaxResource := by
    calc
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (insert instantiated Gamma) <=
          (binaryFormulaCode instantiated).length +
            FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
              Gamma := hinsertRaw
      _ <= syntaxResource + syntaxResource :=
        Nat.add_le_add hinstantiatedTerm hcontextGamma
      _ <= generalContextCoordinate syntaxResource := by
        unfold generalContextCoordinate
        omega
  have hweak := weakeningFullAssemblyCost_le_general
    (insert instantiated Gamma) syntaxResource hinsert
  have hexists := existsIntroFullAssemblyCost_le_general Gamma body witnessTerm
    syntaxResource hresource hcontextGamma hbody hwitness hinstantiatedTerm
    hexistential
  unfold hybridExistsWitnessStructuralPayloadEnvelope
    hybridExistsWitnessGeneralPayloadEnvelope
  dsimp only [formula, witnessTerm, instantiated, Gamma] at hweak hexists ⊢
  omega

theorem fiveShortNumeralRewritingFormula_code_length_le_uniform
    (formula : LO.FirstOrder.ArithmeticSemisentence 5)
    (value0 value1 value2 value3 value4 bitBound : Nat)
    (hsize0 : Nat.size value0 <= bitBound)
    (hsize1 : Nat.size value1 <= bitBound)
    (hsize2 : Nat.size value2 <= bitBound)
    (hsize3 : Nat.size value3 <= bitBound)
    (hsize4 : Nat.size value4 <= bitBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) formula) ⇜
        ![shortBinaryNumeralTerm value0, shortBinaryNumeralTerm value1,
          shortBinaryNumeralTerm value2, shortBinaryNumeralTerm value3,
          shortBinaryNumeralTerm value4])).length <=
      uniformRewritingFormulaCodeEnvelope
        (binaryNumeralTermCodeEnvelope bitBound)
        (binaryFormulaCode (Rewriting.emb (ξ := Nat) formula)).length := by
  let rewriting : Rew ℒₒᵣ Nat 5 Nat 0 := Rew.subst
    ![shortBinaryNumeralTerm value0, shortBinaryNumeralTerm value1,
      shortBinaryNumeralTerm value2, shortBinaryNumeralTerm value3,
      shortBinaryNumeralTerm value4]
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro index
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      fin_cases index
      · exact binaryNumeralTerm_code_length_le_envelope value0 bitBound hsize0
      · exact binaryNumeralTerm_code_length_le_envelope value1 bitBound hsize1
      · exact binaryNumeralTerm_code_length_le_envelope value2 bitBound hsize2
      · exact binaryNumeralTerm_code_length_le_envelope value3 bitBound hsize3
      · exact binaryNumeralTerm_code_length_le_envelope value4 bitBound hsize4
    · intro index
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) formula)
  simpa only [rewriting] using hraw

theorem fiveShortNumeralRewritingFormula_freeVariables_eq_empty
    (formula : LO.FirstOrder.ArithmeticSemisentence 5)
    (value0 value1 value2 value3 value4 : Nat) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜
      ![shortBinaryNumeralTerm value0, shortBinaryNumeralTerm value1,
        shortBinaryNumeralTerm value2, shortBinaryNumeralTerm value3,
        shortBinaryNumeralTerm value4]).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value0
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value1
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value2
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value3
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value4

def binaryNatStatusDoubleClosedFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let failedCode := uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactBinaryNatFailedStatusSliceDef.val)).length
  let completedCode := uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatCompletedStatusPrefixDef.val)).length
  failedCode + completedCode + 1

theorem compactBinaryNatFailedStatusSliceClosedFormula_code_length_le_uniform
    (tokenTable width tokenCount start finish bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatFailedStatusSliceClosedFormula
        tokenTable width tokenCount start finish)).length <=
      binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound := by
  have hraw := fiveShortNumeralRewritingFormula_code_length_le_uniform
    compactBinaryNatFailedStatusSliceDef.val tokenTable width tokenCount start
    finish bitBound htableSize hwidthSize htokenCountSize hstartSize hfinishSize
  unfold compactBinaryNatFailedStatusSliceClosedFormula
    binaryNatStatusDoubleClosedFormulaCodeEnvelope
  dsimp only
  omega

theorem compactBinaryNatFailedStatusSliceClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start finish : Nat) :
    (compactBinaryNatFailedStatusSliceClosedFormula
      tokenTable width tokenCount start finish).freeVariables = ∅ := by
  unfold compactBinaryNatFailedStatusSliceClosedFormula
  exact fiveShortNumeralRewritingFormula_freeVariables_eq_empty
    compactBinaryNatFailedStatusSliceDef.val tokenTable width tokenCount start
    finish

theorem
    compactBinaryNatCompletedStatusPrefixClosedFormula_code_length_le_uniform
    (tokenTable width tokenCount start outputStart bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatCompletedStatusPrefixClosedFormula
        tokenTable width tokenCount start outputStart)).length <=
      binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound := by
  have hraw := fiveShortNumeralRewritingFormula_code_length_le_uniform
    compactBinaryNatCompletedStatusPrefixDef.val tokenTable width tokenCount
    start outputStart bitBound htableSize hwidthSize htokenCountSize hstartSize
    houtputStartSize
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
    binaryNatStatusDoubleClosedFormulaCodeEnvelope
  dsimp only
  omega

theorem
    compactBinaryNatCompletedStatusPrefixClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start outputStart : Nat) :
    (compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount start outputStart).freeVariables = ∅ := by
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
  exact fiveShortNumeralRewritingFormula_freeVariables_eq_empty
    compactBinaryNatCompletedStatusPrefixDef.val tokenTable width tokenCount
    start outputStart

private theorem binaryFormulaCode_body_length_le_exists
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    binaryNatStatusSevenLeafSyntaxPolynomial numericBound bitBound
  let atomicResource :=
    additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound
  let entryResource :=
    additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound
  let resource67 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource entryResource
  let resource567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource resource67
  let resource4567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    entryResource resource567
  let resource34567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource resource4567
  let resource234567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource resource34567
  hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
    resource234567

def binaryNatStatusOuterExistsSyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  binaryNatStatusSevenLeafFullyUniformPayloadPolynomial numericBound bitBound +
    binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound +
    binaryNumeralTermCodeEnvelope bitBound + 1

def binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridExistsWitnessGeneralPayloadEnvelope
    (binaryNatStatusOuterExistsSyntaxPolynomial numericBound bitBound)
    (binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
      numericBound bitBound)

theorem sevenLeafRightConjunctionFixedChildren_le_fullyUniform
    (numericBound bitBound : Nat)
    (formula1 formula2 formula3 formula4 formula5 formula6 formula7 :
      ValuationFormula)
    (hvariables1 : formula1.freeVariables ⊆ {0})
    (hvariables2 : formula2.freeVariables ⊆ {0})
    (hvariables3 : formula3.freeVariables ⊆ {0})
    (hvariables4 : formula4.freeVariables ⊆ {0})
    (hvariables5 : formula5.freeVariables ⊆ {0})
    (hvariables6 : formula6.freeVariables ⊆ {0})
    (hvariables7 : formula7.freeVariables ⊆ {0})
    (hcode1 : (binaryFormulaCode formula1).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode2 : (binaryFormulaCode formula2).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode3 : (binaryFormulaCode formula3).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode4 : (binaryFormulaCode formula4).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound)
    (hcode5 : (binaryFormulaCode formula5).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode6 : (binaryFormulaCode formula6).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hcode7 : (binaryFormulaCode formula7).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound) :
    sevenLeafRightConjunctionStructuralPayloadEnvelope statusZeroValuation
        formula1 formula2 formula3 formula4 formula5 formula6 formula7
        (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
        (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
        (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
        (additiveTokenCellFixedWidthEntryPayloadPolynomial
          numericBound bitBound)
        (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
        (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
        (additiveTokenCellFixedWidthEntryPayloadPolynomial
          numericBound bitBound) <=
      binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let formula67 := formula6 ⋏ formula7
  let formula567 := formula5 ⋏ formula67
  let formula4567 := formula4 ⋏ formula567
  let formula34567 := formula3 ⋏ formula4567
  let formula234567 := formula2 ⋏ formula34567
  let formula1234567 := formula1 ⋏ formula234567
  let contextCode := additiveTokenCellContextFormulaCodeSumEnvelope numericBound
  let atomicCode := additiveTokenCellAtomicFormulaCodeEnvelope bitBound
  let entryCode := additiveTokenCellEntryFormulaCodeEnvelope bitBound
  let conjunctionTag := (binaryNatCode 4).length
  let syntaxResource :=
    binaryNatStatusSevenLeafSyntaxPolynomial numericBound bitBound
  let atomicResource :=
    additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound
  let entryResource :=
    additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound
  let structural67 := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation formula6 formula7 atomicResource entryResource
  let structural567 := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation formula5 formula67 atomicResource structural67
  let structural4567 := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation formula4 formula567 entryResource structural567
  let structural34567 := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation formula3 formula4567 atomicResource structural4567
  let structural234567 := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation formula2 formula34567 atomicResource structural34567
  let structural1234567 := hybridConjunctionStructuralPayloadEnvelope
    statusZeroValuation formula1 formula234567 atomicResource structural234567
  let general67 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource entryResource
  let general567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource general67
  let general4567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    entryResource general567
  let general34567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource general4567
  let general234567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource general34567
  let general1234567 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource general234567
  have hvariables67 : formula67.freeVariables ⊆ {0} := by
    dsimp only [formula67]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables6 hvariables7
  have hvariables567 : formula567.freeVariables ⊆ {0} := by
    dsimp only [formula567]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables5 hvariables67
  have hvariables4567 : formula4567.freeVariables ⊆ {0} := by
    dsimp only [formula4567]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables4 hvariables567
  have hvariables34567 : formula34567.freeVariables ⊆ {0} := by
    dsimp only [formula34567]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables3 hvariables4567
  have hvariables234567 : formula234567.freeVariables ⊆ {0} := by
    dsimp only [formula234567]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables2 hvariables34567
  have hvariables1234567 : formula1234567.freeVariables ⊆ {0} := by
    dsimp only [formula1234567]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hvariables1 hvariables234567
  have hzero : statusZeroValuation 0 <= numericBound := by
    simp [statusZeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
  have contextBound (formula : ValuationFormula)
      (hvariables : formula.freeVariables ⊆ {0}) :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext formula.freeVariables statusZeroValuation) <=
        contextCode := by
    simpa only [contextCode] using
      valuationContextFormulaCodeSum_le_tokenCellEnvelope statusZeroValuation
        formula numericBound hvariables hzero
  have hcode67Raw := binaryFormulaCode_and_length_le_local formula6 formula7
  have hcode67 : (binaryFormulaCode formula67).length <=
      atomicCode + entryCode + conjunctionTag := by
    dsimp only [formula67, atomicCode, entryCode, conjunctionTag]
      at hcode67Raw ⊢
    omega
  have hcode567Raw := binaryFormulaCode_and_length_le_local formula5 formula67
  have hcode567 : (binaryFormulaCode formula567).length <=
      2 * atomicCode + entryCode + 2 * conjunctionTag := by
    dsimp only [formula567] at hcode567Raw ⊢
    omega
  have hcode4567Raw := binaryFormulaCode_and_length_le_local formula4 formula567
  have hcode4567 : (binaryFormulaCode formula4567).length <=
      2 * atomicCode + 2 * entryCode + 3 * conjunctionTag := by
    dsimp only [formula4567] at hcode4567Raw ⊢
    omega
  have hcode34567Raw := binaryFormulaCode_and_length_le_local formula3 formula4567
  have hcode34567 : (binaryFormulaCode formula34567).length <=
      3 * atomicCode + 2 * entryCode + 4 * conjunctionTag := by
    dsimp only [formula34567] at hcode34567Raw ⊢
    omega
  have hcode234567Raw := binaryFormulaCode_and_length_le_local formula2 formula34567
  have hcode234567 : (binaryFormulaCode formula234567).length <=
      4 * atomicCode + 2 * entryCode + 5 * conjunctionTag := by
    dsimp only [formula234567] at hcode234567Raw ⊢
    omega
  have hcode1234567Raw :=
    binaryFormulaCode_and_length_le_local formula1 formula234567
  have hcode1234567 : (binaryFormulaCode formula1234567).length <=
      5 * atomicCode + 2 * entryCode + 6 * conjunctionTag := by
    dsimp only [formula1234567] at hcode1234567Raw ⊢
    omega
  have hsyntaxOne : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold binaryNatStatusSevenLeafSyntaxPolynomial
    dsimp only
    omega
  have hcontextSyntax : contextCode <= syntaxResource := by
    dsimp only [contextCode, syntaxResource]
    unfold binaryNatStatusSevenLeafSyntaxPolynomial
    dsimp only
    omega
  have hatomicSyntax : atomicCode <= syntaxResource := by
    dsimp only [atomicCode, syntaxResource]
    unfold binaryNatStatusSevenLeafSyntaxPolynomial
    dsimp only
    omega
  have hentrySyntax : entryCode <= syntaxResource := by
    dsimp only [entryCode, syntaxResource]
    unfold binaryNatStatusSevenLeafSyntaxPolynomial
    dsimp only
    omega
  have hcode67Syntax : (binaryFormulaCode formula67).length <=
      syntaxResource := hcode67.trans (by
        dsimp only [atomicCode, entryCode, conjunctionTag, syntaxResource]
        unfold binaryNatStatusSevenLeafSyntaxPolynomial
        dsimp only
        omega)
  have hcode567Syntax : (binaryFormulaCode formula567).length <=
      syntaxResource := hcode567.trans (by
        dsimp only [atomicCode, entryCode, conjunctionTag, syntaxResource]
        unfold binaryNatStatusSevenLeafSyntaxPolynomial
        dsimp only
        omega)
  have hcode4567Syntax : (binaryFormulaCode formula4567).length <=
      syntaxResource := hcode4567.trans (by
        dsimp only [atomicCode, entryCode, conjunctionTag, syntaxResource]
        unfold binaryNatStatusSevenLeafSyntaxPolynomial
        dsimp only
        omega)
  have hcode34567Syntax : (binaryFormulaCode formula34567).length <=
      syntaxResource := hcode34567.trans (by
        dsimp only [atomicCode, entryCode, conjunctionTag, syntaxResource]
        unfold binaryNatStatusSevenLeafSyntaxPolynomial
        dsimp only
        omega)
  have hcode234567Syntax : (binaryFormulaCode formula234567).length <=
      syntaxResource := hcode234567.trans (by
        dsimp only [atomicCode, entryCode, conjunctionTag, syntaxResource]
        unfold binaryNatStatusSevenLeafSyntaxPolynomial
        dsimp only
        omega)
  have hcode1234567Syntax : (binaryFormulaCode formula1234567).length <=
      syntaxResource := hcode1234567.trans (by
        dsimp only [atomicCode, entryCode, conjunctionTag, syntaxResource]
        unfold binaryNatStatusSevenLeafSyntaxPolynomial
        dsimp only
        omega)
  have hstructural67 : structural67 <= general67 := by
    dsimp only [structural67, general67]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general
      statusZeroValuation formula6 formula7 atomicResource entryResource
      syntaxResource hsyntaxOne
      ((contextBound formula67 hvariables67).trans hcontextSyntax)
      (hcode6.trans hatomicSyntax) (hcode7.trans hentrySyntax) hcode67Syntax
  have hstructural567Base : structural567 <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
        structural67 := by
    dsimp only [structural567]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general
      statusZeroValuation formula5 formula67 atomicResource structural67
      syntaxResource hsyntaxOne
      ((contextBound formula567 hvariables567).trans hcontextSyntax)
      (hcode5.trans hatomicSyntax) hcode67Syntax hcode567Syntax
  have hstructural567 : structural567 <= general567 :=
    hstructural567Base.trans
      (hybridConjunctionGeneralPayloadEnvelope_mono le_rfl hstructural67)
  have hstructural4567Base : structural4567 <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource entryResource
        structural567 := by
    dsimp only [structural4567]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general
      statusZeroValuation formula4 formula567 entryResource structural567
      syntaxResource hsyntaxOne
      ((contextBound formula4567 hvariables4567).trans hcontextSyntax)
      (hcode4.trans hentrySyntax) hcode567Syntax hcode4567Syntax
  have hstructural4567 : structural4567 <= general4567 :=
    hstructural4567Base.trans
      (hybridConjunctionGeneralPayloadEnvelope_mono le_rfl hstructural567)
  have hstructural34567Base : structural34567 <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
        structural4567 := by
    dsimp only [structural34567]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general
      statusZeroValuation formula3 formula4567 atomicResource structural4567
      syntaxResource hsyntaxOne
      ((contextBound formula34567 hvariables34567).trans hcontextSyntax)
      (hcode3.trans hatomicSyntax) hcode4567Syntax hcode34567Syntax
  have hstructural34567 : structural34567 <= general34567 :=
    hstructural34567Base.trans
      (hybridConjunctionGeneralPayloadEnvelope_mono le_rfl hstructural4567)
  have hstructural234567Base : structural234567 <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
        structural34567 := by
    dsimp only [structural234567]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general
      statusZeroValuation formula2 formula34567 atomicResource structural34567
      syntaxResource hsyntaxOne
      ((contextBound formula234567 hvariables234567).trans hcontextSyntax)
      (hcode2.trans hatomicSyntax) hcode34567Syntax hcode234567Syntax
  have hstructural234567 : structural234567 <= general234567 :=
    hstructural234567Base.trans
      (hybridConjunctionGeneralPayloadEnvelope_mono le_rfl hstructural34567)
  have hstructural1234567Base : structural1234567 <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
        structural234567 := by
    dsimp only [structural1234567]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general
      statusZeroValuation formula1 formula234567 atomicResource structural234567
      syntaxResource hsyntaxOne
      ((contextBound formula1234567 hvariables1234567).trans hcontextSyntax)
      (hcode1.trans hatomicSyntax) hcode234567Syntax hcode1234567Syntax
  have hstructural1234567 : structural1234567 <= general1234567 :=
    hstructural1234567Base.trans
      (hybridConjunctionGeneralPayloadEnvelope_mono le_rfl hstructural234567)
  unfold sevenLeafRightConjunctionStructuralPayloadEnvelope
    binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
  dsimp only [formula67, formula567, formula4567, formula34567,
    formula234567, formula1234567, syntaxResource, atomicResource,
    entryResource, structural67, structural567, structural4567,
    structural34567, structural234567, structural1234567, general67,
    general567, general4567, general34567, general234567, general1234567]
    at hstructural1234567 ⊢
  exact hstructural1234567

theorem
    compactFixedWidthEntryShortNumeralsAtValueTermCertificate_structuralPayloadBound_le_tokenCellFixed
    (tokenTable width cursor numericBound bitBound : Nat)
    (valueTerm : ValuationTerm)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size (termValue statusZeroValuation valueTerm) <= bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound)
    (hvalueClosed : valueTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry
      (termValue statusZeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue statusZeroValuation (shortBinaryNumeralTerm width))
      (termValue statusZeroValuation (shortBinaryNumeralTerm cursor))
      (termValue statusZeroValuation valueTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          statusZeroValuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm cursor)
          valueTerm hentry) <=
      additiveTokenCellFixedWidthEntryPayloadPolynomial
        numericBound bitBound := by
  have hopen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      statusZeroValuation (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm cursor) valueTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width) (by
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      hvalueClosed hentry
  have hfixed :=
    additiveTokenCellFixedWidthEntryAtClosedValueTermPayloadPolynomial_le_fixed
      tokenTable width cursor numericBound bitBound valueTerm hwidthValue
      hcursorValue htableSize hwidthSize hcursorSize hvalueSize hvalueCode
      hvalueClosed
  exact hopen.trans hfixed

theorem compactFixedWidthEntryShortNumeralsAtValueTermFormula_code_length_le
    (tokenTable width cursor bitBound : Nat)
    (valueTerm : ValuationTerm)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    (binaryFormulaCode
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm cursor) valueTerm)).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound := by
  exact additiveTokenCellEntryAtClosedValueTermFormula_code_length_le_uniform
    tokenTable width cursor bitBound valueTerm htableSize hwidthSize hcursorSize
    hvalueCode

def compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound

theorem
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount start finish numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hstartValue : start <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hgraph : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hgraph) <=
      compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let valueTerm : ValuationTerm := ‘0’
  let finishTerm := shortBinaryNumeralTerm finish
  have hgraphCell : CompactAdditiveTokenCell
      tokenTable width tokenCount start 0 finish := by
    unfold CompactBinaryNatRunningStatusSlice at hgraph
    exact hgraph
  have hcell : CompactAdditiveTokenCell
      (termValue statusZeroValuation tableTerm)
      (termValue statusZeroValuation widthTerm)
      (termValue statusZeroValuation countTerm)
      (termValue statusZeroValuation startTerm)
      (termValue statusZeroValuation valueTerm)
      (termValue statusZeroValuation finishTerm) := by
    dsimp only [tableTerm, widthTerm, countTerm, startTerm, valueTerm,
      finishTerm]
    simpa only [termValue_shortBinaryNumeralTerm,
      termValue_statusZeroValuation_zero] using hgraphCell
  have huniform :=
    compactAdditiveTokenCellShortNumeralsAtValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount start 0 finish numericBound bitBound
      valueTerm (by
        dsimp only [valueTerm]
        exact shortBinaryNumeralTerm_zero_eq_paZero.symm)
      hwidthValue hstartValue htableSize hwidthSize htokenCountSize hstartSize
      (by simp) hfinishSize hcell
  change hybridFormulaStructuralPayloadBound
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        tableTerm widthTerm countTerm startTerm valueTerm finishTerm hcell) <= _
  simpa only [compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial,
    tableTerm, widthTerm, countTerm, startTerm, valueTerm, finishTerm] using
    huniform

theorem
    compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount start finish innerStart numericBound bitBound :
      Nat)
    (hwidthValue : width <= numericBound)
    (hstartValue : start <= numericBound)
    (hinnerValue : innerStart <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hinnerSize : Nat.size innerStart <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hinner : innerStart <= tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 0 finish) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate
          tokenTable width tokenCount start finish innerStart hinner) <=
      binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let finishTerm := shortBinaryNumeralTerm finish
  let innerTerm := shortBinaryNumeralTerm innerStart
  let oneTerm : ValuationTerm := ‘1’
  let zeroTerm : ValuationTerm := ‘0’
  let guardFormula : ValuationFormula :=
    “!!innerTerm < !!countTerm + 1”
  let startLtFormula : ValuationFormula := “!!startTerm < !!countTerm”
  let firstSuccessorFormula : ValuationFormula :=
    “!!innerTerm = !!startTerm + 1”
  let firstEntryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm startTerm oneTerm
  let innerLtFormula : ValuationFormula := “!!innerTerm < !!countTerm”
  let secondSuccessorFormula : ValuationFormula :=
    “!!finishTerm = !!innerTerm + 1”
  let secondEntryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm innerTerm zeroTerm
  let guardCertificate :=
    boundedWitnessGuardCertificate innerStart tokenCount hinner.1
  let startLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      start tokenCount hinner.2.1.1
  let firstSuccessorCertificate :=
    successorEqualityCertificate start innerStart hinner.2.1.2.1
  have hfirstEntry : CompactFixedWidthEntry
      (termValue statusZeroValuation tableTerm)
      (termValue statusZeroValuation widthTerm)
      (termValue statusZeroValuation startTerm)
      (termValue statusZeroValuation oneTerm) := by
    dsimp only [tableTerm, widthTerm, startTerm, oneTerm]
    simpa only [termValue_shortBinaryNumeralTerm,
      termValue_statusZeroValuation_one] using hinner.2.1.2.2
  let firstEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      statusZeroValuation tableTerm widthTerm startTerm oneTerm hfirstEntry
  let innerLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      innerStart tokenCount hinner.2.2.1
  let secondSuccessorCertificate :=
    successorEqualityCertificate innerStart finish hinner.2.2.2.1
  have hsecondEntry : CompactFixedWidthEntry
      (termValue statusZeroValuation tableTerm)
      (termValue statusZeroValuation widthTerm)
      (termValue statusZeroValuation innerTerm)
      (termValue statusZeroValuation zeroTerm) := by
    dsimp only [tableTerm, widthTerm, innerTerm, zeroTerm]
    simpa only [termValue_shortBinaryNumeralTerm,
      termValue_statusZeroValuation_zero] using hinner.2.2.2.2
  let secondEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      statusZeroValuation tableTerm widthTerm innerTerm zeroTerm hsecondEntry
  have hguard :=
    (boundedWitnessGuardCertificate_structuralPayloadBound_le_public
      innerStart tokenCount hinner.1).trans
    (additiveTokenCellGuardPayloadPolynomial_le_fixed innerStart tokenCount
      numericBound bitBound hinnerSize htokenCountSize)
  have hstartLt :=
    (closedLtCertificate_structuralPayloadBound_le_public
      start tokenCount hinner.2.1.1).trans
    (additiveTokenCellCursorPayloadPolynomial_le_fixed start tokenCount
      numericBound bitBound hstartSize htokenCountSize)
  have hfirstSuccessor :=
    (successorEqualityCertificate_structuralPayloadBound_le_public
      start innerStart hinner.2.1.2.1).trans
    (additiveTokenCellSuccessorPayloadPolynomial_le_fixed start innerStart
      numericBound bitBound hstartSize hinnerSize)
  have hfirstEntryFixed :=
    compactFixedWidthEntryShortNumeralsAtValueTermCertificate_structuralPayloadBound_le_tokenCellFixed
      tokenTable width start numericBound bitBound oneTerm hwidthValue
      hstartValue htableSize hwidthSize hstartSize (by
        simpa only [oneTerm, termValue_statusZeroValuation_one, Nat.size_one] using
          hbitPositive)
      (by
        dsimp only [oneTerm]
        exact paOneTerm_code_length_le_binaryNumeralEnvelope bitBound
          hbitPositive)
      (by
        dsimp only [oneTerm]
        exact arithmeticOneTerm_freeVariables_eq_empty)
      hfirstEntry
  have hinnerLt :=
    (closedLtCertificate_structuralPayloadBound_le_public
      innerStart tokenCount hinner.2.2.1).trans
    (additiveTokenCellCursorPayloadPolynomial_le_fixed innerStart tokenCount
      numericBound bitBound hinnerSize htokenCountSize)
  have hsecondSuccessor :=
    (successorEqualityCertificate_structuralPayloadBound_le_public
      innerStart finish hinner.2.2.2.1).trans
    (additiveTokenCellSuccessorPayloadPolynomial_le_fixed innerStart finish
      numericBound bitBound hinnerSize hfinishSize)
  have hsecondEntryFixed :=
    compactFixedWidthEntryShortNumeralsAtValueTermCertificate_structuralPayloadBound_le_tokenCellFixed
      tokenTable width innerStart numericBound bitBound zeroTerm hwidthValue
      hinnerValue htableSize hwidthSize hinnerSize (by
        simp only [zeroTerm, termValue_statusZeroValuation_zero, Nat.size_zero]
        exact Nat.zero_le bitBound)
      (by
        dsimp only [zeroTerm]
        exact paZeroTerm_code_length_le_binaryNumeralEnvelope bitBound)
      (by
        dsimp only [zeroTerm]
        exact arithmeticZeroTerm_freeVariables_eq_empty)
      hsecondEntry
  have hseven := sevenLeafRightConjunctionStructuralPayloadBound_le_envelope
    guardCertificate startLtCertificate firstSuccessorCertificate
    firstEntryCertificate innerLtCertificate secondSuccessorCertificate
    secondEntryCertificate
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound)
    hguard hstartLt hfirstSuccessor hfirstEntryFixed hinnerLt
    hsecondSuccessor hsecondEntryFixed
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hcountClosed : countTerm.freeVariables = ∅ := by
    dsimp only [countTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstartClosed : startTerm.freeVariables = ∅ := by
    dsimp only [startTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty start
  have hfinishClosed : finishTerm.freeVariables = ∅ := by
    dsimp only [finishTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty finish
  have hinnerClosed : innerTerm.freeVariables = ∅ := by
    dsimp only [innerTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty innerStart
  have hguardVariables : guardFormula.freeVariables ⊆ {0} := by
    have hclosed : guardFormula.freeVariables = ∅ := by
      dsimp only [guardFormula]
      simp [hinnerClosed, hcountClosed, arithmeticAddTerm_freeVariables,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hstartLtVariables : startLtFormula.freeVariables ⊆ {0} := by
    have hclosed : startLtFormula.freeVariables = ∅ := by
      dsimp only [startLtFormula]
      simp [hstartClosed, hcountClosed]
    rw [hclosed]
    exact Finset.empty_subset _
  have hfirstSuccessorVariables :
      firstSuccessorFormula.freeVariables ⊆ {0} := by
    have hclosed : firstSuccessorFormula.freeVariables = ∅ := by
      dsimp only [firstSuccessorFormula]
      simp [hinnerClosed, hstartClosed, arithmeticAddTerm_freeVariables,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hfirstEntryVariables : firstEntryFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm startTerm oneTerm htableClosed hwidthClosed (by
        rw [hstartClosed]
        exact Finset.empty_subset _)
      arithmeticOneTerm_freeVariables_eq_empty
  have hinnerLtVariables : innerLtFormula.freeVariables ⊆ {0} := by
    have hclosed : innerLtFormula.freeVariables = ∅ := by
      dsimp only [innerLtFormula]
      simp [hinnerClosed, hcountClosed]
    rw [hclosed]
    exact Finset.empty_subset _
  have hsecondSuccessorVariables :
      secondSuccessorFormula.freeVariables ⊆ {0} := by
    have hclosed : secondSuccessorFormula.freeVariables = ∅ := by
      dsimp only [secondSuccessorFormula]
      simp [hfinishClosed, hinnerClosed, arithmeticAddTerm_freeVariables,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hsecondEntryVariables : secondEntryFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm innerTerm zeroTerm htableClosed hwidthClosed (by
        rw [hinnerClosed]
        exact Finset.empty_subset _)
      arithmeticZeroTerm_freeVariables_eq_empty
  have hguardCode := additiveTokenCellGuardFormula_code_length_le_uniform
    innerStart tokenCount bitBound hinnerSize htokenCountSize
  have hstartLtCode := additiveTokenCellCursorFormula_code_length_le_uniform
    start tokenCount bitBound hstartSize htokenCountSize
  have hfirstSuccessorCode :=
    additiveTokenCellSuccessorFormula_code_length_le_uniform start innerStart
      bitBound hstartSize hinnerSize
  have hfirstEntryCode :=
    compactFixedWidthEntryShortNumeralsAtValueTermFormula_code_length_le
      tokenTable width start bitBound oneTerm htableSize hwidthSize hstartSize
      (by
        dsimp only [oneTerm]
        exact paOneTerm_code_length_le_binaryNumeralEnvelope bitBound
          hbitPositive)
  have hinnerLtCode := additiveTokenCellCursorFormula_code_length_le_uniform
    innerStart tokenCount bitBound hinnerSize htokenCountSize
  have hsecondSuccessorCode :=
    additiveTokenCellSuccessorFormula_code_length_le_uniform innerStart finish
      bitBound hinnerSize hfinishSize
  have hsecondEntryCode :=
    compactFixedWidthEntryShortNumeralsAtValueTermFormula_code_length_le
      tokenTable width innerStart bitBound zeroTerm htableSize hwidthSize
      hinnerSize (by
        dsimp only [zeroTerm]
        exact paZeroTerm_code_length_le_binaryNumeralEnvelope bitBound)
  have hassembly := sevenLeafRightConjunctionFixedChildren_le_fullyUniform
    numericBound bitBound guardFormula startLtFormula firstSuccessorFormula
    firstEntryFormula innerLtFormula secondSuccessorFormula secondEntryFormula
    hguardVariables hstartLtVariables hfirstSuccessorVariables
    hfirstEntryVariables hinnerLtVariables hsecondSuccessorVariables
    hsecondEntryVariables hguardCode hstartLtCode hfirstSuccessorCode
    hfirstEntryCode hinnerLtCode hsecondSuccessorCode hsecondEntryCode
  have hzeroValuation : statusZeroValuation =
      FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation := by
    funext index
    rfl
  rw [hzeroValuation] at hassembly
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
          startLtCertificate
          (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
            firstSuccessorCertificate
            (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
              firstEntryCertificate
              (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
                innerLtCertificate
                (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  secondSuccessorCertificate secondEntryCertificate)))))) <= _
  exact hseven.trans (by
    simpa only [guardFormula, startLtFormula, firstSuccessorFormula,
      firstEntryFormula, innerLtFormula, secondSuccessorFormula,
      secondEntryFormula, tableTerm, widthTerm, countTerm, startTerm,
      finishTerm, innerTerm, oneTerm, zeroTerm] using hassembly)

theorem
    compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount start outputStart innerStart numericBound bitBound :
      Nat)
    (hwidthValue : width <= numericBound)
    (hstartValue : start <= numericBound)
    (hinnerValue : innerStart <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (hinnerSize : Nat.size innerStart <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hinner : innerStart <= tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 1 outputStart) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate
          tokenTable width tokenCount start outputStart innerStart hinner) <=
      binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let outputStartTerm := shortBinaryNumeralTerm outputStart
  let innerTerm := shortBinaryNumeralTerm innerStart
  let oneTerm : ValuationTerm := ‘1’
  let guardFormula : ValuationFormula :=
    “!!innerTerm < !!countTerm + 1”
  let startLtFormula : ValuationFormula := “!!startTerm < !!countTerm”
  let firstSuccessorFormula : ValuationFormula :=
    “!!innerTerm = !!startTerm + 1”
  let firstEntryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm startTerm oneTerm
  let innerLtFormula : ValuationFormula := “!!innerTerm < !!countTerm”
  let secondSuccessorFormula : ValuationFormula :=
    “!!outputStartTerm = !!innerTerm + 1”
  let secondEntryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm innerTerm oneTerm
  let guardCertificate :=
    boundedWitnessGuardCertificate innerStart tokenCount hinner.1
  let startLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      start tokenCount hinner.2.1.1
  let firstSuccessorCertificate :=
    successorEqualityCertificate start innerStart hinner.2.1.2.1
  have hfirstEntry : CompactFixedWidthEntry
      (termValue statusZeroValuation tableTerm)
      (termValue statusZeroValuation widthTerm)
      (termValue statusZeroValuation startTerm)
      (termValue statusZeroValuation oneTerm) := by
    dsimp only [tableTerm, widthTerm, startTerm, oneTerm]
    simpa only [termValue_shortBinaryNumeralTerm,
      termValue_statusZeroValuation_one] using hinner.2.1.2.2
  let firstEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      statusZeroValuation tableTerm widthTerm startTerm oneTerm hfirstEntry
  let innerLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      innerStart tokenCount hinner.2.2.1
  let secondSuccessorCertificate :=
    successorEqualityCertificate innerStart outputStart hinner.2.2.2.1
  have hsecondEntry : CompactFixedWidthEntry
      (termValue statusZeroValuation tableTerm)
      (termValue statusZeroValuation widthTerm)
      (termValue statusZeroValuation innerTerm)
      (termValue statusZeroValuation oneTerm) := by
    dsimp only [tableTerm, widthTerm, innerTerm, oneTerm]
    simpa only [termValue_shortBinaryNumeralTerm,
      termValue_statusZeroValuation_one] using hinner.2.2.2.2
  let secondEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      statusZeroValuation tableTerm widthTerm innerTerm oneTerm hsecondEntry
  have hguard :=
    (boundedWitnessGuardCertificate_structuralPayloadBound_le_public
      innerStart tokenCount hinner.1).trans
    (additiveTokenCellGuardPayloadPolynomial_le_fixed innerStart tokenCount
      numericBound bitBound hinnerSize htokenCountSize)
  have hstartLt :=
    (closedLtCertificate_structuralPayloadBound_le_public
      start tokenCount hinner.2.1.1).trans
    (additiveTokenCellCursorPayloadPolynomial_le_fixed start tokenCount
      numericBound bitBound hstartSize htokenCountSize)
  have hfirstSuccessor :=
    (successorEqualityCertificate_structuralPayloadBound_le_public
      start innerStart hinner.2.1.2.1).trans
    (additiveTokenCellSuccessorPayloadPolynomial_le_fixed start innerStart
      numericBound bitBound hstartSize hinnerSize)
  have hfirstEntryFixed :=
    compactFixedWidthEntryShortNumeralsAtValueTermCertificate_structuralPayloadBound_le_tokenCellFixed
      tokenTable width start numericBound bitBound oneTerm hwidthValue
      hstartValue htableSize hwidthSize hstartSize (by
        simpa only [oneTerm, termValue_statusZeroValuation_one, Nat.size_one] using
          hbitPositive)
      (by
        dsimp only [oneTerm]
        exact paOneTerm_code_length_le_binaryNumeralEnvelope bitBound
          hbitPositive)
      (by
        dsimp only [oneTerm]
        exact arithmeticOneTerm_freeVariables_eq_empty)
      hfirstEntry
  have hinnerLt :=
    (closedLtCertificate_structuralPayloadBound_le_public
      innerStart tokenCount hinner.2.2.1).trans
    (additiveTokenCellCursorPayloadPolynomial_le_fixed innerStart tokenCount
      numericBound bitBound hinnerSize htokenCountSize)
  have hsecondSuccessor :=
    (successorEqualityCertificate_structuralPayloadBound_le_public
      innerStart outputStart hinner.2.2.2.1).trans
    (additiveTokenCellSuccessorPayloadPolynomial_le_fixed innerStart outputStart
      numericBound bitBound hinnerSize houtputStartSize)
  have hsecondEntryFixed :=
    compactFixedWidthEntryShortNumeralsAtValueTermCertificate_structuralPayloadBound_le_tokenCellFixed
      tokenTable width innerStart numericBound bitBound oneTerm hwidthValue
      hinnerValue htableSize hwidthSize hinnerSize (by
        simp only [oneTerm, termValue_statusZeroValuation_one, Nat.size_one]
        exact hbitPositive)
      (by
        dsimp only [oneTerm]
        exact paOneTerm_code_length_le_binaryNumeralEnvelope bitBound
          hbitPositive)
      (by
        dsimp only [oneTerm]
        exact arithmeticOneTerm_freeVariables_eq_empty)
      hsecondEntry
  have hseven := sevenLeafRightConjunctionStructuralPayloadBound_le_envelope
    guardCertificate startLtCertificate firstSuccessorCertificate
    firstEntryCertificate innerLtCertificate secondSuccessorCertificate
    secondEntryCertificate
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound)
    hguard hstartLt hfirstSuccessor hfirstEntryFixed hinnerLt
    hsecondSuccessor hsecondEntryFixed
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hcountClosed : countTerm.freeVariables = ∅ := by
    dsimp only [countTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstartClosed : startTerm.freeVariables = ∅ := by
    dsimp only [startTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty start
  have houtputStartClosed : outputStartTerm.freeVariables = ∅ := by
    dsimp only [outputStartTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty outputStart
  have hinnerClosed : innerTerm.freeVariables = ∅ := by
    dsimp only [innerTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty innerStart
  have hguardVariables : guardFormula.freeVariables ⊆ {0} := by
    have hclosed : guardFormula.freeVariables = ∅ := by
      dsimp only [guardFormula]
      simp [hinnerClosed, hcountClosed, arithmeticAddTerm_freeVariables,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hstartLtVariables : startLtFormula.freeVariables ⊆ {0} := by
    have hclosed : startLtFormula.freeVariables = ∅ := by
      dsimp only [startLtFormula]
      simp [hstartClosed, hcountClosed]
    rw [hclosed]
    exact Finset.empty_subset _
  have hfirstSuccessorVariables :
      firstSuccessorFormula.freeVariables ⊆ {0} := by
    have hclosed : firstSuccessorFormula.freeVariables = ∅ := by
      dsimp only [firstSuccessorFormula]
      simp [hinnerClosed, hstartClosed, arithmeticAddTerm_freeVariables,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hfirstEntryVariables : firstEntryFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm startTerm oneTerm htableClosed hwidthClosed (by
        rw [hstartClosed]
        exact Finset.empty_subset _)
      arithmeticOneTerm_freeVariables_eq_empty
  have hinnerLtVariables : innerLtFormula.freeVariables ⊆ {0} := by
    have hclosed : innerLtFormula.freeVariables = ∅ := by
      dsimp only [innerLtFormula]
      simp [hinnerClosed, hcountClosed]
    rw [hclosed]
    exact Finset.empty_subset _
  have hsecondSuccessorVariables :
      secondSuccessorFormula.freeVariables ⊆ {0} := by
    have hclosed : secondSuccessorFormula.freeVariables = ∅ := by
      dsimp only [secondSuccessorFormula]
      simp [houtputStartClosed, hinnerClosed, arithmeticAddTerm_freeVariables,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hsecondEntryVariables : secondEntryFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm innerTerm oneTerm htableClosed hwidthClosed (by
        rw [hinnerClosed]
        exact Finset.empty_subset _)
      arithmeticOneTerm_freeVariables_eq_empty
  have hguardCode := additiveTokenCellGuardFormula_code_length_le_uniform
    innerStart tokenCount bitBound hinnerSize htokenCountSize
  have hstartLtCode := additiveTokenCellCursorFormula_code_length_le_uniform
    start tokenCount bitBound hstartSize htokenCountSize
  have hfirstSuccessorCode :=
    additiveTokenCellSuccessorFormula_code_length_le_uniform start innerStart
      bitBound hstartSize hinnerSize
  have hfirstEntryCode :=
    compactFixedWidthEntryShortNumeralsAtValueTermFormula_code_length_le
      tokenTable width start bitBound oneTerm htableSize hwidthSize hstartSize
      (by
        dsimp only [oneTerm]
        exact paOneTerm_code_length_le_binaryNumeralEnvelope bitBound
          hbitPositive)
  have hinnerLtCode := additiveTokenCellCursorFormula_code_length_le_uniform
    innerStart tokenCount bitBound hinnerSize htokenCountSize
  have hsecondSuccessorCode :=
    additiveTokenCellSuccessorFormula_code_length_le_uniform innerStart outputStart
      bitBound hinnerSize houtputStartSize
  have hsecondEntryCode :=
    compactFixedWidthEntryShortNumeralsAtValueTermFormula_code_length_le
      tokenTable width innerStart bitBound oneTerm htableSize hwidthSize
      hinnerSize (by
        dsimp only [oneTerm]
        exact paOneTerm_code_length_le_binaryNumeralEnvelope bitBound
          hbitPositive)
  have hassembly := sevenLeafRightConjunctionFixedChildren_le_fullyUniform
    numericBound bitBound guardFormula startLtFormula firstSuccessorFormula
    firstEntryFormula innerLtFormula secondSuccessorFormula secondEntryFormula
    hguardVariables hstartLtVariables hfirstSuccessorVariables
    hfirstEntryVariables hinnerLtVariables hsecondSuccessorVariables
    hsecondEntryVariables hguardCode hstartLtCode hfirstSuccessorCode
    hfirstEntryCode hinnerLtCode hsecondSuccessorCode hsecondEntryCode
  have hzeroValuation : statusZeroValuation =
      FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation := by
    funext index
    rfl
  rw [hzeroValuation] at hassembly
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
          startLtCertificate
          (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
            firstSuccessorCertificate
            (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
              firstEntryCertificate
              (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
                innerLtCertificate
                (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  secondSuccessorCertificate secondEntryCertificate)))))) <= _
  exact hseven.trans (by
    simpa only [guardFormula, startLtFormula, firstSuccessorFormula,
      firstEntryFormula, innerLtFormula, secondSuccessorFormula,
      secondEntryFormula, tableTerm, widthTerm, countTerm, startTerm,
      outputStartTerm, innerTerm, oneTerm] using hassembly)

theorem
    compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount start finish numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hstartValue : start <= numericBound)
    (hinnerValue : start + 1 <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hinnerSize : Nat.size (start + 1) <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hgraph : CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hgraph) <=
      binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let innerStart := start + 1
  let body := compactBinaryNatFailedStatusSliceWitnessBody
    tokenTable width tokenCount start finish
  let postResource := binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
    numericBound bitBound
  let syntaxResource := binaryNatStatusOuterExistsSyntaxPolynomial
    numericBound bitBound
  have hinner : innerStart <= tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 0 finish := by
    simpa only [innerStart] using
      compactBinaryNatFailedStatusSlice_deterministicWitness
        tokenTable width tokenCount start finish hgraph
  let post :=
    compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate
      tokenTable width tokenCount start finish innerStart hinner
  let instantiated :=
    FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.cast
      (compactBinaryNatFailedStatusSliceWitnessBody_substitution_alignment
        tokenTable width tokenCount start finish innerStart).symm post
  have hpost : hybridFormulaStructuralPayloadBound post <= postResource := by
    dsimp only [post, postResource]
    exact
      compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount start finish innerStart numericBound bitBound
        hwidthValue hstartValue (by simpa only [innerStart] using hinnerValue)
        htableSize hwidthSize htokenCountSize hstartSize hfinishSize
        (by simpa only [innerStart] using hinnerSize) hbitPositive hinner
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated <=
      postResource := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body innerStart instantiated postResource hinstantiated
  have hclosedCode :=
    compactBinaryNatFailedStatusSliceClosedFormula_code_length_le_uniform
      tokenTable width tokenCount start finish bitBound htableSize hwidthSize
      htokenCountSize hstartSize hfinishSize
  have hexistentialCode :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound := by
    dsimp only [body]
    rw [← compactBinaryNatFailedStatusSliceClosedFormula_alignment
      tokenTable width tokenCount start finish]
    exact hclosedCode
  have hbodyCode : (binaryFormulaCode body).length <=
      binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound :=
    (binaryFormulaCode_body_length_le_exists body).trans hexistentialCode
  have hwitnessCode :
      (binaryTermCode (shortBinaryNumeralTerm innerStart)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope innerStart bitBound (by
      simpa only [innerStart] using hinnerSize)
  have hinstantiatedCodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      instantiated
  have hinstantiatedCode :
      (binaryFormulaCode
        (body/[shortBinaryNumeralTerm innerStart])).length <= postResource := by
    exact hinstantiatedCodeRaw.trans hinstantiated
  have hexistentialVariables :
      (∃⁰ body : ValuationFormula).freeVariables = ∅ := by
    dsimp only [body]
    rw [← compactBinaryNatFailedStatusSliceClosedFormula_alignment
      tokenTable width tokenCount start finish]
    exact
      compactBinaryNatFailedStatusSliceClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount start finish
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (∃⁰ body : ValuationFormula).freeVariables
            FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation) <=
        syntaxResource := by
    rw [hexistentialVariables]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hsyntaxOne : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold binaryNatStatusOuterExistsSyntaxPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxResource :=
    hbodyCode.trans (by
      dsimp only [syntaxResource]
      unfold binaryNatStatusOuterExistsSyntaxPolynomial
      omega)
  have hwitnessSyntax :
      (binaryTermCode (shortBinaryNumeralTerm innerStart)).length <=
        syntaxResource := hwitnessCode.trans (by
    dsimp only [syntaxResource]
    unfold binaryNatStatusOuterExistsSyntaxPolynomial
    omega)
  have hinstantiatedSyntax :
      (binaryFormulaCode
        (body/[shortBinaryNumeralTerm innerStart])).length <= syntaxResource :=
    hinstantiatedCode.trans (by
      dsimp only [syntaxResource, postResource]
      unfold binaryNatStatusOuterExistsSyntaxPolynomial
      omega)
  have hexistentialSyntax :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        syntaxResource := hexistentialCode.trans (by
    dsimp only [syntaxResource]
    unfold binaryNatStatusOuterExistsSyntaxPolynomial
    omega)
  have hgeneral := hybridExistsWitnessStructuralPayloadEnvelope_le_general
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation
    body innerStart postResource syntaxResource hsyntaxOne hcontext hbodySyntax
    hwitnessSyntax hinstantiatedSyntax hexistentialSyntax
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        body innerStart instantiated) <= _
  exact hexists.trans (by
    simpa only [binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial,
      syntaxResource, postResource] using hgeneral)


theorem
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount start outputStart numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hstartValue : start <= numericBound)
    (hinnerValue : start + 1 <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (hinnerSize : Nat.size (start + 1) <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hgraph : CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount start outputStart) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start outputStart hgraph) <=
      binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let innerStart := start + 1
  let body := compactBinaryNatCompletedStatusPrefixWitnessBody
    tokenTable width tokenCount start outputStart
  let postResource := binaryNatStatusSevenLeafFullyUniformPayloadPolynomial
    numericBound bitBound
  let syntaxResource := binaryNatStatusOuterExistsSyntaxPolynomial
    numericBound bitBound
  have hinner : innerStart <= tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 1 outputStart := by
    simpa only [innerStart] using
      compactBinaryNatCompletedStatusPrefix_deterministicWitness
        tokenTable width tokenCount start outputStart hgraph
  let post :=
    compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate
      tokenTable width tokenCount start outputStart innerStart hinner
  let instantiated :=
    FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.cast
      (compactBinaryNatCompletedStatusPrefixWitnessBody_substitution_alignment
        tokenTable width tokenCount start outputStart innerStart).symm post
  have hpost : hybridFormulaStructuralPayloadBound post <= postResource := by
    dsimp only [post, postResource]
    exact
      compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount start outputStart innerStart numericBound bitBound
        hwidthValue hstartValue (by simpa only [innerStart] using hinnerValue)
        htableSize hwidthSize htokenCountSize hstartSize houtputStartSize
        (by simpa only [innerStart] using hinnerSize) hbitPositive hinner
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated <=
      postResource := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body innerStart instantiated postResource hinstantiated
  have hclosedCode :=
    compactBinaryNatCompletedStatusPrefixClosedFormula_code_length_le_uniform
      tokenTable width tokenCount start outputStart bitBound htableSize hwidthSize
      htokenCountSize hstartSize houtputStartSize
  have hexistentialCode :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound := by
    dsimp only [body]
    rw [← compactBinaryNatCompletedStatusPrefixClosedFormula_alignment
      tokenTable width tokenCount start outputStart]
    exact hclosedCode
  have hbodyCode : (binaryFormulaCode body).length <=
      binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound :=
    (binaryFormulaCode_body_length_le_exists body).trans hexistentialCode
  have hwitnessCode :
      (binaryTermCode (shortBinaryNumeralTerm innerStart)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope innerStart bitBound (by
      simpa only [innerStart] using hinnerSize)
  have hinstantiatedCodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      instantiated
  have hinstantiatedCode :
      (binaryFormulaCode
        (body/[shortBinaryNumeralTerm innerStart])).length <= postResource := by
    exact hinstantiatedCodeRaw.trans hinstantiated
  have hexistentialVariables :
      (∃⁰ body : ValuationFormula).freeVariables = ∅ := by
    dsimp only [body]
    rw [← compactBinaryNatCompletedStatusPrefixClosedFormula_alignment
      tokenTable width tokenCount start outputStart]
    exact
      compactBinaryNatCompletedStatusPrefixClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount start outputStart
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (∃⁰ body : ValuationFormula).freeVariables
            FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation) <=
        syntaxResource := by
    rw [hexistentialVariables]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hsyntaxOne : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold binaryNatStatusOuterExistsSyntaxPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxResource :=
    hbodyCode.trans (by
      dsimp only [syntaxResource]
      unfold binaryNatStatusOuterExistsSyntaxPolynomial
      omega)
  have hwitnessSyntax :
      (binaryTermCode (shortBinaryNumeralTerm innerStart)).length <=
        syntaxResource := hwitnessCode.trans (by
    dsimp only [syntaxResource]
    unfold binaryNatStatusOuterExistsSyntaxPolynomial
    omega)
  have hinstantiatedSyntax :
      (binaryFormulaCode
        (body/[shortBinaryNumeralTerm innerStart])).length <= syntaxResource :=
    hinstantiatedCode.trans (by
      dsimp only [syntaxResource, postResource]
      unfold binaryNatStatusOuterExistsSyntaxPolynomial
      omega)
  have hexistentialSyntax :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        syntaxResource := hexistentialCode.trans (by
    dsimp only [syntaxResource]
    unfold binaryNatStatusOuterExistsSyntaxPolynomial
    omega)
  have hgeneral := hybridExistsWitnessStructuralPayloadEnvelope_le_general
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation
    body innerStart postResource syntaxResource hsyntaxOne hcontext hbodySyntax
    hwitnessSyntax hinstantiatedSyntax hexistentialSyntax
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        body innerStart instantiated) <= _
  exact hexists.trans (by
    simpa only [binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial,
      syntaxResource, postResource] using hgeneral)



#print axioms sevenLeafRightConjunctionFixedChildren_le_fullyUniform
#print axioms sevenLeafRightConjunctionFormula_code_length_le_syntaxPolynomial
#print axioms hybridExistsWitnessStructuralPayloadEnvelope_le_general
#print axioms
  compactBinaryNatFailedStatusSliceClosedFormula_code_length_le_uniform
#print axioms
  compactBinaryNatCompletedStatusPrefixClosedFormula_code_length_le_uniform
#print axioms
  compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
#print axioms
  compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
#print axioms
  compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
#print axioms
  compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
#print axioms
  compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform

end FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
