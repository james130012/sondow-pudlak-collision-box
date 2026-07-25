import integration.FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fixed leaf bounds for the closed direct additive boundary table

The endpoint inequalities, both fixed-width entries, and the bounded row
universal are all charged against resources depending only on the common
numeric and bit-width coordinates.  Formula-assembly costs remain explicit;
the next layer bounds them by one closed syntax coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveBoundaryTableDirectCompiler
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler

private abbrev boundaryFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private theorem boundaryBinaryRelationFormula_freeVariables
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

def boundaryClosedLeFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * orderAtomicFormulaCodeEnvelope
      (binaryNumeralTermCodeEnvelope bitBound) + 8

def boundaryClosedLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let formulaCode := boundaryClosedLeFormulaCodePolynomial bitBound
  2 * compilePositiveRelationFixedPayloadPolynomial 0 termCode +
    3 * smallContextAssemblyEnvelope formulaCode + 1

theorem boundaryClosedLeStructuralPayloadEnvelope_le_fixed
    (valuation : Nat -> Nat) (left right bitBound : Nat)
    (hvaluationZero : valuation 0 = 0)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    boundaryClosedLeStructuralPayloadEnvelope valuation left right <=
      boundaryClosedLeFixedPayloadPolynomial bitBound := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let atomicCode := orderAtomicFormulaCodeEnvelope termCode
  let formulaCode := boundaryClosedLeFormulaCodePolynomial bitBound
  have hleftClosed : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hrightClosed : rightTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty right
  have hleftCode : (binaryTermCode leftTerm).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hrightCode : (binaryTermCode rightTerm).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hrightSize
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change leftTerm.freeVariables ⊆ {0}
    rw [hleftClosed]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [hrightClosed]
    simp
  have hequalityPublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial valuation
      Language.Eq.eq args hfirst hsecond
  have hequalityFixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed valuation Language.Eq.eq
      args 0 termCode hfirst hsecond (by simpa [hvaluationZero]) hleftCode
      hrightCode
  have hequalityResource := hequalityPublic.trans hequalityFixed
  have hstrictPublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial valuation
      Language.ORing.Rel.lt args hfirst hsecond
  have hstrictFixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed valuation
      Language.ORing.Rel.lt args 0 termCode hfirst hsecond
      (by simpa [hvaluationZero]) hleftCode hrightCode
  have hstrictResource := hstrictPublic.trans hstrictFixed
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      atomicCode := by
    simpa only [equalityFormula, args, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq leftTerm
        rightTerm termCode hleftCode hrightCode)
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      atomicCode := by
    simpa only [strictFormula, args, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt leftTerm
        rightTerm termCode hleftCode hrightCode)
  have hatomicFormula : atomicCode <= formulaCode := by
    unfold formulaCode boundaryClosedLeFormulaCodePolynomial
    dsimp only [atomicCode, termCode]
    omega
  have hequalityFormula := hequalityCode.trans hatomicFormula
  have hstrictFormula := hstrictCode.trans hatomicFormula
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have htag : (binaryNatCode 5).length <= 8 := by decide
    dsimp only [targetFormula]
    simp only [binaryFormulaCode, List.length_append]
    unfold formulaCode boundaryClosedLeFormulaCodePolynomial
    dsimp only [atomicCode, termCode] at *
    omega
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    have hequalityClosed : equalityFormula.freeVariables = ∅ := by
      dsimp only [equalityFormula, args]
      rw [boundaryBinaryRelationFormula_freeVariables]
      simp [hleftClosed, hrightClosed]
    have hstrictClosed : strictFormula.freeVariables = ∅ := by
      dsimp only [strictFormula, args]
      rw [boundaryBinaryRelationFormula_freeVariables]
      simp [hleftClosed, hrightClosed]
    dsimp only [targetFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hGammaEmpty : Gamma = ∅ := by
    unfold Gamma valuationContext
    rw [htargetClosed]
    simp
  have hGammaCard : Gamma.card <= 4 := by
    rw [hGammaEmpty]
    simp
  have hcontext : FormulaCodeBound Gamma formulaCode := by
    rw [hGammaEmpty]
    intro formula hformula
    simp at hformula
  have hequalityContext : FormulaCodeBound (insert equalityFormula Gamma)
      formulaCode := hcontext.insert hequalityFormula
  have hstrictContext : FormulaCodeBound (insert strictFormula Gamma)
      formulaCode := hcontext.insert hstrictFormula
  have hequalityCard : (insert equalityFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le equalityFormula Gamma
    omega
  have hstrictCard : (insert strictFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le strictFormula Gamma
    omega
  have hweakEquality := weakeningFullAssemblyCost_le_small
    (insert equalityFormula Gamma) formulaCode hequalityCard hequalityContext
  have hweakStrict := weakeningFullAssemblyCost_le_small
    (insert strictFormula Gamma) formulaCode hstrictCard hstrictContext
  have hdisjunction := disjunctionFullAssemblyCost_le_small Gamma
    equalityFormula strictFormula formulaCode hGammaCard hcontext
    hequalityFormula hstrictFormula htargetCode
  unfold boundaryClosedLeStructuralPayloadEnvelope
    boundaryValuationLeStructuralPayloadEnvelope
    boundaryClosedLeFixedPayloadPolynomial
  dsimp only [leftTerm, rightTerm, args, equalityFormula, strictFormula,
    targetFormula, Gamma, termCode, formulaCode] at *
  omega

def boundaryEndpointEntryFormulaCodePolynomial (bitBound : Nat) : Nat :=
  boundaryRowEmbeddedEntryFormulaCodeFromTermPolynomial
    (boundaryEndpointEntryTermCodeCeiling bitBound)

private theorem compactFixedWidthEntrySubstitution_code_length_le_fixed
    {targetArity : Nat} (bitBound : Nat)
    (terms : Fin 4 -> ArithmeticSemiterm Nat targetArity)
    (hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        boundaryEndpointEntryTermCodeCeiling bitBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        terms)).length <=
      boundaryEndpointEntryFormulaCodePolynomial bitBound := by
  let source : ArithmeticSemiformula Nat 4 :=
    Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val
  let rewriting : Rew ℒₒᵣ Nat 4 Nat targetArity := Rew.subst terms
  have hrewriting : RewritingImageCodeBound rewriting
      (boundaryEndpointEntryTermCodeCeiling bitBound) := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      exact hterms coordinate
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (boundaryEndpointEntryTermCodeCeiling bitBound) hrewriting source
  simpa only [boundaryEndpointEntryFormulaCodePolynomial,
    boundaryRowEmbeddedEntryFormulaCodeFromTermPolynomial, source,
    rewriting] using hraw

theorem compactFixedWidthBoundaryEndpointFormula_code_length_le_fixed
    (table width value bitBound : Nat) (indexTerm : ValuationTerm)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      boundaryEndpointEntryInputTermCodeCeiling bitBound) :
    (binaryFormulaCode
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value))).length <=
      boundaryEndpointEntryFormulaCodePolynomial bitBound := by
  let terms : Fin 4 -> ValuationTerm :=
    ![shortBinaryNumeralTerm table, shortBinaryNumeralTerm width, indexTerm,
      shortBinaryNumeralTerm value]
  have hnumeral : binaryNumeralTermCodeEnvelope bitBound <=
      boundaryEndpointEntryTermCodeCeiling bitBound := by
    unfold boundaryEndpointEntryTermCodeCeiling
      boundaryEndpointEntryInputTermCodeCeiling
    omega
  have hinput : boundaryEndpointEntryInputTermCodeCeiling bitBound <=
      boundaryEndpointEntryTermCodeCeiling bitBound := by
    unfold boundaryEndpointEntryTermCodeCeiling
    omega
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        boundaryEndpointEntryTermCodeCeiling bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact (binaryNumeralTerm_code_length_le_envelope table bitBound
        htableSize).trans hnumeral
    · exact (binaryNumeralTerm_code_length_le_envelope width bitBound
        hwidthSize).trans hnumeral
    · exact hindexCode.trans hinput
    · exact (binaryNumeralTerm_code_length_le_envelope value bitBound
        hvalueSize).trans hnumeral
  simpa only [compactFixedWidthEntryAtValuationFormula, terms] using
    (compactFixedWidthEntrySubstitution_code_length_le_fixed bitBound terms
      hterms)

theorem compactAdditiveBoundaryTableUniversalFormula_code_length_le_fixed
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      ((compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
        (shortBinaryNumeralTerm partCount))).length <=
      boundaryRowUniversalShellSourceFormulaPolynomial numericBound
        bitBound := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := Rew.bShift (shortBinaryNumeralTerm partCount)
  let universalBody := termBoundedUniversalBody boundTerm body
  let termBound := boundaryRowUniversalShellTermPolynomial numericBound
    bitBound
  let rawFormulaBound :=
    boundaryRowUniversalShellRawFormulaPolynomial numericBound bitBound
  let sourceFormulaBound :=
    boundaryRowUniversalShellSourceFormulaPolynomial numericBound bitBound
  have hcountSize : Nat.size partCount <= bitBound :=
    (Nat.size_le_size hpartCount).trans hnumericSize
  have hshortCode :
      (binaryTermCode (shortBinaryNumeralTerm partCount)).length <=
        binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope partCount bitBound hcountSize
  have hboundTermShift := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm partCount)
  have hshortSymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm partCount)
  have hboundTermRaw : (binaryTermCode boundTerm).length <=
      3 * (binaryTermCode (shortBinaryNumeralTerm partCount)).length := by
    dsimp only [boundTerm]
    omega
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [termBound]
    unfold boundaryRowUniversalShellTermPolynomial
    omega
  have hbodyFixed : (binaryFormulaCode body).length <=
      boundaryRowUniversalBodyFormulaCodePolynomial numericBound
        bitBound := by
    simpa only [body] using
      compactAdditiveBoundaryTableRowBody_code_length_le_fixed tokenCount
        boundaryTable numericBound bitBound htokenCount htableSize
        hnumericSize
  have hbody : (binaryFormulaCode body).length <= rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold boundaryRowUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have htermBoundFormulaRaw := finiteCaseLessThanFormula_code_length_le
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) boundTerm
  have htermBoundFormulaTight :
      (binaryFormulaCode (termBoundFormula boundTerm)).length <=
        (binaryTermCode
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length +
          (binaryTermCode boundTerm).length +
            finiteCaseLessThanFormulaCodeOverhead := by
    simpa only [termBoundFormula] using htermBoundFormulaRaw
  have hzeroTerm :
      (binaryTermCode
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <= termBound := by
    have hzeroCode :
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
            (binaryTermCode (&0 : ValuationTerm)).length := by decide
    dsimp only [termBound]
    unfold boundaryRowUniversalShellTermPolynomial
    omega
  have htermBoundFormula :
      (binaryFormulaCode (termBoundFormula boundTerm)).length <=
        rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold boundaryRowUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have huniversalBodyRaw := binarySemiformulaCode_implication_length_le
    (termBoundFormula boundTerm) body
  have huniversalBodyTight : (binaryFormulaCode universalBody).length <=
      2 * (binaryFormulaCode (termBoundFormula boundTerm)).length +
        (binaryFormulaCode body).length + (binaryNatCode 5).length := by
    simpa only [universalBody, termBoundedUniversalBody] using
      huniversalBodyRaw
  have htagFive : (binaryNatCode 5).length <= 64 := by decide
  have huniversalBody : (binaryFormulaCode universalBody).length <=
      sourceFormulaBound := by
    dsimp only [sourceFormulaBound]
    unfold boundaryRowUniversalShellSourceFormulaPolynomial
    omega
  have huniversalFormulaRaw := binaryFormulaCode_all_length_le universalBody
  have huniversalFormula :
      (binaryFormulaCode
        (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition)).length <=
          sourceFormulaBound := by
    dsimp only [sourceFormulaBound]
    unfold boundaryRowUniversalShellSourceFormulaPolynomial
    omega
  have halignment :
      (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition) =
        body.ballLT (shortBinaryNumeralTerm partCount) := by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm partCount)) body) =
        body.ballLT (shortBinaryNumeralTerm partCount)
    rw [termBoundedUniversal_eq_ball]
    rfl
  rw [← halignment]
  exact huniversalFormula

theorem boundaryClosedLeFormula_code_length_le_fixed
    (left right bitBound : Nat)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” : ValuationFormula)).length <=
      boundaryClosedLeFormulaCodePolynomial bitBound := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let atomicCode := orderAtomicFormulaCodeEnvelope termCode
  have hleftCode : (binaryTermCode leftTerm).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hrightCode : (binaryTermCode rightTerm).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hrightSize
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      atomicCode := by
    simpa only [equalityFormula, args, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq leftTerm
        rightTerm termCode hleftCode hrightCode)
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      atomicCode := by
    simpa only [strictFormula, args, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt leftTerm
        rightTerm termCode hleftCode hrightCode)
  have htag : (binaryNatCode 5).length <= 8 := by decide
  change (binaryFormulaCode (equalityFormula ⋎ strictFormula)).length <= _
  calc
    (binaryFormulaCode (equalityFormula ⋎ strictFormula)).length <=
        2 * atomicCode + 8 := by
      simp only [binaryFormulaCode, List.length_append]
      omega
    _ = boundaryClosedLeFormulaCodePolynomial bitBound := by
      rfl

private theorem compactFixedWidthEntryAtValuationFormula_freeVariables_eq_empty
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm indexTerm
      valueTerm).freeVariables = ∅ := by
  unfold compactFixedWidthEntryAtValuationFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact htable
  · exact hwidth
  · exact hindex
  · exact hvalue

private theorem boundaryClosedLeFormula_freeVariables_eq_empty
    (left right : Nat) :
    (“!!(shortBinaryNumeralTerm left) ≤
      !!(shortBinaryNumeralTerm right)” : ValuationFormula).freeVariables =
        ∅ := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq
    ![leftTerm, rightTerm]
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt
    ![leftTerm, rightTerm]
  have hleft : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hright : rightTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty right
  change (equalityFormula ⋎ strictFormula).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_or]
  have hequality : equalityFormula.freeVariables = ∅ := by
    dsimp only [equalityFormula]
    rw [boundaryBinaryRelationFormula_freeVariables]
    simp [hleft, hright]
  have hstrict : strictFormula.freeVariables = ∅ := by
    dsimp only [strictFormula]
    rw [boundaryBinaryRelationFormula_freeVariables]
    simp [hleft, hright]
  rw [hequality, hstrict]
  simp

theorem transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource rightResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hconjunctionCode : (binaryFormulaCode (left ⋏ right)).length <=
      syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource rightResource <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        rightResource := by
  have hclosed : (left ⋏ right).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hleftClosed,
      hrightClosed]
    simp
  have hcontext : formulaCodeSum
      (valuationContext (left ⋏ right).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
    valuation left right leftResource rightResource syntaxResource hpositive
    hcontext hleftCode hrightCode hconjunctionCode
  simpa only [transparentHybridConjunctionPayloadEnvelope,
    hybridConjunctionStructuralPayloadEnvelope] using hraw

def compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leafCode := boundaryClosedLeFormulaCodePolynomial bitBound +
    boundaryEndpointEntryFormulaCodePolynomial bitBound +
    boundaryRowUniversalShellSourceFormulaPolynomial numericBound bitBound + 1
  5 * leafCode + 4 * (binaryNatCode 4).length + 1

def compactAdditiveBoundaryTableUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  let leResource := boundaryClosedLeFixedPayloadPolynomial bitBound
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      (boundaryEndpointEntryScale numericBound bitBound)
  let universalResource :=
    boundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  2 * leResource + 2 * entryResource + universalResource +
    12 * generalContextAssemblyEnvelope syntaxResource

def compactAdditiveBoundaryTableUniformDirectFixedLeafPayloadEnvelope
    (tokenCount partCount start finish boundaryTable numericBound bitBound :
      Nat) : Nat :=
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount) (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm partCount)
  let leResource := boundaryClosedLeFixedPayloadPolynomial bitBound
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      (boundaryEndpointEntryScale numericBound bitBound)
  let universalResource :=
    boundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  let finishEntryUniversalResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryFixedZeroValuation
      finishEntryFormula universalFormula entryResource universalResource
  let startEntryTailResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryFixedZeroValuation
      startEntryFormula (finishEntryFormula ⋏ universalFormula) entryResource
      finishEntryUniversalResource
  let finishTailResource :=
    transparentHybridConjunctionPayloadEnvelope boundaryFixedZeroValuation
      finishFormula
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula))
      leResource startEntryTailResource
  transparentHybridConjunctionPayloadEnvelope boundaryFixedZeroValuation
    startFormula
    (finishFormula ⋏
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula)))
    leResource finishTailResource

theorem compactAdditiveBoundaryTableUniformDirectPayloadEnvelope_le_fixedLeaf
    (tokenCount partCount start finish boundaryTable numericBound bitBound :
      Nat)
    (hstartBound : start <= tokenCount)
    (hfinishBound : finish <= tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveBoundaryTableUniformDirectPayloadEnvelope tokenCount
        partCount start finish boundaryTable numericBound bitBound <=
      compactAdditiveBoundaryTableUniformDirectFixedLeafPayloadEnvelope
        tokenCount partCount start finish boundaryTable numericBound
        bitBound := by
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount) (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm partCount)
  let leResource := boundaryClosedLeFixedPayloadPolynomial bitBound
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      (boundaryEndpointEntryScale numericBound bitBound)
  let universalResource :=
    boundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstartSize : Nat.size start <= bitBound :=
    (Nat.size_le_size (hstartBound.trans htokenCount)).trans hnumericSize
  have hfinishSize : Nat.size finish <= bitBound :=
    (Nat.size_le_size (hfinishBound.trans htokenCount)).trans hnumericSize
  have hstartResource :
      boundaryClosedLeStructuralPayloadEnvelope boundaryFixedZeroValuation
          start tokenCount <= leResource := by
    exact boundaryClosedLeStructuralPayloadEnvelope_le_fixed
      boundaryFixedZeroValuation start tokenCount bitBound (by rfl) hstartSize
      htokenSize
  have hfinishResource :
      boundaryClosedLeStructuralPayloadEnvelope boundaryFixedZeroValuation
          finish tokenCount <= leResource := by
    exact boundaryClosedLeStructuralPayloadEnvelope_le_fixed
      boundaryFixedZeroValuation finish tokenCount bitBound (by rfl)
      hfinishSize
      htokenSize
  have huniversalResource :
      compactAdditiveBoundaryTableRowsUniformDirectUniversalResource
          tokenCount partCount boundaryTable numericBound bitBound <=
        universalResource :=
    compactAdditiveBoundaryTableRowsUniformDirectUniversalResource_le_fixed
      tokenCount partCount boundaryTable numericBound bitBound htokenCount
      hpartCount htableSize hnumericSize
  have hfinishEntryUniversal :=
    transparentHybridConjunctionPayloadEnvelope_mono
      boundaryFixedZeroValuation finishEntryFormula universalFormula
      (Nat.le_refl entryResource) huniversalResource
  have hstartEntryTail :=
    transparentHybridConjunctionPayloadEnvelope_mono
      boundaryFixedZeroValuation startEntryFormula
      (finishEntryFormula ⋏ universalFormula) (Nat.le_refl entryResource)
      hfinishEntryUniversal
  have hfinishTail := transparentHybridConjunctionPayloadEnvelope_mono
    boundaryFixedZeroValuation finishFormula
    (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula))
    hfinishResource hstartEntryTail
  have htotal := transparentHybridConjunctionPayloadEnvelope_mono
    boundaryFixedZeroValuation startFormula
    (finishFormula ⋏
      (startEntryFormula ⋏ (finishEntryFormula ⋏ universalFormula)))
    hstartResource hfinishTail
  simpa only [compactAdditiveBoundaryTableUniformDirectPayloadEnvelope,
    compactAdditiveBoundaryTableUniformDirectFixedLeafPayloadEnvelope,
    startFormula, finishFormula, startEntryFormula, finishEntryFormula,
    universalFormula, leResource, entryResource, universalResource,
    boundaryFixedZeroValuation] using htotal

theorem
    compactAdditiveBoundaryTableUniformDirectFixedLeafPayloadEnvelope_le_fixed
    (tokenCount partCount start finish boundaryTable numericBound bitBound :
      Nat)
    (hstartBound : start <= tokenCount)
    (hfinishBound : finish <= tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveBoundaryTableUniformDirectFixedLeafPayloadEnvelope
        tokenCount partCount start finish boundaryTable numericBound
        bitBound <=
      compactAdditiveBoundaryTableUniformDirectFixedPayloadPolynomial
        numericBound bitBound := by
  let startFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let startEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm start)
  let finishEntryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm partCount) (shortBinaryNumeralTerm finish)
  let universalFormula :=
    (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
      (shortBinaryNumeralTerm partCount)
  let finishEntryUniversalFormula := finishEntryFormula ⋏ universalFormula
  let startEntryTailFormula := startEntryFormula ⋏
    finishEntryUniversalFormula
  let finishTailFormula := finishFormula ⋏ startEntryTailFormula
  let totalFormula := startFormula ⋏ finishTailFormula
  let syntaxResource :=
    compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  let leafCode := boundaryClosedLeFormulaCodePolynomial bitBound +
    boundaryEndpointEntryFormulaCodePolynomial bitBound +
    boundaryRowUniversalShellSourceFormulaPolynomial numericBound bitBound + 1
  let leResource := boundaryClosedLeFixedPayloadPolynomial bitBound
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      (boundaryEndpointEntryScale numericBound bitBound)
  let universalResource :=
    boundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  let finishEntryUniversalResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource entryResource
      universalResource
  let startEntryTailResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource entryResource
      finishEntryUniversalResource
  let finishTailResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource leResource
      startEntryTailResource
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hpartSize : Nat.size partCount <= bitBound :=
    (Nat.size_le_size hpartCount).trans hnumericSize
  have hstartSize : Nat.size start <= bitBound :=
    (Nat.size_le_size (hstartBound.trans htokenCount)).trans hnumericSize
  have hfinishSize : Nat.size finish <= bitBound :=
    (Nat.size_le_size (hfinishBound.trans htokenCount)).trans hnumericSize
  have hstartIndexCode :
      (binaryTermCode (unaryNumeralTerm 0)).length <=
        boundaryEndpointEntryInputTermCodeCeiling bitBound := by
    unfold boundaryEndpointEntryInputTermCodeCeiling
    omega
  have hfinishIndexCode :
      (binaryTermCode (shortBinaryNumeralTerm partCount)).length <=
        boundaryEndpointEntryInputTermCodeCeiling bitBound := by
    exact (binaryNumeralTerm_code_length_le_envelope partCount bitBound
      hpartSize).trans (by
        unfold boundaryEndpointEntryInputTermCodeCeiling
        omega)
  have hstartCodeRaw := boundaryClosedLeFormula_code_length_le_fixed start
    tokenCount bitBound hstartSize htokenSize
  have hfinishCodeRaw := boundaryClosedLeFormula_code_length_le_fixed finish
    tokenCount bitBound hfinishSize htokenSize
  have hstartEntryCodeRaw :=
    compactFixedWidthBoundaryEndpointFormula_code_length_le_fixed
      boundaryTable tokenCount start bitBound (unaryNumeralTerm 0) htableSize
      htokenSize hstartSize hstartIndexCode
  have hfinishEntryCodeRaw :=
    compactFixedWidthBoundaryEndpointFormula_code_length_le_fixed
      boundaryTable tokenCount finish bitBound
      (shortBinaryNumeralTerm partCount) htableSize htokenSize hfinishSize
      hfinishIndexCode
  have huniversalCodeRaw :=
    compactAdditiveBoundaryTableUniversalFormula_code_length_le_fixed
      tokenCount partCount boundaryTable numericBound bitBound htokenCount
      hpartCount htableSize hnumericSize
  have hstartCode : (binaryFormulaCode startFormula).length <= leafCode := by
    dsimp only [startFormula, leafCode]
    omega
  have hfinishCode : (binaryFormulaCode finishFormula).length <= leafCode := by
    dsimp only [finishFormula, leafCode]
    omega
  have hstartEntryCode : (binaryFormulaCode startEntryFormula).length <=
      leafCode := by
    dsimp only [startEntryFormula, leafCode]
    omega
  have hfinishEntryCode : (binaryFormulaCode finishEntryFormula).length <=
      leafCode := by
    dsimp only [finishEntryFormula, leafCode]
    omega
  have huniversalCode : (binaryFormulaCode universalFormula).length <=
      leafCode := by
    dsimp only [universalFormula, leafCode]
    omega
  have hfinishEntryUniversalCodeRaw := binaryFormulaCode_and_length_le_local
    finishEntryFormula universalFormula
  have hfinishEntryUniversalCodeTight :
      (binaryFormulaCode finishEntryUniversalFormula).length <=
        2 * leafCode + (binaryNatCode 4).length := by
    have hraw :
        (binaryFormulaCode finishEntryUniversalFormula).length <=
          (binaryFormulaCode finishEntryFormula).length +
            (binaryFormulaCode universalFormula).length +
              (binaryNatCode 4).length := by
      simpa only [finishEntryUniversalFormula] using
        hfinishEntryUniversalCodeRaw
    omega
  have hfinishEntryUniversalCode :
      (binaryFormulaCode finishEntryUniversalFormula).length <=
        syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
    dsimp only [leafCode] at *
    omega
  have hstartEntryTailCodeRaw := binaryFormulaCode_and_length_le_local
    startEntryFormula finishEntryUniversalFormula
  have hstartEntryTailCodeTight :
      (binaryFormulaCode startEntryTailFormula).length <=
        3 * leafCode + 2 * (binaryNatCode 4).length := by
    have hraw : (binaryFormulaCode startEntryTailFormula).length <=
        (binaryFormulaCode startEntryFormula).length +
          (binaryFormulaCode finishEntryUniversalFormula).length +
            (binaryNatCode 4).length := by
      simpa only [startEntryTailFormula] using hstartEntryTailCodeRaw
    omega
  have hstartEntryTailCode :
      (binaryFormulaCode startEntryTailFormula).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
    dsimp only [leafCode] at *
    omega
  have hfinishTailCodeRaw := binaryFormulaCode_and_length_le_local
    finishFormula startEntryTailFormula
  have hfinishTailCodeTight :
      (binaryFormulaCode finishTailFormula).length <=
        4 * leafCode + 3 * (binaryNatCode 4).length := by
    have hraw : (binaryFormulaCode finishTailFormula).length <=
        (binaryFormulaCode finishFormula).length +
          (binaryFormulaCode startEntryTailFormula).length +
            (binaryNatCode 4).length := by
      simpa only [finishTailFormula] using hfinishTailCodeRaw
    omega
  have hfinishTailCode : (binaryFormulaCode finishTailFormula).length <=
      syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
    dsimp only [leafCode] at *
    omega
  have htotalCodeRaw := binaryFormulaCode_and_length_le_local startFormula
    finishTailFormula
  have htotalCodeTight : (binaryFormulaCode totalFormula).length <=
      5 * leafCode + 4 * (binaryNatCode 4).length := by
    have hraw : (binaryFormulaCode totalFormula).length <=
        (binaryFormulaCode startFormula).length +
          (binaryFormulaCode finishTailFormula).length +
            (binaryNatCode 4).length := by
      simpa only [totalFormula] using htotalCodeRaw
    omega
  have htotalCode : (binaryFormulaCode totalFormula).length <=
      syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
    dsimp only [leafCode] at *
    omega
  have hleafSyntax : leafCode <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
    dsimp only [leafCode]
    omega
  have hstartSyntax := hstartCode.trans hleafSyntax
  have hfinishSyntax := hfinishCode.trans hleafSyntax
  have hstartEntrySyntax := hstartEntryCode.trans hleafSyntax
  have hfinishEntrySyntax := hfinishEntryCode.trans hleafSyntax
  have huniversalSyntax := huniversalCode.trans hleafSyntax
  have hpositive : 1 <= syntaxResource := by
    change 1 <=
      compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
        numericBound bitBound
    unfold compactAdditiveBoundaryTableUniformDirectAssemblySyntaxPolynomial
    exact Nat.le_add_left 1 _
  have hstartClosed : startFormula.freeVariables = ∅ := by
    simpa only [startFormula] using
      boundaryClosedLeFormula_freeVariables_eq_empty start tokenCount
  have hfinishClosed : finishFormula.freeVariables = ∅ := by
    simpa only [finishFormula] using
      boundaryClosedLeFormula_freeVariables_eq_empty finish tokenCount
  have hstartIndexClosed : (unaryNumeralTerm 0).freeVariables = ∅ := by
    simp [unaryNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]
  have hstartEntryClosed : startEntryFormula.freeVariables = ∅ := by
    dsimp only [startEntryFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_eq_empty
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm start)
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hstartIndexClosed (shortBinaryNumeralTerm_freeVariables_eq_empty start)
  have hfinishEntryClosed : finishEntryFormula.freeVariables = ∅ := by
    dsimp only [finishEntryFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_eq_empty
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm partCount)
      (shortBinaryNumeralTerm finish)
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty partCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty finish)
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    simpa only [universalFormula] using
      compactAdditiveBoundaryTableUniversalFormula_freeVariables_eq_empty
        tokenCount partCount boundaryTable
  have hfinishEntryUniversalClosed :
      finishEntryUniversalFormula.freeVariables = ∅ := by
    dsimp only [finishEntryUniversalFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hfinishEntryClosed,
      huniversalClosed]
    simp
  have hstartEntryTailClosed : startEntryTailFormula.freeVariables = ∅ := by
    dsimp only [startEntryTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hstartEntryClosed,
      hfinishEntryUniversalClosed]
    simp
  have hfinishTailClosed : finishTailFormula.freeVariables = ∅ := by
    dsimp only [finishTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hfinishClosed,
      hstartEntryTailClosed]
    simp
  have hfinishEntryUniversal :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      boundaryFixedZeroValuation finishEntryFormula universalFormula
      entryResource universalResource syntaxResource hpositive
      hfinishEntryClosed huniversalClosed hfinishEntrySyntax
      huniversalSyntax hfinishEntryUniversalCode
  have hstartEntryTailMono := transparentHybridConjunctionPayloadEnvelope_mono
    boundaryFixedZeroValuation startEntryFormula finishEntryUniversalFormula
    (Nat.le_refl entryResource) hfinishEntryUniversal
  have hstartEntryTailGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      boundaryFixedZeroValuation startEntryFormula finishEntryUniversalFormula
      entryResource finishEntryUniversalResource syntaxResource hpositive
      hstartEntryClosed hfinishEntryUniversalClosed hstartEntrySyntax
      hfinishEntryUniversalCode hstartEntryTailCode
  have hstartEntryTail := hstartEntryTailMono.trans hstartEntryTailGeneral
  have hfinishTailMono := transparentHybridConjunctionPayloadEnvelope_mono
    boundaryFixedZeroValuation finishFormula startEntryTailFormula
    (Nat.le_refl leResource) hstartEntryTail
  have hfinishTailGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      boundaryFixedZeroValuation finishFormula startEntryTailFormula
      leResource startEntryTailResource syntaxResource hpositive
      hfinishClosed hstartEntryTailClosed hfinishSyntax hstartEntryTailCode
      hfinishTailCode
  have hfinishTail := hfinishTailMono.trans hfinishTailGeneral
  have htotalMono := transparentHybridConjunctionPayloadEnvelope_mono
    boundaryFixedZeroValuation startFormula finishTailFormula
    (Nat.le_refl leResource) hfinishTail
  have htotalGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      boundaryFixedZeroValuation startFormula finishTailFormula leResource
      finishTailResource syntaxResource hpositive hstartClosed
      hfinishTailClosed hstartSyntax hfinishTailCode htotalCode
  have htotal := htotalMono.trans htotalGeneral
  unfold compactAdditiveBoundaryTableUniformDirectFixedLeafPayloadEnvelope
  dsimp only [startFormula, finishFormula, startEntryFormula,
    finishEntryFormula, universalFormula, leResource, entryResource,
    universalResource]
  exact htotal.trans (by
    change hybridConjunctionGeneralPayloadEnvelope syntaxResource leResource
        finishTailResource <=
      compactAdditiveBoundaryTableUniformDirectFixedPayloadPolynomial
        numericBound bitBound
    unfold compactAdditiveBoundaryTableUniformDirectFixedPayloadPolynomial
      hybridConjunctionGeneralPayloadEnvelope
    change
      leResource + finishTailResource +
          3 * generalContextAssemblyEnvelope syntaxResource <=
        2 * leResource + 2 * entryResource + universalResource +
          12 * generalContextAssemblyEnvelope syntaxResource
    dsimp only [finishTailResource, startEntryTailResource,
      finishEntryUniversalResource]
    unfold hybridConjunctionGeneralPayloadEnvelope
    omega)

theorem compactAdditiveBoundaryTableUniformDirectPayloadEnvelope_le_fixed
    (tokenCount partCount start finish boundaryTable numericBound bitBound :
      Nat)
    (hstartBound : start <= tokenCount)
    (hfinishBound : finish <= tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveBoundaryTableUniformDirectPayloadEnvelope tokenCount
        partCount start finish boundaryTable numericBound bitBound <=
      compactAdditiveBoundaryTableUniformDirectFixedPayloadPolynomial
        numericBound bitBound :=
  (compactAdditiveBoundaryTableUniformDirectPayloadEnvelope_le_fixedLeaf
    tokenCount partCount start finish boundaryTable numericBound bitBound
    hstartBound hfinishBound htokenCount hpartCount htableSize
    hnumericSize).trans
      (compactAdditiveBoundaryTableUniformDirectFixedLeafPayloadEnvelope_le_fixed
        tokenCount partCount start finish boundaryTable numericBound bitBound
        hstartBound hfinishBound htokenCount hpartCount htableSize
        hnumericSize)

#print axioms boundaryClosedLeStructuralPayloadEnvelope_le_fixed
#print axioms
  compactAdditiveBoundaryTableUniformDirectPayloadEnvelope_le_fixedLeaf
#print axioms
  compactAdditiveBoundaryTableUniformDirectPayloadEnvelope_le_fixed

end FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds
