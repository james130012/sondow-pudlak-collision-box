import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveProductSplitFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fixed payload bound for the fully uniform parser-state core

The ten checked leaves are charged to one numeric and one bit-width
coordinate.  Nine direct conjunctions assemble the exact closed parser-state
formula; no proof-dependent finite sum survives in the final resource.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
open FoundationCompactNumericListedDirectAdditiveProductSplitFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds

abbrev parserFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.zeroValuation

private theorem parserFixedBinaryFunctionTerm_freeVariables
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

private theorem parserFixedBinaryFunctionTerm_code_length_le
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func functionSymbol ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead functionSymbol := by
  simp [Matrix.fun_eq_vec_two, binaryTermCode,
    binaryFunctionTermCodeOverhead]
  omega

private theorem parserFixedBinaryRelationFormula_freeVariables
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right]).freeVariables =
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

private theorem parserFixedArithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem productSplitClosedFormula_freeVariables_eq_empty
    (tokenCount start middle finish : Nat) :
    (compactAdditiveProductSplitClosedFormula tokenCount start middle
      finish).freeVariables = ∅ := by
  unfold compactAdditiveProductSplitClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem natSizeClosedFormula_freeVariables_eq_empty
    (size value : Nat) :
    (compactNatSizeClosedFormula size value).freeVariables = ∅ := by
  unfold compactNatSizeClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem parserAreaFormula_freeVariables_eq_empty
    (boundarySize count tokenCount : Nat) :
    (“!!(shortBinaryNumeralTerm boundarySize) ≤
      (!!(shortBinaryNumeralTerm count) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula).freeVariables =
      ∅ := by
  let leftTerm := shortBinaryNumeralTerm boundarySize
  let countTerm := shortBinaryNumeralTerm count
  let oneTerm : ValuationTerm := ‘1’
  let sumTerm : ValuationTerm := ‘!!countTerm + !!oneTerm’
  let tokenTerm := shortBinaryNumeralTerm tokenCount
  let rightTerm : ValuationTerm := ‘!!sumTerm * !!tokenTerm’
  have hleft : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundarySize
  have hcount : countTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty count
  have hone : oneTerm.freeVariables = ∅ := by
    simpa only [oneTerm] using
      parserFixedArithmeticOneTerm_freeVariables_eq_empty
  have hsum : sumTerm.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiterm.func Language.Add.add
        ![countTerm, oneTerm]).freeVariables = ∅
    rw [parserFixedBinaryFunctionTerm_freeVariables, hcount, hone]
    simp
  have htoken : tokenTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hright : rightTerm.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiterm.func Language.Mul.mul
        ![sumTerm, tokenTerm]).freeVariables = ∅
    rw [parserFixedBinaryFunctionTerm_freeVariables, hsum, htoken]
    simp
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm] ⋎
      LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![leftTerm, rightTerm]).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_or,
    parserFixedBinaryRelationFormula_freeVariables,
    parserFixedBinaryRelationFormula_freeVariables, hleft, hright]
  simp

def parserAreaFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  let termCode := completedAreaTermCodePolynomial bitBound
  let formulaCode := completedAreaFormulaCodePolynomial bitBound
  2 * compilePositiveRelationFixedPayloadPolynomial 0 termCode +
    3 * generalContextAssemblyEnvelope formulaCode

private theorem parserAreaRightTerm_code_length_le_fixed
    (tokenCount count bitBound : Nat)
    (htokenWidth : Nat.size tokenCount <= bitBound)
    (hcountWidth : Nat.size count <= bitBound) :
    (binaryTermCode
      (‘(!!(shortBinaryNumeralTerm count) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)’ : ValuationTerm)).length <=
      completedAreaTermCodePolynomial bitBound := by
  let countTerm := shortBinaryNumeralTerm count
  let oneTerm : ValuationTerm := ‘1’
  let sumTerm : ValuationTerm := ‘!!countTerm + !!oneTerm’
  let tokenTerm := shortBinaryNumeralTerm tokenCount
  let rightTerm : ValuationTerm := ‘!!sumTerm * !!tokenTerm’
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  have hcount : (binaryTermCode countTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope count bitBound hcountWidth
  have htoken : (binaryTermCode tokenTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope tokenCount bitBound htokenWidth
  have hsum : (binaryTermCode sumTerm).length <=
      (binaryTermCode countTerm).length +
        (binaryTermCode oneTerm).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    change
      (binaryTermCode
        (LO.FirstOrder.Semiterm.func Language.Add.add
          ![countTerm, oneTerm])).length <= _
    exact parserFixedBinaryFunctionTerm_code_length_le Language.Add.add
      countTerm oneTerm
  have hright : (binaryTermCode rightTerm).length <=
      (binaryTermCode sumTerm).length +
        (binaryTermCode tokenTerm).length +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    change
      (binaryTermCode
        (LO.FirstOrder.Semiterm.func Language.Mul.mul
          ![sumTerm, tokenTerm])).length <= _
    exact parserFixedBinaryFunctionTerm_code_length_le Language.Mul.mul
      sumTerm tokenTerm
  change (binaryTermCode rightTerm).length <= _
  unfold completedAreaTermCodePolynomial
  dsimp only [oneTerm] at hsum
  dsimp only [numeralCode, oneTerm]
  omega

private theorem parserAreaRelationFormula_code_length_le_fixed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft : (binaryTermCode left).length <=
      completedAreaTermCodePolynomial bitBound)
    (hright : (binaryTermCode right).length <=
      completedAreaTermCodePolynomial bitBound) :
    (binaryFormulaCode
      (binaryRelationFormula relationSymbol left right)).length <=
      orderAtomicFormulaCodeEnvelope
        (completedAreaTermCodePolynomial bitBound) := by
  exact binaryRelationFormula_code_le_orderAtomic relationSymbol left right
    (completedAreaTermCodePolynomial bitBound) hleft hright

theorem boundaryAreaStructuralPayloadPolynomial_le_fixed
    (boundarySize count tokenCount boundaryTable numericBound bitBound : Nat)
    (hsize : boundarySize = Nat.size boundaryTable)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    boundaryAreaStructuralPayloadPolynomial boundarySize count tokenCount <=
      parserAreaFixedPayloadPolynomial bitBound := by
  let valuation : Nat -> Nat := parserFixedZeroValuation
  let leftTerm := shortBinaryNumeralTerm boundarySize
  let countTerm := shortBinaryNumeralTerm count
  let oneTerm : ValuationTerm := ‘1’
  let sumTerm : ValuationTerm := ‘!!countTerm + !!oneTerm’
  let tokenTerm := shortBinaryNumeralTerm tokenCount
  let rightTerm : ValuationTerm := ‘!!sumTerm * !!tokenTerm’
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  let termCode := completedAreaTermCodePolynomial bitBound
  let atomicCode := orderAtomicFormulaCodeEnvelope termCode
  let formulaCode := completedAreaFormulaCodePolynomial bitBound
  have htokenWidth : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hcountWidth : Nat.size count <= bitBound :=
    (Nat.size_le_size hcount).trans hnumericSize
  have hboundarySizeWidth : Nat.size boundarySize <= bitBound := by
    rw [hsize]
    exact
      (natSize_le_of_le (Nat.le_refl (Nat.size boundaryTable))).trans
        htableSize
  have hleftClosed : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundarySize
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    change
      (LO.FirstOrder.Semiterm.func Language.Mul.mul
        ![sumTerm, tokenTerm]).freeVariables = ∅
    rw [parserFixedBinaryFunctionTerm_freeVariables]
    have hsum : sumTerm.freeVariables = ∅ := by
      dsimp only [sumTerm]
      change
        (LO.FirstOrder.Semiterm.func Language.Add.add
          ![countTerm, oneTerm]).freeVariables = ∅
      rw [parserFixedBinaryFunctionTerm_freeVariables]
      simp [countTerm, oneTerm,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        parserFixedArithmeticOneTerm_freeVariables_eq_empty]
    rw [hsum]
    simp [tokenTerm, shortBinaryNumeralTerm_freeVariables_eq_empty]
  have hleftCode : (binaryTermCode leftTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope
      boundarySize bitBound hboundarySizeWidth
    have hlarge : binaryNumeralTermCodeEnvelope bitBound <=
        completedAreaTermCodePolynomial bitBound := by
      unfold completedAreaTermCodePolynomial
      dsimp only
      omega
    simpa only [leftTerm, termCode] using hraw.trans hlarge
  have hrightCode : (binaryTermCode rightTerm).length <= termCode := by
    simpa only [rightTerm, sumTerm, countTerm, oneTerm, tokenTerm, termCode]
      using parserAreaRightTerm_code_length_le_fixed tokenCount count bitBound
        htokenWidth hcountWidth
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change leftTerm.freeVariables ⊆ {0}
    rw [hleftClosed]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [hrightClosed]
    simp
  have hequalityResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed valuation Language.Eq.eq
      args 0 termCode hfirst hsecond (by rfl) hleftCode hrightCode
  have hstrictResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed valuation
      Language.ORing.Rel.lt args 0 termCode hfirst hsecond (by rfl)
      hleftCode hrightCode
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      atomicCode := by
    simpa only [equalityFormula, args, binaryRelationFormula] using
      parserAreaRelationFormula_code_length_le_fixed Language.Eq.eq leftTerm
        rightTerm bitBound hleftCode hrightCode
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      atomicCode := by
    simpa only [strictFormula, args, binaryRelationFormula] using
      parserAreaRelationFormula_code_length_le_fixed Language.LT.lt leftTerm
        rightTerm bitBound hleftCode hrightCode
  have hatomicFormula : atomicCode <= formulaCode := by
    unfold formulaCode completedAreaFormulaCodePolynomial
    dsimp only [atomicCode, termCode]
    omega
  have hequalityFormula := hequalityCode.trans hatomicFormula
  have hstrictFormula := hstrictCode.trans hatomicFormula
  have htargetCode : (binaryFormulaCode targetFormula).length <= formulaCode := by
    have htag : (binaryNatCode 5).length <= 8 := by decide
    dsimp only [targetFormula]
    simp only [binaryFormulaCode, List.length_append]
    unfold formulaCode completedAreaFormulaCodePolynomial
    dsimp only [atomicCode, termCode] at *
    omega
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    have hequalityClosed : equalityFormula.freeVariables = ∅ := by
      dsimp only [equalityFormula, args]
      rw [parserFixedBinaryRelationFormula_freeVariables, hleftClosed,
        hrightClosed]
      simp
    have hstrictClosed : strictFormula.freeVariables = ∅ := by
      dsimp only [strictFormula, args]
      rw [parserFixedBinaryRelationFormula_freeVariables, hleftClosed,
        hrightClosed]
      simp
    dsimp only [targetFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hGammaEmpty : Gamma = ∅ := by
    unfold Gamma valuationContext
    rw [htargetClosed]
    simp
  have hpositive : 1 <= formulaCode := by
    unfold formulaCode completedAreaFormulaCodePolynomial
    dsimp only [atomicCode, termCode]
    omega
  have hGammaSum :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          Gamma <= formulaCode := by
    rw [hGammaEmpty]
    simp [FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hequalitySum :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (insert equalityFormula Gamma) <=
        generalContextCoordinate formulaCode := by
    have hraw := formulaCodeSum_insert_le Gamma equalityFormula
    unfold generalContextCoordinate
    omega
  have hstrictSum :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (insert strictFormula Gamma) <=
        generalContextCoordinate formulaCode := by
    have hraw := formulaCodeSum_insert_le Gamma strictFormula
    unfold generalContextCoordinate
    omega
  have hweakEquality := weakeningFullAssemblyCost_le_general
    (insert equalityFormula Gamma) formulaCode hequalitySum
  have hweakStrict := weakeningFullAssemblyCost_le_general
    (insert strictFormula Gamma) formulaCode hstrictSum
  have hdisjunction := disjunctionFullAssemblyCost_le_general Gamma
    equalityFormula strictFormula formulaCode hpositive hGammaSum
    hequalityFormula hstrictFormula htargetCode
  unfold boundaryAreaStructuralPayloadPolynomial
    parserValuationLeStructuralPayloadPolynomial
    parserAreaFixedPayloadPolynomial
  rw [parserZeroValuation_eq_public]
  dsimp only [parserFixedZeroValuation, valuation, leftTerm, countTerm,
    oneTerm, sumTerm, tokenTerm,
    rightTerm, args, equalityFormula, strictFormula, targetFormula, Gamma,
    termCode, formulaCode] at *
  omega

private theorem transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
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
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (left ⋏ right).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
    valuation left right leftResource rightResource syntaxResource hpositive
    hcontext hleftCode hrightCode hconjunctionCode
  change hybridConjunctionStructuralPayloadEnvelope valuation left right
      leftResource rightResource <= _
  exact hraw

structure FixedClosedDirectFormulaBound
    (formula : ValuationFormula) (payloadResource codeResource : Nat) where
  proof : CertifiedPAContextProof
    (valuationContext formula.freeVariables parserFixedZeroValuation) formula
  payloadLength_le : proof.payloadLength <= payloadResource
  closed : formula.freeVariables = ∅
  codeLength_le : (binaryFormulaCode formula).length <= codeResource

noncomputable def fixedClosedDirectFormulaBoundOfProof
    {formula : ValuationFormula}
    (proof : CertifiedPAContextProof
      (valuationContext formula.freeVariables parserFixedZeroValuation)
      formula)
    (resource : Nat)
    (hpayload : proof.payloadLength <= resource)
    (hclosed : formula.freeVariables = ∅) :
    FixedClosedDirectFormulaBound formula resource resource where
  proof := proof
  payloadLength_le := hpayload
  closed := hclosed
  codeLength_le :=
    (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      proof).trans hpayload

noncomputable def fixedClosedDirectFormulaBoundOfEmptyProof
    {formula : ValuationFormula}
    (proof : CertifiedPAContextProof ∅ formula)
    (resource : Nat)
    (hpayload : proof.payloadLength <= resource)
    (hclosed : formula.freeVariables = ∅) :
    FixedClosedDirectFormulaBound formula resource resource := by
  have hcontext : (∅ : Finset ValuationFormula) =
      valuationContext formula.freeVariables parserFixedZeroValuation := by
    rw [hclosed]
    simp [valuationContext]
  let atValuation := CertifiedPAContextProof.castContext hcontext proof
  refine {
    proof := atValuation
    payloadLength_le := ?_
    closed := hclosed
    codeLength_le := ?_
  }
  · dsimp only [atValuation]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hpayload
  · exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        proof).trans hpayload

noncomputable def FixedClosedDirectFormulaBound.conjunction
    {left right : ValuationFormula}
    {leftPayload rightPayload leftCode rightCode : Nat}
    (leftBound : FixedClosedDirectFormulaBound left leftPayload leftCode)
    (rightBound : FixedClosedDirectFormulaBound right rightPayload rightCode)
    (syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hleftSyntax : leftCode <= syntaxResource)
    (hrightSyntax : rightCode <= syntaxResource)
    (hconjunctionSyntax :
      leftCode + rightCode + (binaryNatCode 4).length <= syntaxResource) :
    FixedClosedDirectFormulaBound (left ⋏ right)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource leftPayload
        rightPayload)
      (leftCode + rightCode + (binaryNatCode 4).length) := by
  let proof := compileDirectConjunction leftBound.proof rightBound.proof
  have hraw : proof.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope parserFixedZeroValuation
        left right leftPayload rightPayload :=
    compileDirectConjunction_payloadLength_le leftBound.proof rightBound.proof
      leftPayload rightPayload leftBound.payloadLength_le
      rightBound.payloadLength_le
  have henvelope := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    parserFixedZeroValuation left right leftPayload rightPayload
    syntaxResource hpositive leftBound.closed rightBound.closed
    (leftBound.codeLength_le.trans hleftSyntax)
    (rightBound.codeLength_le.trans hrightSyntax) (by
      have hleftCode := leftBound.codeLength_le
      have hrightCode := rightBound.codeLength_le
      simp only [binaryFormulaCode, List.length_append]
      omega)
  refine {
    proof := proof
    payloadLength_le := hraw.trans henvelope
    closed := ?_
    codeLength_le := ?_
  }
  · rw [LO.FirstOrder.Semiformula.freeVariables_and, leftBound.closed,
      rightBound.closed]
    simp
  · have hleftCode := leftBound.codeLength_le
    have hrightCode := rightBound.codeLength_le
    simp only [binaryFormulaCode, List.length_append]
    omega

def compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 * productSplitFixedPayloadPolynomial bitBound +
    2 * compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    tripleBoundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    2 * compactNatSizeFixedPayloadPolynomial bitBound +
    2 * parserAreaFixedPayloadPolynomial bitBound +
    9 * (binaryNatCode 4).length + 1

def compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  2 * productSplitFixedPayloadPolynomial bitBound +
    2 * compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    tripleBoundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    2 * compactNatSizeFixedPayloadPolynomial bitBound +
    2 * parserAreaFixedPayloadPolynomial bitBound +
    27 * generalContextAssemblyEnvelope syntaxResource

noncomputable def compactUnifiedParserStateCoreFullyUniformDirectFixedBound
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokensCount : coordinates.tokensCount <= numericBound)
    (htasksCount : coordinates.tasksCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (htokensTableSize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htasksTableSize : Nat.size coordinates.tasksBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ClosedDirectFormulaBound
      (compactUnifiedParserStateCoreClosedFormula tokenTable width tokenCount
        coordinates.start coordinates.finish coordinates.tokensFinish
        coordinates.tasksFinish coordinates.tokensBoundary
        coordinates.tokensCount coordinates.tasksBoundary
        coordinates.tasksCount sizeWitness.tokensBoundarySize
        sizeWitness.tasksBoundarySize)
      (compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
        numericBound bitBound) := by
  rcases hgraph with
    ⟨houter, htokensLayout, htokensRows, hinner, htasksLayout, htasksRows,
      htokensSize, htokensArea, htasksSize, htasksArea⟩
  let tokensLayoutData := compactAdditiveStructuredListLayoutDataOfLayout
    tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary htokensLayout
  let tasksLayoutData := compactAdditiveStructuredListLayoutDataOfLayout
    tokenTable width tokenCount coordinates.tokensFinish coordinates.tasksCount
      coordinates.tasksFinish coordinates.tasksBoundary htasksLayout
  let outerFormula := compactAdditiveProductSplitClosedFormula tokenCount
    coordinates.start coordinates.tokensFinish coordinates.finish
  let tokensLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
  let tokensRowsFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount coordinates.tokensCount coordinates.tokensBoundary
  let innerFormula := compactAdditiveProductSplitClosedFormula tokenCount
    coordinates.tokensFinish coordinates.tasksFinish coordinates.finish
  let tasksLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.tokensFinish coordinates.tasksCount
      coordinates.tasksFinish coordinates.tasksBoundary
  let tasksRowsFormula := compactAdditiveTripleBoundaryRowsClosedFormula
    tokenCount coordinates.tasksCount coordinates.tasksBoundary
  let tokensSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  let tokensAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tokensBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tokensCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let tasksSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  let tasksAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tasksBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tasksCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let outerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph tokenCount
      coordinates.start coordinates.tokensFinish coordinates.finish houter
  let tokensLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
      tokensLayoutData.bodyStart numericBound bitBound
      tokensLayoutData.bodyStart_le_tokenCount tokensLayoutData.header
      tokensLayoutData.boundaryFinish_le_tokenCount
      tokensLayoutData.boundaryStartEntry tokensLayoutData.boundaryFinishEntry
      tokensLayoutData.rows htokenCount htokensCount htokensTableSize
      hnumericSize
  let tokensRowsRaw :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount coordinates.tokensCount coordinates.tokensBoundary
      numericBound bitBound htokensRows htokenCount htokensCount
      htokensTableSize hnumericSize
  let innerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph tokenCount
      coordinates.tokensFinish coordinates.tasksFinish coordinates.finish
      hinner
  let tasksLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
      tasksLayoutData.bodyStart numericBound bitBound
      tasksLayoutData.bodyStart_le_tokenCount tasksLayoutData.header
      tasksLayoutData.boundaryFinish_le_tokenCount
      tasksLayoutData.boundaryStartEntry tasksLayoutData.boundaryFinishEntry
      tasksLayoutData.rows htokenCount htasksCount htasksTableSize hnumericSize
  let tasksRowsRaw :=
    compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount coordinates.tasksCount coordinates.tasksBoundary
      numericBound bitBound htasksRows htokenCount htasksCount htasksTableSize
      hnumericSize
  let tokensSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary htokensSize
  let tokensAreaCertificate := boundaryAreaCertificate
    sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
      htokensArea
  let tasksSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary htasksSize
  let tasksAreaCertificate := boundaryAreaCertificate
    sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount htasksArea
  let outerResource := productSplitFixedPayloadPolynomial bitBound
  let tokensLayoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let tokensRowsResource :=
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  let innerResource := productSplitFixedPayloadPolynomial bitBound
  let tasksLayoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let tasksRowsResource :=
    tripleBoundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  let tokensSizeResource := compactNatSizeFixedPayloadPolynomial bitBound
  let tokensAreaResource := parserAreaFixedPayloadPolynomial bitBound
  let tasksSizeResource := compactNatSizeFixedPayloadPolynomial bitBound
  let tasksAreaResource := parserAreaFixedPayloadPolynomial bitBound
  let syntaxResource :=
    compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  have hfinishBound : coordinates.finish <= numericBound :=
    houter.2.2.trans htokenCount
  have hstartBound : coordinates.start <= numericBound :=
    (Nat.le_of_lt houter.1).trans
      ((Nat.le_of_lt houter.2.1).trans hfinishBound)
  have htokensFinishBound : coordinates.tokensFinish <= numericBound :=
    (Nat.le_of_lt houter.2.1).trans hfinishBound
  have htasksFinishBound : coordinates.tasksFinish <= numericBound :=
    (Nat.le_of_lt hinner.2.1).trans hfinishBound
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstartSize : Nat.size coordinates.start <= bitBound :=
    (Nat.size_le_size hstartBound).trans hnumericSize
  have hfinishSize : Nat.size coordinates.finish <= bitBound :=
    (Nat.size_le_size hfinishBound).trans hnumericSize
  have htokensFinishSize : Nat.size coordinates.tokensFinish <= bitBound :=
    (Nat.size_le_size htokensFinishBound).trans hnumericSize
  have htasksFinishSize : Nat.size coordinates.tasksFinish <= bitBound :=
    (Nat.size_le_size htasksFinishBound).trans hnumericSize
  have houterProof : outerCertificate.compile.payloadLength <= outerResource :=
    compactAdditiveProductSplitExplicitHybridCertificate_payloadLength_le_fixed
      tokenCount coordinates.start coordinates.tokensFinish
      coordinates.finish bitBound houter htokenCountSize hstartSize
      htokensFinishSize hfinishSize
  have htokensLayoutProof : tokensLayoutRaw.payloadLength <=
      tokensLayoutResource :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
      tokensLayoutData.bodyStart numericBound bitBound
      tokensLayoutData.bodyStart_le_tokenCount tokensLayoutData.header
      tokensLayoutData.boundaryFinish_le_tokenCount
      tokensLayoutData.boundaryStartEntry tokensLayoutData.boundaryFinishEntry
      tokensLayoutData.rows hwidthBound htokenCount htokensCount
      htokenTableSize htokensTableSize hnumericSize
  have htokensRowsProof : tokensRowsRaw.payloadLength <= tokensRowsResource :=
    (compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
      tokenCount coordinates.tokensCount coordinates.tokensBoundary
      numericBound bitBound htokensRows htokenCount htokensCount
      htokensTableSize hnumericSize).trans
      (compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource_le_fixed
        tokenCount coordinates.tokensCount coordinates.tokensBoundary
        numericBound bitBound htokenCount htokensCount htokensTableSize
        hnumericSize)
  have hinnerProof : innerCertificate.compile.payloadLength <= innerResource :=
    compactAdditiveProductSplitExplicitHybridCertificate_payloadLength_le_fixed
      tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish bitBound hinner htokenCountSize htokensFinishSize
      htasksFinishSize hfinishSize
  have htasksLayoutProof : tasksLayoutRaw.payloadLength <=
      tasksLayoutResource :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
      tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
      tasksLayoutData.bodyStart numericBound bitBound
      tasksLayoutData.bodyStart_le_tokenCount tasksLayoutData.header
      tasksLayoutData.boundaryFinish_le_tokenCount
      tasksLayoutData.boundaryStartEntry tasksLayoutData.boundaryFinishEntry
      tasksLayoutData.rows hwidthBound htokenCount htasksCount
      htokenTableSize htasksTableSize hnumericSize
  have htasksRowsProof : tasksRowsRaw.payloadLength <= tasksRowsResource :=
    (compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
      tokenCount coordinates.tasksCount coordinates.tasksBoundary
      numericBound bitBound htasksRows htokenCount htasksCount htasksTableSize
      hnumericSize).trans
      (compactAdditiveTripleBoundaryRowsUniformDirectUniversalResource_le_fixed
        tokenCount coordinates.tasksCount coordinates.tasksBoundary
        numericBound bitBound htokenCount htasksCount htasksTableSize
        hnumericSize)
  have htokensSizeProof : tokensSizeCertificate.compile.payloadLength <=
      tokensSizeResource :=
    (compile_payloadLength_le_structuralPayloadBound
      tokensSizeCertificate).trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        sizeWitness.tokensBoundarySize coordinates.tokensBoundary
        htokensSize).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed
          sizeWitness.tokensBoundarySize coordinates.tokensBoundary bitBound
          htokensSize htokensTableSize))
  have htokensAreaProof : tokensAreaCertificate.compile.payloadLength <=
      tokensAreaResource :=
    (compile_payloadLength_le_structuralPayloadBound
      tokensAreaCertificate).trans
      ((boundaryAreaCertificate_structuralPayloadBound_le_public
        sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
        htokensArea).trans
        (boundaryAreaStructuralPayloadPolynomial_le_fixed
          sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
          coordinates.tokensBoundary numericBound bitBound htokensSize
          htokenCount htokensCount htokensTableSize hnumericSize))
  have htasksSizeProof : tasksSizeCertificate.compile.payloadLength <=
      tasksSizeResource :=
    (compile_payloadLength_le_structuralPayloadBound
      tasksSizeCertificate).trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        sizeWitness.tasksBoundarySize coordinates.tasksBoundary
        htasksSize).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed
          sizeWitness.tasksBoundarySize coordinates.tasksBoundary bitBound
          htasksSize htasksTableSize))
  have htasksAreaProof : tasksAreaCertificate.compile.payloadLength <=
      tasksAreaResource :=
    (compile_payloadLength_le_structuralPayloadBound
      tasksAreaCertificate).trans
      ((boundaryAreaCertificate_structuralPayloadBound_le_public
        sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
        htasksArea).trans
        (boundaryAreaStructuralPayloadPolynomial_le_fixed
          sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
          coordinates.tasksBoundary numericBound bitBound htasksSize
          htokenCount htasksCount htasksTableSize hnumericSize))
  have houterClosed : outerFormula.freeVariables = ∅ := by
    simpa only [outerFormula] using
      productSplitClosedFormula_freeVariables_eq_empty tokenCount
        coordinates.start coordinates.tokensFinish coordinates.finish
  have htokensLayoutClosed : tokensLayoutFormula.freeVariables = ∅ := by
    simpa only [tokensLayoutFormula] using
      compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount coordinates.start coordinates.tokensCount
        coordinates.tokensFinish coordinates.tokensBoundary
  have htokensRowsClosed : tokensRowsFormula.freeVariables = ∅ := by
    simpa only [tokensRowsFormula] using
      compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount coordinates.tokensCount coordinates.tokensBoundary
  have hinnerClosed : innerFormula.freeVariables = ∅ := by
    simpa only [innerFormula] using
      productSplitClosedFormula_freeVariables_eq_empty tokenCount
        coordinates.tokensFinish coordinates.tasksFinish coordinates.finish
  have htasksLayoutClosed : tasksLayoutFormula.freeVariables = ∅ := by
    simpa only [tasksLayoutFormula] using
      compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount coordinates.tokensFinish
        coordinates.tasksCount coordinates.tasksFinish
        coordinates.tasksBoundary
  have htasksRowsClosed : tasksRowsFormula.freeVariables = ∅ := by
    simpa only [tasksRowsFormula] using
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount coordinates.tasksCount coordinates.tasksBoundary
  have htokensSizeClosed : tokensSizeFormula.freeVariables = ∅ := by
    simpa only [tokensSizeFormula] using
      natSizeClosedFormula_freeVariables_eq_empty
        sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  have htokensAreaClosed : tokensAreaFormula.freeVariables = ∅ := by
    simpa only [tokensAreaFormula] using
      parserAreaFormula_freeVariables_eq_empty
        sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
  have htasksSizeClosed : tasksSizeFormula.freeVariables = ∅ := by
    simpa only [tasksSizeFormula] using
      natSizeClosedFormula_freeVariables_eq_empty
        sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  have htasksAreaClosed : tasksAreaFormula.freeVariables = ∅ := by
    simpa only [tasksAreaFormula] using
      parserAreaFormula_freeVariables_eq_empty
        sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
  let outerBound := fixedClosedDirectFormulaBoundOfProof
    outerCertificate.compile outerResource houterProof houterClosed
  let tokensLayoutBound := fixedClosedDirectFormulaBoundOfEmptyProof
    tokensLayoutRaw tokensLayoutResource htokensLayoutProof
      htokensLayoutClosed
  let tokensRowsBound := fixedClosedDirectFormulaBoundOfEmptyProof
    tokensRowsRaw tokensRowsResource htokensRowsProof htokensRowsClosed
  let innerBound := fixedClosedDirectFormulaBoundOfProof
    innerCertificate.compile innerResource hinnerProof hinnerClosed
  let tasksLayoutBound := fixedClosedDirectFormulaBoundOfEmptyProof
    tasksLayoutRaw tasksLayoutResource htasksLayoutProof htasksLayoutClosed
  let tasksRowsBound := fixedClosedDirectFormulaBoundOfEmptyProof
    tasksRowsRaw tasksRowsResource htasksRowsProof htasksRowsClosed
  let tokensSizeBound := fixedClosedDirectFormulaBoundOfProof
    tokensSizeCertificate.compile tokensSizeResource htokensSizeProof
      htokensSizeClosed
  let tokensAreaBound := fixedClosedDirectFormulaBoundOfProof
    tokensAreaCertificate.compile tokensAreaResource htokensAreaProof
      htokensAreaClosed
  let tasksSizeBound := fixedClosedDirectFormulaBoundOfProof
    tasksSizeCertificate.compile tasksSizeResource htasksSizeProof
      htasksSizeClosed
  let tasksAreaBound := fixedClosedDirectFormulaBoundOfProof
    tasksAreaCertificate.compile tasksAreaResource htasksAreaProof
      htasksAreaClosed
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
    omega
  let tasksSizeAreaFormula := tasksSizeFormula ⋏ tasksAreaFormula
  let tasksSizeAreaResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource tasksSizeResource tasksAreaResource
  let tasksSizeAreaCode := tasksSizeResource + tasksAreaResource +
    (binaryNatCode 4).length
  let tasksSizeAreaBound : FixedClosedDirectFormulaBound tasksSizeAreaFormula
      tasksSizeAreaResource tasksSizeAreaCode :=
    FixedClosedDirectFormulaBound.conjunction tasksSizeBound tasksAreaBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, tasksSizeResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let tokensAreaTailFormula := tokensAreaFormula ⋏ tasksSizeAreaFormula
  let tokensAreaTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource tokensAreaResource tasksSizeAreaResource
  let tokensAreaTailCode := tokensAreaResource + tasksSizeAreaCode +
    (binaryNatCode 4).length
  let tokensAreaTailBound : FixedClosedDirectFormulaBound tokensAreaTailFormula
      tokensAreaTailResource tokensAreaTailCode :=
    FixedClosedDirectFormulaBound.conjunction tokensAreaBound
      tasksSizeAreaBound syntaxResource hpositive (by
        dsimp only [syntaxResource, tokensAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tasksSizeAreaCode, tasksSizeResource,
          tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensAreaResource, tasksSizeAreaCode,
          tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let tokensSizeTailFormula := tokensSizeFormula ⋏ tokensAreaTailFormula
  let tokensSizeTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource tokensSizeResource tokensAreaTailResource
  let tokensSizeTailCode := tokensSizeResource + tokensAreaTailCode +
    (binaryNatCode 4).length
  let tokensSizeTailBound : FixedClosedDirectFormulaBound tokensSizeTailFormula
      tokensSizeTailResource tokensSizeTailCode :=
    FixedClosedDirectFormulaBound.conjunction tokensSizeBound
      tokensAreaTailBound syntaxResource hpositive (by
        dsimp only [syntaxResource, tokensSizeResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensAreaTailCode, tokensAreaResource,
          tasksSizeAreaCode, tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensSizeResource, tokensAreaTailCode,
          tokensAreaResource, tasksSizeAreaCode, tasksSizeResource,
          tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let tasksRowsTailFormula := tasksRowsFormula ⋏ tokensSizeTailFormula
  let tasksRowsTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource tasksRowsResource tokensSizeTailResource
  let tasksRowsTailCode := tasksRowsResource + tokensSizeTailCode +
    (binaryNatCode 4).length
  let tasksRowsTailBound : FixedClosedDirectFormulaBound tasksRowsTailFormula
      tasksRowsTailResource tasksRowsTailCode :=
    FixedClosedDirectFormulaBound.conjunction tasksRowsBound
      tokensSizeTailBound syntaxResource hpositive (by
        dsimp only [syntaxResource, tasksRowsResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensSizeTailCode, tokensSizeResource,
          tokensAreaTailCode, tokensAreaResource, tasksSizeAreaCode,
          tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tasksRowsResource, tokensSizeTailCode,
          tokensSizeResource, tokensAreaTailCode, tokensAreaResource,
          tasksSizeAreaCode, tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let tasksLayoutTailFormula := tasksLayoutFormula ⋏ tasksRowsTailFormula
  let tasksLayoutTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource tasksLayoutResource tasksRowsTailResource
  let tasksLayoutTailCode := tasksLayoutResource + tasksRowsTailCode +
    (binaryNatCode 4).length
  let tasksLayoutTailBound : FixedClosedDirectFormulaBound
      tasksLayoutTailFormula tasksLayoutTailResource tasksLayoutTailCode :=
    FixedClosedDirectFormulaBound.conjunction tasksLayoutBound
      tasksRowsTailBound syntaxResource hpositive (by
        dsimp only [syntaxResource, tasksLayoutResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tasksRowsTailCode, tasksRowsResource,
          tokensSizeTailCode, tokensSizeResource, tokensAreaTailCode,
          tokensAreaResource, tasksSizeAreaCode, tasksSizeResource,
          tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tasksLayoutResource, tasksRowsTailCode,
          tasksRowsResource, tokensSizeTailCode, tokensSizeResource,
          tokensAreaTailCode, tokensAreaResource, tasksSizeAreaCode,
          tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let innerTailFormula := innerFormula ⋏ tasksLayoutTailFormula
  let innerTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource innerResource tasksLayoutTailResource
  let innerTailCode := innerResource + tasksLayoutTailCode +
    (binaryNatCode 4).length
  let innerTailBound : FixedClosedDirectFormulaBound innerTailFormula
      innerTailResource innerTailCode :=
    FixedClosedDirectFormulaBound.conjunction innerBound tasksLayoutTailBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, innerResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tasksLayoutTailCode, tasksLayoutResource,
          tasksRowsTailCode, tasksRowsResource, tokensSizeTailCode,
          tokensSizeResource, tokensAreaTailCode, tokensAreaResource,
          tasksSizeAreaCode, tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, innerResource, tasksLayoutTailCode,
          tasksLayoutResource, tasksRowsTailCode, tasksRowsResource,
          tokensSizeTailCode, tokensSizeResource, tokensAreaTailCode,
          tokensAreaResource, tasksSizeAreaCode, tasksSizeResource,
          tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let tokensRowsTailFormula := tokensRowsFormula ⋏ innerTailFormula
  let tokensRowsTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource tokensRowsResource innerTailResource
  let tokensRowsTailCode := tokensRowsResource + innerTailCode +
    (binaryNatCode 4).length
  let tokensRowsTailBound : FixedClosedDirectFormulaBound tokensRowsTailFormula
      tokensRowsTailResource tokensRowsTailCode :=
    FixedClosedDirectFormulaBound.conjunction tokensRowsBound innerTailBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, tokensRowsResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, innerTailCode, innerResource,
          tasksLayoutTailCode, tasksLayoutResource, tasksRowsTailCode,
          tasksRowsResource, tokensSizeTailCode, tokensSizeResource,
          tokensAreaTailCode, tokensAreaResource, tasksSizeAreaCode,
          tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensRowsResource, innerTailCode,
          innerResource, tasksLayoutTailCode, tasksLayoutResource,
          tasksRowsTailCode, tasksRowsResource, tokensSizeTailCode,
          tokensSizeResource, tokensAreaTailCode, tokensAreaResource,
          tasksSizeAreaCode, tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let tokensLayoutTailFormula := tokensLayoutFormula ⋏ tokensRowsTailFormula
  let tokensLayoutTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource tokensLayoutResource tokensRowsTailResource
  let tokensLayoutTailCode := tokensLayoutResource + tokensRowsTailCode +
    (binaryNatCode 4).length
  let tokensLayoutTailBound : FixedClosedDirectFormulaBound
      tokensLayoutTailFormula tokensLayoutTailResource tokensLayoutTailCode :=
    FixedClosedDirectFormulaBound.conjunction tokensLayoutBound
      tokensRowsTailBound syntaxResource hpositive (by
        dsimp only [syntaxResource, tokensLayoutResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensRowsTailCode, tokensRowsResource,
          innerTailCode, innerResource, tasksLayoutTailCode,
          tasksLayoutResource, tasksRowsTailCode, tasksRowsResource,
          tokensSizeTailCode, tokensSizeResource, tokensAreaTailCode,
          tokensAreaResource, tasksSizeAreaCode, tasksSizeResource,
          tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensLayoutResource, tokensRowsTailCode,
          tokensRowsResource, innerTailCode, innerResource,
          tasksLayoutTailCode, tasksLayoutResource, tasksRowsTailCode,
          tasksRowsResource, tokensSizeTailCode, tokensSizeResource,
          tokensAreaTailCode, tokensAreaResource, tasksSizeAreaCode,
          tasksSizeResource, tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let partsFormula := outerFormula ⋏ tokensLayoutTailFormula
  let partsResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    outerResource tokensLayoutTailResource
  let partsCode := outerResource + tokensLayoutTailCode +
    (binaryNatCode 4).length
  let partsBound : FixedClosedDirectFormulaBound partsFormula partsResource
      partsCode :=
    FixedClosedDirectFormulaBound.conjunction outerBound
      tokensLayoutTailBound syntaxResource hpositive (by
        dsimp only [syntaxResource, outerResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, tokensLayoutTailCode,
          tokensLayoutResource, tokensRowsTailCode, tokensRowsResource,
          innerTailCode, innerResource, tasksLayoutTailCode,
          tasksLayoutResource, tasksRowsTailCode, tasksRowsResource,
          tokensSizeTailCode, tokensSizeResource, tokensAreaTailCode,
          tokensAreaResource, tasksSizeAreaCode, tasksSizeResource,
          tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outerResource, tokensLayoutTailCode,
          tokensLayoutResource, tokensRowsTailCode, tokensRowsResource,
          innerTailCode, innerResource, tasksLayoutTailCode,
          tasksLayoutResource, tasksRowsTailCode, tasksRowsResource,
          tokensSizeTailCode, tokensSizeResource, tokensAreaTailCode,
          tokensAreaResource, tasksSizeAreaCode, tasksSizeResource,
          tasksAreaResource]
        unfold compactUnifiedParserStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let closedFormula := compactUnifiedParserStateCoreClosedFormula tokenTable
    width tokenCount coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize
  let explicitFormula := compactUnifiedParserStateCoreExplicitFormula tokenTable
    width tokenCount coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize
  have hpartsFormula : partsFormula = explicitFormula := by
    rfl
  let explicitProof := CertifiedPAContextProof.cast hpartsFormula
    partsBound.proof
  have hformula : explicitFormula = closedFormula :=
    (compactUnifiedParserStateCoreClosedFormula_alignment tokenTable width
      tokenCount coordinates.start coordinates.finish
      coordinates.tokensFinish coordinates.tasksFinish
      coordinates.tokensBoundary coordinates.tokensCount
      coordinates.tasksBoundary coordinates.tasksCount
      sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize).symm
  let formulaProof := CertifiedPAContextProof.cast hformula explicitProof
  have hcontext : valuationContext partsFormula.freeVariables
      parserFixedZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [partsBound.closed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext formulaProof
  refine { proof := proof, payloadLength_le := ?_ }
  change proof.payloadLength <= _
  have hexplicitProofLength : explicitProof.payloadLength =
      partsBound.proof.payloadLength := by
    dsimp only [explicitProof]
    exact CertifiedPAContextProof.cast_payloadLength hpartsFormula
      partsBound.proof
  have hformulaProofLength : formulaProof.payloadLength =
      partsBound.proof.payloadLength := by
    dsimp only [formulaProof]
    rw [CertifiedPAContextProof.cast_payloadLength]
    exact hexplicitProofLength
  have hproofLength : proof.payloadLength = partsBound.proof.payloadLength := by
    dsimp only [proof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hformulaProofLength
  rw [hproofLength]
  apply partsBound.payloadLength_le.trans
  dsimp only [partsResource, tokensLayoutTailResource,
    tokensRowsTailResource, innerTailResource, tasksLayoutTailResource,
    tasksRowsTailResource, tokensSizeTailResource, tokensAreaTailResource,
    tasksSizeAreaResource, outerResource, tokensLayoutResource,
    tokensRowsResource, innerResource, tasksLayoutResource,
    tasksRowsResource, tokensSizeResource, tokensAreaResource,
    tasksSizeResource, tasksAreaResource, syntaxResource]
  unfold hybridConjunctionGeneralPayloadEnvelope
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
  dsimp only
  omega

noncomputable def compileCompactUnifiedParserStateCoreFullyUniformDirectFixed
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokensCount : coordinates.tokensCount <= numericBound)
    (htasksCount : coordinates.tasksCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (htokensTableSize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htasksTableSize : Nat.size coordinates.tasksBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :=
  (compactUnifiedParserStateCoreFullyUniformDirectFixedBound tokenTable width
    tokenCount coordinates sizeWitness hgraph numericBound bitBound
    hwidthBound htokenCount htokensCount htasksCount htokenTableSize
    htokensTableSize htasksTableSize hnumericSize).proof

theorem
    compileCompactUnifiedParserStateCoreFullyUniformDirectFixed_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokensCount : coordinates.tokensCount <= numericBound)
    (htasksCount : coordinates.tasksCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (htokensTableSize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htasksTableSize : Nat.size coordinates.tasksBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactUnifiedParserStateCoreFullyUniformDirectFixed tokenTable
      width tokenCount coordinates sizeWitness hgraph numericBound bitBound
      hwidthBound htokenCount htokensCount htasksCount htokenTableSize
      htokensTableSize htasksTableSize hnumericSize).payloadLength <=
      compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
        numericBound bitBound :=
  (compactUnifiedParserStateCoreFullyUniformDirectFixedBound tokenTable width
    tokenCount coordinates sizeWitness hgraph numericBound bitBound
    hwidthBound htokenCount htokensCount htasksCount htokenTableSize
    htokensTableSize htasksTableSize hnumericSize).payloadLength_le

#print axioms compactUnifiedParserStateCoreFullyUniformDirectFixedBound
#print axioms
  compileCompactUnifiedParserStateCoreFullyUniformDirectFixed_payloadLength_le

end FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
