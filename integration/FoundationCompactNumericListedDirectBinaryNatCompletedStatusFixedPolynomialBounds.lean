import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
import integration.FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellFixedBounds

/-!
# Fixed polynomial bounds for the completed binary-Nat status branch

This layer removes the value-dependent resources from the five leaves of the
completed branch.  It starts with the native `Nat.size` leaf and will assemble
the remaining layout, unit-boundary and area leaves at the same fixed public
coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds

private theorem completedBinaryFunctionTerm_freeVariables
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

private theorem completedBinaryFunctionTerm_code_length_le
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

private theorem completedBinaryRelationFormula_freeVariables
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

private theorem completedArithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact completedBinaryFunctionTerm_freeVariables Language.Add.add left right

private theorem completedArithmeticMulTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact completedBinaryFunctionTerm_freeVariables Language.Mul.mul left right

private theorem completedArithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def compactNatSizeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compileBinaryLengthAtValuationFixedPayloadPolynomial bitBound
    (binaryNumeralTermCodeEnvelope bitBound)

theorem compactNatSizeStructuralPayloadPolynomial_le_fixed
    (size value bitBound : Nat)
    (hsize : size = Nat.size value)
    (hvalueWidth : Nat.size value <= bitBound) :
    compactNatSizeStructuralPayloadPolynomial size value <=
      compactNatSizeFixedPayloadPolynomial bitBound := by
  let valuation : Nat -> Nat := fun _ => 0
  let sizeTerm := shortBinaryNumeralTerm size
  let valueTerm := shortBinaryNumeralTerm value
  let termCodeBound := binaryNumeralTermCodeEnvelope bitBound
  have hsizeWidth : Nat.size size <= bitBound := by
    rw [hsize]
    exact
      (natSize_le_of_le (Nat.le_refl (Nat.size value))).trans hvalueWidth
  have hsizeClosed : sizeTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty size
  have hvalueClosed : valueTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty value
  have hsizeCode : (binaryTermCode sizeTerm).length <= termCodeBound := by
    exact binaryNumeralTerm_code_length_le_envelope size bitBound hsizeWidth
  have hvalueCode : (binaryTermCode valueTerm).length <= termCodeBound := by
    exact binaryNumeralTerm_code_length_le_envelope value bitBound hvalueWidth
  apply compileBinaryLengthAtValuationPayloadPolynomial_le_fixed_of_eq
    valuation sizeTerm valueTerm
    (compactNatSizeStructuralPayloadPolynomial size value)
    (compactNatSizeFixedPayloadPolynomial bitBound) bitBound termCodeBound
  · rfl
  · rfl
  · exact hsizeClosed
  · exact hvalueClosed
  · simpa only [sizeTerm, valuation, termValue_shortBinaryNumeralTerm] using
      hsizeWidth
  · simpa only [valueTerm, valuation, termValue_shortBinaryNumeralTerm] using
      hvalueWidth
  · exact hsizeCode
  · exact hvalueCode

def completedAreaTermCodePolynomial (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  3 * numeralCode + (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add +
    binaryFunctionTermCodeOverhead Language.Mul.mul + 1

def completedAreaFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let atomicCode := orderAtomicFormulaCodeEnvelope
    (completedAreaTermCodePolynomial bitBound)
  2 * atomicCode + 8

def completedAreaFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  let termCode := completedAreaTermCodePolynomial bitBound
  let formulaCode := completedAreaFormulaCodePolynomial bitBound
  2 * compilePositiveRelationFixedPayloadPolynomial 0 termCode +
    3 * smallContextAssemblyEnvelope formulaCode + 1

private theorem completedAreaRightTerm_freeVariables_eq_empty
    (tokenCount outputCount : Nat) :
    (‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’ : ValuationTerm).freeVariables =
        ∅ := by
  rw [completedArithmeticMulTerm_freeVariables,
    completedArithmeticAddTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    completedArithmeticOneTerm_freeVariables_eq_empty,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp

private theorem completedAreaRightTerm_code_length_le_fixed
    (tokenCount outputCount bitBound : Nat)
    (htokenWidth : Nat.size tokenCount <= bitBound)
    (houtputWidth : Nat.size outputCount <= bitBound) :
    (binaryTermCode
      (‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)’ : ValuationTerm)).length <=
      completedAreaTermCodePolynomial bitBound := by
  let outputTerm := shortBinaryNumeralTerm outputCount
  let oneTerm : ValuationTerm := ‘1’
  let sumTerm : ValuationTerm := ‘!!outputTerm + !!oneTerm’
  let tokenTerm := shortBinaryNumeralTerm tokenCount
  let rightTerm : ValuationTerm := ‘!!sumTerm * !!tokenTerm’
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  have houtput : (binaryTermCode outputTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope outputCount bitBound houtputWidth
  have htoken : (binaryTermCode tokenTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope tokenCount bitBound htokenWidth
  have hsum : (binaryTermCode sumTerm).length <=
      (binaryTermCode outputTerm).length +
        (binaryTermCode oneTerm).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    change
      (binaryTermCode
        (LO.FirstOrder.Semiterm.func Language.Add.add
          ![outputTerm, oneTerm])).length <= _
    exact completedBinaryFunctionTerm_code_length_le Language.Add.add
      outputTerm oneTerm
  have hright : (binaryTermCode rightTerm).length <=
      (binaryTermCode sumTerm).length +
        (binaryTermCode tokenTerm).length +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    change
      (binaryTermCode
        (LO.FirstOrder.Semiterm.func Language.Mul.mul
          ![sumTerm, tokenTerm])).length <= _
    exact completedBinaryFunctionTerm_code_length_le Language.Mul.mul
      sumTerm tokenTerm
  change (binaryTermCode rightTerm).length <= _
  unfold completedAreaTermCodePolynomial
  dsimp only [oneTerm] at hsum
  dsimp only [numeralCode, oneTerm]
  omega

private theorem completedAreaRelationFormula_code_length_le_fixed
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

theorem completedAreaStructuralPayloadPolynomial_le_fixed
    (tokenCount outputCount outputBoundary outputBoundarySize
      numericBound bitBound : Nat)
    (hsize : outputBoundarySize = Nat.size outputBoundary)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (htableSize : Nat.size outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    completedAreaStructuralPayloadPolynomial tokenCount outputCount
        outputBoundarySize <=
      completedAreaFixedPayloadPolynomial bitBound := by
  let valuation : Nat -> Nat :=
    FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate.zeroValuation
  let leftTerm := shortBinaryNumeralTerm outputBoundarySize
  let outputTerm := shortBinaryNumeralTerm outputCount
  let oneTerm : ValuationTerm := ‘1’
  let sumTerm : ValuationTerm := ‘!!outputTerm + !!oneTerm’
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
  have houtputWidth : Nat.size outputCount <= bitBound :=
    (Nat.size_le_size houtputCount).trans hnumericSize
  have hboundarySizeWidth : Nat.size outputBoundarySize <= bitBound := by
    rw [hsize]
    exact
      (natSize_le_of_le (Nat.le_refl (Nat.size outputBoundary))).trans
        htableSize
  have hleftClosed : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty outputBoundarySize
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    simpa only [rightTerm, sumTerm, outputTerm, oneTerm, tokenTerm] using
      completedAreaRightTerm_freeVariables_eq_empty tokenCount outputCount
  have hleftCode : (binaryTermCode leftTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope
      outputBoundarySize bitBound hboundarySizeWidth
    have hlarge : binaryNumeralTermCodeEnvelope bitBound <=
        completedAreaTermCodePolynomial bitBound := by
      unfold completedAreaTermCodePolynomial
      dsimp only
      omega
    simpa only [leftTerm, termCode] using hraw.trans hlarge
  have hrightCode : (binaryTermCode rightTerm).length <= termCode := by
    simpa only [rightTerm, sumTerm, outputTerm, oneTerm, tokenTerm, termCode]
      using completedAreaRightTerm_code_length_le_fixed tokenCount outputCount
        bitBound htokenWidth houtputWidth
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
      args 0 termCode hfirst hsecond (by
        change 0 <= 0
        exact le_rfl) hleftCode hrightCode
  have hstrictResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed valuation
      Language.ORing.Rel.lt args 0 termCode hfirst hsecond
      (by
        change 0 <= 0
        exact le_rfl) hleftCode hrightCode
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      atomicCode := by
    simpa only [equalityFormula, args, binaryRelationFormula] using
      completedAreaRelationFormula_code_length_le_fixed Language.Eq.eq
        leftTerm rightTerm bitBound hleftCode hrightCode
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      atomicCode := by
    simpa only [strictFormula, args, binaryRelationFormula] using
      completedAreaRelationFormula_code_length_le_fixed Language.LT.lt
        leftTerm rightTerm bitBound hleftCode hrightCode
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
      rw [completedBinaryRelationFormula_freeVariables]
      simp [hleftClosed, hrightClosed]
    have hstrictClosed : strictFormula.freeVariables = ∅ := by
      dsimp only [strictFormula, args]
      rw [completedBinaryRelationFormula_freeVariables]
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
  unfold completedAreaStructuralPayloadPolynomial
    valuationLeStructuralPayloadPolynomial
    completedAreaFixedPayloadPolynomial
  dsimp only [valuation, leftTerm, outputTerm, oneTerm, sumTerm, tokenTerm,
    rightTerm, args, equalityFormula, strictFormula, targetFormula, Gamma,
    termCode, formulaCode] at *
  omega

/-! ## Unit-boundary universal leaf -/

def unitBoundaryBranchSubstitutionTermCodePolynomial
    (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  5 * numeralCode +
    (binaryTermCode
      (closedShift 2 (&0 : ValuationTerm))).length +
    (binaryTermCode
      (closedShift 2 (‘&0 + 1’ : ValuationTerm))).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 2)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 2)).length + 4

def unitBoundaryEmbeddedEntryFormulaCodeFromTermPolynomial
    (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def unitBoundaryEmbeddedEntryFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  unitBoundaryEmbeddedEntryFormulaCodeFromTermPolynomial
    (unitBoundaryBranchSubstitutionTermCodePolynomial bitBound)

def unitBoundaryBranchTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let entryCode := unitBoundaryEmbeddedEntryFormulaCodePolynomial bitBound
  let successorCode :=
    (binaryFormulaCode
      (“#0 = #1 + 1” : ArithmeticSemiformula Nat 2)).length
  2 * entryCode + successorCode + 2 * (binaryNatCode 4).length + 1

private theorem closedShift_two_code_length_le_five
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    (binaryTermCode (closedShift 2 term)).length <= 5 * bound := by
  have hsymbols : termSymbolCount term <= bound :=
    (termSymbolCount_le_binaryTermCode_length term).trans hterm
  have hfirstRaw := binaryTermCode_bShift_length_le_add_symbols term
  have hfirst : (binaryTermCode (Rew.bShift term)).length <= 3 * bound := by
    omega
  have hshiftedSymbols : termSymbolCount (Rew.bShift term) <= bound := by
    rw [termSymbolCount_bShift]
    exact hsymbols
  have hsecondRaw :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift term)
  change
    (binaryTermCode (Rew.bShift (Rew.bShift term))).length <= 5 * bound
  omega

private theorem closedShift_three_code_length_le_seven
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    (binaryTermCode (closedShift 3 term)).length <= 7 * bound := by
  have hsymbols : termSymbolCount term <= bound :=
    (termSymbolCount_le_binaryTermCode_length term).trans hterm
  have hfirstRaw := binaryTermCode_bShift_length_le_add_symbols term
  have hfirst : (binaryTermCode (Rew.bShift term)).length <= 3 * bound := by
    omega
  have hfirstSymbols : termSymbolCount (Rew.bShift term) <= bound := by
    rw [termSymbolCount_bShift]
    exact hsymbols
  have hsecondRaw :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift term)
  have hsecond :
      (binaryTermCode (Rew.bShift (Rew.bShift term))).length <=
        5 * bound := by
    omega
  have hsecondSymbols :
      termSymbolCount (Rew.bShift (Rew.bShift term)) <= bound := by
    rw [termSymbolCount_bShift, termSymbolCount_bShift]
    exact hsymbols
  have hthirdRaw := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift (Rew.bShift term))
  change
    (binaryTermCode
      (Rew.bShift (Rew.bShift (Rew.bShift term)))).length <= 7 * bound
  omega

private theorem unitBoundarySubstitutionTermCodePolynomial_four_le
    (bitBound : Nat) :
    4 <= unitBoundaryBranchSubstitutionTermCodePolynomial bitBound := by
  unfold unitBoundaryBranchSubstitutionTermCodePolynomial
  dsimp only
  omega

private theorem compactFixedWidthEntryEmbeddedSubstitution_code_length_le_fixed
    {targetArity : Nat} (termCode : Nat)
    (terms : Fin 4 -> ArithmeticSemiterm Nat targetArity)
    (hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        terms)).length <=
      unitBoundaryEmbeddedEntryFormulaCodeFromTermPolynomial termCode := by
  let source : ArithmeticSemiformula Nat 4 :=
    Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val
  let rewriting : Rew ℒₒᵣ Nat 4 Nat targetArity := Rew.subst terms
  have hrewriting : RewritingImageCodeBound rewriting termCode := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      exact hterms coordinate
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting termCode
    hrewriting source
  simpa only [unitBoundaryEmbeddedEntryFormulaCodeFromTermPolynomial, source,
    rewriting] using hraw

theorem compactAdditiveUnitBoundaryRowsBranchTerminal_code_length_le_fixed
    (tokenCount boundaryTable bitBound : Nat)
    (htokenSize : Nat.size tokenCount <= bitBound)
    (htableSize : Nat.size boundaryTable <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveUnitBoundaryRowsBranchTerminal
        tokenCount boundaryTable)).length <=
      unitBoundaryBranchTerminalFormulaCodePolynomial bitBound := by
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm := closedShift 2 (&0 : ValuationTerm)
  let rightIndexTerm := closedShift 2 (‘&0 + 1’ : ValuationTerm)
  let leftValueTerm := (#1 : ArithmeticSemiterm Nat 2)
  let rightValueTerm := (#0 : ArithmeticSemiterm Nat 2)
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 2 :=
    ![closedShift 2 tableTerm, closedShift 2 widthTerm,
      leftIndexTerm, leftValueTerm]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 2 :=
    ![closedShift 2 tableTerm, closedShift 2 widthTerm,
      rightIndexTerm, rightValueTerm]
  let leftFormula : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let successorFormula : ArithmeticSemiformula Nat 2 := “#0 = #1 + 1”
  let termCode := unitBoundaryBranchSubstitutionTermCodePolynomial bitBound
  let entryCode := unitBoundaryEmbeddedEntryFormulaCodePolynomial bitBound
  have htableCode : (binaryTermCode tableTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope boundaryTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope tokenCount bitBound htokenSize
  have htableShiftRaw := closedShift_two_code_length_le_five tableTerm
    (binaryNumeralTermCodeEnvelope bitBound) htableCode
  have hwidthShiftRaw := closedShift_two_code_length_le_five widthTerm
    (binaryNumeralTermCodeEnvelope bitBound) hwidthCode
  have htableShift : (binaryTermCode (closedShift 2 tableTerm)).length <=
      termCode := by
    exact htableShiftRaw.trans (by
      unfold termCode unitBoundaryBranchSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hwidthShift : (binaryTermCode (closedShift 2 widthTerm)).length <=
      termCode := by
    exact hwidthShiftRaw.trans (by
      unfold termCode unitBoundaryBranchSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hleftIndex : (binaryTermCode leftIndexTerm).length <= termCode := by
    unfold termCode unitBoundaryBranchSubstitutionTermCodePolynomial
    dsimp only [leftIndexTerm]
    omega
  have hrightIndex : (binaryTermCode rightIndexTerm).length <= termCode := by
    unfold termCode unitBoundaryBranchSubstitutionTermCodePolynomial
    dsimp only [rightIndexTerm]
    omega
  have hleftValue : (binaryTermCode leftValueTerm).length <= termCode := by
    unfold termCode unitBoundaryBranchSubstitutionTermCodePolynomial
    dsimp only [leftValueTerm]
    omega
  have hrightValue : (binaryTermCode rightValueTerm).length <= termCode := by
    unfold termCode unitBoundaryBranchSubstitutionTermCodePolynomial
    dsimp only [rightValueTerm]
    omega
  have hleftTerms : forall coordinate,
      (binaryTermCode (leftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · change (binaryTermCode (closedShift 2 tableTerm)).length <= termCode
      exact htableShift
    · change (binaryTermCode (closedShift 2 widthTerm)).length <= termCode
      exact hwidthShift
    · change (binaryTermCode leftIndexTerm).length <= termCode
      exact hleftIndex
    · change (binaryTermCode leftValueTerm).length <= termCode
      exact hleftValue
  have hrightTerms : forall coordinate,
      (binaryTermCode (rightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · change (binaryTermCode (closedShift 2 tableTerm)).length <= termCode
      exact htableShift
    · change (binaryTermCode (closedShift 2 widthTerm)).length <= termCode
      exact hwidthShift
    · change (binaryTermCode rightIndexTerm).length <= termCode
      exact hrightIndex
    · change (binaryTermCode rightValueTerm).length <= termCode
      exact hrightValue
  have hleft : (binaryFormulaCode leftFormula).length <= entryCode := by
    simpa only [leftFormula, entryCode, termCode,
      unitBoundaryEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le_fixed
        termCode leftTerms hleftTerms
  have hright : (binaryFormulaCode rightFormula).length <= entryCode := by
    simpa only [rightFormula, entryCode, termCode,
      unitBoundaryEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le_fixed
        termCode rightTerms hrightTerms
  have hinner := andSemiformula_code_length_le rightFormula successorFormula
  have houter := andSemiformula_code_length_le leftFormula
    (rightFormula ⋏ successorFormula)
  change
    (binaryFormulaCode (leftFormula ⋏
      (rightFormula ⋏ successorFormula))).length <= _
  unfold unitBoundaryBranchTerminalFormulaCodePolynomial
  dsimp only [entryCode, successorFormula] at hinner houter ⊢
  omega

private theorem boundedWitnessNumeralTermCodeEnvelope_mono_completed
    {small large : Nat} (hbound : small <= large) :
    boundedWitnessNumeralTermCodeEnvelope small <=
      boundedWitnessNumeralTermCodeEnvelope large := by
  unfold boundedWitnessNumeralTermCodeEnvelope
  exact
    FoundationCompactPAExponentialShortNumeralCompilerBounds.binaryNumeralTermCodeEnvelope_mono_short
      (Nat.size_le_size hbound)

private theorem uniformRewritingFormulaCodeEnvelope_mono_completed
    {smallImage largeImage smallFormula largeFormula : Nat}
    (himage : smallImage <= largeImage)
    (hformula : smallFormula <= largeFormula) :
    uniformRewritingFormulaCodeEnvelope smallImage smallFormula <=
      uniformRewritingFormulaCodeEnvelope largeImage largeFormula := by
  unfold uniformRewritingFormulaCodeEnvelope
  gcongr

private theorem explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_completed
    (contextCodeBound : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        smallBound smallBody <=
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        largeBound largeBody := by
  have hnumeral := boundedWitnessNumeralTermCodeEnvelope_mono_completed hbound
  have hlifted : liftedRewritingImageCodeBound
      (boundedWitnessNumeralTermCodeEnvelope smallBound) <=
      liftedRewritingImageCodeBound
        (boundedWitnessNumeralTermCodeEnvelope largeBound) := by
    unfold liftedRewritingImageCodeBound
    omega
  have htail : explicitWitnessBodyAfterTailPublicCodeEnvelope smallBound
        smallBody <=
      explicitWitnessBodyAfterTailPublicCodeEnvelope largeBound
        largeBody := by
    unfold explicitWitnessBodyAfterTailPublicCodeEnvelope
    exact uniformRewritingFormulaCodeEnvelope_mono_completed hlifted hbody
  have hinstalled : explicitWitnessInstalledPublicCodeEnvelope smallBound
        smallBody <=
      explicitWitnessInstalledPublicCodeEnvelope largeBound largeBody := by
    unfold explicitWitnessInstalledPublicCodeEnvelope
    exact uniformRewritingFormulaCodeEnvelope_mono_completed hnumeral hbody
  have hsuccessor : boundedWitnessSuccessorTermCodeEnvelope smallBound <=
      boundedWitnessSuccessorTermCodeEnvelope largeBound := by
    unfold boundedWitnessSuccessorTermCodeEnvelope
    omega
  have hshifted : boundedWitnessShiftedSuccessorTermCodeEnvelope smallBound <=
      boundedWitnessShiftedSuccessorTermCodeEnvelope largeBound := by
    unfold boundedWitnessShiftedSuccessorTermCodeEnvelope
    exact Nat.mul_le_mul_left 3 hsuccessor
  have hguardCode : boundedWitnessGuardFormulaCodeEnvelope smallBound <=
      boundedWitnessGuardFormulaCodeEnvelope largeBound := by
    unfold boundedWitnessGuardFormulaCodeEnvelope
    omega
  have hopenGuard : boundedWitnessOpenGuardFormulaCodeEnvelope smallBound <=
      boundedWitnessOpenGuardFormulaCodeEnvelope largeBound := by
    unfold boundedWitnessOpenGuardFormulaCodeEnvelope
    omega
  have hmatrix : explicitBoundedWitnessMatrixPublicCodeEnvelope smallBound
        smallBody <=
      explicitBoundedWitnessMatrixPublicCodeEnvelope largeBound largeBody := by
    unfold explicitBoundedWitnessMatrixPublicCodeEnvelope
    omega
  have hbounded :
      explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope
    omega
  have hinstantiated :
      explicitBoundedWitnessInstantiatedPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessInstantiatedPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessInstantiatedPublicCodeEnvelope
    exact substitutionFormulaCodeEnvelope_mono_local hbounded hnumeral
  have hexistential :
      explicitBoundedWitnessExistentialPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessExistentialPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessExistentialPublicCodeEnvelope
    omega
  have hsyntax :
      explicitBoundedWitnessDirectHeadPublicSyntaxResource contextCodeBound
          smallBound smallBody <=
        explicitBoundedWitnessDirectHeadPublicSyntaxResource contextCodeBound
          largeBound largeBody := by
    unfold explicitBoundedWitnessDirectHeadPublicSyntaxResource
    omega
  have hsize : Nat.size smallBound <= Nat.size largeBound :=
    Nat.size_le_size hbound
  have hguardWidth : boundedWitnessGuardUniformBitWidth smallBound <=
      boundedWitnessGuardUniformBitWidth largeBound := by
    unfold boundedWitnessGuardUniformBitWidth boundedWitnessGuardBitWidth
    omega
  have hguardPayload :=
    boundedWitnessGuardPayloadPolynomial_mono_uniform hguardWidth
  have hassembly := generalContextAssemblyEnvelope_mono_uniform hsyntax
  unfold explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
  omega

private theorem closedShiftShortBinaryNumeralPublicCodeEnvelope_mono_completed
    (arity : Nat) {smallBound largeBound : Nat}
    (hbound : smallBound <= largeBound) :
    closedShiftShortBinaryNumeralPublicCodeEnvelope arity smallBound <=
      closedShiftShortBinaryNumeralPublicCodeEnvelope arity largeBound := by
  induction arity with
  | zero =>
      simpa only [closedShiftShortBinaryNumeralPublicCodeEnvelope] using
        boundedWitnessNumeralTermCodeEnvelope_mono_completed hbound
  | succ arity ih =>
      simp only [closedShiftShortBinaryNumeralPublicCodeEnvelope]
      have hnumeral := boundedWitnessNumeralTermCodeEnvelope_mono_completed
        hbound
      omega

theorem explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed
    (arity : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity smallBound
        smallBody <=
      explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity largeBound
        largeBody := by
  have hclosed :=
    closedShiftShortBinaryNumeralPublicCodeEnvelope_mono_completed arity hbound
  have hsuccessor :
      explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope arity
          smallBound <=
        explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope arity
          largeBound := by
    unfold explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope
    omega
  have hshifted :
      explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope arity
          smallBound <=
        explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope arity
          largeBound := by
    unfold explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope
    exact Nat.mul_le_mul_left 3 hsuccessor
  have hguard : explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity
        smallBound <=
      explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity
        largeBound := by
    unfold explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope
    omega
  unfold explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
  omega

theorem explicitBoundedWitnessDirectPublicPayloadEnvelope_two_mono
    (contextCodeBound terminalResource : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
        smallBound smallBody terminalResource <=
      explicitBoundedWitnessDirectPublicPayloadEnvelope 2 contextCodeBound
        largeBound largeBody terminalResource := by
  have hfirst :=
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_completed
      contextCodeBound hbound hbody
  have hrecursive :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 1
      hbound hbody
  have hsecond :=
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_completed
      contextCodeBound hbound hrecursive
  change
    terminalResource +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
            contextCodeBound smallBound smallBody +
        explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
          contextCodeBound smallBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1
            smallBound smallBody) <=
      terminalResource +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
            contextCodeBound largeBound largeBody +
        explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
          contextCodeBound largeBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1
            largeBound largeBody)
  omega

def unitBoundaryUniformBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2
    (unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound)
    numericBound
    (unitBoundaryBranchTerminalFormulaCodePolynomial bitBound)
    (unitBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound)

theorem compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope_le_fixed
    (tokenCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound <=
      unitBoundaryUniformBranchFixedPayloadPolynomial numericBound bitBound := by
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :=
    compactAdditiveUnitBoundaryRowsBranchTerminal_code_length_le_fixed
      tokenCount boundaryTable bitBound htokenSize htableSize
  unfold compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope
    unitBoundaryUniformBranchFixedPayloadPolynomial
  dsimp only
  exact explicitBoundedWitnessDirectPublicPayloadEnvelope_two_mono
    (unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound)
    (unitBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound)
    htokenCount hbody

def unitBoundaryUniversalSubstitutionTermCodePolynomial
    (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  7 * numeralCode +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 3)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 3)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 3)).length +
    (binaryTermCode (‘#2 + 1’ : ArithmeticSemiterm Nat 3)).length + 4

def unitBoundaryUniversalEmbeddedEntryFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  unitBoundaryEmbeddedEntryFormulaCodeFromTermPolynomial
    (unitBoundaryUniversalSubstitutionTermCodePolynomial bitBound)

def unitBoundaryUniversalTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let entryCode :=
    unitBoundaryUniversalEmbeddedEntryFormulaCodePolynomial bitBound
  let successorCode :=
    (binaryFormulaCode
      (“#0 = #1 + 1” : ArithmeticSemiformula Nat 3)).length
  2 * entryCode + successorCode + 2 * (binaryNatCode 4).length + 1

def unitBoundaryUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  let terminalCode :=
    unitBoundaryUniversalTerminalFormulaCodePolynomial bitBound
  let innerCode := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2
    numericBound terminalCode
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    innerCode

theorem compactAdditiveUnitBoundaryRowsTerminal_code_length_le_fixed
    (tokenCount boundaryTable bitBound : Nat)
    (htokenSize : Nat.size tokenCount <= bitBound)
    (htableSize : Nat.size boundaryTable <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveUnitBoundaryRowsTerminal
        tokenCount boundaryTable)).length <=
      unitBoundaryUniversalTerminalFormulaCodePolynomial bitBound := by
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm := (#2 : ArithmeticSemiterm Nat 3)
  let rightIndexTerm := (‘#2 + 1’ : ArithmeticSemiterm Nat 3)
  let leftValueTerm := (#1 : ArithmeticSemiterm Nat 3)
  let rightValueTerm := (#0 : ArithmeticSemiterm Nat 3)
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![closedShift 3 tableTerm, closedShift 3 widthTerm,
      leftIndexTerm, leftValueTerm]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![closedShift 3 tableTerm, closedShift 3 widthTerm,
      rightIndexTerm, rightValueTerm]
  let leftFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let successorFormula : ArithmeticSemiformula Nat 3 := “#0 = #1 + 1”
  let termCode := unitBoundaryUniversalSubstitutionTermCodePolynomial bitBound
  let entryCode :=
    unitBoundaryUniversalEmbeddedEntryFormulaCodePolynomial bitBound
  have htableCode : (binaryTermCode tableTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope boundaryTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope tokenCount bitBound htokenSize
  have htableShiftRaw := closedShift_three_code_length_le_seven tableTerm
    (binaryNumeralTermCodeEnvelope bitBound) htableCode
  have hwidthShiftRaw := closedShift_three_code_length_le_seven widthTerm
    (binaryNumeralTermCodeEnvelope bitBound) hwidthCode
  have htableShift : (binaryTermCode (closedShift 3 tableTerm)).length <=
      termCode := by
    exact htableShiftRaw.trans (by
      unfold termCode unitBoundaryUniversalSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hwidthShift : (binaryTermCode (closedShift 3 widthTerm)).length <=
      termCode := by
    exact hwidthShiftRaw.trans (by
      unfold termCode unitBoundaryUniversalSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hleftIndex : (binaryTermCode leftIndexTerm).length <= termCode := by
    unfold termCode unitBoundaryUniversalSubstitutionTermCodePolynomial
    dsimp only [leftIndexTerm]
    omega
  have hrightIndex : (binaryTermCode rightIndexTerm).length <= termCode := by
    unfold termCode unitBoundaryUniversalSubstitutionTermCodePolynomial
    dsimp only [rightIndexTerm]
    omega
  have hleftValue : (binaryTermCode leftValueTerm).length <= termCode := by
    unfold termCode unitBoundaryUniversalSubstitutionTermCodePolynomial
    dsimp only [leftValueTerm]
    omega
  have hrightValue : (binaryTermCode rightValueTerm).length <= termCode := by
    unfold termCode unitBoundaryUniversalSubstitutionTermCodePolynomial
    dsimp only [rightValueTerm]
    omega
  have hleftTerms : forall coordinate,
      (binaryTermCode (leftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · change (binaryTermCode (closedShift 3 tableTerm)).length <= termCode
      exact htableShift
    · change (binaryTermCode (closedShift 3 widthTerm)).length <= termCode
      exact hwidthShift
    · change (binaryTermCode leftIndexTerm).length <= termCode
      exact hleftIndex
    · change (binaryTermCode leftValueTerm).length <= termCode
      exact hleftValue
  have hrightTerms : forall coordinate,
      (binaryTermCode (rightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · change (binaryTermCode (closedShift 3 tableTerm)).length <= termCode
      exact htableShift
    · change (binaryTermCode (closedShift 3 widthTerm)).length <= termCode
      exact hwidthShift
    · change (binaryTermCode rightIndexTerm).length <= termCode
      exact hrightIndex
    · change (binaryTermCode rightValueTerm).length <= termCode
      exact hrightValue
  have hleft : (binaryFormulaCode leftFormula).length <= entryCode := by
    simpa only [leftFormula, entryCode,
      unitBoundaryUniversalEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le_fixed
        termCode leftTerms hleftTerms
  have hright : (binaryFormulaCode rightFormula).length <= entryCode := by
    simpa only [rightFormula, entryCode,
      unitBoundaryUniversalEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le_fixed
        termCode rightTerms hrightTerms
  have hinner := andSemiformula_code_length_le rightFormula successorFormula
  have houter := andSemiformula_code_length_le leftFormula
    (rightFormula ⋏ successorFormula)
  change
    (binaryFormulaCode (leftFormula ⋏
      (rightFormula ⋏ successorFormula))).length <= _
  unfold unitBoundaryUniversalTerminalFormulaCodePolynomial
  dsimp only [entryCode, successorFormula] at hinner houter ⊢
  omega

theorem compactAdditiveUnitBoundaryRowsBody_code_length_le_fixed
    (tokenCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveUnitBoundaryRowsBody
        tokenCount boundaryTable)).length <=
      unitBoundaryUniversalBodyFormulaCodePolynomial numericBound
        bitBound := by
  let terminal := compactAdditiveUnitBoundaryRowsTerminal
    tokenCount boundaryTable
  let inner := terminal.bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm tokenCount))
  let terminalCode :=
    unitBoundaryUniversalTerminalFormulaCodePolynomial bitBound
  let innerCode := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2
    numericBound terminalCode
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hterminal : (binaryFormulaCode terminal).length <= terminalCode := by
    simpa only [terminal, terminalCode] using
      compactAdditiveUnitBoundaryRowsTerminal_code_length_le_fixed
        tokenCount boundaryTable bitBound htokenSize htableSize
  have hinnerRaw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    (arity := 2) tokenCount terminalCode terminal hterminal
  have hinnerMono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 2
      htokenCount (Nat.le_refl terminalCode)
  have hinner : (binaryFormulaCode inner).length <= innerCode := by
    exact hinnerRaw.trans (by
      simpa only [innerCode] using hinnerMono)
  have houterRaw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    (arity := 1) tokenCount innerCode inner hinner
  have houterMono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 1
      htokenCount (Nat.le_refl innerCode)
  unfold compactAdditiveUnitBoundaryRowsBody
    unitBoundaryUniversalBodyFormulaCodePolynomial
  dsimp only [terminal, inner, terminalCode, innerCode] at houterRaw houterMono ⊢
  exact houterRaw.trans houterMono

def unitBoundaryDirectUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    unitBoundaryUniversalBodyFormulaCodePolynomial numericBound bitBound + 1

def unitBoundaryDirectUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    unitBoundaryDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  boundedUniversalClosedFormulaEnvelope syntaxCode +
    2 * unitBoundaryUniversalBodyFormulaCodePolynomial numericBound bitBound + 1

def unitBoundaryDirectUniversalLocalFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (unitBoundaryDirectUniversalFormulaFixedPolynomial numericBound bitBound)

def unitBoundaryUniformDirectBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (unitBoundaryUniformBranchFixedPayloadPolynomial numericBound bitBound +
      3 * unitBoundaryDirectUniversalLocalFixedPolynomial numericBound
        bitBound)

private theorem finiteCaseFormulaEnvelope_mono_completed
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (hbound : small <= large) :
    finiteCaseFormulaEnvelope subject small <=
      finiteCaseFormulaEnvelope subject large := by
  have hshift : small + 2 <= large + 2 := by omega
  have hequality := finiteEqualityCasesCodePolynomial_mono subject hshift
  have hlower := finiteLowerBoundFormulaCodePolynomial_mono subject hshift
  have hexhaustion := finiteExhaustionFormulaCodePolynomial_mono subject hshift
  have hsteps : (small + 3) * finiteEqualityCaseStepEnvelope subject <=
      (large + 3) * finiteEqualityCaseStepEnvelope subject :=
    Nat.mul_le_mul_right _ (by omega)
  unfold finiteCaseFormulaEnvelope
  omega

theorem boundedUniversalClosedFormulaEnvelope_mono_completed
    {small large : Nat} (hbound : small <= large) :
    boundedUniversalClosedFormulaEnvelope small <=
      boundedUniversalClosedFormulaEnvelope large := by
  have hseed : boundedUniversalSyntaxSeed small <=
      boundedUniversalSyntaxSeed large := by
    unfold boundedUniversalSyntaxSeed
    omega
  have hbody := substitutionFormulaCodeEnvelope_mono_local hseed hseed
  have hcase := finiteCaseFormulaEnvelope_mono_completed
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) hbound
  unfold boundedUniversalClosedFormulaEnvelope
    boundedUniversalClosedBodyCodeEnvelope
  omega

private theorem explicitDirectUniversalLocalPayloadEnvelope_le_fixed_completed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    explicitDirectUniversalLocalPayloadEnvelope count
        (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable) <=
      unitBoundaryDirectUniversalLocalFixedPolynomial numericBound
        bitBound := by
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let bodyCode := unitBoundaryUniversalBodyFormulaCodePolynomial numericBound
    bitBound
  let exactSyntax := explicitDirectUniversalSyntaxResource count body
  let fixedSyntax :=
    unitBoundaryDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let exactFormula := explicitDirectUniversalFormulaEnvelope count body
  let fixedFormula :=
    unitBoundaryDirectUniversalFormulaFixedPolynomial numericBound bitBound
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    simpa only [body, bodyCode] using
      compactAdditiveUnitBoundaryRowsBody_code_length_le_fixed tokenCount
        boundaryTable numericBound bitBound htokenCount htableSize hnumericSize
  have hsyntax : exactSyntax <= fixedSyntax := by
    unfold exactSyntax fixedSyntax explicitDirectUniversalSyntaxResource
      unitBoundaryDirectUniversalSyntaxFixedPolynomial
    dsimp only [body, bodyCode] at hbody ⊢
    omega
  have hclosed := boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula : exactFormula <= fixedFormula := by
    unfold exactFormula fixedFormula explicitDirectUniversalFormulaEnvelope
      unitBoundaryDirectUniversalFormulaFixedPolynomial
    dsimp only [exactSyntax, fixedSyntax, body, bodyCode] at hclosed hbody ⊢
    omega
  exact smallContextAssemblyEnvelope_mono_local hformula

theorem compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope_le_fixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
        tokenCount count boundaryTable numericBound bitBound <=
      unitBoundaryUniformDirectBranchesFixedPayloadPolynomial numericBound
        bitBound := by
  have hraw :=
    compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
      tokenCount count boundaryTable numericBound bitBound
  have hbranch :=
    compactAdditiveUnitBoundaryRowsUniformBranchDirectPayloadEnvelope_le_fixed
      tokenCount boundaryTable numericBound bitBound htokenCount htableSize
      hnumericSize
  have hlocal :=
    explicitDirectUniversalLocalPayloadEnvelope_le_fixed_completed tokenCount
      count boundaryTable numericBound bitBound htokenCount hcount htableSize
      hnumericSize
  unfold explicitDirectUniversalBranchesPayloadPolynomial at hraw
  unfold unitBoundaryUniformDirectBranchesFixedPayloadPolynomial
  exact hraw.trans (Nat.mul_le_mul (by omega) (by omega))

def unitBoundaryContextualBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    unitBoundaryDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    unitBoundaryDirectUniversalFormulaFixedPolynomial numericBound bitBound
  unitBoundaryUniformDirectBranchesFixedPayloadPolynomial numericBound
      bitBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxCode +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode +
    4 * smallContextAssemblyEnvelope formulaCode

theorem cutClosedAssumptionFullAssemblyCost_le_completed
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (caseFormula target : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hcase : (binaryFormulaCode caseFormula).length <= resource)
    (hnegatedCase : (binaryFormulaCode (∼caseFormula)).length <= resource)
    (htarget : (binaryFormulaCode target).length <= resource) :
    cutClosedAssumptionFullAssemblyCost Gamma caseFormula target <=
      smallContextAssemblyEnvelope resource := by
  let rootContext := insert target Gamma
  let caseContext := insert caseFormula rootContext
  let negatedCaseContext := insert (∼caseFormula) rootContext
  have hrootBound : FormulaCodeBound rootContext resource :=
    hGamma.insert htarget
  have hcaseBound : FormulaCodeBound caseContext resource :=
    hrootBound.insert hcase
  have hnegatedCaseBound : FormulaCodeBound negatedCaseContext resource :=
    hrootBound.insert hnegatedCase
  have hrootCardTight : rootContext.card <= 5 := by
    have hstep := Finset.card_insert_le target Gamma
    dsimp only [rootContext]
    omega
  have hrootCard : rootContext.card <= 8 := hrootCardTight.trans (by omega)
  have hcaseCard : caseContext.card <= 8 := by
    have hstep := Finset.card_insert_le caseFormula rootContext
    dsimp only [caseContext]
    omega
  have hnegatedCaseCard : negatedCaseContext.card <= 8 := by
    have hstep := Finset.card_insert_le (∼caseFormula) rootContext
    dsimp only [negatedCaseContext]
    omega
  have hrootSequent := binarySequentCode_length_le_small rootContext resource
    hrootCard hrootBound
  have hcaseSequent := binarySequentCode_length_le_small caseContext resource
    hcaseCard hcaseBound
  have hnegatedCaseSequent := binarySequentCode_length_le_small
    negatedCaseContext resource hnegatedCaseCard hnegatedCaseBound
  have htagSeven : (binaryNatCode 7).length <= 32 := by decide
  have htagNine : (binaryNatCode 9).length <= 32 := by decide
  unfold cutClosedAssumptionFullAssemblyCost
    cutClosedAssumptionDerivationCost smallContextAssemblyEnvelope
  dsimp only [rootContext, caseContext, negatedCaseContext]
    at hrootSequent hcaseSequent hnegatedCaseSequent ⊢
  omega

theorem lowerBoundContradictionFullPayloadCost_le_completed
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (htarget : (binaryFormulaCode target).length <= resource)
    (hfiniteBound : (binaryFormulaCode (finiteBoundFormula bound)).length <=
      resource)
    (hnegatedFiniteBound :
      (binaryFormulaCode (∼finiteBoundFormula bound)).length <= resource)
    (hdoubleNegatedFiniteBound :
      (binaryFormulaCode
        (∼finiteLowerBoundFormula bound (&0))).length <= resource) :
    lowerBoundContradictionFullPayloadCost bound target <=
      smallContextAssemblyEnvelope resource := by
  let Gamma := insert target
    (insert (∼finiteLowerBoundFormula bound (&0))
      (finiteBoundContext bound))
  have hbase : FormulaCodeBound (finiteBoundContext bound) resource := by
    intro formula hformula
    simp only [finiteBoundContext, Finset.mem_singleton] at hformula
    subst formula
    exact hnegatedFiniteBound
  have hGamma : FormulaCodeBound Gamma resource :=
    (hbase.insert hdoubleNegatedFiniteBound).insert htarget
  have hcard : Gamma.card <= 8 := by
    have hbaseCard : (finiteBoundContext bound).card <= 1 := by
      simp [finiteBoundContext]
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula bound (&0)) (finiteBoundContext bound)
    have hsecond := Finset.card_insert_le target
      (insert (∼finiteLowerBoundFormula bound (&0))
        (finiteBoundContext bound))
    dsimp only [Gamma]
    omega
  have hsequent := binarySequentCode_length_le_small Gamma resource hcard
    hGamma
  have htagZero : (binaryNatCode 0).length <= 32 := by decide
  unfold lowerBoundContradictionFullPayloadCost smallContextAssemblyEnvelope
  dsimp only [Gamma] at hsequent ⊢
  omega

theorem contextualBranchesUnderBoundPayloadEnvelope_le_components_completed
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (targetFormula : LO.FirstOrder.ArithmeticProposition)
    (caseResource caseBound cumulativeBound specializationBound
      localBound : Nat)
    (hcase : caseResource <= caseBound)
    (hexhaustion :
      finiteExhaustionAtEigenvariableStructuralPayloadBound bound <=
        cumulativeBound + specializationBound)
    (hlower : lowerBoundContradictionFullPayloadCost bound targetFormula <=
      localBound)
    (hweak : weakeningFullAssemblyCost
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0))
          (contextualFiniteBoundContext Gamma bound))) <= localBound)
    (heliminate :
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        (contextualFiniteBoundContext Gamma bound) targetFormula
        (finiteEqualityCases (&0) bound)
        (finiteLowerBoundFormula bound (&0)) <= localBound)
    (hcut : cutClosedAssumptionFullAssemblyCost
      (contextualFiniteBoundContext Gamma bound)
      (finiteExhaustionFormula bound (&0)) targetFormula <= localBound) :
    contextualBranchesUnderBoundPayloadEnvelope Gamma bound targetFormula
        caseResource <=
      caseBound + cumulativeBound + specializationBound + 4 * localBound := by
  unfold contextualBranchesUnderBoundPayloadEnvelope
    lowerBranchStructuralPayloadBound
  omega

theorem unitBoundaryContextualBranchesResource_le_fixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    contextualBranchesUnderBoundPayloadEnvelope ∅ count
        (Rewriting.free
          (compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable))
        (compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
          tokenCount count boundaryTable numericBound bitBound) <=
      unitBoundaryContextualBranchesFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let targetFormula := Rewriting.free body
  let syntaxCode :=
    unitBoundaryDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    unitBoundaryDirectUniversalFormulaFixedPolynomial numericBound bitBound
  let caseResource :=
    compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
      tokenCount count boundaryTable numericBound bitBound
  let caseBound := unitBoundaryUniformDirectBranchesFixedPayloadPolynomial
    numericBound bitBound
  let finiteContext := contextualFiniteBoundContext
    (∅ : Finset LO.FirstOrder.ArithmeticProposition) count
  let localBound := smallContextAssemblyEnvelope formulaCode
  have hbody : (binaryFormulaCode body).length <=
      unitBoundaryUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveUnitBoundaryRowsBody_code_length_le_fixed tokenCount
      boundaryTable numericBound bitBound htokenCount htableSize hnumericSize
  have hboundSyntax : count <= syntaxCode := by
    unfold syntaxCode unitBoundaryDirectUniversalSyntaxFixedPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxCode := by
    exact hbody.trans (by
      unfold syntaxCode unitBoundaryDirectUniversalSyntaxFixedPolynomial
      omega)
  have hclosedLe : boundedUniversalClosedFormulaEnvelope syntaxCode <=
      formulaCode := by
    unfold formulaCode unitBoundaryDirectUniversalFormulaFixedPolynomial
    dsimp only [syntaxCode]
    omega
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula]
    exact hfree.trans (by
      unfold formulaCode unitBoundaryDirectUniversalFormulaFixedPolynomial
      dsimp only [syntaxCode]
      omega)
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal count syntaxCode
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
  have hfiniteContextBound : FormulaCodeBound finiteContext formulaCode := by
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    exact (show FormulaCodeBound
      (∅ : Finset LO.FirstOrder.ArithmeticProposition) formulaCode by
        intro formula hformula
        simp at hformula).insert (hnegatedFiniteBound.trans hclosedLe)
  have hfiniteContextCard : finiteContext.card <= 4 := by
    dsimp only [finiteContext]
    simp [contextualFiniteBoundContext]
  have hlower : lowerBoundContradictionFullPayloadCost count targetFormula <=
      localBound := by
    exact lowerBoundContradictionFullPayloadCost_le_completed count
      targetFormula formulaCode htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal count syntaxCode
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula count (&0)) finiteContext))
      formulaCode :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula count (&0)) finiteContext)).card <=
          8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula count (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula count (&0)) finiteContext)
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert targetFormula
      (insert (∼finiteLowerBoundFormula count (&0)) finiteContext))
    formulaCode hweakContextCard hweakContextBound
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    finiteContext targetFormula (finiteEqualityCases (&0) count)
      (finiteLowerBoundFormula count (&0)) formulaCode hfiniteContextCard
      hfiniteContextBound htargetCode (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut := cutClosedAssumptionFullAssemblyCost_le_completed
    finiteContext (finiteExhaustionFormula count (&0)) targetFormula
      formulaCode hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial count
      syntaxCode hboundSyntax
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact
      compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope_le_fixed
        tokenCount count boundaryTable numericBound bitBound htokenCount hcount
        htableSize hnumericSize
  change contextualBranchesUnderBoundPayloadEnvelope ∅ count targetFormula
      caseResource <= _
  unfold unitBoundaryContextualBranchesFixedPayloadPolynomial
  dsimp only [syntaxCode, formulaCode, caseBound, localBound]
  exact
    contextualBranchesUnderBoundPayloadEnvelope_le_components_completed ∅
      count targetFormula caseResource caseBound
      (cumulativeFiniteExhaustionPayloadPolynomial syntaxCode)
      (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode)
      localBound hcase hexhaustion hlower hweak heliminate hcut

def unitBoundaryUniversalShellTermPolynomial
    (numericBound bitBound : Nat) : Nat :=
  6 * binaryNumeralTermCodeEnvelope bitBound +
    iteratedSuccessorTermCodePolynomial 0 numericBound +
    (binaryTermCode (&0 : ValuationTerm)).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length + 1

def unitBoundaryUniversalShellRawFormulaPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let termCode := unitBoundaryUniversalShellTermPolynomial numericBound
    bitBound
  let syntaxCode := unitBoundaryDirectUniversalSyntaxFixedPolynomial
    numericBound bitBound
  boundedUniversalClosedFormulaEnvelope syntaxCode +
    paFormulaCodeEnvelope termCode +
    (2 * termCode + finiteCaseLessThanFormulaCodeOverhead) +
    2 * unitBoundaryUniversalBodyFormulaCodePolynomial numericBound bitBound + 1

def unitBoundaryUniversalShellSourceFormulaPolynomial
    (numericBound bitBound : Nat) : Nat :=
  16 * unitBoundaryUniversalShellRawFormulaPolynomial numericBound bitBound +
    128

def unitBoundaryUniversalShellFormulaPolynomial
    (numericBound bitBound : Nat) : Nat :=
  64 * unitBoundaryUniversalShellSourceFormulaPolynomial numericBound
    bitBound + 64

def unitBoundaryUniversalShellLocalPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (unitBoundaryUniversalShellFormulaPolynomial numericBound bitBound)

def unitBoundaryUniformDirectUniversalFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let termCode := unitBoundaryUniversalShellTermPolynomial numericBound
    bitBound
  let formulaCode := unitBoundaryUniversalShellFormulaPolynomial numericBound
    bitBound
  let localBound := unitBoundaryUniversalShellLocalPayloadPolynomial
    numericBound bitBound
  unitBoundaryContextualBranchesFixedPayloadPolynomial numericBound bitBound +
    closedShortBoundEqualityPayloadPolynomial numericBound +
    2 * paPrimitiveCostEnvelope termCode +
    arbitraryContextRelationTransportLocalEnvelope formulaCode termCode +
    12 * localBound

theorem closedShortBoundEqualityPayloadPolynomial_mono_completed
    {small large : Nat} (hbound : small <= large) :
    closedShortBoundEqualityPayloadPolynomial small <=
      closedShortBoundEqualityPayloadPolynomial large := by
  have hshort := shortToIteratedPayloadPolynomial_mono_public hbound
  have hterm := shortToIteratedStepTermCodePolynomial_mono hbound
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
  unfold closedShortBoundEqualityPayloadPolynomial
  omega

theorem
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource_le_fixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
        count boundaryTable numericBound bitBound <=
      unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
        bitBound := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition := ∅
  let shiftedGamma := Gamma.image Rewriting.shift
  let body := compactAdditiveUnitBoundaryRowsBody tokenCount boundaryTable
  let boundTerm := Rew.bShift (shortBinaryNumeralTerm count)
  let bound := count
  let originalBound := freedTermBoundFormula boundTerm
  let canonicalBound := finiteBoundFormula bound
  let targetFormula := Rewriting.free body
  let originalContext := insert (∼originalBound) shiftedGamma
  let canonicalImplication := canonicalBound 🡒 targetFormula
  let freeBoundTerm := Rew.free boundTerm
  let canonicalTerm := iteratedSuccessorTerm 0 bound
  let forwardEquality :=
    (“!!canonicalTerm = !!freeBoundTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let backwardEquality :=
    (“!!freeBoundTerm = !!canonicalTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let subjectTerm := (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  let subjectEquality :=
    (“!!subjectTerm = !!subjectTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let symmetryImplication := forwardEquality 🡒 backwardEquality
  let originalCanonicalImplication := originalBound 🡒 canonicalBound
  let originalTargetImplication := originalBound 🡒 targetFormula
  let universalBody := termBoundedUniversalBody boundTerm body
  let boundEqualityResource :=
    closedShortBoundEqualityPayloadPolynomial count
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ count
    targetFormula
    (compactAdditiveUnitBoundaryRowsUniformDirectBranchesStructuralEnvelope
      tokenCount count boundaryTable numericBound bitBound)
  let termBound := unitBoundaryUniversalShellTermPolynomial numericBound
    bitBound
  let rawFormulaBound :=
    unitBoundaryUniversalShellRawFormulaPolynomial numericBound bitBound
  let sourceFormulaBound :=
    unitBoundaryUniversalShellSourceFormulaPolynomial numericBound bitBound
  let formulaBound :=
    unitBoundaryUniversalShellFormulaPolynomial numericBound bitBound
  let localBound :=
    unitBoundaryUniversalShellLocalPayloadPolynomial numericBound bitBound
  let transportLocal := arbitraryContextRelationTransportLocalEnvelope
    formulaBound termBound
  have hGammaCard : Gamma.card <= 1 := by
    simp [Gamma]
  have hshiftedCard : shiftedGamma.card <= 1 := by
    exact Finset.card_image_le.trans hGammaCard
  have hbound : bound <= numericBound := by
    simpa only [bound] using hcount
  have hcountSize : Nat.size count <= bitBound :=
    (Nat.size_le_size hcount).trans hnumericSize
  have hshortCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <=
        binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope count bitBound hcountSize
  have hrawSource : rawFormulaBound <= sourceFormulaBound := by
    dsimp only [rawFormulaBound, sourceFormulaBound]
    unfold unitBoundaryUniversalShellSourceFormulaPolynomial
    omega
  have hsourceFormula : sourceFormulaBound <= formulaBound := by
    dsimp only [sourceFormulaBound, formulaBound]
    unfold unitBoundaryUniversalShellFormulaPolynomial
    omega
  have hGammaSource : FormulaCodeBound Gamma sourceFormulaBound := by
    intro formula hformula
    simp [Gamma] at hformula
  have hshiftedFormula : FormulaCodeBound shiftedGamma formulaBound := by
    intro formula hformula
    simp [shiftedGamma, Gamma] at hformula
  have hboundTermShift := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm count)
  have hshortSymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm count)
  have hboundTermRaw : (binaryTermCode boundTerm).length <=
      3 * (binaryTermCode (shortBinaryNumeralTerm count)).length := by
    dsimp only [boundTerm]
    omega
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [termBound]
    unfold unitBoundaryUniversalShellTermPolynomial
    omega
  have hfreeBoundRaw := binaryTermCode_free_length_le boundTerm
  have hfreeBound : (binaryTermCode freeBoundTerm).length <= termBound := by
    dsimp only [freeBoundTerm, termBound]
    unfold unitBoundaryUniversalShellTermPolynomial
    omega
  have hcanonicalTermRaw :=
    iteratedSuccessorTerm_code_length_le_polynomial 0 bound
  have hcanonicalTermMono :=
    iteratedSuccessorTermCodePolynomial_mono 0 hbound
  have hcanonicalTerm : (binaryTermCode canonicalTerm).length <=
      termBound := by
    dsimp only [canonicalTerm, termBound]
    unfold unitBoundaryUniversalShellTermPolynomial
    omega
  have hsubjectTerm : (binaryTermCode subjectTerm).length <= termBound := by
    dsimp only [subjectTerm, termBound]
    unfold unitBoundaryUniversalShellTermPolynomial
    omega
  have hbodyFixed : (binaryFormulaCode body).length <=
      unitBoundaryUniversalBodyFormulaCodePolynomial numericBound
        bitBound := by
    simpa only [body] using
      compactAdditiveUnitBoundaryRowsBody_code_length_le_fixed tokenCount
        boundaryTable numericBound bitBound htokenCount htableSize
        hnumericSize
  have hbody : (binaryFormulaCode body).length <= rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have htargetFree := binaryFormulaCode_free_length_le body
  have htargetTight : (binaryFormulaCode targetFormula).length <=
      2 * (binaryFormulaCode body).length := by
    simpa only [targetFormula] using htargetFree
  have htarget : (binaryFormulaCode targetFormula).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have horiginalBoundRaw := finiteCaseLessThanFormula_code_length_le
    subjectTerm freeBoundTerm
  have horiginalBoundTight : (binaryFormulaCode originalBound).length <=
      (binaryTermCode subjectTerm).length +
        (binaryTermCode freeBoundTerm).length +
          finiteCaseLessThanFormulaCodeOverhead := by
    simpa only [originalBound, freedTermBoundFormula, subjectTerm,
      freeBoundTerm] using horiginalBoundRaw
  have horiginalBound : (binaryFormulaCode originalBound).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hsyntaxBound : bound <=
      unitBoundaryDirectUniversalSyntaxFixedPolynomial numericBound
        bitBound := by
    dsimp only [bound]
    unfold unitBoundaryDirectUniversalSyntaxFixedPolynomial
    omega
  have hcanonicalBoundRaw := finiteBoundFormula_code_le_boundedUniversal bound
    (unitBoundaryDirectUniversalSyntaxFixedPolynomial numericBound bitBound)
      hsyntaxBound
  have hcanonicalBoundTight : (binaryFormulaCode canonicalBound).length <=
      boundedUniversalClosedFormulaEnvelope
        (unitBoundaryDirectUniversalSyntaxFixedPolynomial numericBound
          bitBound) := by
    simpa only [canonicalBound] using hcanonicalBoundRaw
  have hcanonicalBound : (binaryFormulaCode canonicalBound).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hforwardEqualityRaw := equalityFormula_code_length_le_paEnvelope
    canonicalTerm freeBoundTerm termBound hcanonicalTerm hfreeBound
  have hforwardEqualityTight :
      (binaryFormulaCode forwardEquality).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [forwardEquality] using hforwardEqualityRaw
  dsimp only [termBound] at hforwardEqualityTight
  have hforwardEquality : (binaryFormulaCode forwardEquality).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hbackwardEqualityRaw := equalityFormula_code_length_le_paEnvelope
    freeBoundTerm canonicalTerm termBound hfreeBound hcanonicalTerm
  have hbackwardEqualityTight :
      (binaryFormulaCode backwardEquality).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [backwardEquality] using hbackwardEqualityRaw
  dsimp only [termBound] at hbackwardEqualityTight
  have hbackwardEquality : (binaryFormulaCode backwardEquality).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hsubjectEqualityRaw := equalityFormula_code_length_le_paEnvelope
    subjectTerm subjectTerm termBound hsubjectTerm hsubjectTerm
  have hsubjectEqualityTight :
      (binaryFormulaCode subjectEquality).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [subjectEquality] using hsubjectEqualityRaw
  dsimp only [termBound] at hsubjectEqualityTight
  have hsubjectEquality : (binaryFormulaCode subjectEquality).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hcoreSource := fun {formula : LO.FirstOrder.ArithmeticProposition}
      (hformula : (binaryFormulaCode formula).length <= rawFormulaBound) =>
    hformula.trans hrawSource
  have himplication := fun
      (left right : LO.FirstOrder.ArithmeticProposition)
      (hleft : (binaryFormulaCode left).length <= rawFormulaBound)
      (hright : (binaryFormulaCode right).length <= rawFormulaBound) => by
    have hraw := binaryFormulaCode_implication_length_le left right
    have htag : (binaryNatCode 5).length <= 64 := by decide
    have : (binaryFormulaCode (left 🡒 right)).length <=
        sourceFormulaBound := by
      dsimp only [sourceFormulaBound]
      unfold unitBoundaryUniversalShellSourceFormulaPolynomial
      omega
    exact this
  have hcanonicalImplication :
      (binaryFormulaCode canonicalImplication).length <=
        sourceFormulaBound := by
    dsimp only [canonicalImplication]
    exact himplication canonicalBound targetFormula hcanonicalBound htarget
  have hsymmetryImplication :
      (binaryFormulaCode symmetryImplication).length <=
        sourceFormulaBound := by
    dsimp only [symmetryImplication]
    exact himplication forwardEquality backwardEquality hforwardEquality
      hbackwardEquality
  have horiginalCanonicalImplication :
      (binaryFormulaCode originalCanonicalImplication).length <=
        sourceFormulaBound := by
    dsimp only [originalCanonicalImplication]
    exact himplication originalBound canonicalBound horiginalBound
      hcanonicalBound
  have horiginalTargetImplication :
      (binaryFormulaCode originalTargetImplication).length <=
        sourceFormulaBound := by
    dsimp only [originalTargetImplication]
    exact himplication originalBound targetFormula horiginalBound htarget
  have hnegated := fun (formula : LO.FirstOrder.ArithmeticProposition)
      (hformula : (binaryFormulaCode formula).length <= sourceFormulaBound) =>
    by
      have hraw := binaryFormulaCode_neg_length_le formula
      have : (binaryFormulaCode (∼formula)).length <= formulaBound := by
        dsimp only [formulaBound]
        unfold unitBoundaryUniversalShellFormulaPolynomial
        omega
      exact this
  have hnegatedOriginalBound := hnegated originalBound
    (hcoreSource horiginalBound)
  have hnegatedCanonicalBound := hnegated canonicalBound
    (hcoreSource hcanonicalBound)
  have hnegatedTarget := hnegated targetFormula (hcoreSource htarget)
  have hnegatedBackward := hnegated backwardEquality
    (hcoreSource hbackwardEquality)
  have hnegatedSymmetryImplication := hnegated symmetryImplication
    hsymmetryImplication
  have hnegatedOriginalCanonicalImplication :=
    hnegated originalCanonicalImplication horiginalCanonicalImplication
  have hnegatedCanonicalImplication :=
    hnegated canonicalImplication hcanonicalImplication
  have htermBoundFormulaRaw := finiteCaseLessThanFormula_code_length_le
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) boundTerm
  have htermBoundFormulaTight :
      (binaryFormulaCode (termBoundFormula boundTerm)).length <=
        (binaryTermCode
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length +
          (binaryTermCode boundTerm).length +
            finiteCaseLessThanFormulaCodeOverhead := by
    simpa only [termBoundFormula] using htermBoundFormulaRaw
  have htermBoundFormula :
      (binaryFormulaCode (termBoundFormula boundTerm)).length <=
        rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold unitBoundaryUniversalShellRawFormulaPolynomial
    have hzeroTerm :
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
            termBound := by
      have hzeroCode :
          (binaryTermCode
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
              (binaryTermCode (&0 : ValuationTerm)).length := by decide
      dsimp only [termBound]
      unfold unitBoundaryUniversalShellTermPolynomial
      omega
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
    unfold unitBoundaryUniversalShellSourceFormulaPolynomial
    omega
  have huniversalFormulaRaw := binaryFormulaCode_all_length_le universalBody
  have huniversalFormula :
      (binaryFormulaCode
        (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition)).length <=
          sourceFormulaBound := by
    dsimp only [sourceFormulaBound]
    unfold unitBoundaryUniversalShellSourceFormulaPolynomial
    omega
  have hfreeUniversalBodyRaw := binaryFormulaCode_free_length_le universalBody
  have hfreeUniversalBody :
      (binaryFormulaCode (Rewriting.free universalBody)).length <=
        formulaBound := by
    dsimp only [formulaBound]
    unfold unitBoundaryUniversalShellFormulaPolynomial
    omega
  have hformulaPositive : sourceFormulaBound <= formulaBound := hsourceFormula
  have horiginalBoundFormula := (hcoreSource horiginalBound).trans
    hformulaPositive
  have hcanonicalBoundFormula := (hcoreSource hcanonicalBound).trans
    hformulaPositive
  have htargetFormula := (hcoreSource htarget).trans hformulaPositive
  have hforwardEqualityFormula := (hcoreSource hforwardEquality).trans
    hformulaPositive
  have hbackwardEqualityFormula := (hcoreSource hbackwardEquality).trans
    hformulaPositive
  have hsubjectEqualityFormula := (hcoreSource hsubjectEquality).trans
    hformulaPositive
  have hcanonicalImplicationFormula := hcanonicalImplication.trans
    hformulaPositive
  have hsymmetryImplicationFormula := hsymmetryImplication.trans
    hformulaPositive
  have horiginalCanonicalImplicationFormula :=
    horiginalCanonicalImplication.trans hformulaPositive
  have horiginalTargetImplicationFormula :=
    horiginalTargetImplication.trans hformulaPositive
  have horiginalContextBound : FormulaCodeBound originalContext formulaBound :=
    by
      dsimp only [originalContext]
      exact hshiftedFormula.insert hnegatedOriginalBound
  have horiginalContextCard : originalContext.card <= 4 := by
    have hstep := Finset.card_insert_le (∼originalBound) shiftedGamma
    dsimp only [originalContext]
    omega
  have hboundEquality : boundEqualityResource <=
      closedShortBoundEqualityPayloadPolynomial numericBound := by
    dsimp only [boundEqualityResource]
    exact closedShortBoundEqualityPayloadPolynomial_mono_completed hcount
  have hbranches : branchResource <=
      unitBoundaryContextualBranchesFixedPayloadPolynomial numericBound
        bitBound := by
    dsimp only [branchResource, targetFormula]
    exact unitBoundaryContextualBranchesResource_le_fixed tokenCount count
      boundaryTable numericBound bitBound htokenCount hcount htableSize
        hnumericSize
  have hcanonicalDischarge :=
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
      shiftedGamma canonicalBound targetFormula formulaBound (by omega)
        hshiftedFormula htargetFormula hcanonicalImplicationFormula
          hnegatedCanonicalBound
  have hcanonicalInsertBound : FormulaCodeBound
      (insert canonicalImplication originalContext) formulaBound :=
    horiginalContextBound.insert hcanonicalImplicationFormula
  have hcanonicalInsertCard :
      (insert canonicalImplication originalContext).card <= 8 := by
    have hstep := Finset.card_insert_le canonicalImplication originalContext
    omega
  have hweakCanonical := weakeningFullAssemblyCost_le_small
    (insert canonicalImplication originalContext) formulaBound
      hcanonicalInsertCard hcanonicalInsertBound
  have horiginalAssumption := assumptionFullPayloadCost_le_small
    originalContext originalBound formulaBound horiginalContextCard
      horiginalContextBound horiginalBoundFormula
  have hsymmetry := equalitySymmetryImplication_payloadLength_le_primitive
    canonicalTerm freeBoundTerm termBound hcanonicalTerm hfreeBound
  have hsymmetryInsertBound : FormulaCodeBound
      (insert symmetryImplication shiftedGamma) formulaBound :=
    hshiftedFormula.insert hsymmetryImplicationFormula
  have hsymmetryInsertCard :
      (insert symmetryImplication shiftedGamma).card <= 8 := by
    have hstep := Finset.card_insert_le symmetryImplication shiftedGamma
    omega
  have hweakSymmetry := weakeningFullAssemblyCost_le_small
    (insert symmetryImplication shiftedGamma) formulaBound
      hsymmetryInsertCard hsymmetryInsertBound
  have hmpSymmetry := contextualModusPonensFullAssemblyCost_le_small
    shiftedGamma forwardEquality backwardEquality formulaBound (by omega)
      hshiftedFormula hforwardEqualityFormula hbackwardEqualityFormula
        hsymmetryImplicationFormula hnegatedSymmetryImplication
          hnegatedBackward
  have hbackwardInsertBound : FormulaCodeBound
      (insert backwardEquality originalContext) formulaBound :=
    horiginalContextBound.insert hbackwardEqualityFormula
  have hbackwardInsertCard :
      (insert backwardEquality originalContext).card <= 8 := by
    have hstep := Finset.card_insert_le backwardEquality originalContext
    omega
  have hweakBackward := weakeningFullAssemblyCost_le_small
    (insert backwardEquality originalContext) formulaBound
      hbackwardInsertCard hbackwardInsertBound
  have hreflexivity := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    subjectTerm termBound hsubjectTerm
  have hsubjectInsertBound : FormulaCodeBound
      (insert subjectEquality originalContext) formulaBound :=
    horiginalContextBound.insert hsubjectEqualityFormula
  have hsubjectInsertCard :
      (insert subjectEquality originalContext).card <= 8 := by
    have hstep := Finset.card_insert_le subjectEquality originalContext
    omega
  have hweakSubject := weakeningFullAssemblyCost_le_small
    (insert subjectEquality originalContext) formulaBound hsubjectInsertCard
      hsubjectInsertBound
  let backwardResource :=
    (equalitySymmetryImplication canonicalTerm freeBoundTerm).payloadLength +
      weakeningFullAssemblyCost (insert symmetryImplication shiftedGamma) +
      boundEqualityResource +
      contextualModusPonensFullAssemblyCost shiftedGamma forwardEquality
        backwardEquality
  let backwardUnderOriginalResource := backwardResource +
    weakeningFullAssemblyCost (insert backwardEquality originalContext)
  let subjectResource :=
    (proveEqualityReflexivityAtTerm subjectTerm).payloadLength +
      weakeningFullAssemblyCost (insert subjectEquality originalContext)
  have htransport :=
    relationTransportImplicationStructuralPayloadBound_le_arbitraryContext
      originalContext Language.ORing.Rel.lt subjectTerm freeBoundTerm
      subjectTerm canonicalTerm subjectResource backwardUnderOriginalResource
      formulaBound termBound horiginalContextCard horiginalContextBound
      hsubjectTerm hfreeBound hsubjectTerm hcanonicalTerm
  have hmpOriginalCanonical :=
    contextualModusPonensFullAssemblyCost_le_small originalContext
      originalBound canonicalBound formulaBound horiginalContextCard
      horiginalContextBound horiginalBoundFormula hcanonicalBoundFormula
      horiginalCanonicalImplicationFormula
      hnegatedOriginalCanonicalImplication hnegatedCanonicalBound
  have hmpCanonicalTarget :=
    contextualModusPonensFullAssemblyCost_le_small originalContext
      canonicalBound targetFormula formulaBound horiginalContextCard
      horiginalContextBound hcanonicalBoundFormula htargetFormula
      hcanonicalImplicationFormula hnegatedCanonicalImplication
      hnegatedTarget
  have horiginalDischarge :=
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
      shiftedGamma originalBound targetFormula formulaBound (by omega)
      hshiftedFormula htargetFormula horiginalTargetImplicationFormula
      hnegatedOriginalBound
  have hshiftSource : 2 * sourceFormulaBound <= formulaBound := by
    dsimp only [formulaBound]
    unfold unitBoundaryUniversalShellFormulaPolynomial
    omega
  have huniversalIntroduction :=
    contextualUniversalIntroductionFullAssemblyCost_le_openIndexUniversalShell
      Gamma universalBody sourceFormulaBound formulaBound (by omega)
      hGammaSource (huniversalBody.trans hformulaPositive)
      hfreeUniversalBody huniversalFormula hshiftSource
  have hlocalBound : localBound =
      smallContextAssemblyEnvelope formulaBound := by
    dsimp only [localBound, formulaBound]
    rfl
  simp only [shiftedGamma, canonicalBound, targetFormula]
    at hcanonicalDischarge
  simp only [canonicalImplication, canonicalBound, targetFormula,
    originalContext, originalBound, shiftedGamma] at hweakCanonical
  simp only [originalContext, originalBound, shiftedGamma]
    at horiginalAssumption
  simp only [canonicalTerm, freeBoundTerm] at hsymmetry
  simp only [symmetryImplication, forwardEquality, backwardEquality,
    shiftedGamma, canonicalTerm, freeBoundTerm] at hweakSymmetry
  simp only [shiftedGamma, forwardEquality, backwardEquality, canonicalTerm,
    freeBoundTerm] at hmpSymmetry
  simp only [backwardEquality, originalContext, originalBound, shiftedGamma,
    canonicalTerm, freeBoundTerm] at hweakBackward
  simp only [subjectTerm] at hreflexivity
  simp only [subjectEquality, subjectTerm, originalContext, originalBound,
    shiftedGamma] at hweakSubject
  simp only [originalContext, originalBound, shiftedGamma, subjectTerm,
    freeBoundTerm, canonicalTerm, subjectResource, backwardResource,
    backwardUnderOriginalResource, symmetryImplication, forwardEquality,
    backwardEquality, subjectEquality] at htransport
  simp only [originalContext, originalBound, shiftedGamma, canonicalBound]
    at hmpOriginalCanonical
  simp only [originalContext, originalBound, shiftedGamma, canonicalBound,
    targetFormula] at hmpCanonicalTarget
  simp only [shiftedGamma, originalBound, targetFormula]
    at horiginalDischarge
  simp only [universalBody] at huniversalIntroduction
  change compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound
      boundTerm body boundEqualityResource branchResource <=
    unitBoundaryContextualBranchesFixedPayloadPolynomial numericBound
        bitBound +
      closedShortBoundEqualityPayloadPolynomial numericBound +
      2 * paPrimitiveCostEnvelope termBound + transportLocal +
      12 * localBound
  rw [hlocalBound]
  unfold compileContextualTermBoundedUniversalPayloadEnvelope
  dsimp only [shiftedGamma, originalBound, canonicalBound, originalContext,
    canonicalImplication, forwardEquality, backwardEquality, subjectEquality,
    symmetryImplication, originalCanonicalImplication,
    originalTargetImplication, universalBody, freeBoundTerm, canonicalTerm,
    subjectTerm, backwardResource, backwardUnderOriginalResource,
    subjectResource, transportLocal]
  omega

#print axioms compactNatSizeStructuralPayloadPolynomial_le_fixed
#print axioms completedAreaStructuralPayloadPolynomial_le_fixed
#print axioms
  compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource_le_fixed

end FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
