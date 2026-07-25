import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPABitAtomArityCodeBounds
import integration.FoundationCompactPABinaryBitValuationFixedPolynomialBounds
import integration.FoundationCompactPAContextualBranchesFixedAssembly
import integration.FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

/-!
# Fixed atomic resources for syntax-task-list equality

This module closes the proof-dependent atomic leaves shared by parser
failure and continuation branches.  Count equality and each three-cell task
row are charged only against common numeric and bit bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitAtomArityCodeBounds
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABinaryBitValuationFixedPolynomialBounds
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBranchesFixedAssembly
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

private abbrev taskSameRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation

def taskSameRowsAtomicTermCodePolynomial (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound + 1

def taskSameRowsRowTermCodePolynomial (bitBound : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    (binaryTermCode (‘2’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def taskSameRowsAtomicRowBodyTermCodePolynomial
    (termBound : Nat) : Nat :=
  8 * termBound +
    3 * binaryFunctionTermCodeOverhead Language.Mul.mul +
    binaryFunctionTermCodeOverhead Language.Add.add +
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length + 1

def taskSameRowsAtomicRowBodyCodePolynomial (termBound : Nat) : Nat :=
  64 * (bitAtomArityCodePolynomial
    (taskSameRowsAtomicRowBodyTermCodePolynomial termBound) + 1)

def taskSameRowsAtomicRowUniversalShellScale
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound + 1

def taskSameRowsAtomicRowUniversalFixedPayloadPolynomial
    (numericBound bitBound termBound branchBound : Nat) : Nat :=
  let bodyCode := taskSameRowsAtomicRowBodyCodePolynomial termBound
  let syntaxCode := numericBound + bodyCode
  let scale :=
    taskSameRowsAtomicRowUniversalShellScale numericBound bitBound
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    syntaxCode bodyCode branchBound
    (compileShiftedBoundEqualityFixedPayloadPolynomial scale)

def taskSameRowsAtomicRowBitTermCodePolynomial
    (termBound : Nat) : Nat :=
  8 * termBound +
    4 * binaryFunctionTermCodeOverhead Language.Mul.mul +
    2 * (binaryTermCode (&0 : ValuationTerm)).length +
    2 * binaryFunctionTermCodeOverhead Language.Add.add + 4

def taskSameRowsAtomicRowBitLiteralFixedPayloadPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  binaryBitValuationFixedLiteralPayloadPolynomial numericBound
    (taskSameRowsAtomicRowBitTermCodePolynomial termBound)
    (atomicRowEqBitPositionTraceWidth numericBound) bitBound

def taskSameRowsAtomicRowBitLiteralFormulaCodePolynomial
    (termBound : Nat) : Nat :=
  binaryBitLiteralFormulaCodeEnvelope
    (taskSameRowsAtomicRowBitTermCodePolynomial termBound)

def taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
    (numericBound termBound : Nat) : Nat :=
  atomicRowEqBitContextFormulaCodeSumEnvelope numericBound +
    16 * (taskSameRowsAtomicRowBitLiteralFormulaCodePolynomial termBound +
      (binaryNatCode 4).length + (binaryNatCode 5).length + 1) + 1

def taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  4 * taskSameRowsAtomicRowBitLiteralFixedPayloadPolynomial numericBound
      bitBound termBound +
    13 * generalContextAssemblyEnvelope
      (taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial numericBound
        termBound)

def taskSameRowsAtomicRowBitBranchPublicPayloadSumFixedPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  numericBound *
    taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial numericBound
      bitBound termBound

def taskSameRowsAtomicRowBranchesFormulaCodePolynomial
    (numericBound termBound : Nat) : Nat :=
  let bodyCode := taskSameRowsAtomicRowBodyCodePolynomial termBound
  boundedUniversalClosedFormulaEnvelope (numericBound + bodyCode) +
    2 * bodyCode

def taskSameRowsAtomicRowBranchesFixedPayloadPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  (numericBound + 1) *
    (taskSameRowsAtomicRowBitBranchPublicPayloadSumFixedPolynomial
        numericBound bitBound termBound +
      3 * smallContextAssemblyEnvelope
        (taskSameRowsAtomicRowBranchesFormulaCodePolynomial numericBound
          termBound))

def taskSameRowsAtomicRowContextualBranchesFixedPayloadPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  contextualBranchesFixedAssemblyEnvelope
    (numericBound + taskSameRowsAtomicRowBodyCodePolynomial termBound)
    (taskSameRowsAtomicRowBranchesFormulaCodePolynomial numericBound termBound)
    (taskSameRowsAtomicRowBranchesFixedPayloadPolynomial numericBound
      bitBound termBound)

def taskSameRowsAtomicRowUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  taskSameRowsAtomicRowUniversalFixedPayloadPolynomial numericBound bitBound
    termBound
    (taskSameRowsAtomicRowContextualBranchesFixedPayloadPolynomial numericBound
      bitBound termBound)

def taskSameRowsAtomicRowOuterTermCodePolynomial
    (termBound : Nat) : Nat :=
  2 * termBound + (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    (termBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (taskSameRowsAtomicRowOuterTermCodePolynomial termBound)

def taskSameRowsAtomicRowOuterUniversalFormulaCodePolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  let bodyCode := taskSameRowsAtomicRowBodyCodePolynomial termBound
  closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
    (numericBound + bodyCode) bodyCode

def taskSameRowsAtomicRowAssemblySyntaxPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  4 * taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial termBound +
    taskSameRowsAtomicRowOuterUniversalFormulaCodePolynomial numericBound
      bitBound termBound +
    4 * (binaryNatCode 4).length + 1

def taskSameRowsCompactAdditiveAtomicRowEqFixedPayloadPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  let syntaxResource :=
    taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
      termBound
  let atomicResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound (taskSameRowsAtomicRowOuterTermCodePolynomial termBound)
  let universalResource :=
    taskSameRowsAtomicRowUniversalFullyFixedPayloadPolynomial numericBound
      bitBound termBound
  hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
    atomicResource atomicResource atomicResource universalResource

def taskSameRowsTaskRowAssemblySyntaxPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  3 * taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
      termBound +
    2 * (binaryNatCode 4).length + 1

def taskSameRowsTaskRowFixedPayloadPolynomial
    (numericBound bitBound termBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (taskSameRowsTaskRowAssemblySyntaxPolynomial numericBound bitBound
      termBound)
    (taskSameRowsCompactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound
      bitBound termBound)
    (taskSameRowsCompactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound
      bitBound termBound)
    (taskSameRowsCompactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound
      bitBound termBound)

def taskSameRowsCountFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (taskSameRowsAtomicTermCodePolynomial bitBound)

private theorem taskSameRowsShortNumeralCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      taskSameRowsAtomicTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold taskSameRowsAtomicTermCodePolynomial
  omega

private theorem taskSameRowsArithmeticAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) = paAddTerm left right := by
  rfl

private theorem taskSameRowsArithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem taskSameRowsBinaryFunctionTerm_freeVariables
    {boundArity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
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
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem taskSameRowsBinaryRelationFormula_freeVariables
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

private theorem taskSameRowsArithmeticMulTerm_eq_func
    (left right : ValuationTerm) :
    paMulTerm left right =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [paMulTerm, Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem taskSameRowsPaMulTerm_freeVariables
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [taskSameRowsArithmeticMulTerm_eq_func]
  exact taskSameRowsBinaryFunctionTerm_freeVariables Language.Mul.mul
    left right

private theorem taskSameRowsOne_closed :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem taskSameRowsTwo_closed :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem taskSameRowsAddOneTerm_closed (value : Nat) :
    (‘!!(shortBinaryNumeralTerm value) + 1’ :
      ValuationTerm).freeVariables = ∅ := by
  rw [taskSameRowsArithmeticAddTerm_eq_func]
  rw [taskSameRowsBinaryFunctionTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    taskSameRowsOne_closed]
  simp

theorem taskSameRowsAddTwoTerm_closed (value : Nat) :
    (‘!!(shortBinaryNumeralTerm value) + 2’ :
      ValuationTerm).freeVariables = ∅ := by
  rw [taskSameRowsArithmeticAddTerm_eq_func]
  rw [taskSameRowsBinaryFunctionTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    taskSameRowsTwo_closed]
  simp

theorem taskSameRowsAddOneTerm_value
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation
        (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm) =
      value + 1 := by
  change termValue valuation (shortBinaryNumeralTerm value) + 1 =
    value + 1
  rw [termValue_shortBinaryNumeralTerm]

theorem taskSameRowsAddTwoTerm_value
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation
        (‘!!(shortBinaryNumeralTerm value) + 2’ : ValuationTerm) =
      value + 2 := by
  change termValue valuation (shortBinaryNumeralTerm value) + 2 =
    value + 2
  rw [termValue_shortBinaryNumeralTerm]

theorem taskSameRowsAddOneTermCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm)).length <=
      taskSameRowsRowTermCodePolynomial bitBound := by
  have hvalueCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm value) (‘1’ : ValuationTerm)
  rw [taskSameRowsArithmeticAddTerm_eq_paAddTerm]
  unfold taskSameRowsRowTermCodePolynomial
  omega

theorem taskSameRowsAddTwoTermCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm value) + 2’ : ValuationTerm)).length <=
      taskSameRowsRowTermCodePolynomial bitBound := by
  have hvalueCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm value) (‘2’ : ValuationTerm)
  rw [taskSameRowsArithmeticAddTerm_eq_paAddTerm]
  unfold taskSameRowsRowTermCodePolynomial
  omega

private theorem taskSameRowsBinaryAddTermCode_le
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func Language.Add.add
        ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  simp [binaryTermCode, binaryFunctionTermCodeOverhead,
    Matrix.fun_eq_vec_two]
  omega

theorem atomicRowEqBitBody_code_length_le_closedTerms
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (termBound : Nat)
    (htableCode :
      (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode :
      (binaryTermCode widthTerm).length <= termBound)
    (hleftCode :
      (binaryTermCode leftTerm).length <= termBound)
    (hotherCode :
      (binaryTermCode otherLeftTerm).length <= termBound) :
    (binaryFormulaCode
      (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
        otherLeftTerm)).length <=
      taskSameRowsAtomicRowBodyCodePolynomial termBound := by
  let leftProduct := paMulTerm leftTerm widthTerm
  let otherProduct := paMulTerm otherLeftTerm widthTerm
  let leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift leftProduct, #0]
  let otherIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift otherProduct, #0]
  let tableValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift tokenTableTerm
  let bodyTermBound :=
    taskSameRowsAtomicRowBodyTermCodePolynomial termBound
  let leftAtom := binaryBitAtomAtTerms leftIndex tableValue
  let otherAtom := binaryBitAtomAtTerms otherIndex tableValue
  have hleftProductRaw := paMulTerm_code_length_le leftTerm widthTerm
  have hotherProductRaw := paMulTerm_code_length_le otherLeftTerm widthTerm
  have hleftProduct :
      (binaryTermCode leftProduct).length <=
        2 * termBound +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [leftProduct]
    omega
  have hotherProduct :
      (binaryTermCode otherProduct).length <=
        2 * termBound +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [otherProduct]
    omega
  have hleftSymbols := termSymbolCount_le_binaryTermCode_length leftProduct
  have hotherSymbols :=
    termSymbolCount_le_binaryTermCode_length otherProduct
  have hleftShiftRaw :=
    binaryTermCode_bShift_length_le_add_symbols leftProduct
  have hotherShiftRaw :=
    binaryTermCode_bShift_length_le_add_symbols otherProduct
  have hleftShift :
      (binaryTermCode (Rew.bShift leftProduct)).length <=
        3 * (2 * termBound +
          binaryFunctionTermCodeOverhead Language.Mul.mul) := by
    omega
  have hotherShift :
      (binaryTermCode (Rew.bShift otherProduct)).length <=
        3 * (2 * termBound +
          binaryFunctionTermCodeOverhead Language.Mul.mul) := by
    omega
  have hleftIndexRaw := taskSameRowsBinaryAddTermCode_le
    (Rew.bShift leftProduct)
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  have hotherIndexRaw := taskSameRowsBinaryAddTermCode_le
    (Rew.bShift otherProduct)
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  have hleftIndex :
      (binaryTermCode leftIndex).length <= bodyTermBound := by
    dsimp only [leftIndex, bodyTermBound,
      taskSameRowsAtomicRowBodyTermCodePolynomial]
    omega
  have hotherIndex :
      (binaryTermCode otherIndex).length <= bodyTermBound := by
    dsimp only [otherIndex, bodyTermBound,
      taskSameRowsAtomicRowBodyTermCodePolynomial]
    omega
  have htableSymbols :=
    termSymbolCount_le_binaryTermCode_length tokenTableTerm
  have htableShiftRaw :=
    binaryTermCode_bShift_length_le_add_symbols tokenTableTerm
  have htableValue :
      (binaryTermCode tableValue).length <= bodyTermBound := by
    dsimp only [tableValue, bodyTermBound,
      taskSameRowsAtomicRowBodyTermCodePolynomial]
    omega
  have hleftAtom :
      (binaryFormulaCode leftAtom).length <=
        bitAtomArityCodePolynomial bodyTermBound :=
    binaryBitAtomAtTerms_code_length_le_arity leftIndex tableValue
      bodyTermBound hleftIndex htableValue
  have hotherAtom :
      (binaryFormulaCode otherAtom).length <=
        bitAtomArityCodePolynomial bodyTermBound :=
    binaryBitAtomAtTerms_code_length_le_arity otherIndex tableValue
      bodyTermBound hotherIndex htableValue
  have hnegLeft := binaryFormulaCode_neg_length_le leftAtom
  have hnegRight := binaryFormulaCode_neg_length_le otherAtom
  change (binaryFormulaCode
    (LO.FirstOrder.Semiformula.neg leftAtom)).length <=
      2 * (binaryFormulaCode leftAtom).length at hnegLeft
  change (binaryFormulaCode
    (LO.FirstOrder.Semiformula.neg otherAtom)).length <=
      2 * (binaryFormulaCode otherAtom).length at hnegRight
  have htagFour : (binaryNatCode 4).length <= 8 := by decide
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  unfold atomicRowEqBitBody
  change (binaryFormulaCode (leftAtom 🡘 otherAtom)).length <= _
  simp only [binaryFormulaCode, List.length_append]
  unfold taskSameRowsAtomicRowBodyCodePolynomial
  dsimp only [bodyTermBound] at hleftAtom hotherAtom
  omega

theorem atomicRowEqBitTerms_code_le_closedTerms
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (termBound : Nat)
    (htableCode :
      (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode :
      (binaryTermCode widthTerm).length <= termBound)
    (hleftCode :
      (binaryTermCode leftTerm).length <= termBound)
    (hotherCode :
      (binaryTermCode otherLeftTerm).length <= termBound) :
    (binaryTermCode
        (atomicRowEqLeftBitIndexTerm widthTerm leftTerm)).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound ∧
      (binaryTermCode
        (atomicRowEqOtherLeftBitIndexTerm widthTerm
          otherLeftTerm)).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound ∧
      (binaryTermCode
        (atomicRowEqBitValueTerm tokenTableTerm)).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound := by
  have hleftProduct := paMulTerm_code_length_le leftTerm widthTerm
  have hotherProduct := paMulTerm_code_length_le otherLeftTerm widthTerm
  have hleftShift :=
    binaryTermCode_shift_length_le (paMulTerm leftTerm widthTerm)
  have hotherShift :=
    binaryTermCode_shift_length_le (paMulTerm otherLeftTerm widthTerm)
  have hleftIndexRaw := paAddTerm_code_length_le
    (Rew.shift (paMulTerm leftTerm widthTerm)) (&0 : ValuationTerm)
  have hotherIndexRaw := paAddTerm_code_length_le
    (Rew.shift (paMulTerm otherLeftTerm widthTerm)) (&0 : ValuationTerm)
  have htableShift := binaryTermCode_shift_length_le tokenTableTerm
  constructor
  · unfold atomicRowEqLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift (paMulTerm leftTerm widthTerm))
        (&0 : ValuationTerm))).length <= _
    exact hleftIndexRaw.trans (by
      unfold taskSameRowsAtomicRowBitTermCodePolynomial
      omega)
  constructor
  · unfold atomicRowEqOtherLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift (paMulTerm otherLeftTerm widthTerm))
        (&0 : ValuationTerm))).length <= _
    exact hotherIndexRaw.trans (by
      unfold taskSameRowsAtomicRowBitTermCodePolynomial
      omega)
  · unfold atomicRowEqBitValueTerm
    exact htableShift.trans (by
      unfold taskSameRowsAtomicRowBitTermCodePolynomial
      omega)

private theorem taskSameRowsTermValue_paMulTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paMulTerm left right) =
      termValue valuation left * termValue valuation right := by
  rw [taskSameRowsArithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem taskSameRowsTermValue_languageAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation
        (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) =
      termValue valuation left + termValue valuation right :=
  termValue_add valuation ![left, right]

theorem atomicRowEqBitTerms_closedTerm_data
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (bitIndex : Nat)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅) :
    let branchValuation := extendValuation bitIndex valuation
    let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
    let otherIndexTerm :=
      atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
    let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
    leftIndexTerm.freeVariables ⊆ {0} ∧
      otherIndexTerm.freeVariables ⊆ {0} ∧
      valueTerm.freeVariables = ∅ ∧
      termValue branchValuation leftIndexTerm =
        termValue valuation leftTerm * termValue valuation widthTerm +
          bitIndex ∧
      termValue branchValuation otherIndexTerm =
        termValue valuation otherLeftTerm * termValue valuation widthTerm +
          bitIndex ∧
      termValue branchValuation valueTerm =
        termValue valuation tokenTableTerm := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  have hleftProduct :
      (paMulTerm leftTerm widthTerm).freeVariables = ∅ := by
    rw [taskSameRowsPaMulTerm_freeVariables, hleftClosed, hwidthClosed]
    simp
  have hotherProduct :
      (paMulTerm otherLeftTerm widthTerm).freeVariables = ∅ := by
    rw [taskSameRowsPaMulTerm_freeVariables, hotherClosed, hwidthClosed]
    simp
  have hleftShift :
      (Rew.shift (paMulTerm leftTerm widthTerm)).freeVariables = ∅ := by
    exact shiftedTerm_freeVariables_eq_empty_of_closed
      (paMulTerm leftTerm widthTerm) hleftProduct
  have hotherShift :
      (Rew.shift (paMulTerm otherLeftTerm widthTerm)).freeVariables = ∅ := by
    exact shiftedTerm_freeVariables_eq_empty_of_closed
      (paMulTerm otherLeftTerm widthTerm) hotherProduct
  have hleftVars : leftIndexTerm.freeVariables ⊆ {0} := by
    unfold leftIndexTerm atomicRowEqLeftBitIndexTerm
    change
      (Semiterm.func Language.Add.add
        ![Rew.shift (paMulTerm leftTerm widthTerm),
          (&0 : ValuationTerm)]).freeVariables ⊆ {0}
    rw [taskSameRowsBinaryFunctionTerm_freeVariables, hleftShift]
    simp
  have hotherVars : otherIndexTerm.freeVariables ⊆ {0} := by
    unfold otherIndexTerm atomicRowEqOtherLeftBitIndexTerm
    change
      (Semiterm.func Language.Add.add
        ![Rew.shift (paMulTerm otherLeftTerm widthTerm),
          (&0 : ValuationTerm)]).freeVariables ⊆ {0}
    rw [taskSameRowsBinaryFunctionTerm_freeVariables, hotherShift]
    simp
  have hvalueClosed : valueTerm.freeVariables = ∅ := by
    unfold valueTerm atomicRowEqBitValueTerm
    exact shiftedTerm_freeVariables_eq_empty_of_closed tokenTableTerm
      htableClosed
  have hleftValue :
      termValue branchValuation leftIndexTerm =
        termValue valuation leftTerm * termValue valuation widthTerm +
          bitIndex := by
    unfold leftIndexTerm atomicRowEqLeftBitIndexTerm branchValuation
    rw [taskSameRowsTermValue_languageAdd, termValue_shift,
      taskSameRowsTermValue_paMulTerm, termValue_fvar,
      extendValuation_zero]
  have hotherValue :
      termValue branchValuation otherIndexTerm =
        termValue valuation otherLeftTerm * termValue valuation widthTerm +
          bitIndex := by
    unfold otherIndexTerm atomicRowEqOtherLeftBitIndexTerm branchValuation
    rw [taskSameRowsTermValue_languageAdd, termValue_shift,
      taskSameRowsTermValue_paMulTerm, termValue_fvar,
      extendValuation_zero]
  have htableValue :
      termValue branchValuation valueTerm =
        termValue valuation tokenTableTerm := by
    unfold valueTerm atomicRowEqBitValueTerm branchValuation
    rw [termValue_shift]
  exact ⟨hleftVars, hotherVars, hvalueClosed, hleftValue, hotherValue,
    htableValue⟩

theorem
    compileBinaryBitLiteralAtAtomicRowClosedTermsPayloadPolynomial_le_fixed
    (expected useOther : Bool) (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (width leftValue otherLeftValue numericBound bitBound termBound
      bitIndex : Nat)
    (hwidthValue : termValue valuation widthTerm = width)
    (hleftValue : termValue valuation leftTerm = leftValue)
    (hotherValue :
      termValue valuation otherLeftTerm = otherLeftValue)
    (hwidth : width <= numericBound)
    (hleft : leftValue <= numericBound)
    (hother : otherLeftValue <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize :
      Nat.size (termValue valuation tokenTableTerm) <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode : (binaryTermCode widthTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode :
      (binaryTermCode otherLeftTerm).length <= termBound) :
    let branchValuation := extendValuation bitIndex valuation
    let indexTerm := if useOther then
      atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm else
      atomicRowEqLeftBitIndexTerm widthTerm leftTerm
    let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
    compileBinaryBitLiteralAtValuationPayloadPolynomial expected
        branchValuation indexTerm valueTerm <=
      taskSameRowsAtomicRowBitLiteralFixedPayloadPolynomial numericBound
        bitBound termBound := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let indexTerm := if useOther then otherIndexTerm else leftIndexTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  have hdata := atomicRowEqBitTerms_closedTerm_data valuation tokenTableTerm
    widthTerm leftTerm otherLeftTerm bitIndex htableClosed hwidthClosed
    hleftClosed hotherClosed
  have hcodes := atomicRowEqBitTerms_code_le_closedTerms tokenTableTerm
    widthTerm leftTerm otherLeftTerm termBound htableCode hwidthCode
    hleftCode hotherCode
  have hindexVars : indexTerm.freeVariables ⊆ {0} := by
    dsimp only [indexTerm]
    split
    · simpa only [otherIndexTerm] using hdata.2.1
    · simpa only [leftIndexTerm] using hdata.1
  have hvalueClosed : valueTerm.freeVariables = ∅ := by
    simpa only [valueTerm] using hdata.2.2.1
  have hcard :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4 := by
    rw [hvalueClosed, Finset.union_empty]
    exact (Finset.card_le_card hindexVars).trans (by simp)
  have hvalues : ∀ coordinate,
      coordinate ∈ indexTerm.freeVariables ∪ valueTerm.freeVariables ->
        branchValuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    rw [hvalueClosed, Finset.union_empty] at hcoordinate
    have hzero := hindexVars hcoordinate
    simp only [Finset.mem_singleton] at hzero
    subst coordinate
    simp only [branchValuation, extendValuation_zero]
    omega
  have hindexCode :
      (binaryTermCode indexTerm).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound := by
    dsimp only [indexTerm]
    split
    · simpa only [otherIndexTerm] using hcodes.2.1
    · simpa only [leftIndexTerm] using hcodes.1
  have hvalueCode :
      (binaryTermCode valueTerm).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound := by
    simpa only [valueTerm] using hcodes.2.2
  have hindexValue :
      termValue branchValuation indexTerm <
        atomicRowEqBitPositionTraceWidth numericBound := by
    have hpositions := atomicRowEqBitPositions_lt_traceWidth width leftValue
      otherLeftValue numericBound bitIndex hwidth hleft hother hbitIndex
    dsimp only [indexTerm]
    split
    · rw [show termValue branchValuation otherIndexTerm =
          otherLeftValue * width + bitIndex by
        simpa only [otherIndexTerm, hotherValue, hwidthValue] using
          hdata.2.2.2.2.1]
      exact hpositions.2
    · rw [show termValue branchValuation leftIndexTerm =
          leftValue * width + bitIndex by
        simpa only [leftIndexTerm, hleftValue, hwidthValue] using
          hdata.2.2.2.1]
      exact hpositions.1
  have hvalueSize :
      Nat.size (termValue branchValuation valueTerm) <= bitBound := by
    rw [show termValue branchValuation valueTerm =
      termValue valuation tokenTableTerm by
        simpa only [valueTerm] using hdata.2.2.2.2.2]
    exact htableSize
  exact compileBinaryBitLiteralAtValuationPayloadPolynomial_le_fixed
    expected branchValuation indexTerm valueTerm numericBound
    (taskSameRowsAtomicRowBitTermCodePolynomial termBound)
    (atomicRowEqBitPositionTraceWidth numericBound) bitBound hcard hvalues
    hindexCode hvalueCode hindexValue hvalueSize

theorem atomicRowEqBitBranchFormulaCodes_le_closedTerms
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (numericBound termBound : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode : (binaryTermCode widthTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode : (binaryTermCode otherLeftTerm).length <= termBound) :
    let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
    let otherIndexTerm :=
      atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
    let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
    let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
    let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
    let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
    let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
    let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
    let otherFalse :=
      binaryBitAtValuationFormula false otherIndexTerm valueTerm
    let forward := (∼leftAtom ⋎ otherAtom)
    let backward := (∼otherAtom ⋎ leftAtom)
    let target := forward ⋏ backward
    let resource :=
      taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial numericBound
        termBound
    (binaryFormulaCode leftTrue).length <= resource ∧
      (binaryFormulaCode leftFalse).length <= resource ∧
      (binaryFormulaCode otherTrue).length <= resource ∧
      (binaryFormulaCode otherFalse).length <= resource ∧
      (binaryFormulaCode forward).length <= resource ∧
      (binaryFormulaCode backward).length <= resource ∧
      (binaryFormulaCode target).length <= resource := by
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
  let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
  let otherFalse :=
    binaryBitAtValuationFormula false otherIndexTerm valueTerm
  let forward := (∼leftAtom ⋎ otherAtom)
  let backward := (∼otherAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let literalCode :=
    taskSameRowsAtomicRowBitLiteralFormulaCodePolynomial termBound
  let resource :=
    taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial numericBound
      termBound
  have htermCodes := atomicRowEqBitTerms_code_le_closedTerms tokenTableTerm
    widthTerm leftTerm otherLeftTerm termBound htableCode hwidthCode hleftCode
    hotherCode
  have hleftIndex :
      (binaryTermCode leftIndexTerm).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound := by
    simpa only [leftIndexTerm] using htermCodes.1
  have hotherIndex :
      (binaryTermCode otherIndexTerm).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound := by
    simpa only [otherIndexTerm] using htermCodes.2.1
  have hvalue :
      (binaryTermCode valueTerm).length <=
        taskSameRowsAtomicRowBitTermCodePolynomial termBound := by
    simpa only [valueTerm] using htermCodes.2.2
  have hleftTrueRaw := binaryBitLiteralAtTerms_code_length_le_uniform true
    leftIndexTerm valueTerm
    (taskSameRowsAtomicRowBitTermCodePolynomial termBound) hleftIndex hvalue
  have hleftFalseRaw := binaryBitLiteralAtTerms_code_length_le_uniform false
    leftIndexTerm valueTerm
    (taskSameRowsAtomicRowBitTermCodePolynomial termBound) hleftIndex hvalue
  have hotherTrueRaw := binaryBitLiteralAtTerms_code_length_le_uniform true
    otherIndexTerm valueTerm
    (taskSameRowsAtomicRowBitTermCodePolynomial termBound) hotherIndex hvalue
  have hotherFalseRaw := binaryBitLiteralAtTerms_code_length_le_uniform false
    otherIndexTerm valueTerm
    (taskSameRowsAtomicRowBitTermCodePolynomial termBound) hotherIndex hvalue
  have hleftTrue : (binaryFormulaCode leftTrue).length <= literalCode := by
    simpa only [leftTrue, binaryBitAtValuationFormula, literalCode,
      taskSameRowsAtomicRowBitLiteralFormulaCodePolynomial] using hleftTrueRaw
  have hleftFalse : (binaryFormulaCode leftFalse).length <= literalCode := by
    simpa only [leftFalse, binaryBitAtValuationFormula, literalCode,
      taskSameRowsAtomicRowBitLiteralFormulaCodePolynomial] using hleftFalseRaw
  have hotherTrue : (binaryFormulaCode otherTrue).length <= literalCode := by
    simpa only [otherTrue, binaryBitAtValuationFormula, literalCode,
      taskSameRowsAtomicRowBitLiteralFormulaCodePolynomial] using hotherTrueRaw
  have hotherFalse : (binaryFormulaCode otherFalse).length <= literalCode := by
    simpa only [otherFalse, binaryBitAtValuationFormula, literalCode,
      taskSameRowsAtomicRowBitLiteralFormulaCodePolynomial] using
      hotherFalseRaw
  have hforwardRaw := binaryFormulaCode_or_length_le_local
    (∼leftAtom) otherAtom
  have hbackwardRaw := binaryFormulaCode_or_length_le_local
    (∼otherAtom) leftAtom
  have hforward : (binaryFormulaCode forward).length <=
      2 * literalCode + (binaryNatCode 5).length := by
    dsimp only [forward]
    have hleftNeg :
        (binaryFormulaCode (∼leftAtom)).length <= literalCode := by
      simpa [leftFalse, leftAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hleftFalse
    have hotherAtom :
        (binaryFormulaCode otherAtom).length <= literalCode := by
      simpa [otherTrue, otherAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hotherTrue
    omega
  have hbackward : (binaryFormulaCode backward).length <=
      2 * literalCode + (binaryNatCode 5).length := by
    dsimp only [backward]
    have hotherNeg :
        (binaryFormulaCode (∼otherAtom)).length <= literalCode := by
      simpa [otherFalse, otherAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hotherFalse
    have hleftAtom :
        (binaryFormulaCode leftAtom).length <= literalCode := by
      simpa [leftTrue, leftAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hleftTrue
    omega
  have htargetRaw := binaryFormulaCode_and_length_le_local forward backward
  have htarget : (binaryFormulaCode target).length <=
      4 * literalCode + 2 * (binaryNatCode 5).length +
        (binaryNatCode 4).length := by
    dsimp only [target] at htargetRaw ⊢
    omega
  have hliteral : literalCode <= resource := by
    dsimp only [literalCode, resource]
    unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
    omega
  have hforwardResource :
      (binaryFormulaCode forward).length <= resource :=
    hforward.trans (by
      dsimp only [literalCode, resource]
      unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
      omega)
  have hbackwardResource :
      (binaryFormulaCode backward).length <= resource :=
    hbackward.trans (by
      dsimp only [literalCode, resource]
      unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
      omega)
  have htargetResource :
      (binaryFormulaCode target).length <= resource :=
    htarget.trans (by
      dsimp only [literalCode, resource]
      unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
      omega)
  exact ⟨hleftTrue.trans hliteral, hleftFalse.trans hliteral,
    hotherTrue.trans hliteral, hotherFalse.trans hliteral,
    hforwardResource, hbackwardResource, htargetResource⟩

theorem atomicRowEqBitBranchFormulaVariables_subset_singleton_closedTerms
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅) :
    let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
    let otherIndexTerm :=
      atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
    let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
    let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
    let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
    let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
    let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
    let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
    let otherFalse :=
      binaryBitAtValuationFormula false otherIndexTerm valueTerm
    let forward := (∼leftAtom ⋎ otherAtom)
    let backward := (∼otherAtom ⋎ leftAtom)
    let target := forward ⋏ backward
    leftTrue.freeVariables ⊆ {0} ∧ leftFalse.freeVariables ⊆ {0} ∧
      otherTrue.freeVariables ⊆ {0} ∧ otherFalse.freeVariables ⊆ {0} ∧
      forward.freeVariables ⊆ {0} ∧ backward.freeVariables ⊆ {0} ∧
      target.freeVariables ⊆ {0} := by
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
  let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
  let otherFalse :=
    binaryBitAtValuationFormula false otherIndexTerm valueTerm
  let forward := (∼leftAtom ⋎ otherAtom)
  let backward := (∼otherAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  have hterms := atomicRowEqBitTerms_closedTerm_data (fun _ => 0)
    tokenTableTerm widthTerm leftTerm otherLeftTerm 0 htableClosed hwidthClosed
    hleftClosed hotherClosed
  have hleftTerm :
      leftIndexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0} := by
    apply Finset.union_subset
    · simpa only [leftIndexTerm] using hterms.1
    · rw [show valueTerm.freeVariables = ∅ by
        simpa only [valueTerm] using hterms.2.2.1]
      simp
  have hotherTerm :
      otherIndexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0} := by
    apply Finset.union_subset
    · simpa only [otherIndexTerm] using hterms.2.1
    · rw [show valueTerm.freeVariables = ∅ by
        simpa only [valueTerm] using hterms.2.2.1]
      simp
  have hleftTrue : leftTrue.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset true leftIndexTerm
      valueTerm).trans hleftTerm
  have hleftFalse : leftFalse.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset false leftIndexTerm
      valueTerm).trans hleftTerm
  have hotherTrue : otherTrue.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset true otherIndexTerm
      valueTerm).trans hotherTerm
  have hotherFalse : otherFalse.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset false otherIndexTerm
      valueTerm).trans hotherTerm
  have hleftAtom : leftAtom.freeVariables ⊆ {0} := by
    simpa [leftTrue, leftAtom, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hleftTrue
  have hotherAtom : otherAtom.freeVariables ⊆ {0} := by
    simpa [otherTrue, otherAtom, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hotherTrue
  have hforward : forward.freeVariables ⊆ {0} := by
    dsimp only [forward]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset (by simpa using hleftAtom) hotherAtom
  have hbackward : backward.freeVariables ⊆ {0} := by
    dsimp only [backward]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset (by simpa using hotherAtom) hleftAtom
  have htarget : target.freeVariables ⊆ {0} := by
    dsimp only [target]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hforward hbackward
  exact ⟨hleftTrue, hleftFalse, hotherTrue, hotherFalse, hforward,
    hbackward, htarget⟩

private theorem taskSameRowsWeakeningFullAssemblyCost_insert_le_general
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hGamma :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          Gamma <= resource)
    (hformula : (binaryFormulaCode formula).length <= resource) :
    weakeningFullAssemblyCost (insert formula Gamma) <=
      generalContextAssemblyEnvelope resource := by
  apply weakeningFullAssemblyCost_le_general
  have hraw :=
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds.formulaCodeSum_insert_le
      Gamma formula
  unfold generalContextCoordinate
  omega

theorem atomicRowEqBitBranchPublicPayloadEnvelope_le_closedTerms_fixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (width leftValue otherLeftValue numericBound bitBound termBound
      bitIndex : Nat)
    (hwidthValue : termValue valuation widthTerm = width)
    (hleftValue : termValue valuation leftTerm = leftValue)
    (hotherValue : termValue valuation otherLeftTerm = otherLeftValue)
    (hwidth : width <= numericBound)
    (hleft : leftValue <= numericBound)
    (hother : otherLeftValue <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize :
      Nat.size (termValue valuation tokenTableTerm) <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode : (binaryTermCode widthTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode : (binaryTermCode otherLeftTerm).length <= termBound) :
    atomicRowEqBitBranchPublicPayloadEnvelope valuation tokenTableTerm
        widthTerm leftTerm otherLeftTerm bitIndex <=
      taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial numericBound
        bitBound termBound := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
  let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
  let otherFalse :=
    binaryBitAtValuationFormula false otherIndexTerm valueTerm
  let forward := (∼leftAtom ⋎ otherAtom)
  let backward := (∼otherAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let leftTrueContext :=
    valuationContext leftTrue.freeVariables branchValuation
  let leftFalseContext :=
    valuationContext leftFalse.freeVariables branchValuation
  let otherTrueContext :=
    valuationContext otherTrue.freeVariables branchValuation
  let otherFalseContext :=
    valuationContext otherFalse.freeVariables branchValuation
  let forwardContext :=
    valuationContext forward.freeVariables branchValuation
  let backwardContext :=
    valuationContext backward.freeVariables branchValuation
  let targetContext := valuationContext target.freeVariables branchValuation
  let syntaxResource :=
    taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial numericBound
      termBound
  let assemblyResource := generalContextAssemblyEnvelope syntaxResource
  have hliteral := fun (expected useOther : Bool) =>
    compileBinaryBitLiteralAtAtomicRowClosedTermsPayloadPolynomial_le_fixed
      expected useOther valuation tokenTableTerm widthTerm leftTerm
      otherLeftTerm width leftValue otherLeftValue numericBound bitBound
      termBound bitIndex hwidthValue hleftValue hotherValue hwidth hleft
      hother hbitIndex htableSize htableClosed hwidthClosed hleftClosed
      hotherClosed htableCode hwidthCode hleftCode hotherCode
  have hleftTruePayload := hliteral true false
  have hleftFalsePayload := hliteral false false
  have hotherTruePayload := hliteral true true
  have hotherFalsePayload := hliteral false true
  have hcodes := atomicRowEqBitBranchFormulaCodes_le_closedTerms
    tokenTableTerm widthTerm leftTerm otherLeftTerm numericBound termBound
    htableCode hwidthCode hleftCode hotherCode
  have hleftTrueCode :
      (binaryFormulaCode leftTrue).length <= syntaxResource := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
      syntaxResource] using hcodes.1
  have hleftFalseCode :
      (binaryFormulaCode leftFalse).length <= syntaxResource := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
      syntaxResource] using hcodes.2.1
  have hotherTrueCode :
      (binaryFormulaCode otherTrue).length <= syntaxResource := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
      syntaxResource] using hcodes.2.2.1
  have hotherFalseCode :
      (binaryFormulaCode otherFalse).length <= syntaxResource := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
      syntaxResource] using hcodes.2.2.2.1
  have hforwardCode :
      (binaryFormulaCode forward).length <= syntaxResource := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
      syntaxResource] using hcodes.2.2.2.2.1
  have hbackwardCode :
      (binaryFormulaCode backward).length <= syntaxResource := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
      syntaxResource] using hcodes.2.2.2.2.2.1
  have htargetCode :
      (binaryFormulaCode target).length <= syntaxResource := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
      syntaxResource] using hcodes.2.2.2.2.2.2
  have hvars :=
    atomicRowEqBitBranchFormulaVariables_subset_singleton_closedTerms
      tokenTableTerm widthTerm leftTerm otherLeftTerm htableClosed hwidthClosed
      hleftClosed hotherClosed
  have hleftTrueVars : leftTrue.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.1
  have hleftFalseVars : leftFalse.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.1
  have hotherTrueVars : otherTrue.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.1
  have hotherFalseVars : otherFalse.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.1
  have hforwardVars : forward.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.2.1
  have hbackwardVars : backward.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.2.2.1
  have htargetVars : target.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.2.2.2
  have hbranchZero : branchValuation 0 <= numericBound := by
    simp only [branchValuation, extendValuation_zero]
    omega
  have hcontext :
      ∀ formula : ValuationFormula, formula.freeVariables ⊆ {0} ->
        FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
            (valuationContext formula.freeVariables branchValuation) <=
          syntaxResource := by
    intro formula hformula
    have hraw :=
      valuationContextFormulaCodeSum_le_atomicRowEqBitEnvelope branchValuation
        formula.freeVariables numericBound hformula hbranchZero
    apply hraw.trans
    dsimp only [syntaxResource]
    unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
    omega
  have hleftTrueContext := hcontext leftTrue hleftTrueVars
  have hleftFalseContext := hcontext leftFalse hleftFalseVars
  have hotherTrueContext := hcontext otherTrue hotherTrueVars
  have hotherFalseContext := hcontext otherFalse hotherFalseVars
  have hforwardContext := hcontext forward hforwardVars
  have hbackwardContext := hcontext backward hbackwardVars
  have htargetContext := hcontext target htargetVars
  have hweakLeftTrue :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general leftTrueContext
      leftTrue syntaxResource hleftTrueContext hleftTrueCode
  have hweakLeftFalse :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general leftFalseContext
      leftFalse syntaxResource hleftFalseContext hleftFalseCode
  have hweakOtherTrue :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general otherTrueContext
      otherTrue syntaxResource hotherTrueContext hotherTrueCode
  have hweakOtherFalse :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general otherFalseContext
      otherFalse syntaxResource hotherFalseContext hotherFalseCode
  have hweakLeftFalseForward :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general forwardContext
      leftFalse syntaxResource hforwardContext hleftFalseCode
  have hweakOtherTrueForward :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general forwardContext
      otherTrue syntaxResource hforwardContext hotherTrueCode
  have hweakOtherFalseBackward :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general backwardContext
      otherFalse syntaxResource hbackwardContext hotherFalseCode
  have hweakLeftTrueBackward :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general backwardContext
      leftTrue syntaxResource hbackwardContext hleftTrueCode
  have hdisjunctionForward := disjunctionFullAssemblyCost_le_general
    forwardContext (∼leftAtom) otherAtom syntaxResource (by
      dsimp only [syntaxResource]
      unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
      omega) hforwardContext (by
        simpa [leftFalse, leftAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hleftFalseCode) (by
        simpa [otherTrue, otherAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hotherTrueCode) (by
        simpa only [forward] using hforwardCode)
  have hdisjunctionBackward := disjunctionFullAssemblyCost_le_general
    backwardContext (∼otherAtom) leftAtom syntaxResource (by
      dsimp only [syntaxResource]
      unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
      omega) hbackwardContext (by
        simpa [otherFalse, otherAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hotherFalseCode) (by
        simpa [leftTrue, leftAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hleftTrueCode) (by
        simpa only [backward] using hbackwardCode)
  have hweakForwardTarget :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general targetContext
      forward syntaxResource htargetContext hforwardCode
  have hweakBackwardTarget :=
    taskSameRowsWeakeningFullAssemblyCost_insert_le_general targetContext
      backward syntaxResource htargetContext hbackwardCode
  have hconjunction := conjunctionFullAssemblyCost_le_general targetContext
    forward backward syntaxResource (by
      dsimp only [syntaxResource]
      unfold taskSameRowsAtomicRowBitBranchAssemblySyntaxPolynomial
      omega) htargetContext hforwardCode hbackwardCode htargetCode
  simp only [Bool.false_eq_true, ↓reduceIte] at hleftTruePayload
  simp only [Bool.false_eq_true, ↓reduceIte] at hleftFalsePayload
  simp only [↓reduceIte] at hotherTruePayload
  simp only [↓reduceIte] at hotherFalsePayload
  unfold atomicRowEqBitBranchPublicPayloadEnvelope
    taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial
  dsimp only [branchValuation, leftIndexTerm, otherIndexTerm, valueTerm,
    leftAtom, otherAtom, leftTrue, leftFalse, otherTrue, otherFalse, forward,
    backward, target, leftTrueContext, leftFalseContext, otherTrueContext,
    otherFalseContext, forwardContext, backwardContext, targetContext,
    syntaxResource, assemblyResource] at *
  omega

theorem atomicRowEqBitBranchPublicPayloadSum_le_closedTerms_fixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (width leftValue otherLeftValue numericBound bitBound termBound : Nat)
    (hwidthValue : termValue valuation widthTerm = width)
    (hleftValue : termValue valuation leftTerm = leftValue)
    (hotherValue : termValue valuation otherLeftTerm = otherLeftValue)
    (hwidth : width <= numericBound)
    (hleft : leftValue <= numericBound)
    (hother : otherLeftValue <= numericBound)
    (htableSize :
      Nat.size (termValue valuation tokenTableTerm) <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode : (binaryTermCode widthTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode : (binaryTermCode otherLeftTerm).length <= termBound) :
    atomicRowEqBitBranchPublicPayloadSum valuation tokenTableTerm widthTerm
        leftTerm otherLeftTerm <=
      taskSameRowsAtomicRowBitBranchPublicPayloadSumFixedPolynomial
        numericBound bitBound termBound := by
  unfold atomicRowEqBitBranchPublicPayloadSum
  rw [hwidthValue]
  calc
    (∑ bitIndex : Fin width,
        atomicRowEqBitBranchPublicPayloadEnvelope valuation tokenTableTerm
          widthTerm leftTerm otherLeftTerm bitIndex) <=
      ∑ _bitIndex : Fin width,
        taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial numericBound
          bitBound termBound := by
            apply Finset.sum_le_sum
            intro bitIndex _
            exact
              atomicRowEqBitBranchPublicPayloadEnvelope_le_closedTerms_fixed
                valuation tokenTableTerm widthTerm leftTerm otherLeftTerm width
                leftValue otherLeftValue numericBound bitBound termBound
                bitIndex hwidthValue hleftValue hotherValue hwidth hleft hother
                bitIndex.isLt htableSize htableClosed hwidthClosed hleftClosed
                hotherClosed htableCode hwidthCode hleftCode hotherCode
    _ = width *
        taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial numericBound
          bitBound termBound := by simp
    _ <= numericBound *
        taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial numericBound
          bitBound termBound :=
      Nat.mul_le_mul_right
        (taskSameRowsAtomicRowBitBranchFixedPayloadPolynomial numericBound
          bitBound termBound) hwidth
    _ = taskSameRowsAtomicRowBitBranchPublicPayloadSumFixedPolynomial
        numericBound bitBound termBound := by rfl

private theorem taskSameRowsFiniteCaseFormulaEnvelope_mono
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

private theorem taskSameRowsBoundedUniversalClosedFormulaEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    boundedUniversalClosedFormulaEnvelope small <=
      boundedUniversalClosedFormulaEnvelope large := by
  have hseed : boundedUniversalSyntaxSeed small <=
      boundedUniversalSyntaxSeed large := by
    unfold boundedUniversalSyntaxSeed
    omega
  have hbody := substitutionFormulaCodeEnvelope_mono_local hseed hseed
  have hcase := taskSameRowsFiniteCaseFormulaEnvelope_mono
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) hbound
  unfold boundedUniversalClosedFormulaEnvelope
    boundedUniversalClosedBodyCodeEnvelope
  omega

theorem atomicRowEqBitBody_freeVariables_eq_empty_closedTerms
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅) :
    (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
      otherLeftTerm).freeVariables = ∅ := by
  let leftProduct := paMulTerm leftTerm widthTerm
  let otherProduct := paMulTerm otherLeftTerm widthTerm
  let leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift leftProduct, #0]
  let otherIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift otherProduct, #0]
  let tableValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift tokenTableTerm
  have hleftProduct : leftProduct.freeVariables = ∅ := by
    dsimp only [leftProduct]
    rw [taskSameRowsPaMulTerm_freeVariables, hleftClosed, hwidthClosed]
    simp
  have hotherProduct : otherProduct.freeVariables = ∅ := by
    dsimp only [otherProduct]
    rw [taskSameRowsPaMulTerm_freeVariables, hotherClosed, hwidthClosed]
    simp
  have hleftShift : (Rew.bShift leftProduct).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty leftProduct hleftProduct
  have hotherShift : (Rew.bShift otherProduct).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty otherProduct hotherProduct
  have hleftIndex : leftIndex.freeVariables = ∅ := by
    dsimp only [leftIndex]
    rw [taskSameRowsBinaryFunctionTerm_freeVariables, hleftShift]
    simp
  have hotherIndex : otherIndex.freeVariables = ∅ := by
    dsimp only [otherIndex]
    rw [taskSameRowsBinaryFunctionTerm_freeVariables, hotherShift]
    simp
  have htableValue : tableValue.freeVariables = ∅ := by
    dsimp only [tableValue]
    exact bShift_freeVariables_eq_empty_of_empty tokenTableTerm htableClosed
  have hleftAtom :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      bitDef.val ![leftIndex, tableValue] (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hleftIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact htableValue
            | succ coordinate => exact Fin.elim0 coordinate)
  have hotherAtom :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      bitDef.val ![otherIndex, tableValue] (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hotherIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact htableValue
            | succ coordinate => exact Fin.elim0 coordinate)
  unfold atomicRowEqBitBody binaryBitAtomAtTerms
  dsimp only [leftProduct, otherProduct, leftIndex, otherIndex,
    tableValue] at hleftAtom hotherAtom ⊢
  simp only [LogicalConnective.iff,
    LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_imp,
    hleftAtom, hotherAtom, Finset.empty_union]

theorem atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_closedTerms
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅) :
    (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm)
      (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
        otherLeftTerm)).freeVariables = ∅ := by
  have hshiftWidth : (Rew.bShift widthTerm).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty widthTerm hwidthClosed
  have hbody :=
    atomicRowEqBitBody_freeVariables_eq_empty_closedTerms tokenTableTerm
      widthTerm leftTerm otherLeftTerm htableClosed hwidthClosed hleftClosed
      hotherClosed
  have htermBound :
      (termBoundFormula
        (Rew.bShift widthTerm)).freeVariables = ∅ := by
    unfold termBoundFormula finiteCaseLessThanFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => simp at hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈ (Rew.bShift widthTerm).freeVariables at hcoordinate
            rw [hshiftWidth] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp,
    htermBound, hbody, Finset.empty_union]

theorem
    atomicRowEqBranchesTransparentStructuralEnvelope_le_closedTerms_fixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (width leftValue otherLeftValue numericBound bitBound termBound : Nat)
    (hwidthValue : termValue valuation widthTerm = width)
    (hleftValue : termValue valuation leftTerm = leftValue)
    (hotherValue : termValue valuation otherLeftTerm = otherLeftValue)
    (hwidth : width <= numericBound)
    (hleft : leftValue <= numericBound)
    (hother : otherLeftValue <= numericBound)
    (htableSize :
      Nat.size (termValue valuation tokenTableTerm) <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode : (binaryTermCode widthTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode : (binaryTermCode otherLeftTerm).length <= termBound) :
    atomicRowEqBranchesTransparentStructuralEnvelope valuation tokenTableTerm
        widthTerm leftTerm otherLeftTerm <=
      taskSameRowsAtomicRowBranchesFixedPayloadPolynomial numericBound
        bitBound termBound := by
  let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
    otherLeftTerm
  let outerFormula :=
    ∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let leafResource :=
    atomicRowEqBitBranchPublicPayloadSum valuation tokenTableTerm widthTerm
      leftTerm otherLeftTerm
  let bodyCode := taskSameRowsAtomicRowBodyCodePolynomial termBound
  let formulaResource :=
    taskSameRowsAtomicRowBranchesFormulaCodePolynomial numericBound termBound
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_closedTerms
        tokenTableTerm widthTerm leftTerm otherLeftTerm htableClosed
        hwidthClosed hleftClosed hotherClosed
  have hGammaCard :
      ((valuationContext outerVariables valuation).image
        Rewriting.shift).card <= 1 := by
    rw [houter]
    simp [valuationContext]
  have hraw :=
    hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
      width outerVariables valuation body leafResource hGammaCard
      (caseCount := width) le_rfl
  have hleaf : leafResource <=
      taskSameRowsAtomicRowBitBranchPublicPayloadSumFixedPolynomial
        numericBound bitBound termBound := by
    dsimp only [leafResource]
    exact atomicRowEqBitBranchPublicPayloadSum_le_closedTerms_fixed valuation
      tokenTableTerm widthTerm leftTerm otherLeftTerm width leftValue
      otherLeftValue numericBound bitBound termBound hwidthValue hleftValue
      hotherValue hwidth hleft hother htableSize htableClosed hwidthClosed
      hleftClosed hotherClosed htableCode hwidthCode hleftCode hotherCode
  have hbodyCode : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode]
    exact atomicRowEqBitBody_code_length_le_closedTerms tokenTableTerm widthTerm
      leftTerm otherLeftTerm termBound htableCode hwidthCode hleftCode
      hotherCode
  have hsyntax :
      explicitHybridUniversalSyntaxResource width body <=
        numericBound + bodyCode := by
    unfold explicitHybridUniversalSyntaxResource
    omega
  have hclosed :=
    taskSameRowsBoundedUniversalClosedFormulaEnvelope_mono hsyntax
  have hexplicit :
      explicitHybridUniversalFormulaEnvelope width body <=
        formulaResource := by
    unfold explicitHybridUniversalFormulaEnvelope
    dsimp only [formulaResource, bodyCode,
      taskSameRowsAtomicRowBranchesFormulaCodePolynomial] at hclosed ⊢
    exact Nat.add_le_add hclosed (Nat.mul_le_mul_left 2 hbodyCode)
  have hcontextual :
      contextualHybridUniversalFormulaEnvelope
          ((valuationContext outerVariables valuation).image Rewriting.shift)
          width body <= formulaResource := by
    rw [houter]
    simp only [valuationContext, Finset.image_empty,
      contextualHybridUniversalFormulaEnvelope,
      contextualHybridUniversalFormulaCodeSum, Finset.sum_empty, Nat.add_zero]
    exact hexplicit
  have hlocal := smallContextAssemblyEnvelope_mono_local hcontextual
  have hinner :
      leafResource +
          3 * contextualHybridUniversalLocalPayloadEnvelope
            ((valuationContext outerVariables valuation).image Rewriting.shift)
              width body <=
        taskSameRowsAtomicRowBitBranchPublicPayloadSumFixedPolynomial
            numericBound bitBound termBound +
          3 * smallContextAssemblyEnvelope formulaResource := by
    unfold contextualHybridUniversalLocalPayloadEnvelope at hlocal ⊢
    omega
  have hfactor : width + 1 <= numericBound + 1 := by omega
  have hproduct := Nat.mul_le_mul hfactor hinner
  unfold atomicRowEqBranchesTransparentStructuralEnvelope
    taskSameRowsAtomicRowBranchesFixedPayloadPolynomial
  dsimp only [body, outerFormula, outerVariables, leafResource, bodyCode,
    formulaResource] at hraw hproduct ⊢
  rw [hwidthValue]
  exact hraw.trans hproduct

theorem atomicRowEqContextualBranchesResource_le_closedTerms_fixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (width leftValue otherLeftValue numericBound bitBound termBound : Nat)
    (hwidthValue : termValue valuation widthTerm = width)
    (hleftValue : termValue valuation leftTerm = leftValue)
    (hotherValue : termValue valuation otherLeftTerm = otherLeftValue)
    (hwidth : width <= numericBound)
    (hleft : leftValue <= numericBound)
    (hother : otherLeftValue <= numericBound)
    (htableSize :
      Nat.size (termValue valuation tokenTableTerm) <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode : (binaryTermCode widthTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode : (binaryTermCode otherLeftTerm).length <= termBound) :
    let body :=
      atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
    let outerFormula :=
      ∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body
    let Gamma := valuationContext outerFormula.freeVariables valuation
    contextualBranchesUnderBoundPayloadEnvelope
        (Gamma.image Rewriting.shift) width (Rewriting.free body)
        (atomicRowEqBranchesTransparentStructuralEnvelope valuation
          tokenTableTerm widthTerm leftTerm otherLeftTerm) <=
      taskSameRowsAtomicRowContextualBranchesFixedPayloadPolynomial
        numericBound bitBound termBound := by
  let body :=
    atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let outerFormula :=
    ∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let shiftedGamma := Gamma.image Rewriting.shift
  let syntaxCode :=
    numericBound + taskSameRowsAtomicRowBodyCodePolynomial termBound
  let formulaCode :=
    taskSameRowsAtomicRowBranchesFormulaCodePolynomial numericBound termBound
  let caseResource :=
    atomicRowEqBranchesTransparentStructuralEnvelope valuation tokenTableTerm
      widthTerm leftTerm otherLeftTerm
  let caseBound :=
    taskSameRowsAtomicRowBranchesFixedPayloadPolynomial numericBound bitBound
      termBound
  let targetFormula := Rewriting.free body
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_closedTerms
        tokenTableTerm widthTerm leftTerm otherLeftTerm htableClosed
        hwidthClosed hleftClosed hotherClosed
  have hshiftedEmpty : shiftedGamma = ∅ := by
    dsimp only [shiftedGamma, Gamma]
    rw [houter]
    simp [valuationContext]
  have hboundSyntax : width <= syntaxCode := by
    dsimp only [syntaxCode]
    omega
  have hclosedLe :
      boundedUniversalClosedFormulaEnvelope syntaxCode <= formulaCode := by
    dsimp only [syntaxCode, formulaCode,
      taskSameRowsAtomicRowBranchesFormulaCodePolynomial]
    omega
  have hbodyCode :
      (binaryFormulaCode body).length <=
        taskSameRowsAtomicRowBodyCodePolynomial termBound := by
    dsimp only [body]
    exact atomicRowEqBitBody_code_length_le_closedTerms tokenTableTerm widthTerm
      leftTerm otherLeftTerm termBound htableCode hwidthCode hleftCode
      hotherCode
  have htargetFree := binaryFormulaCode_free_length_le body
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= formulaCode := by
    dsimp only [targetFormula, formulaCode,
      taskSameRowsAtomicRowBranchesFormulaCodePolynomial]
    omega
  have hGammaCard : shiftedGamma.card <= 1 := by
    rw [hshiftedEmpty]
    simp
  have hGammaBound : FormulaCodeBound shiftedGamma formulaCode := by
    intro formula hformula
    rw [hshiftedEmpty] at hformula
    simp at hformula
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact
      atomicRowEqBranchesTransparentStructuralEnvelope_le_closedTerms_fixed
        valuation tokenTableTerm widthTerm leftTerm otherLeftTerm width
        leftValue otherLeftValue numericBound bitBound termBound hwidthValue
        hleftValue hotherValue hwidth hleft hother htableSize htableClosed
        hwidthClosed hleftClosed hotherClosed htableCode hwidthCode hleftCode
        hotherCode
  change contextualBranchesUnderBoundPayloadEnvelope shiftedGamma width
      targetFormula caseResource <= _
  unfold taskSameRowsAtomicRowContextualBranchesFixedPayloadPolynomial
  exact contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly
    shiftedGamma width syntaxCode formulaCode caseResource caseBound
    targetFormula hboundSyntax hclosedLe htargetCode hGammaCard hGammaBound
    hcase

theorem
    atomicRowEqUniversalStructuralPayloadEnvelope_le_closedTerms_of_branch
    (valuation : Nat -> Nat)
    (tokenTableTerm leftTerm otherLeftTerm : ValuationTerm)
    (width numericBound bitBound termBound branchBound : Nat)
    (hwidth : width <= numericBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode : (binaryTermCode otherLeftTerm).length <= termBound)
    (hbranch :
      let body := atomicRowEqBitBody tokenTableTerm
        (shortBinaryNumeralTerm width) leftTerm otherLeftTerm
      let outerFormula := ∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm width)) body
      let Gamma := valuationContext outerFormula.freeVariables valuation
      contextualBranchesUnderBoundPayloadEnvelope
          (Gamma.image Rewriting.shift) width (Rewriting.free body)
          (atomicRowEqBranchesTransparentStructuralEnvelope valuation
            tokenTableTerm (shortBinaryNumeralTerm width) leftTerm
            otherLeftTerm) <= branchBound) :
    atomicRowEqUniversalStructuralPayloadEnvelope valuation tokenTableTerm
        (shortBinaryNumeralTerm width) leftTerm otherLeftTerm <=
      taskSameRowsAtomicRowUniversalFixedPayloadPolynomial numericBound
        bitBound termBound branchBound := by
  let widthTerm : ValuationTerm := shortBinaryNumeralTerm width
  let body :=
    atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let boundEqualityResource :=
    compileShiftedBoundEqualityPayloadResource valuation outerVariables
      widthTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) width (Rewriting.free body)
    (atomicRowEqBranchesTransparentStructuralEnvelope valuation
      tokenTableTerm widthTerm leftTerm otherLeftTerm)
  let bodyCode := taskSameRowsAtomicRowBodyCodePolynomial termBound
  let syntaxCode := numericBound + bodyCode
  let scale :=
    taskSameRowsAtomicRowUniversalShellScale numericBound bitBound
  let boundEqualityBound :=
    compileShiftedBoundEqualityFixedPayloadPolynomial scale
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, widthTerm]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_closedTerms
        tokenTableTerm (shortBinaryNumeralTerm width) leftTerm otherLeftTerm
        htableClosed
        (shortBinaryNumeralTerm_freeVariables_eq_empty width)
        hleftClosed hotherClosed
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode, widthTerm]
    exact atomicRowEqBitBody_code_length_le_closedTerms tokenTableTerm
      (shortBinaryNumeralTerm width) leftTerm otherLeftTerm termBound
      htableCode hwidthCode hleftCode hotherCode
  have hsyntax : width <= syntaxCode := by
    dsimp only [syntaxCode, bodyCode]
    omega
  have hbranchFixed : branchResource <= branchBound := by
    dsimp only [branchResource, Gamma, outerVariables, outerFormula, body,
      widthTerm]
    exact hbranch
  have houterSubset : outerVariables ⊆ {0} := by
    rw [houter]
    simp
  have houterValues : ∀ index, index ∈ outerVariables ->
      valuation index <= scale := by
    intro index hindex
    rw [houter] at hindex
    simp at hindex
  have hvalue : termValue valuation widthTerm <= scale := by
    dsimp only [widthTerm, scale]
    simp only [termValue_shortBinaryNumeralTerm]
    unfold taskSameRowsAtomicRowUniversalShellScale
    omega
  have hshortCode :
      (binaryTermCode widthTerm).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    dsimp only [widthTerm]
    exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hcode : (binaryTermCode widthTerm).length <= scale := by
    dsimp only [scale]
    unfold taskSameRowsAtomicRowUniversalShellScale
    omega
  have hboundPublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial valuation
      outerVariables widthTerm hwidthClosed
  have hboundFixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
      valuation outerVariables widthTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial valuation
        outerVariables widthTerm)
      boundEqualityBound scale rfl rfl hwidthClosed houterSubset houterValues
      hvalue hcode
  have hbound : boundEqualityResource <= boundEqualityBound := by
    dsimp only [boundEqualityResource]
    exact hboundPublic.trans hboundFixed
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body width numericBound bitBound syntaxCode bodyCode
      boundEqualityResource branchResource boundEqualityBound branchBound
      hwidth hwidthSize hsyntax hbody hbound hbranchFixed
  simpa only [atomicRowEqUniversalStructuralPayloadEnvelope, body,
    outerFormula, outerVariables, Gamma, boundEqualityResource,
    branchResource, houter, valuationContext, Finset.image_empty,
    termValue_shortBinaryNumeralTerm,
    taskSameRowsAtomicRowUniversalFixedPayloadPolynomial, bodyCode,
    syntaxCode, scale, boundEqualityBound, widthTerm] using hshell

theorem atomicRowEqUniversalStructuralPayloadEnvelope_le_closedTerms_fixed
    (valuation : Nat -> Nat)
    (tokenTableTerm leftTerm otherLeftTerm : ValuationTerm)
    (width leftValue otherLeftValue numericBound bitBound termBound : Nat)
    (hleftValue : termValue valuation leftTerm = leftValue)
    (hotherValue : termValue valuation otherLeftTerm = otherLeftValue)
    (hwidth : width <= numericBound)
    (hleft : leftValue <= numericBound)
    (hother : otherLeftValue <= numericBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htableSize :
      Nat.size (termValue valuation tokenTableTerm) <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hotherClosed : otherLeftTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hotherCode : (binaryTermCode otherLeftTerm).length <= termBound) :
    atomicRowEqUniversalStructuralPayloadEnvelope valuation tokenTableTerm
        (shortBinaryNumeralTerm width) leftTerm otherLeftTerm <=
      taskSameRowsAtomicRowUniversalFullyFixedPayloadPolynomial numericBound
        bitBound termBound := by
  let branchBound :=
    taskSameRowsAtomicRowContextualBranchesFixedPayloadPolynomial numericBound
      bitBound termBound
  have hwidthValue :
      termValue valuation (shortBinaryNumeralTerm width) = width :=
    termValue_shortBinaryNumeralTerm valuation width
  have hbranch :=
    atomicRowEqContextualBranchesResource_le_closedTerms_fixed valuation
      tokenTableTerm (shortBinaryNumeralTerm width) leftTerm otherLeftTerm
      width leftValue otherLeftValue numericBound bitBound termBound
      hwidthValue hleftValue hotherValue hwidth hleft hother htableSize
      htableClosed (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      hleftClosed hotherClosed htableCode hwidthCode hleftCode hotherCode
  have hshell :=
    atomicRowEqUniversalStructuralPayloadEnvelope_le_closedTerms_of_branch
      valuation tokenTableTerm leftTerm otherLeftTerm width numericBound
      bitBound termBound branchBound hwidth hwidthSize htableClosed
      hleftClosed hotherClosed htableCode hwidthCode hleftCode hotherCode
      (by simpa only [branchBound] using hbranch)
  simpa only [taskSameRowsAtomicRowUniversalFullyFixedPayloadPolynomial,
    branchBound] using hshell

theorem
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_closedTerms_fixed
    (valuation : Nat -> Nat)
    (tokenTableTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm)
    (width leftValue otherLeftValue numericBound bitBound termBound : Nat)
    (hleftValue : termValue valuation leftTerm = leftValue)
    (hotherLeftValue :
      termValue valuation otherLeftTerm = otherLeftValue)
    (hwidth : width <= numericBound)
    (hleft : leftValue <= numericBound)
    (hotherLeft : otherLeftValue <= numericBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htableSize :
      Nat.size (termValue valuation tokenTableTerm) <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hrightClosed : rightTerm.freeVariables = ∅)
    (hotherLeftClosed : otherLeftTerm.freeVariables = ∅)
    (hotherRightClosed : otherRightTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termBound)
    (htokenCountCode :
      (binaryTermCode tokenCountTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hrightCode : (binaryTermCode rightTerm).length <= termBound)
    (hotherLeftCode :
      (binaryTermCode otherLeftTerm).length <= termBound)
    (hotherRightCode :
      (binaryTermCode otherRightTerm).length <= termBound) :
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        tokenTableTerm (shortBinaryNumeralTerm width) tokenCountTerm leftTerm
        rightTerm otherLeftTerm otherRightTerm <=
      taskSameRowsCompactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound
        bitBound termBound := by
  let widthTerm : ValuationTerm := shortBinaryNumeralTerm width
  let leftSumTerm : ValuationTerm := ‘!!leftTerm + 1’
  let otherSumTerm : ValuationTerm := ‘!!otherLeftTerm + 1’
  let leftStrictFormula : ValuationFormula :=
    “!!leftTerm < !!tokenCountTerm”
  let leftSuccessorFormula : ValuationFormula :=
    “!!rightTerm = !!leftSumTerm”
  let otherStrictFormula : ValuationFormula :=
    “!!otherLeftTerm < !!tokenCountTerm”
  let otherSuccessorFormula : ValuationFormula :=
    “!!otherRightTerm = !!otherSumTerm”
  let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
    otherLeftTerm
  let universalFormula : ValuationFormula := body.ballLT widthTerm
  let formula45 := otherSuccessorFormula ⋏ universalFormula
  let formula345 := otherStrictFormula ⋏ formula45
  let formula2345 := leftSuccessorFormula ⋏ formula345
  let totalFormula := leftStrictFormula ⋏ formula2345
  let termCode := taskSameRowsAtomicRowOuterTermCodePolynomial termBound
  let atomicCode :=
    taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial termBound
  let universalCode :=
    taskSameRowsAtomicRowOuterUniversalFormulaCodePolynomial numericBound
      bitBound termBound
  let syntaxResource :=
    taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
      termBound
  let leftStrictResource := atomicRowEqStrictStructuralPayloadResource
    valuation leftTerm tokenCountTerm
  let leftSuccessorResource := atomicRowEqSuccessorStructuralPayloadResource
    valuation leftTerm rightTerm
  let otherStrictResource := atomicRowEqStrictStructuralPayloadResource
    valuation otherLeftTerm tokenCountTerm
  let otherSuccessorResource := atomicRowEqSuccessorStructuralPayloadResource
    valuation otherLeftTerm otherRightTerm
  let universalResource := atomicRowEqUniversalStructuralPayloadEnvelope
    valuation tokenTableTerm widthTerm leftTerm otherLeftTerm
  let atomicResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound termCode
  let universalFixed :=
    taskSameRowsAtomicRowUniversalFullyFixedPayloadPolynomial numericBound
      bitBound termBound
  have hleftSumClosed : leftSumTerm.freeVariables = ∅ := by
    dsimp only [leftSumTerm]
    rw [taskSameRowsArithmeticAddTerm_eq_func,
      taskSameRowsBinaryFunctionTerm_freeVariables, hleftClosed,
      taskSameRowsOne_closed]
    simp
  have hotherSumClosed : otherSumTerm.freeVariables = ∅ := by
    dsimp only [otherSumTerm]
    rw [taskSameRowsArithmeticAddTerm_eq_func,
      taskSameRowsBinaryFunctionTerm_freeVariables, hotherLeftClosed,
      taskSameRowsOne_closed]
    simp
  have hleftSumCode : (binaryTermCode leftSumTerm).length <= termCode := by
    have hraw := paAddTerm_code_length_le leftTerm (‘1’ : ValuationTerm)
    dsimp only [leftSumTerm, termCode]
    rw [taskSameRowsArithmeticAddTerm_eq_paAddTerm]
    exact hraw.trans (by
      unfold taskSameRowsAtomicRowOuterTermCodePolynomial
      omega)
  have hotherSumCode :
      (binaryTermCode otherSumTerm).length <= termCode := by
    have hraw := paAddTerm_code_length_le otherLeftTerm (‘1’ : ValuationTerm)
    dsimp only [otherSumTerm, termCode]
    rw [taskSameRowsArithmeticAddTerm_eq_paAddTerm]
    exact hraw.trans (by
      unfold taskSameRowsAtomicRowOuterTermCodePolynomial
      omega)
  have hterm : ∀ term : ValuationTerm,
      (binaryTermCode term).length <= termBound ->
        (binaryTermCode term).length <= termCode := by
    intro term hcode
    dsimp only [termCode]
    unfold taskSameRowsAtomicRowOuterTermCodePolynomial
    omega
  have hleftStrictResource : leftStrictResource <= atomicResource := by
    dsimp only [leftStrictResource, atomicResource]
    unfold atomicRowEqStrictStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.ORing.Rel.lt leftTerm tokenCountTerm numericBound termCode
      hleftClosed htokenCountClosed (hterm leftTerm hleftCode)
      (hterm tokenCountTerm htokenCountCode)
  have hleftSuccessorResource :
      leftSuccessorResource <= atomicResource := by
    dsimp only [leftSuccessorResource, atomicResource]
    unfold atomicRowEqSuccessorStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.Eq.eq rightTerm leftSumTerm numericBound termCode
      hrightClosed hleftSumClosed (hterm rightTerm hrightCode) hleftSumCode
  have hotherStrictResource : otherStrictResource <= atomicResource := by
    dsimp only [otherStrictResource, atomicResource]
    unfold atomicRowEqStrictStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.ORing.Rel.lt otherLeftTerm tokenCountTerm numericBound termCode
      hotherLeftClosed htokenCountClosed (hterm otherLeftTerm hotherLeftCode)
      (hterm tokenCountTerm htokenCountCode)
  have hotherSuccessorResource :
      otherSuccessorResource <= atomicResource := by
    dsimp only [otherSuccessorResource, atomicResource]
    unfold atomicRowEqSuccessorStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.Eq.eq otherRightTerm otherSumTerm numericBound termCode
      hotherRightClosed hotherSumClosed
      (hterm otherRightTerm hotherRightCode) hotherSumCode
  have huniversalResource : universalResource <= universalFixed := by
    dsimp only [universalResource, universalFixed, widthTerm]
    exact
      atomicRowEqUniversalStructuralPayloadEnvelope_le_closedTerms_fixed
        valuation tokenTableTerm leftTerm otherLeftTerm width leftValue
        otherLeftValue numericBound bitBound termBound hleftValue
        hotherLeftValue hwidth hleft hotherLeft hwidthSize htableSize
        htableClosed hleftClosed hotherLeftClosed htableCode hwidthCode
        hleftCode hotherLeftCode
  have hleftStrictCode :
      (binaryFormulaCode leftStrictFormula).length <= atomicCode := by
    dsimp only [leftStrictFormula, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.lt_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt leftTerm
        tokenCountTerm termCode (hterm leftTerm hleftCode)
        (hterm tokenCountTerm htokenCountCode))
  have hleftSuccessorCode :
      (binaryFormulaCode leftSuccessorFormula).length <= atomicCode := by
    dsimp only [leftSuccessorFormula, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.eq_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq rightTerm
        leftSumTerm termCode (hterm rightTerm hrightCode) hleftSumCode)
  have hotherStrictCode :
      (binaryFormulaCode otherStrictFormula).length <= atomicCode := by
    dsimp only [otherStrictFormula, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.lt_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt otherLeftTerm
        tokenCountTerm termCode (hterm otherLeftTerm hotherLeftCode)
        (hterm tokenCountTerm htokenCountCode))
  have hotherSuccessorCode :
      (binaryFormulaCode otherSuccessorFormula).length <= atomicCode := by
    dsimp only [otherSuccessorFormula, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.eq_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq otherRightTerm
        otherSumTerm termCode (hterm otherRightTerm hotherRightCode)
        hotherSumCode)
  have hbodyCode :
      (binaryFormulaCode body).length <=
        taskSameRowsAtomicRowBodyCodePolynomial termBound := by
    dsimp only [body, widthTerm]
    exact atomicRowEqBitBody_code_length_le_closedTerms tokenTableTerm
      (shortBinaryNumeralTerm width) leftTerm otherLeftTerm termBound
      htableCode hwidthCode hleftCode hotherLeftCode
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= universalCode := by
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source body width
        numericBound bitBound
        (numericBound + taskSameRowsAtomicRowBodyCodePolynomial termBound)
        (taskSameRowsAtomicRowBodyCodePolynomial termBound) hwidthSize hbodyCode
    have halign :
        (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body) =
          universalFormula := by
      dsimp only [universalFormula]
      rw [termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    dsimp only [universalCode]
    unfold taskSameRowsAtomicRowOuterUniversalFormulaCodePolynomial
    exact hraw
  have hleftStrictClosed : leftStrictFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![leftTerm, tokenCountTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hleftClosed,
      htokenCountClosed]
    simp
  have hleftSuccessorClosed :
      leftSuccessorFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![rightTerm, leftSumTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hrightClosed,
      hleftSumClosed]
    simp
  have hotherStrictClosed : otherStrictFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![otherLeftTerm, tokenCountTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hotherLeftClosed,
      htokenCountClosed]
    simp
  have hotherSuccessorClosed :
      otherSuccessorFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![otherRightTerm, otherSumTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hotherRightClosed,
      hotherSumClosed]
    simp
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    have halign :
        (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body) =
          universalFormula := by
      dsimp only [universalFormula]
      rw [termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    dsimp only [body, widthTerm]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_closedTerms
        tokenTableTerm (shortBinaryNumeralTerm width) leftTerm otherLeftTerm
        htableClosed (shortBinaryNumeralTerm_freeVariables_eq_empty width)
        hleftClosed hotherLeftClosed
  have htotalClosed : totalFormula.freeVariables = ∅ := by
    dsimp only [totalFormula, formula2345, formula345, formula45]
    simp only [LO.FirstOrder.Semiformula.freeVariables_and,
      hleftStrictClosed, hleftSuccessorClosed, hotherStrictClosed,
      hotherSuccessorClosed, huniversalClosed, Finset.empty_union]
  have hcode45Raw :=
    binaryFormulaCode_and_length_le_local otherSuccessorFormula universalFormula
  have hcode345Raw :=
    binaryFormulaCode_and_length_le_local otherStrictFormula formula45
  have hcode2345Raw :=
    binaryFormulaCode_and_length_le_local leftSuccessorFormula formula345
  have hcodeTotalRaw :=
    binaryFormulaCode_and_length_le_local leftStrictFormula formula2345
  have hcode45 :
      (binaryFormulaCode formula45).length <=
        atomicCode + universalCode + (binaryNatCode 4).length := by
    dsimp only [formula45] at hcode45Raw ⊢
    omega
  have hcode345 :
      (binaryFormulaCode formula345).length <=
        2 * atomicCode + universalCode +
          2 * (binaryNatCode 4).length := by
    dsimp only [formula345] at hcode345Raw ⊢
    omega
  have hcode2345 :
      (binaryFormulaCode formula2345).length <=
        3 * atomicCode + universalCode +
          3 * (binaryNatCode 4).length := by
    dsimp only [formula2345] at hcode2345Raw ⊢
    omega
  have hcodeTotal :
      (binaryFormulaCode totalFormula).length <=
        4 * atomicCode + universalCode +
          4 * (binaryNatCode 4).length := by
    dsimp only [totalFormula] at hcodeTotalRaw ⊢
    omega
  have htotalCode :
      (binaryFormulaCode totalFormula).length <= syntaxResource := by
    apply hcodeTotal.trans
    dsimp only [syntaxResource]
    unfold taskSameRowsAtomicRowAssemblySyntaxPolynomial
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold taskSameRowsAtomicRowAssemblySyntaxPolynomial
    omega
  have hgeneral :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral valuation
      leftStrictFormula leftSuccessorFormula otherStrictFormula
      otherSuccessorFormula universalFormula leftStrictResource
      leftSuccessorResource otherStrictResource otherSuccessorResource
      universalResource syntaxResource hpositive htotalClosed htotalCode
  have hmono :
      hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource
          leftStrictResource leftSuccessorResource otherStrictResource
          otherSuccessorResource universalResource <=
        hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource
          atomicResource atomicResource atomicResource atomicResource
          universalFixed := by
    unfold hybridFiveConjunctionGeneralPayloadEnvelope
      hybridConjunctionGeneralPayloadEnvelope
    omega
  unfold compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope
    taskSameRowsCompactAdditiveAtomicRowEqFixedPayloadPolynomial
  dsimp only [widthTerm, leftSumTerm, otherSumTerm, leftStrictFormula,
    leftSuccessorFormula, otherStrictFormula, otherSuccessorFormula, body,
    universalFormula, formula45, formula345, formula2345, totalFormula,
    termCode, atomicCode, universalCode, syntaxResource, leftStrictResource,
    leftSuccessorResource, otherStrictResource, otherSuccessorResource,
    universalResource, atomicResource, universalFixed] at hgeneral hmono ⊢
  exact hgeneral.trans hmono

theorem compactAdditiveAtomicRowEqAtValuationFormula_closed_code_le_fixed
    (tokenTableTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm)
    (width numericBound bitBound termBound : Nat)
    (hwidthSize : Nat.size width <= bitBound)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hrightClosed : rightTerm.freeVariables = ∅)
    (hotherLeftClosed : otherLeftTerm.freeVariables = ∅)
    (hotherRightClosed : otherRightTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termBound)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termBound)
    (htokenCountCode :
      (binaryTermCode tokenCountTerm).length <= termBound)
    (hleftCode : (binaryTermCode leftTerm).length <= termBound)
    (hrightCode : (binaryTermCode rightTerm).length <= termBound)
    (hotherLeftCode :
      (binaryTermCode otherLeftTerm).length <= termBound)
    (hotherRightCode :
      (binaryTermCode otherRightTerm).length <= termBound) :
    let formula := compactAdditiveAtomicRowEqAtValuationFormula
      tokenTableTerm (shortBinaryNumeralTerm width) tokenCountTerm leftTerm
      rightTerm otherLeftTerm otherRightTerm
    formula.freeVariables = ∅ ∧
      (binaryFormulaCode formula).length <=
        taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
          termBound := by
  let widthTerm : ValuationTerm := shortBinaryNumeralTerm width
  let leftSumTerm : ValuationTerm := ‘!!leftTerm + 1’
  let otherSumTerm : ValuationTerm := ‘!!otherLeftTerm + 1’
  let formula1 : ValuationFormula := “!!leftTerm < !!tokenCountTerm”
  let formula2 : ValuationFormula := “!!rightTerm = !!leftSumTerm”
  let formula3 : ValuationFormula := “!!otherLeftTerm < !!tokenCountTerm”
  let formula4 : ValuationFormula := “!!otherRightTerm = !!otherSumTerm”
  let body :=
    atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let formula5 : ValuationFormula := body.ballLT widthTerm
  let tail45 := formula4 ⋏ formula5
  let tail345 := formula3 ⋏ tail45
  let tail2345 := formula2 ⋏ tail345
  let explicitFormula := formula1 ⋏ tail2345
  let termCode := taskSameRowsAtomicRowOuterTermCodePolynomial termBound
  let atomicCode :=
    taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial termBound
  let universalCode :=
    taskSameRowsAtomicRowOuterUniversalFormulaCodePolynomial numericBound
      bitBound termBound
  let syntaxResource :=
    taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
      termBound
  have hleftSumClosed : leftSumTerm.freeVariables = ∅ := by
    dsimp only [leftSumTerm]
    rw [taskSameRowsArithmeticAddTerm_eq_func,
      taskSameRowsBinaryFunctionTerm_freeVariables, hleftClosed,
      taskSameRowsOne_closed]
    simp
  have hotherSumClosed : otherSumTerm.freeVariables = ∅ := by
    dsimp only [otherSumTerm]
    rw [taskSameRowsArithmeticAddTerm_eq_func,
      taskSameRowsBinaryFunctionTerm_freeVariables, hotherLeftClosed,
      taskSameRowsOne_closed]
    simp
  have hleftSumCode : (binaryTermCode leftSumTerm).length <= termCode := by
    have hraw := paAddTerm_code_length_le leftTerm (‘1’ : ValuationTerm)
    dsimp only [leftSumTerm, termCode]
    rw [taskSameRowsArithmeticAddTerm_eq_paAddTerm]
    exact hraw.trans (by
      unfold taskSameRowsAtomicRowOuterTermCodePolynomial
      omega)
  have hotherSumCode :
      (binaryTermCode otherSumTerm).length <= termCode := by
    have hraw := paAddTerm_code_length_le otherLeftTerm (‘1’ : ValuationTerm)
    dsimp only [otherSumTerm, termCode]
    rw [taskSameRowsArithmeticAddTerm_eq_paAddTerm]
    exact hraw.trans (by
      unfold taskSameRowsAtomicRowOuterTermCodePolynomial
      omega)
  have hterm : ∀ term : ValuationTerm,
      (binaryTermCode term).length <= termBound ->
        (binaryTermCode term).length <= termCode := by
    intro term hcode
    dsimp only [termCode]
    unfold taskSameRowsAtomicRowOuterTermCodePolynomial
    omega
  have hformula1Code :
      (binaryFormulaCode formula1).length <= atomicCode := by
    dsimp only [formula1, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.lt_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt leftTerm
        tokenCountTerm termCode (hterm leftTerm hleftCode)
        (hterm tokenCountTerm htokenCountCode))
  have hformula2Code :
      (binaryFormulaCode formula2).length <= atomicCode := by
    dsimp only [formula2, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.eq_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq rightTerm
        leftSumTerm termCode (hterm rightTerm hrightCode) hleftSumCode)
  have hformula3Code :
      (binaryFormulaCode formula3).length <= atomicCode := by
    dsimp only [formula3, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.lt_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt otherLeftTerm
        tokenCountTerm termCode (hterm otherLeftTerm hotherLeftCode)
        (hterm tokenCountTerm htokenCountCode))
  have hformula4Code :
      (binaryFormulaCode formula4).length <= atomicCode := by
    dsimp only [formula4, atomicCode]
    unfold taskSameRowsAtomicRowOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.eq_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq otherRightTerm
        otherSumTerm termCode (hterm otherRightTerm hotherRightCode)
        hotherSumCode)
  have hbodyCode :
      (binaryFormulaCode body).length <=
        taskSameRowsAtomicRowBodyCodePolynomial termBound := by
    dsimp only [body, widthTerm]
    exact atomicRowEqBitBody_code_length_le_closedTerms tokenTableTerm
      (shortBinaryNumeralTerm width) leftTerm otherLeftTerm termBound
      htableCode hwidthCode hleftCode hotherLeftCode
  have hformula5Code :
      (binaryFormulaCode formula5).length <= universalCode := by
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source body width
        numericBound bitBound
        (numericBound + taskSameRowsAtomicRowBodyCodePolynomial termBound)
        (taskSameRowsAtomicRowBodyCodePolynomial termBound) hwidthSize hbodyCode
    have halign :
        (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body) =
          formula5 := by
      dsimp only [formula5]
      rw [termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    dsimp only [universalCode]
    unfold taskSameRowsAtomicRowOuterUniversalFormulaCodePolynomial
    exact hraw
  have hformula1Closed : formula1.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![leftTerm, tokenCountTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hleftClosed,
      htokenCountClosed]
    simp
  have hformula2Closed : formula2.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![rightTerm, leftSumTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hrightClosed,
      hleftSumClosed]
    simp
  have hformula3Closed : formula3.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![otherLeftTerm, tokenCountTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hotherLeftClosed,
      htokenCountClosed]
    simp
  have hformula4Closed : formula4.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![otherRightTerm, otherSumTerm]).freeVariables = ∅
    rw [taskSameRowsBinaryRelationFormula_freeVariables, hotherRightClosed,
      hotherSumClosed]
    simp
  have hformula5Closed : formula5.freeVariables = ∅ := by
    have halign :
        (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body) =
          formula5 := by
      dsimp only [formula5]
      rw [termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    dsimp only [body, widthTerm]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_closedTerms
        tokenTableTerm (shortBinaryNumeralTerm width) leftTerm otherLeftTerm
        htableClosed (shortBinaryNumeralTerm_freeVariables_eq_empty width)
        hleftClosed hotherLeftClosed
  have hexplicitClosed : explicitFormula.freeVariables = ∅ := by
    dsimp only [explicitFormula, tail2345, tail345, tail45]
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hformula1Closed,
      hformula2Closed, hformula3Closed, hformula4Closed, hformula5Closed,
      Finset.empty_union]
  have h45Raw := binaryFormulaCode_and_length_le_local formula4 formula5
  have h345Raw := binaryFormulaCode_and_length_le_local formula3 tail45
  have h2345Raw := binaryFormulaCode_and_length_le_local formula2 tail345
  have htotalRaw := binaryFormulaCode_and_length_le_local formula1 tail2345
  have h45 :
      (binaryFormulaCode tail45).length <=
        atomicCode + universalCode + (binaryNatCode 4).length := by
    dsimp only [tail45] at h45Raw ⊢
    omega
  have h345 :
      (binaryFormulaCode tail345).length <=
        2 * atomicCode + universalCode +
          2 * (binaryNatCode 4).length := by
    dsimp only [tail345] at h345Raw ⊢
    omega
  have h2345 :
      (binaryFormulaCode tail2345).length <=
        3 * atomicCode + universalCode +
          3 * (binaryNatCode 4).length := by
    dsimp only [tail2345] at h2345Raw ⊢
    omega
  have hexplicitCode :
      (binaryFormulaCode explicitFormula).length <= syntaxResource := by
    dsimp only [explicitFormula] at htotalRaw ⊢
    apply htotalRaw.trans
    dsimp only [syntaxResource]
    unfold taskSameRowsAtomicRowAssemblySyntaxPolynomial
    omega
  let formula := compactAdditiveAtomicRowEqAtValuationFormula tokenTableTerm
    widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm otherRightTerm
  have halign : formula = explicitFormula := by
    dsimp only [formula, explicitFormula, formula1, formula2, formula3,
      formula4, formula5, tail45, tail345, tail2345, body, leftSumTerm,
      otherSumTerm]
    exact compactAdditiveAtomicRowEqAtValuationFormula_alignment
      tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm
  change formula.freeVariables = ∅ ∧
    (binaryFormulaCode formula).length <= syntaxResource
  rw [halign]
  exact ⟨hexplicitClosed, hexplicitCode⟩

theorem compactAdditiveSyntaxTaskRowEq_component_bounds
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound : Nat)
    (hrow : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight)
    (htokenCount : tokenCount <= numericBound) :
    sourceLeft <= numericBound ∧
      sourceLeft + 1 <= numericBound ∧
      sourceLeft + 2 <= numericBound ∧
      sourceRight <= numericBound ∧
      targetLeft <= numericBound ∧
      targetLeft + 1 <= numericBound ∧
      targetLeft + 2 <= numericBound ∧
      targetRight <= numericBound := by
  unfold CompactAdditiveSyntaxTaskRowEq at hrow
  unfold CompactAdditiveAtomicRowEq at hrow
  omega

theorem
    compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound bitBound : Nat)
    (hrow : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation
        tokenTable width tokenCount sourceLeft sourceRight targetLeft
        targetRight <=
      taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
        (taskSameRowsRowTermCodePolynomial bitBound) := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let countTerm := shortBinaryNumeralTerm tokenCount
  let sourceLeftTerm := shortBinaryNumeralTerm sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm targetLeft
  let targetRightTerm := shortBinaryNumeralTerm targetRight
  let sourceOneTerm : ValuationTerm := ‘!!sourceLeftTerm + 1’
  let sourceTwoTerm : ValuationTerm := ‘!!sourceLeftTerm + 2’
  let targetOneTerm : ValuationTerm := ‘!!targetLeftTerm + 1’
  let targetTwoTerm : ValuationTerm := ‘!!targetLeftTerm + 2’
  let termBound := taskSameRowsRowTermCodePolynomial bitBound
  let firstFormula := compactAdditiveAtomicRowEqAtValuationFormula
    tableTerm (shortBinaryNumeralTerm width) countTerm sourceLeftTerm
    sourceOneTerm targetLeftTerm targetOneTerm
  let secondFormula := compactAdditiveAtomicRowEqAtValuationFormula
    tableTerm (shortBinaryNumeralTerm width) countTerm sourceOneTerm
    sourceTwoTerm targetOneTerm targetTwoTerm
  let thirdFormula := compactAdditiveAtomicRowEqAtValuationFormula
    tableTerm (shortBinaryNumeralTerm width) countTerm sourceTwoTerm
    sourceRightTerm targetTwoTerm targetRightTerm
  let firstResource :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
      tableTerm (shortBinaryNumeralTerm width) countTerm sourceLeftTerm
      sourceOneTerm targetLeftTerm targetOneTerm
  let secondResource :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
      tableTerm (shortBinaryNumeralTerm width) countTerm sourceOneTerm
      sourceTwoTerm targetOneTerm targetTwoTerm
  let thirdResource :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
      tableTerm (shortBinaryNumeralTerm width) countTerm sourceTwoTerm
      sourceRightTerm targetTwoTerm targetRightTerm
  let fixedResource :=
    taskSameRowsCompactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound
      bitBound termBound
  let syntaxResource :=
    taskSameRowsTaskRowAssemblySyntaxPolynomial numericBound bitBound termBound
  have hcomponents := compactAdditiveSyntaxTaskRowEq_component_bounds
    tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
    numericBound hrow htokenCount
  have hsourceLeft := hcomponents.1
  have hsourceOne := hcomponents.2.1
  have hsourceTwo := hcomponents.2.2.1
  have hsourceRight := hcomponents.2.2.2.1
  have htargetLeft := hcomponents.2.2.2.2.1
  have htargetOne := hcomponents.2.2.2.2.2.1
  have htargetTwo := hcomponents.2.2.2.2.2.2.1
  have htargetRight := hcomponents.2.2.2.2.2.2.2
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hsourceLeftSize : Nat.size sourceLeft <= bitBound :=
    (Nat.size_le_size hsourceLeft).trans hnumericSize
  have hsourceRightSize : Nat.size sourceRight <= bitBound :=
    (Nat.size_le_size hsourceRight).trans hnumericSize
  have htargetLeftSize : Nat.size targetLeft <= bitBound :=
    (Nat.size_le_size htargetLeft).trans hnumericSize
  have htargetRightSize : Nat.size targetRight <= bitBound :=
    (Nat.size_le_size htargetRight).trans hnumericSize
  have hshortCode : ∀ value,
      Nat.size value <= bitBound ->
        (binaryTermCode (shortBinaryNumeralTerm value)).length <= termBound := by
    intro value hvalue
    have hraw :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
    dsimp only [termBound]
    unfold taskSameRowsRowTermCodePolynomial
    omega
  have htableCode : (binaryTermCode tableTerm).length <= termBound := by
    dsimp only [tableTerm]
    exact hshortCode tokenTable htableSize
  have hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termBound :=
    hshortCode width hwidthSize
  have hcountCode : (binaryTermCode countTerm).length <= termBound := by
    dsimp only [countTerm]
    exact hshortCode tokenCount htokenCountSize
  have hsourceLeftCode :
      (binaryTermCode sourceLeftTerm).length <= termBound := by
    dsimp only [sourceLeftTerm]
    exact hshortCode sourceLeft hsourceLeftSize
  have hsourceRightCode :
      (binaryTermCode sourceRightTerm).length <= termBound := by
    dsimp only [sourceRightTerm]
    exact hshortCode sourceRight hsourceRightSize
  have htargetLeftCode :
      (binaryTermCode targetLeftTerm).length <= termBound := by
    dsimp only [targetLeftTerm]
    exact hshortCode targetLeft htargetLeftSize
  have htargetRightCode :
      (binaryTermCode targetRightTerm).length <= termBound := by
    dsimp only [targetRightTerm]
    exact hshortCode targetRight htargetRightSize
  have hsourceOneCode :
      (binaryTermCode sourceOneTerm).length <= termBound := by
    dsimp only [sourceOneTerm, termBound]
    exact taskSameRowsAddOneTermCode_le sourceLeft bitBound hsourceLeftSize
  have hsourceTwoCode :
      (binaryTermCode sourceTwoTerm).length <= termBound := by
    dsimp only [sourceTwoTerm, termBound]
    exact taskSameRowsAddTwoTermCode_le sourceLeft bitBound hsourceLeftSize
  have htargetOneCode :
      (binaryTermCode targetOneTerm).length <= termBound := by
    dsimp only [targetOneTerm, termBound]
    exact taskSameRowsAddOneTermCode_le targetLeft bitBound htargetLeftSize
  have htargetTwoCode :
      (binaryTermCode targetTwoTerm).length <= termBound := by
    dsimp only [targetTwoTerm, termBound]
    exact taskSameRowsAddTwoTermCode_le targetLeft bitBound htargetLeftSize
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hcountClosed : countTerm.freeVariables = ∅ := by
    dsimp only [countTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hsourceLeftClosed : sourceLeftTerm.freeVariables = ∅ := by
    dsimp only [sourceLeftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceLeft
  have hsourceRightClosed : sourceRightTerm.freeVariables = ∅ := by
    dsimp only [sourceRightTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceRight
  have htargetLeftClosed : targetLeftTerm.freeVariables = ∅ := by
    dsimp only [targetLeftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty targetLeft
  have htargetRightClosed : targetRightTerm.freeVariables = ∅ := by
    dsimp only [targetRightTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty targetRight
  have hsourceOneClosed : sourceOneTerm.freeVariables = ∅ := by
    dsimp only [sourceOneTerm]
    exact taskSameRowsAddOneTerm_closed sourceLeft
  have hsourceTwoClosed : sourceTwoTerm.freeVariables = ∅ := by
    dsimp only [sourceTwoTerm]
    exact taskSameRowsAddTwoTerm_closed sourceLeft
  have htargetOneClosed : targetOneTerm.freeVariables = ∅ := by
    dsimp only [targetOneTerm]
    exact taskSameRowsAddOneTerm_closed targetLeft
  have htargetTwoClosed : targetTwoTerm.freeVariables = ∅ := by
    dsimp only [targetTwoTerm]
    exact taskSameRowsAddTwoTerm_closed targetLeft
  have htableValue :
      Nat.size (termValue valuation tableTerm) <= bitBound := by
    dsimp only [tableTerm]
    simpa only [termValue_shortBinaryNumeralTerm] using htableSize
  have hfirstResource : firstResource <= fixedResource := by
    dsimp only [firstResource, fixedResource, tableTerm, countTerm,
      sourceLeftTerm, sourceOneTerm, targetLeftTerm, targetOneTerm, termBound]
    exact
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_closedTerms_fixed
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (‘!!(shortBinaryNumeralTerm sourceLeft) + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm targetLeft)
        (‘!!(shortBinaryNumeralTerm targetLeft) + 1’ : ValuationTerm)
        width sourceLeft targetLeft numericBound bitBound
        (taskSameRowsRowTermCodePolynomial bitBound)
        (termValue_shortBinaryNumeralTerm valuation sourceLeft)
        (termValue_shortBinaryNumeralTerm valuation targetLeft)
        hwidth hsourceLeft htargetLeft hwidthSize htableValue htableClosed
        hcountClosed hsourceLeftClosed hsourceOneClosed htargetLeftClosed
        htargetOneClosed htableCode hwidthCode hcountCode hsourceLeftCode
        hsourceOneCode htargetLeftCode htargetOneCode
  have hsecondResource : secondResource <= fixedResource := by
    dsimp only [secondResource, fixedResource, tableTerm, countTerm,
      sourceOneTerm, sourceTwoTerm, targetOneTerm, targetTwoTerm, termBound]
    exact
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_closedTerms_fixed
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!(shortBinaryNumeralTerm sourceLeft) + 1’ : ValuationTerm)
        (‘!!(shortBinaryNumeralTerm sourceLeft) + 2’ : ValuationTerm)
        (‘!!(shortBinaryNumeralTerm targetLeft) + 1’ : ValuationTerm)
        (‘!!(shortBinaryNumeralTerm targetLeft) + 2’ : ValuationTerm)
        width (sourceLeft + 1) (targetLeft + 1) numericBound bitBound
        (taskSameRowsRowTermCodePolynomial bitBound)
        (taskSameRowsAddOneTerm_value valuation sourceLeft)
        (taskSameRowsAddOneTerm_value valuation targetLeft)
        hwidth hsourceOne htargetOne hwidthSize htableValue htableClosed
        hcountClosed hsourceOneClosed hsourceTwoClosed htargetOneClosed
        htargetTwoClosed htableCode hwidthCode hcountCode hsourceOneCode
        hsourceTwoCode htargetOneCode htargetTwoCode
  have hthirdResource : thirdResource <= fixedResource := by
    dsimp only [thirdResource, fixedResource, tableTerm, countTerm,
      sourceTwoTerm, sourceRightTerm, targetTwoTerm, targetRightTerm,
      termBound]
    exact
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_closedTerms_fixed
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!(shortBinaryNumeralTerm sourceLeft) + 2’ : ValuationTerm)
        (shortBinaryNumeralTerm sourceRight)
        (‘!!(shortBinaryNumeralTerm targetLeft) + 2’ : ValuationTerm)
        (shortBinaryNumeralTerm targetRight)
        width (sourceLeft + 2) (targetLeft + 2) numericBound bitBound
        (taskSameRowsRowTermCodePolynomial bitBound)
        (taskSameRowsAddTwoTerm_value valuation sourceLeft)
        (taskSameRowsAddTwoTerm_value valuation targetLeft)
        hwidth hsourceTwo htargetTwo hwidthSize htableValue htableClosed
        hcountClosed hsourceTwoClosed hsourceRightClosed htargetTwoClosed
        htargetRightClosed htableCode hwidthCode hcountCode hsourceTwoCode
        hsourceRightCode htargetTwoCode htargetRightCode
  have hfirstSyntax :=
    compactAdditiveAtomicRowEqAtValuationFormula_closed_code_le_fixed
      tableTerm countTerm sourceLeftTerm sourceOneTerm targetLeftTerm
      targetOneTerm width numericBound bitBound termBound hwidthSize
      htableClosed hcountClosed hsourceLeftClosed hsourceOneClosed
      htargetLeftClosed htargetOneClosed htableCode hwidthCode hcountCode
      hsourceLeftCode hsourceOneCode htargetLeftCode htargetOneCode
  have hsecondSyntax :=
    compactAdditiveAtomicRowEqAtValuationFormula_closed_code_le_fixed
      tableTerm countTerm sourceOneTerm sourceTwoTerm targetOneTerm
      targetTwoTerm width numericBound bitBound termBound hwidthSize
      htableClosed hcountClosed hsourceOneClosed hsourceTwoClosed
      htargetOneClosed htargetTwoClosed htableCode hwidthCode hcountCode
      hsourceOneCode hsourceTwoCode htargetOneCode htargetTwoCode
  have hthirdSyntax :=
    compactAdditiveAtomicRowEqAtValuationFormula_closed_code_le_fixed
      tableTerm countTerm sourceTwoTerm sourceRightTerm targetTwoTerm
      targetRightTerm width numericBound bitBound termBound hwidthSize
      htableClosed hcountClosed hsourceTwoClosed hsourceRightClosed
      htargetTwoClosed htargetRightClosed htableCode hwidthCode hcountCode
      hsourceTwoCode hsourceRightCode htargetTwoCode htargetRightCode
  have hfirstClosed : firstFormula.freeVariables = ∅ := by
    simpa only [firstFormula] using hfirstSyntax.1
  have hsecondClosed : secondFormula.freeVariables = ∅ := by
    simpa only [secondFormula] using hsecondSyntax.1
  have hthirdClosed : thirdFormula.freeVariables = ∅ := by
    simpa only [thirdFormula] using hthirdSyntax.1
  have hfirstCode :
      (binaryFormulaCode firstFormula).length <=
        taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
          termBound := by
    simpa only [firstFormula] using hfirstSyntax.2
  have hsecondCode :
      (binaryFormulaCode secondFormula).length <=
        taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
          termBound := by
    simpa only [secondFormula] using hsecondSyntax.2
  have hthirdCode :
      (binaryFormulaCode thirdFormula).length <=
        taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound bitBound
          termBound := by
    simpa only [thirdFormula] using hthirdSyntax.2
  have htotalClosed :
      (firstFormula ⋏ (secondFormula ⋏ thirdFormula)).freeVariables = ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hfirstClosed,
      hsecondClosed, hthirdClosed, Finset.empty_union]
  have hinnerRaw :=
    binaryFormulaCode_and_length_le_local secondFormula thirdFormula
  have htotalRaw :=
    binaryFormulaCode_and_length_le_local firstFormula
      (secondFormula ⋏ thirdFormula)
  have hinnerCode :
      (binaryFormulaCode (secondFormula ⋏ thirdFormula)).length <=
        2 * taskSameRowsAtomicRowAssemblySyntaxPolynomial numericBound
            bitBound termBound +
          (binaryNatCode 4).length := by
    omega
  have htotalCode :
      (binaryFormulaCode
        (firstFormula ⋏ (secondFormula ⋏ thirdFormula))).length <=
          syntaxResource := by
    dsimp only [syntaxResource]
    unfold taskSameRowsTaskRowAssemblySyntaxPolynomial
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold taskSameRowsTaskRowAssemblySyntaxPolynomial
    omega
  have hgeneral :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      valuation firstFormula secondFormula thirdFormula firstResource
      secondResource thirdResource syntaxResource hpositive htotalClosed
      htotalCode
  have hmono :
      hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource firstResource
          secondResource thirdResource <=
        hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
          fixedResource fixedResource fixedResource := by
    unfold hybridThreeConjunctionGeneralPayloadEnvelope
      hybridConjunctionGeneralPayloadEnvelope
    omega
  unfold compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope
    taskSameRowsTaskRowFixedPayloadPolynomial
  dsimp only [tableTerm, countTerm, sourceLeftTerm, sourceRightTerm,
    targetLeftTerm, targetRightTerm, sourceOneTerm, sourceTwoTerm,
    targetOneTerm, targetTwoTerm, firstFormula, secondFormula, thirdFormula,
    firstResource, secondResource, thirdResource, fixedResource,
    syntaxResource, termBound] at hgeneral hmono ⊢
  exact hgeneral.trans hmono

theorem countEqualityCertificate_structuralPayloadBound_le_fixed
    (sourceCount targetCount bitBound : Nat)
    (hcount : targetCount = sourceCount)
    (hsourceSize : Nat.size sourceCount <= bitBound)
    (htargetSize : Nat.size targetCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (countEqualityCertificate sourceCount targetCount hcount) <=
      taskSameRowsCountFixedPayloadPolynomial bitBound := by
  change compilePositiveRelationPayloadResource taskSameRowsZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm targetCount,
        shortBinaryNumeralTerm sourceCount] <= _
  unfold taskSameRowsCountFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    taskSameRowsZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm targetCount)
    (shortBinaryNumeralTerm sourceCount)
    0 (taskSameRowsAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (taskSameRowsShortNumeralCode_le targetCount bitBound htargetSize)
    (taskSameRowsShortNumeralCode_le sourceCount bitBound hsourceSize)

theorem compactAdditiveSyntaxTaskRowEqFormula_code_length_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound bitBound : Nat)
    (hrow : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm sourceLeft,
          shortBinaryNumeralTerm sourceRight,
          shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm targetRight])).length <=
      taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
        (taskSameRowsRowTermCodePolynomial bitBound) := by
  let certificate :=
    compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph valuation
      tokenTable width tokenCount sourceLeft sourceRight targetLeft
      targetRight hrow
  have hpayload :
      hybridFormulaStructuralPayloadBound certificate <=
        taskSameRowsTaskRowFixedPayloadPolynomial numericBound bitBound
          (taskSameRowsRowTermCodePolynomial bitBound) := by
    exact
      (compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        valuation tokenTable width tokenCount sourceLeft sourceRight
        targetLeft targetRight hrow).trans
      (compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope_le_fullyFixed
        valuation tokenTable width tokenCount sourceLeft sourceRight
        targetLeft targetRight numericBound bitBound hrow hwidth htokenCount
        htableSize hnumericSize)
  have hcode :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  simpa only [certificate,
    compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph] using
      hcode.trans hpayload

#print axioms countEqualityCertificate_structuralPayloadBound_le_fixed
#print axioms
  compactAdditiveSyntaxTaskRowEqFormula_code_length_le_fullyFixed
#print axioms taskSameRowsAddOneTermCode_le
#print axioms taskSameRowsAddTwoTermCode_le
#print axioms atomicRowEqBitBody_code_length_le_closedTerms
#print axioms
  compileBinaryBitLiteralAtAtomicRowClosedTermsPayloadPolynomial_le_fixed
#print axioms atomicRowEqBitBranchFormulaCodes_le_closedTerms
#print axioms
  atomicRowEqBitBranchFormulaVariables_subset_singleton_closedTerms
#print axioms
  atomicRowEqBitBranchPublicPayloadEnvelope_le_closedTerms_fixed
#print axioms
  atomicRowEqBitBranchPublicPayloadSum_le_closedTerms_fixed
#print axioms
  atomicRowEqBranchesTransparentStructuralEnvelope_le_closedTerms_fixed
#print axioms
  atomicRowEqContextualBranchesResource_le_closedTerms_fixed
#print axioms
  atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_closedTerms
#print axioms
  atomicRowEqUniversalStructuralPayloadEnvelope_le_closedTerms_of_branch
#print axioms
  atomicRowEqUniversalStructuralPayloadEnvelope_le_closedTerms_fixed
#print axioms
  compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_closedTerms_fixed
#print axioms
  compactAdditiveAtomicRowEqAtValuationFormula_closed_code_le_fixed
#print axioms
  compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope_le_fullyFixed
#print axioms compactAdditiveSyntaxTaskRowEq_component_bounds

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsAtomicFixedBounds
