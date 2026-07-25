import integration.FoundationCompactNumericListedDirectNegationFormulaTagWitnessPostSyntaxFixedBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds
import integration.FoundationCompactPAFreeFormulaVariableTransport

/-!
# Fixed syntax bounds for the open negation-tag witness bodies

The open bodies contain one bound variable and shifted closed numeral terms.
All term, atomic-formula, conjunction, witness, and existential codes are
bounded directly from the common numeral bit bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 60000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagWitnessOpenSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagWitnessPostFixedBounds

def negationFormulaTagWitnessOpenTermCodePolynomial (bitBound : Nat) : Nat :=
  let closedTermCode := negationFormulaTagAtomicTermCodePolynomial bitBound
  let boundVariableCode :=
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length
  16 * (closedTermCode + boundVariableCode +
    (binaryTermCode (‘1’ : ArithmeticSemiterm Nat 1)).length +
    (binaryTermCode (‘2’ : ArithmeticSemiterm Nat 1)).length +
    (binaryTermCode (‘4’ : ArithmeticSemiterm Nat 1)).length +
    binaryFunctionTermCodeOverhead Language.Add.add +
    binaryFunctionTermCodeOverhead Language.Mul.mul + 1)

def negationFormulaTagWitnessOpenAtomicCodePolynomial
    (bitBound : Nat) : Nat :=
  4 * negationFormulaTagWitnessOpenTermCodePolynomial bitBound + 128

def negationFormulaTagWitnessOpenBodyCodePolynomial
    (bitBound : Nat) : Nat :=
  32 * (negationFormulaTagWitnessOpenAtomicCodePolynomial bitBound + 1)

def negationFormulaTagWitnessExistentialSyntaxPolynomial
    (bitBound : Nat) : Nat :=
  negationFormulaTagWitnessOpenBodyCodePolynomial bitBound +
    negationFormulaTagWitnessPostSyntaxPolynomial bitBound +
    negationFormulaTagAtomicTermCodePolynomial bitBound + 32

private theorem binaryFunctionTermCode_length_le_open
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func functionSymbol ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead functionSymbol := by
  simp [Matrix.fun_eq_vec_two, binaryTermCode,
    binaryFunctionTermCodeOverhead]
  omega

theorem binaryFunctionTerm_freeVariables_open
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat arity) :
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

private theorem binaryRelationFormulaCode_length_le_open
    {arity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length + 96 := by
  have htag0 : (binaryNatCode 0).length <= 32 := by decide
  have htag2 : (binaryNatCode 2).length <= 32 := by decide
  have hrelation :
      (binaryNatCode (Encodable.encode relationSymbol)).length <= 32 := by
    cases relationSymbol <;> decide
  simp [Matrix.fun_eq_vec_two, binaryFormulaCode]
  omega

theorem binaryRelationFormula_freeVariables_open
    {arity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat arity) :
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

private theorem binaryAndSemiformulaCode_length_le_open
    {arity : Nat}
    (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (left ⋏ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 8 := by
  have htag : (binaryNatCode 4).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem shiftedShortNumeralCode_le_open
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (Rew.bShift (shortBinaryNumeralTerm value) :
        ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  have hclosed :=
    tagShortNumeralCode_le value bitBound hvalue
  have hshift :=
    binaryTermCode_bShift_length_le_add_symbols
      (shortBinaryNumeralTerm value)
  have hsymbols :=
    termSymbolCount_le_binaryTermCode_length
      (shortBinaryNumeralTerm value)
  unfold negationFormulaTagWitnessOpenTermCodePolynomial
  dsimp only
  omega

theorem witnessBoundVariableCode_le_open (bitBound : Nat) :
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  unfold negationFormulaTagWitnessOpenTermCodePolynomial
  dsimp only
  omega

theorem openOneCode_le (bitBound : Nat) :
    (binaryTermCode (‘1’ : ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  unfold negationFormulaTagWitnessOpenTermCodePolynomial
  dsimp only
  omega

theorem openTwoCode_le (bitBound : Nat) :
    (binaryTermCode (‘2’ : ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  unfold negationFormulaTagWitnessOpenTermCodePolynomial
  dsimp only
  omega

theorem openFourCode_le (bitBound : Nat) :
    (binaryTermCode (‘4’ : ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  unfold negationFormulaTagWitnessOpenTermCodePolynomial
  dsimp only
  omega

theorem openMulTwoWitnessCode_le (bitBound : Nat) :
    (binaryTermCode
      (‘2 * #0’ : ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  have hraw := binaryFunctionTermCode_length_le_open Language.Mul.mul
    (‘2’ : ArithmeticSemiterm Nat 1) (#0 : ArithmeticSemiterm Nat 1)
  change
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func Language.Mul.mul
        ![(‘2’ : ArithmeticSemiterm Nat 1),
          (#0 : ArithmeticSemiterm Nat 1)])).length <= _
  have htwo := openTwoCode_le bitBound
  have hbound := witnessBoundVariableCode_le_open bitBound
  unfold negationFormulaTagWitnessOpenTermCodePolynomial at *
  dsimp only at *
  omega

theorem openMulTwoWitnessAddOneCode_le (bitBound : Nat) :
    (binaryTermCode
      (‘2 * #0 + 1’ : ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  have hmulRaw := binaryFunctionTermCode_length_le_open Language.Mul.mul
    (‘2’ : ArithmeticSemiterm Nat 1) (#0 : ArithmeticSemiterm Nat 1)
  have hmul :
      (binaryTermCode
        (‘2 * #0’ : ArithmeticSemiterm Nat 1)).length <=
        (binaryTermCode (‘2’ : ArithmeticSemiterm Nat 1)).length +
          (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    change
      (binaryTermCode
        (LO.FirstOrder.Semiterm.func Language.Mul.mul
          ![(‘2’ : ArithmeticSemiterm Nat 1),
            (#0 : ArithmeticSemiterm Nat 1)])).length <= _
    exact hmulRaw
  have hraw := binaryFunctionTermCode_length_le_open Language.Add.add
    (‘2 * #0’ : ArithmeticSemiterm Nat 1)
    (‘1’ : ArithmeticSemiterm Nat 1)
  change
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func Language.Add.add
        ![(‘2 * #0’ : ArithmeticSemiterm Nat 1),
          (‘1’ : ArithmeticSemiterm Nat 1)])).length <= _
  have hone := openOneCode_le bitBound
  have htwo := openTwoCode_le bitBound
  have hbound := witnessBoundVariableCode_le_open bitBound
  unfold negationFormulaTagWitnessOpenTermCodePolynomial at *
  dsimp only at *
  omega

theorem shiftedShortNumeralAddOneCode_le_open
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (‘!!(Rew.bShift (shortBinaryNumeralTerm value)) + 1’ :
        ArithmeticSemiterm Nat 1)).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound := by
  have hclosed := tagShortNumeralCode_le value bitBound hvalue
  have hshiftRaw := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm value)
  have hsymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm value)
  have hraw := binaryFunctionTermCode_length_le_open Language.Add.add
    (Rew.bShift (shortBinaryNumeralTerm value) :
      ArithmeticSemiterm Nat 1)
    (‘1’ : ArithmeticSemiterm Nat 1)
  change
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func Language.Add.add
        ![(Rew.bShift (shortBinaryNumeralTerm value) :
            ArithmeticSemiterm Nat 1),
          (‘1’ : ArithmeticSemiterm Nat 1)])).length <= _
  have hone := openOneCode_le bitBound
  unfold negationFormulaTagWitnessOpenTermCodePolynomial at *
  dsimp only at *
  omega

private theorem openAtomicFormulaCode_le
    {relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2}
    (left right : ArithmeticSemiterm Nat 1) (bitBound : Nat)
    (hleft : (binaryTermCode left).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound)
    (hright : (binaryTermCode right).length <=
      negationFormulaTagWitnessOpenTermCodePolynomial bitBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
      negationFormulaTagWitnessOpenAtomicCodePolynomial bitBound := by
  have hraw := binaryRelationFormulaCode_length_le_open relationSymbol
    left right
  unfold negationFormulaTagWitnessOpenAtomicCodePolynomial
  omega

private theorem threeOpenAtomicFormulaCode_le
    (formula1 formula2 formula3 : ArithmeticSemiformula Nat 1)
    (bitBound : Nat)
    (h1 : (binaryFormulaCode formula1).length <=
      negationFormulaTagWitnessOpenAtomicCodePolynomial bitBound)
    (h2 : (binaryFormulaCode formula2).length <=
      negationFormulaTagWitnessOpenAtomicCodePolynomial bitBound)
    (h3 : (binaryFormulaCode formula3).length <=
      negationFormulaTagWitnessOpenAtomicCodePolynomial bitBound) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      negationFormulaTagWitnessOpenBodyCodePolynomial bitBound := by
  have hinner := binaryAndSemiformulaCode_length_le_open formula2 formula3
  have houter := binaryAndSemiformulaCode_length_le_open
    formula1 (formula2 ⋏ formula3)
  unfold negationFormulaTagWitnessOpenBodyCodePolynomial
  omega

theorem evenWitnessBody_code_le_fixed
    (tag mapped bitBound : Nat)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    (binaryFormulaCode
      (compactNegationFormulaTagEvenWitnessBody tag mapped)).length <=
      negationFormulaTagWitnessOpenBodyCodePolynomial bitBound := by
  let pairFormula : ArithmeticSemiformula Nat 1 := “#0 < 4”
  let equalityFormula : ArithmeticSemiformula Nat 1 :=
    “!!(Rew.bShift (shortBinaryNumeralTerm tag)) = 2 * #0”
  let successorFormula : ArithmeticSemiformula Nat 1 :=
    “!!(Rew.bShift (shortBinaryNumeralTerm mapped)) =
      !!(Rew.bShift (shortBinaryNumeralTerm tag)) + 1”
  have hpair := openAtomicFormulaCode_le
    (relationSymbol := Language.LT.lt)
    (#0 : ArithmeticSemiterm Nat 1) (‘4’ : ArithmeticSemiterm Nat 1)
    bitBound (witnessBoundVariableCode_le_open bitBound)
    (openFourCode_le bitBound)
  have hequality := openAtomicFormulaCode_le
    (relationSymbol := Language.Eq.eq)
    (Rew.bShift (shortBinaryNumeralTerm tag) :
      ArithmeticSemiterm Nat 1)
    (‘2 * #0’ : ArithmeticSemiterm Nat 1) bitBound
    (shiftedShortNumeralCode_le_open tag bitBound htagSize)
    (openMulTwoWitnessCode_le bitBound)
  have hsuccessor := openAtomicFormulaCode_le
    (relationSymbol := Language.Eq.eq)
    (Rew.bShift (shortBinaryNumeralTerm mapped) :
      ArithmeticSemiterm Nat 1)
    (‘!!(Rew.bShift (shortBinaryNumeralTerm tag)) + 1’ :
      ArithmeticSemiterm Nat 1)
    bitBound (shiftedShortNumeralCode_le_open mapped bitBound hmappedSize)
    (shiftedShortNumeralAddOneCode_le_open tag bitBound htagSize)
  unfold compactNegationFormulaTagEvenWitnessBody
  exact threeOpenAtomicFormulaCode_le pairFormula equalityFormula
    successorFormula bitBound hpair hequality hsuccessor

theorem oddWitnessBody_code_le_fixed
    (tag mapped bitBound : Nat)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    (binaryFormulaCode
      (compactNegationFormulaTagOddWitnessBody tag mapped)).length <=
      negationFormulaTagWitnessOpenBodyCodePolynomial bitBound := by
  let pairFormula : ArithmeticSemiformula Nat 1 := “#0 < 4”
  let equalityFormula : ArithmeticSemiformula Nat 1 :=
    “!!(Rew.bShift (shortBinaryNumeralTerm tag)) = 2 * #0 + 1”
  let successorFormula : ArithmeticSemiformula Nat 1 :=
    “!!(Rew.bShift (shortBinaryNumeralTerm tag)) =
      !!(Rew.bShift (shortBinaryNumeralTerm mapped)) + 1”
  have hpair := openAtomicFormulaCode_le
    (relationSymbol := Language.LT.lt)
    (#0 : ArithmeticSemiterm Nat 1) (‘4’ : ArithmeticSemiterm Nat 1)
    bitBound (witnessBoundVariableCode_le_open bitBound)
    (openFourCode_le bitBound)
  have hequality := openAtomicFormulaCode_le
    (relationSymbol := Language.Eq.eq)
    (Rew.bShift (shortBinaryNumeralTerm tag) :
      ArithmeticSemiterm Nat 1)
    (‘2 * #0 + 1’ : ArithmeticSemiterm Nat 1) bitBound
    (shiftedShortNumeralCode_le_open tag bitBound htagSize)
    (openMulTwoWitnessAddOneCode_le bitBound)
  have hsuccessor := openAtomicFormulaCode_le
    (relationSymbol := Language.Eq.eq)
    (Rew.bShift (shortBinaryNumeralTerm tag) :
      ArithmeticSemiterm Nat 1)
    (‘!!(Rew.bShift (shortBinaryNumeralTerm mapped)) + 1’ :
      ArithmeticSemiterm Nat 1)
    bitBound (shiftedShortNumeralCode_le_open tag bitBound htagSize)
    (shiftedShortNumeralAddOneCode_le_open mapped bitBound hmappedSize)
  unfold compactNegationFormulaTagOddWitnessBody
  exact threeOpenAtomicFormulaCode_le pairFormula equalityFormula
    successorFormula bitBound hpair hequality hsuccessor

theorem evenWitnessExistentialFormula_code_le_fixed
    (tag mapped bitBound : Nat)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    (binaryFormulaCode
      (∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped :
        ValuationFormula)).length <=
      negationFormulaTagWitnessExistentialSyntaxPolynomial bitBound := by
  have hbody := evenWitnessBody_code_le_fixed tag mapped bitBound htagSize
    hmappedSize
  have hexists := binaryFormulaCode_exs_length_le
    (compactNegationFormulaTagEvenWitnessBody tag mapped)
  unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
  omega

theorem oddWitnessExistentialFormula_code_le_fixed
    (tag mapped bitBound : Nat)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    (binaryFormulaCode
      (∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped :
        ValuationFormula)).length <=
      negationFormulaTagWitnessExistentialSyntaxPolynomial bitBound := by
  have hbody := oddWitnessBody_code_le_fixed tag mapped bitBound htagSize
    hmappedSize
  have hexists := binaryFormulaCode_exs_length_le
    (compactNegationFormulaTagOddWitnessBody tag mapped)
  unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
  omega

private theorem openOne_freeVariables_eq_empty :
    (‘1’ : ArithmeticSemiterm Nat 1).freeVariables = ∅ := by
  change
    (Rew.bShift (‘1’ : ValuationTerm) :
      ArithmeticSemiterm Nat 1).freeVariables = ∅
  rw [bShiftTerm_freeVariables_eq]
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem openTwo_freeVariables_eq_empty :
    (‘2’ : ArithmeticSemiterm Nat 1).freeVariables = ∅ := by
  change
    (Rew.bShift (‘2’ : ValuationTerm) :
      ArithmeticSemiterm Nat 1).freeVariables = ∅
  rw [bShiftTerm_freeVariables_eq]
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem openFour_freeVariables_eq_empty :
    (‘4’ : ArithmeticSemiterm Nat 1).freeVariables = ∅ := by
  change
    (Rew.bShift (‘4’ : ValuationTerm) :
      ArithmeticSemiterm Nat 1).freeVariables = ∅
  rw [bShiftTerm_freeVariables_eq]
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem openMulTwoWitness_freeVariables_eq_empty :
    (‘2 * #0’ : ArithmeticSemiterm Nat 1).freeVariables = ∅ := by
  change
    (LO.FirstOrder.Semiterm.func Language.Mul.mul
      ![(‘2’ : ArithmeticSemiterm Nat 1),
        (#0 : ArithmeticSemiterm Nat 1)]).freeVariables = ∅
  rw [binaryFunctionTerm_freeVariables_open]
  rw [openTwo_freeVariables_eq_empty]
  simp

private theorem openMulTwoWitnessAddOne_freeVariables_eq_empty :
    (‘2 * #0 + 1’ : ArithmeticSemiterm Nat 1).freeVariables = ∅ := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![(‘2 * #0’ : ArithmeticSemiterm Nat 1),
        (‘1’ : ArithmeticSemiterm Nat 1)]).freeVariables = ∅
  rw [binaryFunctionTerm_freeVariables_open,
    openMulTwoWitness_freeVariables_eq_empty,
    openOne_freeVariables_eq_empty]
  simp

private theorem shiftedShortNumeralAddOne_freeVariables_eq_empty
    (value : Nat) :
    (‘!!(Rew.bShift (shortBinaryNumeralTerm value)) + 1’ :
      ArithmeticSemiterm Nat 1).freeVariables = ∅ := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![(Rew.bShift (shortBinaryNumeralTerm value) :
          ArithmeticSemiterm Nat 1),
        (‘1’ : ArithmeticSemiterm Nat 1)]).freeVariables = ∅
  rw [binaryFunctionTerm_freeVariables_open, bShiftTerm_freeVariables_eq,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    openOne_freeVariables_eq_empty]
  simp

theorem evenWitnessExistential_freeVariables_eq_empty
    (tag mapped : Nat) :
    (∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped :
      ValuationFormula).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_exs]
  unfold compactNegationFormulaTagEvenWitnessBody
  simp [bShiftTerm_freeVariables_eq,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    LO.FirstOrder.Semiterm.Operator.operator]
  exact ⟨openFour_freeVariables_eq_empty,
    openMulTwoWitness_freeVariables_eq_empty,
    shiftedShortNumeralAddOne_freeVariables_eq_empty tag⟩

theorem oddWitnessExistential_freeVariables_eq_empty
    (tag mapped : Nat) :
    (∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped :
      ValuationFormula).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_exs]
  unfold compactNegationFormulaTagOddWitnessBody
  simp [bShiftTerm_freeVariables_eq,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    LO.FirstOrder.Semiterm.Operator.operator]
  exact ⟨openFour_freeVariables_eq_empty,
    openMulTwoWitnessAddOne_freeVariables_eq_empty,
    shiftedShortNumeralAddOne_freeVariables_eq_empty mapped⟩

#print axioms evenWitnessBody_code_le_fixed
#print axioms oddWitnessBody_code_le_fixed
#print axioms evenWitnessExistentialFormula_code_le_fixed
#print axioms oddWitnessExistentialFormula_code_le_fixed
#print axioms evenWitnessExistential_freeVariables_eq_empty
#print axioms oddWitnessExistential_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNegationFormulaTagWitnessOpenSyntaxFixedBounds
