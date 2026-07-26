import integration.FoundationCompactNumericListedDirectParserSyntaxTraceBoundedDirectCompiler
import integration.FoundationCompactPAValuationTermCompilerBounds

/-! # Checked PA equality for the exact parser fuel term -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds

def compactParserSyntaxExactFuel (inputCount : Nat) : Nat :=
  16 * (inputCount + 1) * (inputCount + 1) + 8

def compactParserSyntaxExactNativeNumeralTerm
    (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator (Semiterm.Operator.numeral ℒₒᵣ value) ![]

def compactParserSyntaxExactFuelTerm (inputCount : Nat) : ValuationTerm :=
  ‘!!(compactParserSyntaxExactNativeNumeralTerm 16) *
      (!!(shortBinaryNumeralTerm inputCount) + 1) *
      (!!(shortBinaryNumeralTerm inputCount) + 1) +
      !!(compactParserSyntaxExactNativeNumeralTerm 8)’

private theorem arithmeticAddTerm_eq_func_exactFuel
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func_exactFuel
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_exactFuel
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_exactFuel]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul_exactFuel
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func_exactFuel]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne_exactFuel
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem arithmeticAddTerm_freeVariables_exactFuel
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func_exactFuel,
    LO.FirstOrder.Semiterm.freeVariables_func]
  ext candidate
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨coordinate, hcoordinate⟩
    fin_cases coordinate
    · exact Or.inl hcoordinate
    · exact Or.inr hcoordinate
  · rintro (hleft | hright)
    · exact ⟨0, hleft⟩
    · exact ⟨1, hright⟩

private theorem arithmeticMulTerm_freeVariables_exactFuel
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticMulTerm_eq_func_exactFuel,
    LO.FirstOrder.Semiterm.freeVariables_func]
  ext candidate
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨coordinate, hcoordinate⟩
    fin_cases coordinate
    · exact Or.inl hcoordinate
    · exact Or.inr hcoordinate
  · rintro (hleft | hright)
    · exact ⟨0, hleft⟩
    · exact ⟨1, hright⟩

private theorem arithmeticOneTerm_freeVariables_exactFuel :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.numeral_one,
    Semiterm.Operator.One.term_eq]

@[simp] theorem compactParserSyntaxExactNativeNumeralTerm_value
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation
      (compactParserSyntaxExactNativeNumeralTerm value) = value := by
  simp [compactParserSyntaxExactNativeNumeralTerm, termValue]

@[simp] theorem
    compactParserSyntaxExactNativeNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (compactParserSyntaxExactNativeNumeralTerm value).freeVariables = ∅ := by
  simp [compactParserSyntaxExactNativeNumeralTerm,
    Semiterm.Operator.operator]

theorem compactParserSyntaxExactFuelTerm_value
    (inputCount : Nat) :
    termValue (fun _ => 0) (compactParserSyntaxExactFuelTerm inputCount) =
      compactParserSyntaxExactFuel inputCount := by
  simp [compactParserSyntaxExactFuelTerm, compactParserSyntaxExactFuel,
    termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd_exactFuel,
    termValue_arithmeticMul_exactFuel, termValue_arithmeticOne_exactFuel]

theorem compactParserSyntaxExactFuelTerm_freeVariables_eq_empty
    (inputCount : Nat) :
    (compactParserSyntaxExactFuelTerm inputCount).freeVariables = ∅ := by
  let countTerm : ValuationTerm := shortBinaryNumeralTerm inputCount
  let successorTerm : ValuationTerm := ‘!!countTerm + 1’
  let firstProduct : ValuationTerm :=
    ‘!!(compactParserSyntaxExactNativeNumeralTerm 16) * !!successorTerm’
  let product : ValuationTerm := ‘!!firstProduct * !!successorTerm’
  have hcount : countTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty inputCount
  have hsuccessor : successorTerm.freeVariables = ∅ := by
    dsimp only [successorTerm]
    rw [arithmeticAddTerm_freeVariables_exactFuel, hcount,
      arithmeticOneTerm_freeVariables_exactFuel]
    simp
  have hfirst : firstProduct.freeVariables = ∅ := by
    dsimp only [firstProduct]
    rw [arithmeticMulTerm_freeVariables_exactFuel,
      compactParserSyntaxExactNativeNumeralTerm_freeVariables_eq_empty,
      hsuccessor]
    simp
  have hproduct : product.freeVariables = ∅ := by
    dsimp only [product]
    rw [arithmeticMulTerm_freeVariables_exactFuel, hfirst, hsuccessor]
    simp
  change
    (‘!!product +
      !!(compactParserSyntaxExactNativeNumeralTerm 8)’ :
      ValuationTerm).freeVariables = ∅
  rw [arithmeticAddTerm_freeVariables_exactFuel, hproduct,
    compactParserSyntaxExactNativeNumeralTerm_freeVariables_eq_empty]
  simp

structure ParserSyntaxExactFuelEqualityBound
    (inputCount : Nat) (resource : Nat) where
  proof : CertifiedPAContextProof ∅
    (“!!(shortBinaryNumeralTerm (compactParserSyntaxExactFuel inputCount)) =
      !!(compactParserSyntaxExactFuelTerm inputCount)” : ValuationFormula)
  payloadLength_le : proof.payloadLength <= resource

def compactParserSyntaxExactFuelEqualityPayloadResource
    (inputCount : Nat) : Nat :=
  compileTermValueEqualityPayloadResource (fun _ => 0)
    (compactParserSyntaxExactFuelTerm inputCount)

noncomputable def compactParserSyntaxExactFuelEqualityBound
    (inputCount : Nat) :
    ParserSyntaxExactFuelEqualityBound inputCount
      (compactParserSyntaxExactFuelEqualityPayloadResource inputCount) := by
  let term := compactParserSyntaxExactFuelTerm inputCount
  let raw := compileTermValueEquality (fun _ => 0) term
  have hformula :
      (“!!(shortBinaryNumeralTerm
          (termValue (fun _ => 0) term)) = !!term” : ValuationFormula) =
        (“!!(shortBinaryNumeralTerm
          (compactParserSyntaxExactFuel inputCount)) = !!term” :
          ValuationFormula) := by
    rw [compactParserSyntaxExactFuelTerm_value]
  let aligned := CertifiedPAContextProof.cast hformula raw
  have hcontext :
      valuationContext term.freeVariables (fun _ => 0) = ∅ := by
    rw [compactParserSyntaxExactFuelTerm_freeVariables_eq_empty]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext aligned
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _
    (CertifiedPAContextProof.cast _ raw)).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]
  exact compileTermValueEquality_payloadLength_le_resource (fun _ => 0) term

#print axioms compactParserSyntaxExactFuelTerm_value
#print axioms compactParserSyntaxExactFuelEqualityBound

end FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
