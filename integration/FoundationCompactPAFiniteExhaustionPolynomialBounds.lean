import integration.FoundationCompactPAFiniteExhaustionBounds

/-!
# Polynomial syntax bounds for finite PA exhaustion

This module starts the compression of the finite-exhaustion structural bound.
It proves a linear code bound for iterated successor numerals and a quadratic
code bound for the finite equality disjunction.  Both bounds depend only on
the actual syntax input and the numeric case count.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteExhaustionPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor

def finiteCaseAddTermCodeOverhead : Nat :=
  2 * (binaryNatCode 2).length +
    (binaryNatCode
      (Encodable.encode
        (Language.Add.add : LO.FirstOrder.Language.Func ℒₒᵣ 2))).length

theorem finiteCaseAddTerm_code_length_le
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode (finiteCaseAddTerm left right)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        finiteCaseAddTermCodeOverhead := by
  simp [finiteCaseAddTerm, Matrix.fun_eq_vec_two, binaryTermCode,
    finiteCaseAddTermCodeOverhead]
  omega

def iteratedSuccessorTermCodePolynomial
    (arity value : Nat) : Nat :=
  (binaryTermCode (finiteCaseZeroTerm arity)).length +
    value *
      ((binaryTermCode (finiteCaseOneTerm arity)).length +
        finiteCaseAddTermCodeOverhead)

theorem iteratedSuccessorTerm_code_length_le_polynomial
    (arity value : Nat) :
    (binaryTermCode (iteratedSuccessorTerm arity value)).length <=
      iteratedSuccessorTermCodePolynomial arity value := by
  induction value with
  | zero =>
      simp [iteratedSuccessorTermCodePolynomial]
  | succ value ih =>
      have hstep := finiteCaseAddTerm_code_length_le
        (iteratedSuccessorTerm arity value) (finiteCaseOneTerm arity)
      rw [iteratedSuccessorTerm_succ]
      calc
        (binaryTermCode
            (finiteCaseAddTerm (iteratedSuccessorTerm arity value)
              (finiteCaseOneTerm arity))).length <=
            (binaryTermCode (iteratedSuccessorTerm arity value)).length +
              (binaryTermCode (finiteCaseOneTerm arity)).length +
              finiteCaseAddTermCodeOverhead := hstep
        _ <= iteratedSuccessorTermCodePolynomial arity value +
              (binaryTermCode (finiteCaseOneTerm arity)).length +
              finiteCaseAddTermCodeOverhead := by omega
        _ = iteratedSuccessorTermCodePolynomial arity (value + 1) := by
          unfold iteratedSuccessorTermCodePolynomial
          ring

def finiteCaseEqualityFormulaCodeOverhead : Nat :=
  (binaryNatCode 0).length + (binaryNatCode 2).length +
    (binaryNatCode
      (Encodable.encode
        (Language.Eq.eq : LO.FirstOrder.Language.Rel ℒₒᵣ 2))).length

theorem finiteCaseEqualityFormula_code_length_le
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode (finiteCaseEqualityFormula left right)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        finiteCaseEqualityFormulaCodeOverhead := by
  simp [finiteCaseEqualityFormula, Matrix.fun_eq_vec_two,
    binaryFormulaCode, finiteCaseEqualityFormulaCodeOverhead]
  omega

theorem binaryFormulaCode_or_length_le_finite
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (left ⋎ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + (binaryNatCode 5).length := by
  simp [binaryFormulaCode]
  omega

def finiteEqualityCaseStepEnvelope
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity) : Nat :=
  (binaryTermCode (finiteCaseZeroTerm arity)).length +
    (binaryTermCode (finiteCaseOneTerm arity)).length +
    finiteCaseAddTermCodeOverhead +
    (binaryTermCode subject).length +
    finiteCaseEqualityFormulaCodeOverhead +
    (binaryNatCode 5).length + 1

theorem finiteCaseEqualityFormula_iterated_code_length_le_step
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (index : Nat) :
    (binaryFormulaCode
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm arity index) subject)).length <=
      (index + 1) * finiteEqualityCaseStepEnvelope subject := by
  let step :=
    (binaryTermCode (finiteCaseOneTerm arity)).length +
      finiteCaseAddTermCodeOverhead
  let fixed :=
    (binaryTermCode (finiteCaseZeroTerm arity)).length +
      (binaryTermCode subject).length +
      finiteCaseEqualityFormulaCodeOverhead
  let envelope := finiteEqualityCaseStepEnvelope subject
  have hterm := iteratedSuccessorTerm_code_length_le_polynomial arity index
  have hformula := finiteCaseEqualityFormula_code_length_le
    (iteratedSuccessorTerm arity index) subject
  have hstep : step <= envelope := by
    simp only [step, envelope, finiteEqualityCaseStepEnvelope]
    omega
  have hfixed : fixed <= envelope := by
    simp only [fixed, envelope, finiteEqualityCaseStepEnvelope]
    omega
  have hscaled := Nat.mul_le_mul_left index hstep
  calc
    (binaryFormulaCode
        (finiteCaseEqualityFormula
          (iteratedSuccessorTerm arity index) subject)).length <=
        (binaryTermCode (iteratedSuccessorTerm arity index)).length +
          (binaryTermCode subject).length +
          finiteCaseEqualityFormulaCodeOverhead := hformula
    _ <= fixed + index * step := by
      simp only [iteratedSuccessorTermCodePolynomial] at hterm
      simp only [fixed, step]
      omega
    _ <= envelope + index * envelope := by omega
    _ = (index + 1) * envelope := by ring

def finiteEqualityCasesCodePolynomial
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (bound : Nat) : Nat :=
  (binaryFormulaCode
      (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat arity)).length +
    (bound + 1) * (bound + 1) *
      finiteEqualityCaseStepEnvelope subject

theorem finiteEqualityCases_code_length_le_polynomial
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (bound : Nat) :
    (binaryFormulaCode (finiteEqualityCases subject bound)).length <=
      finiteEqualityCasesCodePolynomial subject bound := by
  induction bound with
  | zero =>
      simp [finiteEqualityCasesCodePolynomial]
  | succ bound ih =>
      let envelope := finiteEqualityCaseStepEnvelope subject
      have hequality :=
        finiteCaseEqualityFormula_iterated_code_length_le_step subject bound
      have hor := binaryFormulaCode_or_length_le_finite
        (finiteEqualityCases subject bound)
        (finiteCaseEqualityFormula
          (iteratedSuccessorTerm arity bound) subject)
      have htag : (binaryNatCode 5).length <= envelope := by
        simp only [envelope, finiteEqualityCaseStepEnvelope]
        omega
      have hbranch :
          (binaryFormulaCode
            (finiteCaseEqualityFormula
              (iteratedSuccessorTerm arity bound) subject)).length +
              (binaryNatCode 5).length <=
            (bound + 2) * envelope := by
        have htagScaled : (binaryNatCode 5).length <= envelope := htag
        dsimp only [envelope] at htagScaled ⊢
        calc
          _ <= (bound + 1) * finiteEqualityCaseStepEnvelope subject +
                finiteEqualityCaseStepEnvelope subject :=
            Nat.add_le_add hequality htagScaled
          _ = (bound + 2) * finiteEqualityCaseStepEnvelope subject := by
            ring
      have hcoefficient :
          (bound + 1) * (bound + 1) + (bound + 2) <=
            (bound + 2) * (bound + 2) := by
        nlinarith
      have hscaled :
          ((bound + 1) * (bound + 1) + (bound + 2)) * envelope <=
            (bound + 2) * (bound + 2) * envelope :=
        Nat.mul_le_mul_right envelope hcoefficient
      rw [finiteEqualityCases_succ]
      unfold finiteEqualityCasesCodePolynomial at ih ⊢
      dsimp only [envelope] at hbranch hscaled
      calc
        (binaryFormulaCode
            (finiteEqualityCases subject bound ⋎
              finiteCaseEqualityFormula
                (iteratedSuccessorTerm arity bound) subject)).length <=
            (binaryFormulaCode (finiteEqualityCases subject bound)).length +
              (binaryFormulaCode
                (finiteCaseEqualityFormula
                  (iteratedSuccessorTerm arity bound) subject)).length +
              (binaryNatCode 5).length := hor
        _ <= (binaryFormulaCode
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat arity)).length +
              (bound + 1) * (bound + 1) *
                finiteEqualityCaseStepEnvelope subject +
              ((binaryFormulaCode
                (finiteCaseEqualityFormula
                  (iteratedSuccessorTerm arity bound) subject)).length +
                (binaryNatCode 5).length) := by omega
        _ <= (binaryFormulaCode
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat arity)).length +
              (bound + 1) * (bound + 1) *
                finiteEqualityCaseStepEnvelope subject +
              (bound + 2) * finiteEqualityCaseStepEnvelope subject :=
          Nat.add_le_add_left hbranch _
        _ = (binaryFormulaCode
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat arity)).length +
              ((bound + 1) * (bound + 1) + (bound + 2)) *
                finiteEqualityCaseStepEnvelope subject := by ring
        _ <= (binaryFormulaCode
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat arity)).length +
              (bound + 2) * (bound + 2) *
                finiteEqualityCaseStepEnvelope subject :=
          Nat.add_le_add_left hscaled _

def finiteCaseLessThanFormulaCodeOverhead : Nat :=
  (binaryNatCode 0).length + (binaryNatCode 2).length +
    (binaryNatCode
      (Encodable.encode
        (Language.ORing.Rel.lt :
          LO.FirstOrder.Language.Rel ℒₒᵣ 2))).length

theorem finiteCaseLessThanFormula_code_length_le
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode (finiteCaseLessThanFormula left right)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        finiteCaseLessThanFormulaCodeOverhead := by
  simp [finiteCaseLessThanFormula, Matrix.fun_eq_vec_two,
    binaryFormulaCode, finiteCaseLessThanFormulaCodeOverhead]
  omega

def finiteLowerBoundFormulaCodePolynomial
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (bound : Nat) : Nat :=
  2 * ((binaryTermCode subject).length +
    iteratedSuccessorTermCodePolynomial arity bound +
    finiteCaseLessThanFormulaCodeOverhead)

theorem finiteLowerBoundLike_code_length_le_polynomial
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (bound : Nat) :
    (binaryFormulaCode
      (∼finiteCaseLessThanFormula subject
        (iteratedSuccessorTerm arity bound))).length <=
      finiteLowerBoundFormulaCodePolynomial subject bound := by
  have hterm := iteratedSuccessorTerm_code_length_le_polynomial arity bound
  have hrelation := finiteCaseLessThanFormula_code_length_le
    subject (iteratedSuccessorTerm arity bound)
  have hneg := binaryFormulaCode_neg_length_le
    (finiteCaseLessThanFormula subject
      (iteratedSuccessorTerm arity bound))
  unfold finiteLowerBoundFormulaCodePolynomial
  omega

def finiteExhaustionFormulaCodePolynomial
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (bound : Nat) : Nat :=
  finiteEqualityCasesCodePolynomial subject bound +
    finiteLowerBoundFormulaCodePolynomial subject bound +
    (binaryNatCode 5).length

theorem finiteExhaustionLike_code_length_le_polynomial
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (bound : Nat) :
    (binaryFormulaCode
      (finiteEqualityCases subject bound ⋎
        ∼finiteCaseLessThanFormula subject
          (iteratedSuccessorTerm arity bound))).length <=
      finiteExhaustionFormulaCodePolynomial subject bound := by
  have hcases := finiteEqualityCases_code_length_le_polynomial subject bound
  have hlower := finiteLowerBoundLike_code_length_le_polynomial subject bound
  have hor := binaryFormulaCode_or_length_le_finite
    (finiteEqualityCases subject bound)
    (∼finiteCaseLessThanFormula subject
      (iteratedSuccessorTerm arity bound))
  unfold finiteExhaustionFormulaCodePolynomial
  omega

theorem finiteExhaustionFormula_code_length_le_polynomial
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFormulaCode (finiteExhaustionFormula bound subject)).length <=
      finiteExhaustionFormulaCodePolynomial subject bound := by
  exact finiteExhaustionLike_code_length_le_polynomial subject bound

theorem finiteLowerBoundFormula_code_length_le_polynomial
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFormulaCode (finiteLowerBoundFormula bound subject)).length <=
      finiteLowerBoundFormulaCodePolynomial subject bound := by
  exact finiteLowerBoundLike_code_length_le_polynomial subject bound

theorem finiteExhaustionBody_code_length_le_polynomial
    (bound : Nat) :
    (binaryFormulaCode (finiteExhaustionBody bound)).length <=
      finiteExhaustionFormulaCodePolynomial
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bound := by
  exact finiteExhaustionLike_code_length_le_polynomial (#0) bound

#print axioms iteratedSuccessorTerm_code_length_le_polynomial
#print axioms finiteEqualityCases_code_length_le_polynomial
#print axioms finiteExhaustionFormula_code_length_le_polynomial
#print axioms finiteExhaustionBody_code_length_le_polynomial

end FoundationCompactPAFiniteExhaustionPolynomialBounds
