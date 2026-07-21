import integration.FoundationCompactPAFiniteExhaustionPolynomialBounds
import integration.FoundationCompactPAContextCostPolynomialBounds
import integration.FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-!
# Full payload compression for finite PA exhaustion

This module turns the exact recursive payload ledger of finite exhaustion into
one fixed polynomial.  The first layer below gives every generated case formula
one common syntax coordinate; later layers charge each proof constructor and
recursive case step to that coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteCaseAdvance
open FoundationCompactPALowerBoundSuccessor
open FoundationCompactPACertifiedInduction
open FoundationCompactPAFiniteExhaustionBase
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionInduction
open FoundationCompactPAFiniteExhaustionBounds
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedUniversalIntroduction
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

theorem iteratedSuccessorTermCodePolynomial_mono
    (arity : Nat) {small large : Nat} (h : small <= large) :
    iteratedSuccessorTermCodePolynomial arity small <=
      iteratedSuccessorTermCodePolynomial arity large := by
  unfold iteratedSuccessorTermCodePolynomial
  gcongr

theorem finiteEqualityCasesCodePolynomial_mono
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    {small large : Nat} (h : small <= large) :
    finiteEqualityCasesCodePolynomial subject small <=
      finiteEqualityCasesCodePolynomial subject large := by
  unfold finiteEqualityCasesCodePolynomial
  gcongr

theorem finiteLowerBoundFormulaCodePolynomial_mono
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    {small large : Nat} (h : small <= large) :
    finiteLowerBoundFormulaCodePolynomial subject small <=
      finiteLowerBoundFormulaCodePolynomial subject large := by
  have hterm := iteratedSuccessorTermCodePolynomial_mono arity h
  unfold finiteLowerBoundFormulaCodePolynomial
  omega

theorem finiteExhaustionFormulaCodePolynomial_mono
    {arity : Nat}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    {small large : Nat} (h : small <= large) :
    finiteExhaustionFormulaCodePolynomial subject small <=
      finiteExhaustionFormulaCodePolynomial subject large := by
  have hcases := finiteEqualityCasesCodePolynomial_mono subject h
  have hlower := finiteLowerBoundFormulaCodePolynomial_mono subject h
  unfold finiteExhaustionFormulaCodePolynomial
  omega

def finiteCaseFormulaEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  16 * (finiteEqualityCasesCodePolynomial subject (bound + 2) +
    finiteLowerBoundFormulaCodePolynomial subject (bound + 2) +
    finiteExhaustionFormulaCodePolynomial subject (bound + 2) +
    (bound + 3) * finiteEqualityCaseStepEnvelope subject +
    (binaryFormulaCode
      (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length + 1)

theorem finiteEqualityCases_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    (binaryFormulaCode (finiteEqualityCases subject index)).length <=
      finiteCaseFormulaEnvelope subject bound := by
  have hraw := finiteEqualityCases_code_length_le_polynomial subject index
  have hmono := finiteEqualityCasesCodePolynomial_mono subject hindex
  unfold finiteCaseFormulaEnvelope
  omega

theorem finiteCaseEqualityFormula_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    (binaryFormulaCode
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 index) subject)).length <=
      finiteCaseFormulaEnvelope subject bound := by
  have hraw := finiteCaseEqualityFormula_iterated_code_length_le_step
    subject index
  have hcoefficient : index + 1 <= bound + 3 := by omega
  have hscaled := Nat.mul_le_mul_right
    (finiteEqualityCaseStepEnvelope subject) hcoefficient
  unfold finiteCaseFormulaEnvelope
  omega

theorem finiteLowerBoundFormula_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    (binaryFormulaCode
      (finiteLowerBoundFormula index subject)).length <=
      finiteCaseFormulaEnvelope subject bound := by
  have hraw := finiteLowerBoundFormula_code_length_le_polynomial
    index subject
  have hmono := finiteLowerBoundFormulaCodePolynomial_mono subject hindex
  unfold finiteCaseFormulaEnvelope
  omega

theorem finiteExhaustionFormula_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    (binaryFormulaCode
      (finiteExhaustionFormula index subject)).length <=
      finiteCaseFormulaEnvelope subject bound := by
  have hraw := finiteExhaustionFormula_code_length_le_polynomial
    index subject
  have hmono := finiteExhaustionFormulaCodePolynomial_mono subject hindex
  unfold finiteCaseFormulaEnvelope
  omega

theorem negatedFiniteEqualityCases_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    (binaryFormulaCode
      (∼finiteEqualityCases subject index)).length <=
      finiteCaseFormulaEnvelope subject bound := by
  have hformulaRaw := finiteEqualityCases_code_length_le_polynomial
    subject index
  have hmono := finiteEqualityCasesCodePolynomial_mono subject hindex
  have hformula : (binaryFormulaCode
      (finiteEqualityCases subject index)).length <=
      finiteEqualityCasesCodePolynomial subject (bound + 2) :=
    hformulaRaw.trans hmono
  have hraw := binaryFormulaCode_neg_length_le
    (finiteEqualityCases subject index)
  unfold finiteCaseFormulaEnvelope at hformula ⊢
  omega

theorem negatedFiniteCaseEqualityFormula_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    (binaryFormulaCode
      (∼finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 index) subject)).length <=
      finiteCaseFormulaEnvelope subject bound := by
  have hformulaRaw := finiteCaseEqualityFormula_iterated_code_length_le_step
    subject index
  have hcoefficient : index + 1 <= bound + 3 := by omega
  have hscaled := Nat.mul_le_mul_right
    (finiteEqualityCaseStepEnvelope subject) hcoefficient
  have hformula : (binaryFormulaCode
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 index) subject)).length <=
      (bound + 3) * finiteEqualityCaseStepEnvelope subject :=
    hformulaRaw.trans hscaled
  have hraw := binaryFormulaCode_neg_length_le
    (finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 index) subject)
  unfold finiteCaseFormulaEnvelope at hformula ⊢
  omega

theorem negatedFiniteExhaustionFormula_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    (binaryFormulaCode
      (∼finiteExhaustionFormula index subject)).length <=
      finiteCaseFormulaEnvelope subject bound := by
  have hformulaRaw := finiteExhaustionFormula_code_length_le_polynomial
    index subject
  have hmono := finiteExhaustionFormulaCodePolynomial_mono subject hindex
  have hformula : (binaryFormulaCode
      (finiteExhaustionFormula index subject)).length <=
      finiteExhaustionFormulaCodePolynomial subject (bound + 2) :=
    hformulaRaw.trans hmono
  have hraw := binaryFormulaCode_neg_length_le
    (finiteExhaustionFormula index subject)
  unfold finiteCaseFormulaEnvelope at hformula ⊢
  omega

theorem negatedFalse_code_le_caseEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    (binaryFormulaCode
      (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length <=
      finiteCaseFormulaEnvelope subject bound := by
  unfold finiteCaseFormulaEnvelope
  omega

def finiteAdvanceFormulaEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  4 * (finiteCaseFormulaEnvelope subject bound +
    finiteCaseFormulaEnvelope (successorOf subject) bound + 1)

theorem finiteCaseFormulaEnvelope_le_advance
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    finiteCaseFormulaEnvelope subject bound <=
      finiteAdvanceFormulaEnvelope subject bound := by
  unfold finiteAdvanceFormulaEnvelope
  omega

theorem successorFiniteCaseFormulaEnvelope_le_advance
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    finiteCaseFormulaEnvelope (successorOf subject) bound <=
      finiteAdvanceFormulaEnvelope subject bound := by
  unfold finiteAdvanceFormulaEnvelope
  omega

/-! ## Uniform term coordinates for every finite branch -/

def finiteClosedTermEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  4 * ((binaryTermCode subject).length +
    (binaryTermCode (successorOf subject)).length +
    iteratedSuccessorTermCodePolynomial 0 (bound + 3) + 1)

def finiteOpenTermEnvelope (bound : Nat) : Nat :=
  4 * ((binaryTermCode unarySuccessorTerm).length +
    iteratedSuccessorTermCodePolynomial 1 (bound + 3) + 1)

theorem subject_code_le_finiteClosedTermEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    (binaryTermCode subject).length <=
      finiteClosedTermEnvelope subject bound := by
  unfold finiteClosedTermEnvelope
  omega

theorem successorSubject_code_le_finiteClosedTermEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    (binaryTermCode (successorOf subject)).length <=
      finiteClosedTermEnvelope subject bound := by
  unfold finiteClosedTermEnvelope
  omega

theorem iteratedSuccessorTerm_code_le_finiteClosedTermEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 3) :
    (binaryTermCode (iteratedSuccessorTerm 0 index)).length <=
      finiteClosedTermEnvelope subject bound := by
  have hraw := iteratedSuccessorTerm_code_length_le_polynomial 0 index
  have hmono := iteratedSuccessorTermCodePolynomial_mono 0 hindex
  unfold finiteClosedTermEnvelope
  omega

theorem unarySuccessorTerm_code_le_finiteOpenTermEnvelope
    (bound : Nat) :
    (binaryTermCode unarySuccessorTerm).length <=
      finiteOpenTermEnvelope bound := by
  unfold finiteOpenTermEnvelope
  omega

theorem iteratedSuccessorTerm_open_code_le_finiteOpenTermEnvelope
    (index bound : Nat) (hindex : index <= bound + 3) :
    (binaryTermCode (iteratedSuccessorTerm 1 index)).length <=
      finiteOpenTermEnvelope bound := by
  have hraw := iteratedSuccessorTerm_code_length_le_polynomial 1 index
  have hmono := iteratedSuccessorTermCodePolynomial_mono 1 hindex
  unfold finiteOpenTermEnvelope
  omega

/-! ## The two branch-local proof producers under one fixed polynomial -/

def finiteSuccessorEqualityPayloadEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  let closedTermBound := finiteClosedTermEnvelope subject bound
  let openTermBound := finiteOpenTermEnvelope bound
  openTermBound *
    uniformUnaryTransportLocalEnvelope closedTermBound openTermBound

theorem successorEqualityUnderCaseStructuralPayloadBound_le_polynomial
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) (hindex : index <= bound + 2) :
    successorEqualityUnderCaseStructuralPayloadBound index subject <=
      finiteSuccessorEqualityPayloadEnvelope subject bound := by
  let left := iteratedSuccessorTerm 0 index
  let closedTermBound := finiteClosedTermEnvelope subject bound
  let openTermBound := finiteOpenTermEnvelope bound
  have hleft : (binaryTermCode left).length <= closedTermBound := by
    dsimp only [left, closedTermBound]
    exact iteratedSuccessorTerm_code_le_finiteClosedTermEnvelope
      subject index bound (by omega)
  have hright : (binaryTermCode subject).length <= closedTermBound := by
    dsimp only [closedTermBound]
    exact subject_code_le_finiteClosedTermEnvelope subject bound
  have hopen : (binaryTermCode unarySuccessorTerm).length <=
      openTermBound := by
    dsimp only [openTermBound]
    exact unarySuccessorTerm_code_le_finiteOpenTermEnvelope bound
  have hraw :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_openCode
      unarySuccessorTerm left subject openTermBound hopen
  have hlocal := unaryTransportLocalEnvelope_le_uniform
    left subject closedTermBound openTermBound hleft hright
  unfold successorEqualityUnderCaseStructuralPayloadBound
    finiteSuccessorEqualityPayloadEnvelope
  dsimp only [left, closedTermBound, openTermBound] at hraw hlocal ⊢
  exact hraw.trans (Nat.mul_le_mul_left _ hlocal)

def finiteFinalLowerPayloadEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  let closedTermBound := finiteClosedTermEnvelope subject bound
  let openTermBound := finiteOpenTermEnvelope bound
  uniformAtomicTransportPayloadEnvelope closedTermBound openTermBound
    (orderPrimitiveCostEnvelope closedTermBound)

theorem finalLowerBoundUnderCaseStructuralPayloadBound_le_polynomial
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) (hindex : index <= bound + 2) :
    finalLowerBoundUnderCaseStructuralPayloadBound index subject <=
      finiteFinalLowerPayloadEnvelope subject bound := by
  let left := iteratedSuccessorTerm 0 index
  let closedTermBound := finiteClosedTermEnvelope subject bound
  let openTermBound := finiteOpenTermEnvelope bound
  let sourcePayloadBound := ltIrreflFullPayloadBound
    (iteratedSuccessorTerm 0 (index + 1))
  let uniformSourcePayloadBound := orderPrimitiveCostEnvelope closedTermBound
  have hleft : (binaryTermCode left).length <= closedTermBound := by
    dsimp only [left, closedTermBound]
    exact iteratedSuccessorTerm_code_le_finiteClosedTermEnvelope
      subject index bound (by omega)
  have hright : (binaryTermCode subject).length <= closedTermBound := by
    dsimp only [closedTermBound]
    exact subject_code_le_finiteClosedTermEnvelope subject bound
  have hfirst :
      (binaryTermCode ((finalCaseArguments index) 0)).length <=
        openTermBound := by
    dsimp only [openTermBound]
    simpa [finalCaseArguments] using
      unarySuccessorTerm_code_le_finiteOpenTermEnvelope bound
  have hsecond :
      (binaryTermCode ((finalCaseArguments index) 1)).length <=
        openTermBound := by
    dsimp only [openTermBound]
    simpa [finalCaseArguments] using
      iteratedSuccessorTerm_open_code_le_finiteOpenTermEnvelope
        (index + 1) bound (by omega)
  have hsourceTerm :
      (binaryTermCode (iteratedSuccessorTerm 0 (index + 1))).length <=
        closedTermBound := by
    dsimp only [closedTermBound]
    exact iteratedSuccessorTerm_code_le_finiteClosedTermEnvelope
      subject (index + 1) bound (by omega)
  have hsource : sourcePayloadBound <= uniformSourcePayloadBound := by
    dsimp only [sourcePayloadBound, uniformSourcePayloadBound]
    exact ltIrreflFullPayloadBound_le_primitive
      (iteratedSuccessorTerm 0 (index + 1)) closedTermBound hsourceTerm
  have hraw :=
    negativeTransportUnderAssumptionStructuralPayloadBound_le_polynomial
      Language.ORing.Rel.lt (finalCaseArguments index) left subject
      sourcePayloadBound openTermBound hfirst hsecond
  have hwiden := atomicTransportPayloadEnvelope_mono left subject
    (smallOpen := openTermBound) (largeOpen := openTermBound)
    (smallSource := sourcePayloadBound)
    (largeSource := uniformSourcePayloadBound) le_rfl hsource
  have huniform := atomicTransportPayloadEnvelope_le_uniform
    left subject closedTermBound openTermBound uniformSourcePayloadBound
    hleft hright
  unfold finalLowerBoundUnderCaseStructuralPayloadBound
    finiteFinalLowerPayloadEnvelope
  dsimp only [left, closedTermBound, openTermBound, sourcePayloadBound,
    uniformSourcePayloadBound] at hraw hwiden huniform ⊢
  exact hraw.trans (hwiden.trans huniform)

/-! ## Charging every finite disjunction injection to one local resource -/

theorem finiteEqualityCaseDisjunctionCost_le_resource
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound resource : Nat)
    (hindex : index + 1 <= bound + 2)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hcase : finiteCaseFormulaEnvelope subject bound <= resource) :
    CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
        (finiteEqualityCases subject index)
        (finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) subject) <=
      smallContextAssemblyEnvelope resource := by
  have hleft := (finiteEqualityCases_code_le_caseEnvelope
    subject index bound (by omega)).trans hcase
  have hright := (finiteCaseEqualityFormula_code_le_caseEnvelope
    subject index bound (by omega)).trans hcase
  have hdisjunctionRaw := finiteEqualityCases_code_le_caseEnvelope
    subject (index + 1) bound hindex
  have hdisjunction :
      (binaryFormulaCode
        (finiteEqualityCases subject index ⋎
          finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 index) subject)).length <=
        resource := by
    rw [← finiteEqualityCases_succ]
    exact hdisjunctionRaw.trans hcase
  exact disjunctionFullAssemblyCost_le_small Gamma
    (finiteEqualityCases subject index)
    (finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 index) subject)
    resource hcard hGamma hleft hright hdisjunction

theorem finiteEqualityCaseContext_formulaCodeBound_advance
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    FormulaCodeBound
      ({∼finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) subject} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (finiteAdvanceFormulaEnvelope subject bound) := by
  intro formula hformula
  simp only [Finset.mem_singleton] at hformula
  subst formula
  exact (negatedFiniteCaseEqualityFormula_code_le_caseEnvelope
    subject index bound hindex).trans
      (finiteCaseFormulaEnvelope_le_advance subject bound)

theorem advanceInjectEqualityCaseStructuralPayloadBound_le_polynomial
    (prefixLength remainingLength : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat)
    (htotal : prefixLength + 1 + remainingLength + 1 <= bound + 2) :
    injectEqualityCaseStructuralPayloadBound
        ({∼finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 prefixLength) subject} :
          Finset LO.FirstOrder.ArithmeticProposition)
        (prefixLength + 1) remainingLength (successorOf subject)
        (successorEqualityUnderCaseStructuralPayloadBound
          prefixLength subject) <=
      finiteSuccessorEqualityPayloadEnvelope subject bound +
        (remainingLength + 1) *
          smallContextAssemblyEnvelope
            (finiteAdvanceFormulaEnvelope subject bound) := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 prefixLength) subject}
  let resource := finiteAdvanceFormulaEnvelope subject bound
  let localCost := smallContextAssemblyEnvelope resource
  have hprefix : prefixLength <= bound + 2 := by omega
  have hcard : Gamma.card <= 4 := by
    dsimp only [Gamma]
    simp
  have hGamma : FormulaCodeBound Gamma resource := by
    dsimp only [Gamma, resource]
    exact finiteEqualityCaseContext_formulaCodeBound_advance
      subject prefixLength bound hprefix
  have hcase : finiteCaseFormulaEnvelope (successorOf subject) bound <=
      resource := by
    dsimp only [resource]
    exact successorFiniteCaseFormulaEnvelope_le_advance subject bound
  have hequality :=
    successorEqualityUnderCaseStructuralPayloadBound_le_polynomial
      prefixLength subject bound hprefix
  induction remainingLength with
  | zero =>
      have hcost := finiteEqualityCaseDisjunctionCost_le_resource
        (Gamma := Gamma) (successorOf subject) (prefixLength + 1)
        bound resource (by omega) hcard hGamma hcase
      simp only [injectEqualityCaseStructuralPayloadBound]
      dsimp only [Gamma, resource, localCost] at hequality hcost ⊢
      calc
        successorEqualityUnderCaseStructuralPayloadBound prefixLength subject +
              CertifiedPAContextProof.disjunctionFullAssemblyCost
                {∼finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 prefixLength) subject}
                (finiteEqualityCases (successorOf subject)
                  (prefixLength + 1))
                (finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 (prefixLength + 1))
                  (successorOf subject)) <=
            finiteSuccessorEqualityPayloadEnvelope subject bound +
              smallContextAssemblyEnvelope
                (finiteAdvanceFormulaEnvelope subject bound) :=
          Nat.add_le_add hequality hcost
        _ = finiteSuccessorEqualityPayloadEnvelope subject bound +
              (0 + 1) * smallContextAssemblyEnvelope
                (finiteAdvanceFormulaEnvelope subject bound) := by ring
  | succ remainingLength ih =>
      have hsmaller :
          prefixLength + 1 + remainingLength + 1 <= bound + 2 := by omega
      have hprevious := ih hsmaller
      have hcost := finiteEqualityCaseDisjunctionCost_le_resource
        (Gamma := Gamma) (successorOf subject)
        (Nat.succ (prefixLength + 1 + remainingLength)) bound resource
        (by omega) hcard hGamma hcase
      simp only [injectEqualityCaseStructuralPayloadBound]
      dsimp only [Gamma, resource, localCost] at hprevious hcost ⊢
      calc
        injectEqualityCaseStructuralPayloadBound
              {∼finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 prefixLength) subject}
              (prefixLength + 1) remainingLength (successorOf subject)
              (successorEqualityUnderCaseStructuralPayloadBound
                prefixLength subject) +
            CertifiedPAContextProof.disjunctionFullAssemblyCost
              {∼finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 prefixLength) subject}
              (finiteEqualityCases (successorOf subject)
                (Nat.succ (prefixLength + 1 + remainingLength)))
              (finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0
                  (Nat.succ (prefixLength + 1 + remainingLength)))
                (successorOf subject)) <=
            (finiteSuccessorEqualityPayloadEnvelope subject bound +
              (remainingLength + 1) *
                smallContextAssemblyEnvelope
                  (finiteAdvanceFormulaEnvelope subject bound)) +
              smallContextAssemblyEnvelope
                (finiteAdvanceFormulaEnvelope subject bound) :=
          Nat.add_le_add hprevious hcost
        _ = finiteSuccessorEqualityPayloadEnvelope subject bound +
              (remainingLength + 1 + 1) *
                smallContextAssemblyEnvelope
                  (finiteAdvanceFormulaEnvelope subject bound) := by ring

/-! ## The three outer constructors used by prefix advancement -/

theorem finiteExFalsoAssumptionCost_le_advance
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
        (finiteExhaustionFormula index (successorOf subject)) <=
      smallContextAssemblyEnvelope
        (finiteAdvanceFormulaEnvelope subject bound) := by
  have htarget := (finiteExhaustionFormula_code_le_caseEnvelope
    (successorOf subject) index bound hindex).trans
      (successorFiniteCaseFormulaEnvelope_le_advance subject bound)
  have hfalse := (negatedFalse_code_le_caseEnvelope subject bound).trans
    (finiteCaseFormulaEnvelope_le_advance subject bound)
  exact exFalsoAssumptionFullPayloadCost_le_small
    (finiteExhaustionFormula index (successorOf subject))
    (finiteAdvanceFormulaEnvelope subject bound) htarget hfalse

theorem finiteExhaustionDisjunctionCost_le_advance
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (contextIndex totalBound bound : Nat)
    (hcontextIndex : contextIndex <= bound + 2)
    (htotalBound : totalBound <= bound + 2) :
    CertifiedPAContextProof.disjunctionFullAssemblyCost
        ({∼finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 contextIndex) subject} :
          Finset LO.FirstOrder.ArithmeticProposition)
        (finiteEqualityCases (successorOf subject) totalBound)
        (finiteLowerBoundFormula totalBound (successorOf subject)) <=
      smallContextAssemblyEnvelope
        (finiteAdvanceFormulaEnvelope subject bound) := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 contextIndex) subject}
  let resource := finiteAdvanceFormulaEnvelope subject bound
  have hcard : Gamma.card <= 4 := by
    dsimp only [Gamma]
    simp
  have hGamma : FormulaCodeBound Gamma resource := by
    dsimp only [Gamma, resource]
    exact finiteEqualityCaseContext_formulaCodeBound_advance
      subject contextIndex bound hcontextIndex
  have hleft := (finiteEqualityCases_code_le_caseEnvelope
    (successorOf subject) totalBound bound htotalBound).trans
      (successorFiniteCaseFormulaEnvelope_le_advance subject bound)
  have hright := (finiteLowerBoundFormula_code_le_caseEnvelope
    (successorOf subject) totalBound bound htotalBound).trans
      (successorFiniteCaseFormulaEnvelope_le_advance subject bound)
  have hdisjunctionRaw := (finiteExhaustionFormula_code_le_caseEnvelope
    (successorOf subject) totalBound bound htotalBound).trans
      (successorFiniteCaseFormulaEnvelope_le_advance subject bound)
  have hdisjunction :
      (binaryFormulaCode
        (finiteEqualityCases (successorOf subject) totalBound ⋎
          finiteLowerBoundFormula totalBound
            (successorOf subject))).length <= resource := by
    simpa [finiteExhaustionFormula, finiteLowerBoundFormula] using
      hdisjunctionRaw
  exact disjunctionFullAssemblyCost_le_small Gamma
    (finiteEqualityCases (successorOf subject) totalBound)
    (finiteLowerBoundFormula totalBound (successorOf subject))
    resource hcard hGamma hleft hright hdisjunction

theorem finiteEliminateCaseCost_le_advance
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (prefixLength totalBound bound : Nat)
    (hprefix : prefixLength + 1 <= bound + 2)
    (htotal : totalBound <= bound + 2) :
    CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        ∅ (finiteExhaustionFormula totalBound (successorOf subject))
        (finiteEqualityCases subject prefixLength)
        (finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 prefixLength) subject) <=
      smallContextAssemblyEnvelope
        (finiteAdvanceFormulaEnvelope subject bound) := by
  let resource := finiteAdvanceFormulaEnvelope subject bound
  have hGamma : FormulaCodeBound
      (∅ : Finset LO.FirstOrder.ArithmeticProposition) resource := by
    intro formula hformula
    simp at hformula
  have htarget := (finiteExhaustionFormula_code_le_caseEnvelope
    (successorOf subject) totalBound bound htotal).trans
      (successorFiniteCaseFormulaEnvelope_le_advance subject bound)
  have hnegatedLeft := (negatedFiniteEqualityCases_code_le_caseEnvelope
    subject prefixLength bound (by omega)).trans
      (finiteCaseFormulaEnvelope_le_advance subject bound)
  have hnegatedRight :=
    (negatedFiniteCaseEqualityFormula_code_le_caseEnvelope
      subject prefixLength bound (by omega)).trans
        (finiteCaseFormulaEnvelope_le_advance subject bound)
  have hnegatedDisjunctionRaw :=
    (negatedFiniteEqualityCases_code_le_caseEnvelope
      subject (prefixLength + 1) bound hprefix).trans
        (finiteCaseFormulaEnvelope_le_advance subject bound)
  have hnegatedDisjunction :
      (binaryFormulaCode
        (∼(finiteEqualityCases subject prefixLength ⋎
          finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 prefixLength) subject))).length <=
        resource := by
    simpa only [finiteEqualityCases_succ] using hnegatedDisjunctionRaw
  exact eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    (∅ : Finset LO.FirstOrder.ArithmeticProposition)
    (finiteExhaustionFormula totalBound (successorOf subject))
    (finiteEqualityCases subject prefixLength)
    (finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 prefixLength) subject)
    resource (by simp) hGamma htarget hnegatedLeft hnegatedRight
    hnegatedDisjunction

def finiteAdvanceLocalPayloadEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  finiteSuccessorEqualityPayloadEnvelope subject bound +
    finiteFinalLowerPayloadEnvelope subject bound +
    4 * smallContextAssemblyEnvelope
      (finiteAdvanceFormulaEnvelope subject bound) + 1

theorem finiteSuccessorEqualityPayloadEnvelope_le_advanceLocal
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    finiteSuccessorEqualityPayloadEnvelope subject bound <=
      finiteAdvanceLocalPayloadEnvelope subject bound := by
  unfold finiteAdvanceLocalPayloadEnvelope
  omega

theorem finiteFinalLowerPayloadEnvelope_le_advanceLocal
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    finiteFinalLowerPayloadEnvelope subject bound <=
      finiteAdvanceLocalPayloadEnvelope subject bound := by
  unfold finiteAdvanceLocalPayloadEnvelope
  omega

theorem finiteAdvanceContextCost_le_local
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) :
    smallContextAssemblyEnvelope
        (finiteAdvanceFormulaEnvelope subject bound) <=
      finiteAdvanceLocalPayloadEnvelope subject bound := by
  unfold finiteAdvanceLocalPayloadEnvelope
  omega

/-! ## Polynomial compression of the complete prefix recursion -/

def advanceFiniteCasePrefixPayloadPolynomial
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound prefixLength : Nat) : Nat :=
  (prefixLength + 1) * (bound + 5) *
    finiteAdvanceLocalPayloadEnvelope subject bound

theorem advanceFiniteCasePrefixStructuralPayloadBound_le_polynomial
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (prefixLength remainingLength bound : Nat)
    (htotal : prefixLength + remainingLength <= bound + 2) :
    advanceFiniteCasePrefixStructuralPayloadBound
        subject prefixLength remainingLength <=
      advanceFiniteCasePrefixPayloadPolynomial
        subject bound prefixLength := by
  let localCost := finiteAdvanceLocalPayloadEnvelope subject bound
  have hcontextLocal :
      smallContextAssemblyEnvelope
          (finiteAdvanceFormulaEnvelope subject bound) <= localCost := by
    dsimp only [localCost]
    exact finiteAdvanceContextCost_le_local subject bound
  induction prefixLength generalizing remainingLength with
  | zero =>
      have hbase := finiteExFalsoAssumptionCost_le_advance
        subject remainingLength bound (by omega)
      have hbaseLocal :
          CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
              (finiteExhaustionFormula remainingLength
                (successorOf subject)) <= localCost :=
        hbase.trans hcontextLocal
      have hscale : localCost <= (bound + 5) * localCost := by
        have := Nat.mul_le_mul_right localCost (show 1 <= bound + 5 by omega)
        simpa using this
      simp only [advanceFiniteCasePrefixStructuralPayloadBound]
      unfold advanceFiniteCasePrefixPayloadPolynomial
      dsimp only [localCost] at hbaseLocal hscale ⊢
      exact hbaseLocal.trans (by simpa using hscale)
  | succ prefixLength ih =>
      cases remainingLength with
      | zero =>
          have hleft := ih 1 (by omega)
          have hfinalRaw :=
            finalLowerBoundUnderCaseStructuralPayloadBound_le_polynomial
              prefixLength subject bound (by omega)
          have hfinal :
              finalLowerBoundUnderCaseStructuralPayloadBound
                  prefixLength subject <= localCost :=
            hfinalRaw.trans (by
              dsimp only [localCost]
              exact finiteFinalLowerPayloadEnvelope_le_advanceLocal
                subject bound)
          have hdisjunctionRaw :=
            finiteExhaustionDisjunctionCost_le_advance
              subject prefixLength (prefixLength + 1) bound
              (by omega) (by omega)
          have hdisjunction :
              CertifiedPAContextProof.disjunctionFullAssemblyCost
                  ({∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 prefixLength) subject} :
                    Finset LO.FirstOrder.ArithmeticProposition)
                  (finiteEqualityCases (successorOf subject)
                    (prefixLength + 1))
                  (finiteLowerBoundFormula (prefixLength + 1)
                    (successorOf subject)) <= localCost :=
            hdisjunctionRaw.trans hcontextLocal
          have heliminateRaw := finiteEliminateCaseCost_le_advance
            subject prefixLength (prefixLength + 1) bound
            (by omega) (by omega)
          have heliminate :
              CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
                  ∅ (finiteExhaustionFormula (prefixLength + 1)
                    (successorOf subject))
                  (finiteEqualityCases subject prefixLength)
                  (finiteCaseEqualityFormula
                    (iteratedSuccessorTerm 0 prefixLength) subject) <=
                localCost := heliminateRaw.trans hcontextLocal
          have hchunk :
              (finalLowerBoundUnderCaseStructuralPayloadBound
                  prefixLength subject +
                CertifiedPAContextProof.disjunctionFullAssemblyCost
                  ({∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 prefixLength) subject} :
                    Finset LO.FirstOrder.ArithmeticProposition)
                  (finiteEqualityCases (successorOf subject)
                    (prefixLength + 1))
                  (finiteLowerBoundFormula (prefixLength + 1)
                    (successorOf subject))) +
                CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
                  ∅ (finiteExhaustionFormula (prefixLength + 1)
                    (successorOf subject))
                  (finiteEqualityCases subject prefixLength)
                  (finiteCaseEqualityFormula
                    (iteratedSuccessorTerm 0 prefixLength) subject) <=
                (bound + 5) * localCost := by
            calc
              _ <= localCost + localCost + localCost :=
                Nat.add_le_add (Nat.add_le_add hfinal hdisjunction) heliminate
              _ = 3 * localCost := by ring
              _ <= (bound + 5) * localCost :=
                Nat.mul_le_mul_right localCost (by omega)
          simp only [advanceFiniteCasePrefixStructuralPayloadBound]
          unfold advanceFiniteCasePrefixPayloadPolynomial at hleft ⊢
          dsimp only [localCost] at hleft hchunk ⊢
          calc
            _ <= ((prefixLength + 1) * (bound + 5) *
                    finiteAdvanceLocalPayloadEnvelope subject bound) +
                  (bound + 5) *
                    finiteAdvanceLocalPayloadEnvelope subject bound := by
              rw [Nat.add_assoc]
              exact Nat.add_le_add hleft hchunk
            _ = (prefixLength + 1 + 1) * (bound + 5) *
                  finiteAdvanceLocalPayloadEnvelope subject bound := by ring
      | succ remainingLength =>
          have hleft := ih (remainingLength + 2) (by omega)
          have hinjectRaw :=
            advanceInjectEqualityCaseStructuralPayloadBound_le_polynomial
              prefixLength remainingLength subject bound (by omega)
          have hequalityLocal :
              finiteSuccessorEqualityPayloadEnvelope subject bound <=
                localCost := by
            dsimp only [localCost]
            exact finiteSuccessorEqualityPayloadEnvelope_le_advanceLocal
              subject bound
          have hinject :
              injectEqualityCaseStructuralPayloadBound
                  ({∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 prefixLength) subject} :
                    Finset LO.FirstOrder.ArithmeticProposition)
                  (prefixLength + 1) remainingLength (successorOf subject)
                  (successorEqualityUnderCaseStructuralPayloadBound
                    prefixLength subject) <=
                localCost + (remainingLength + 1) * localCost := by
            exact hinjectRaw.trans
              (Nat.add_le_add hequalityLocal
                (Nat.mul_le_mul_left _ hcontextLocal))
          let totalBound := (prefixLength + 1) + (remainingLength + 1)
          have hdisjunctionRaw :=
            finiteExhaustionDisjunctionCost_le_advance
              subject prefixLength totalBound bound (by omega) (by
                dsimp only [totalBound]
                omega)
          have hdisjunction :
              CertifiedPAContextProof.disjunctionFullAssemblyCost
                  ({∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 prefixLength) subject} :
                    Finset LO.FirstOrder.ArithmeticProposition)
                  (finiteEqualityCases (successorOf subject) totalBound)
                  (finiteLowerBoundFormula totalBound
                    (successorOf subject)) <= localCost :=
            hdisjunctionRaw.trans hcontextLocal
          have heliminateRaw := finiteEliminateCaseCost_le_advance
            subject prefixLength totalBound bound (by omega) (by
              dsimp only [totalBound]
              omega)
          have heliminate :
              CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
                  ∅ (finiteExhaustionFormula totalBound
                    (successorOf subject))
                  (finiteEqualityCases subject prefixLength)
                  (finiteCaseEqualityFormula
                    (iteratedSuccessorTerm 0 prefixLength) subject) <=
                localCost := heliminateRaw.trans hcontextLocal
          have hcoefficient : remainingLength + 4 <= bound + 5 := by omega
          have hchunk :
              injectEqualityCaseStructuralPayloadBound
                    ({∼finiteCaseEqualityFormula
                        (iteratedSuccessorTerm 0 prefixLength) subject} :
                      Finset LO.FirstOrder.ArithmeticProposition)
                    (prefixLength + 1) remainingLength
                    (successorOf subject)
                    (successorEqualityUnderCaseStructuralPayloadBound
                      prefixLength subject) +
                  CertifiedPAContextProof.disjunctionFullAssemblyCost
                    ({∼finiteCaseEqualityFormula
                        (iteratedSuccessorTerm 0 prefixLength) subject} :
                      Finset LO.FirstOrder.ArithmeticProposition)
                    (finiteEqualityCases (successorOf subject) totalBound)
                    (finiteLowerBoundFormula totalBound
                      (successorOf subject)) +
                CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
                  ∅ (finiteExhaustionFormula totalBound
                    (successorOf subject))
                  (finiteEqualityCases subject prefixLength)
                  (finiteCaseEqualityFormula
                    (iteratedSuccessorTerm 0 prefixLength) subject) <=
                (bound + 5) * localCost := by
            calc
              _ <= (localCost + (remainingLength + 1) * localCost) +
                    localCost + localCost :=
                Nat.add_le_add (Nat.add_le_add hinject hdisjunction) heliminate
              _ = (remainingLength + 4) * localCost := by ring
              _ <= (bound + 5) * localCost :=
                Nat.mul_le_mul_right localCost hcoefficient
          simp only [advanceFiniteCasePrefixStructuralPayloadBound]
          unfold advanceFiniteCasePrefixPayloadPolynomial at hleft ⊢
          dsimp only [localCost, totalBound] at hleft hchunk ⊢
          calc
            _ <= ((prefixLength + 1) * (bound + 5) *
                    finiteAdvanceLocalPayloadEnvelope subject bound) +
                  (bound + 5) *
                    finiteAdvanceLocalPayloadEnvelope subject bound := by
              rw [Nat.add_assoc]
              exact Nat.add_le_add hleft hchunk
            _ = (prefixLength + 1 + 1) * (bound + 5) *
                  finiteAdvanceLocalPayloadEnvelope subject bound := by ring

/-! ## Linear compression of the zero branch -/

def finiteClosedDisjunctionCostEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  96 + 24 * finiteCaseFormulaEnvelope subject bound

theorem disjunctionSyntaxBudget_le_three_mul
    (left right : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hdisjunction : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    FoundationCompactCertifiedDisjunction.disjunctionSyntaxBudget left right <=
      3 * resource := by
  unfold FoundationCompactCertifiedDisjunction.disjunctionSyntaxBudget
  omega

theorem finiteEqualityCaseClosedDisjunctionCost_le
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index + 1 <= bound + 2) :
    96 + 8 * FoundationCompactCertifiedDisjunction.disjunctionSyntaxBudget
        (finiteEqualityCases subject index)
        (finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) subject) <=
      finiteClosedDisjunctionCostEnvelope subject bound := by
  have hleft := finiteEqualityCases_code_le_caseEnvelope
    subject index bound (by omega)
  have hright := finiteCaseEqualityFormula_code_le_caseEnvelope
    subject index bound (by omega)
  have hdisjunctionRaw := finiteEqualityCases_code_le_caseEnvelope
    subject (index + 1) bound hindex
  have hdisjunction :
      (binaryFormulaCode
        (finiteEqualityCases subject index ⋎
          finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 index) subject)).length <=
        finiteCaseFormulaEnvelope subject bound := by
    rw [← finiteEqualityCases_succ]
    exact hdisjunctionRaw
  have hsyntax := disjunctionSyntaxBudget_le_three_mul
    (finiteEqualityCases subject index)
    (finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 index) subject)
    (finiteCaseFormulaEnvelope subject bound) hleft hright hdisjunction
  unfold finiteClosedDisjunctionCostEnvelope
  omega

theorem finiteExhaustionClosedDisjunctionCost_le
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 2) :
    96 + 8 * FoundationCompactCertifiedDisjunction.disjunctionSyntaxBudget
        (finiteEqualityCases subject index)
        (finiteLowerBoundFormula index subject) <=
      finiteClosedDisjunctionCostEnvelope subject bound := by
  have hleft := finiteEqualityCases_code_le_caseEnvelope
    subject index bound hindex
  have hright := finiteLowerBoundFormula_code_le_caseEnvelope
    subject index bound hindex
  have hdisjunctionRaw := finiteExhaustionFormula_code_le_caseEnvelope
    subject index bound hindex
  have hdisjunction :
      (binaryFormulaCode
        (finiteEqualityCases subject index ⋎
          finiteLowerBoundFormula index subject)).length <=
        finiteCaseFormulaEnvelope subject bound := by
    simpa [finiteExhaustionFormula, finiteLowerBoundFormula] using
      hdisjunctionRaw
  have hsyntax := disjunctionSyntaxBudget_le_three_mul
    (finiteEqualityCases subject index)
    (finiteLowerBoundFormula index subject)
    (finiteCaseFormulaEnvelope subject bound) hleft hright hdisjunction
  unfold finiteClosedDisjunctionCostEnvelope
  omega

theorem injectZeroEqualityCaseStructuralPayloadBound_le_polynomial
    (tailLength bound : Nat) (htail : tailLength <= bound) :
    injectZeroEqualityCaseStructuralPayloadBound tailLength <=
      finiteCaseZeroEqualityStructuralPayloadBound +
        (tailLength + 1) *
          finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound := by
  induction tailLength with
  | zero =>
      have hcost := finiteEqualityCaseClosedDisjunctionCost_le
        inductionZeroTerm 0 bound (by omega)
      have hcostZero :
          96 + 8 * FoundationCompactCertifiedDisjunction.disjunctionSyntaxBudget
              (⊥ : LO.FirstOrder.ArithmeticProposition)
              (finiteCaseEqualityFormula (finiteCaseZeroTerm 0)
                inductionZeroTerm) <=
            finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound := by
        simpa only [finiteEqualityCases_zero, iteratedSuccessorTerm_zero]
          using hcost
      simp only [injectZeroEqualityCaseStructuralPayloadBound]
      rw [Nat.add_assoc]
      calc
        _ <= finiteCaseZeroEqualityStructuralPayloadBound +
              finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound :=
          Nat.add_le_add_left hcostZero _
        _ = finiteCaseZeroEqualityStructuralPayloadBound +
              (0 + 1) *
                finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound := by
          ring
  | succ tailLength ih =>
      have hprevious := ih (by omega)
      have hcost := finiteEqualityCaseClosedDisjunctionCost_le
        inductionZeroTerm (tailLength + 1) bound (by omega)
      simp only [injectZeroEqualityCaseStructuralPayloadBound]
      rw [Nat.add_assoc]
      calc
        _ <= (finiteCaseZeroEqualityStructuralPayloadBound +
                (tailLength + 1) *
                  finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound) +
              finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound :=
          Nat.add_le_add hprevious hcost
        _ = finiteCaseZeroEqualityStructuralPayloadBound +
              (tailLength + 1 + 1) *
                finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound := by
          ring

def finiteExhaustionZeroPayloadPolynomial (bound : Nat) : Nat :=
  finiteCaseZeroEqualityStructuralPayloadBound +
    finiteCaseZeroNotLessStructuralPayloadBound +
    (bound + 2) *
      finiteClosedDisjunctionCostEnvelope inductionZeroTerm bound + 1

theorem finiteExhaustionZeroStructuralPayloadBound_le_polynomial
    (bound : Nat) :
    finiteExhaustionZeroStructuralPayloadBound bound <=
      finiteExhaustionZeroPayloadPolynomial bound := by
  cases bound with
  | zero =>
      have hcostRaw := finiteExhaustionClosedDisjunctionCost_le
        inductionZeroTerm 0 0 (by omega)
      have hcost :
          96 + 8 * FoundationCompactCertifiedDisjunction.disjunctionSyntaxBudget
              (⊥ : LO.FirstOrder.ArithmeticProposition)
              (∼finiteCaseLessThanFormula inductionZeroTerm
                (finiteCaseZeroTerm 0)) <=
            finiteClosedDisjunctionCostEnvelope inductionZeroTerm 0 := by
        simpa only [finiteEqualityCases_zero, finiteLowerBoundFormula,
          iteratedSuccessorTerm_zero] using hcostRaw
      simp only [finiteExhaustionZeroStructuralPayloadBound,
        finiteExhaustionZeroFormulaStructuralPayloadBound]
      unfold finiteExhaustionZeroPayloadPolynomial
      omega
  | succ tailLength =>
      have hinject :=
        injectZeroEqualityCaseStructuralPayloadBound_le_polynomial
          tailLength (tailLength + 1) (by omega)
      have hcostRaw := finiteExhaustionClosedDisjunctionCost_le
        inductionZeroTerm (tailLength + 1) (tailLength + 1) (by omega)
      have hcost :
          96 + 8 * FoundationCompactCertifiedDisjunction.disjunctionSyntaxBudget
              (finiteEqualityCases inductionZeroTerm (tailLength + 1))
              (∼finiteCaseLessThanFormula inductionZeroTerm
                (iteratedSuccessorTerm 0 (tailLength + 1))) <=
            finiteClosedDisjunctionCostEnvelope inductionZeroTerm
              (tailLength + 1) := by
        simpa only [finiteLowerBoundFormula] using hcostRaw
      have hcoefficient : tailLength + 2 <= tailLength + 3 := by omega
      have hscaled := Nat.mul_le_mul_right
        (finiteClosedDisjunctionCostEnvelope inductionZeroTerm
          (tailLength + 1)) hcoefficient
      simp only [finiteExhaustionZeroStructuralPayloadBound,
        finiteExhaustionZeroFormulaStructuralPayloadBound]
      rw [Nat.add_assoc]
      unfold finiteExhaustionZeroPayloadPolynomial
      calc
        _ <= (finiteCaseZeroEqualityStructuralPayloadBound +
                (tailLength + 1) *
                  finiteClosedDisjunctionCostEnvelope inductionZeroTerm
                    (tailLength + 1)) +
              finiteClosedDisjunctionCostEnvelope inductionZeroTerm
                (tailLength + 1) := Nat.add_le_add hinject hcost
        _ = finiteCaseZeroEqualityStructuralPayloadBound +
              (tailLength + 2) *
                finiteClosedDisjunctionCostEnvelope inductionZeroTerm
                  (tailLength + 1) := by ring
        _ <= finiteCaseZeroEqualityStructuralPayloadBound +
              (tailLength + 3) *
                finiteClosedDisjunctionCostEnvelope inductionZeroTerm
                  (tailLength + 1) :=
          Nat.add_le_add_left hscaled _
        _ <= finiteCaseZeroEqualityStructuralPayloadBound +
              finiteCaseZeroNotLessStructuralPayloadBound +
              (tailLength + 3) *
                finiteClosedDisjunctionCostEnvelope inductionZeroTerm
                  (tailLength + 1) + 1 := by
          omega
        _ = finiteCaseZeroEqualityStructuralPayloadBound +
              finiteCaseZeroNotLessStructuralPayloadBound +
              (tailLength + 1 + 2) *
                finiteClosedDisjunctionCostEnvelope inductionZeroTerm
                  (tailLength + 1) + 1 := by ring

/-! ## Primitive compression for successor-order reasoning -/

theorem addCommutativityStructuralPayloadBound_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    addCommutativityStructuralPayloadBound left right <=
      paPrimitiveCostEnvelope termBound := by
  have hfirst := specializationCost_fixedFormula_le
    addCommutativityOuterBody left termBound (by simp) hleft
  have hsecond := specializationCost_stage1Formula_le
    (addCommutativityInnerBody left) right termBound
    (addCommutativityInnerBody_code_le_stage1 left termBound hleft) hright
  unfold addCommutativityStructuralPayloadBound paPrimitiveCostEnvelope
  omega

theorem addZeroStructuralPayloadBound_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hterm : (binaryTermCode term).length <= termBound) :
    addZeroStructuralPayloadBound term <=
      paPrimitiveCostEnvelope termBound := by
  have hcost := specializationCost_fixedFormula_le
    addZeroBody term termBound (by simp) hterm
  unfold addZeroStructuralPayloadBound paPrimitiveCostEnvelope
  omega

theorem equalityTransitivityStructuralPayloadBound_le_primitive
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftPayloadBound rightPayloadBound termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    equalityTransitivityStructuralPayloadBound left middle right
        leftPayloadBound rightPayloadBound <=
      leftPayloadBound + rightPayloadBound +
        paPrimitiveCostEnvelope termBound := by
  let firstEq :=
    (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition)
  let secondEq :=
    (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)
  let finalEq :=
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
  let secondImplication := secondEq 🡒 finalEq
  have hfirstSpecialization := specializationCost_fixedFormula_le
    equalityTransitivityOuterBody left termBound (by simp) hleft
  have hsecondSpecialization := specializationCost_stage1Formula_le
    (equalityTransitivityMiddleBody left) middle termBound
    (equalityTransitivityMiddleBody_code_le_stage1
      left termBound hleft) hmiddle
  have hthirdSpecialization := specializationCost_stage2Formula_le
    (equalityTransitivityInnerBody left middle) right termBound
    (equalityTransitivityInnerBody_code_le_stage2
      left middle termBound hleft hmiddle) hright
  have hfirstEq : (binaryFormulaCode firstEq).length <=
      paFormulaCodeEnvelope termBound := by
    exact equalityFormula_code_length_le_paEnvelope
      left middle termBound hleft hmiddle
  have hsecondEq : (binaryFormulaCode secondEq).length <=
      paFormulaCodeEnvelope termBound := by
    exact equalityFormula_code_length_le_paEnvelope
      middle right termBound hmiddle hright
  have hfinalEq : (binaryFormulaCode finalEq).length <=
      paFormulaCodeEnvelope termBound := by
    exact equalityFormula_code_length_le_paEnvelope
      left right termBound hleft hright
  have hsecondImplicationRaw :=
    binaryFormulaCode_implication_length_le secondEq finalEq
  have hsecondImplication :
      (binaryFormulaCode secondImplication).length <=
        paDerivedFormulaCodeEnvelope termBound := by
    dsimp only [secondImplication]
    unfold paDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hbaseToDerived := paFormulaCodeEnvelope_le_derived termBound
  have hmpFirst := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    firstEq secondImplication (paDerivedFormulaCodeEnvelope termBound)
    (hfirstEq.trans hbaseToDerived) hsecondImplication
  have hmpSecond := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    secondEq finalEq (paDerivedFormulaCodeEnvelope termBound)
    (hsecondEq.trans hbaseToDerived) (hfinalEq.trans hbaseToDerived)
  have hmpFirstLocal :
      equalityTransitivityFirstMPSyntaxBudget left middle right <=
        paLocalAssemblyCostEnvelope termBound := by
    dsimp only [firstEq, secondEq, finalEq, secondImplication] at hmpFirst
    simpa [equalityTransitivityFirstMPSyntaxBudget,
      paLocalAssemblyCostEnvelope] using hmpFirst
  have hmpSecondLocal :
      equalityTransitivitySecondMPSyntaxBudget left middle right <=
        paLocalAssemblyCostEnvelope termBound := by
    dsimp only [firstEq, secondEq, finalEq] at hmpSecond
    simpa [equalityTransitivitySecondMPSyntaxBudget,
      paLocalAssemblyCostEnvelope] using hmpSecond
  unfold equalityTransitivityStructuralPayloadBound paPrimitiveCostEnvelope
  omega

theorem zeroAddTermEqualsTermStructuralPayloadBound_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hzero : (binaryTermCode paZeroTerm).length <= termBound)
    (hterm : (binaryTermCode term).length <= termBound)
    (hzeroAdd :
      (binaryTermCode (paAddTerm paZeroTerm term)).length <= termBound)
    (haddZero :
      (binaryTermCode (paAddTerm term paZeroTerm)).length <= termBound) :
    zeroAddTermEqualsTermStructuralPayloadBound term <=
      3 * paPrimitiveCostEnvelope termBound := by
  have hcommutativity :=
    addCommutativityStructuralPayloadBound_le_primitive
      paZeroTerm term termBound hzero hterm
  have haddZeroBound := addZeroStructuralPayloadBound_le_primitive
    term termBound hterm
  have htransitivity :=
    equalityTransitivityStructuralPayloadBound_le_primitive
      (paAddTerm paZeroTerm term) (paAddTerm term paZeroTerm) term
      (addCommutativityStructuralPayloadBound paZeroTerm term)
      (addZeroStructuralPayloadBound term) termBound
      hzeroAdd haddZero hterm
  unfold zeroAddTermEqualsTermStructuralPayloadBound
  omega

theorem addLtAddStructuralPayloadBound_le_primitive
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadBound termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (hshift : (binaryTermCode shift).length <= termBound)
    (hleftSum :
      (binaryTermCode (paAddTerm left shift)).length <= termBound)
    (hrightSum :
      (binaryTermCode (paAddTerm right shift)).length <= termBound) :
    addLtAddStructuralPayloadBound left right shift sourcePayloadBound <=
      sourcePayloadBound + 2 * orderPrimitiveCostEnvelope termBound := by
  have himplication := addLtAddImplicationFullPayloadBound_le_primitive
    left right shift termBound hleft hright hshift
  have hmp := lessThanMPSyntaxBudget_le_derived
    left right (paAddTerm left shift) (paAddTerm right shift) termBound
    hleft hright hleftSum hrightSum
  have hmpExact :
      modusPonensSyntaxBudget
          (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
          (“!!left + !!shift < !!right + !!shift” :
            LO.FirstOrder.ArithmeticProposition) <=
        orderDerivedFormulaCodeEnvelope termBound := by
    simpa [paAddTerm] using hmp
  have hmpPrimitive := (hmpExact.trans
    (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have hfinalCost :
      240 + 34 * modusPonensSyntaxBudget
          (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
          (“!!left + !!shift < !!right + !!shift” :
            LO.FirstOrder.ArithmeticProposition) <=
        orderPrimitiveCostEnvelope termBound := by
    unfold orderPrimitiveCostEnvelope
    omega
  unfold addLtAddStructuralPayloadBound
  omega

theorem shiftedZeroOneStructuralPayloadBound_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hzero : (binaryTermCode paZeroTerm).length <= termBound)
    (hone : (binaryTermCode paOneTerm).length <= termBound)
    (hterm : (binaryTermCode term).length <= termBound)
    (hzeroAdd :
      (binaryTermCode (paAddTerm paZeroTerm term)).length <= termBound)
    (honeAdd :
      (binaryTermCode (paAddTerm paOneTerm term)).length <= termBound) :
    shiftedZeroOneStructuralPayloadBound term <=
      3 * orderPrimitiveCostEnvelope termBound := by
  have hraw := addLtAddStructuralPayloadBound_le_primitive
    paZeroTerm paOneTerm term
    (32 + 10 * axiomSyntaxBudget .zeroLtOne) termBound
    hzero hone hterm hzeroAdd honeAdd
  have hsource : 32 + 10 * axiomSyntaxBudget .zeroLtOne <=
      orderPrimitiveCostEnvelope termBound := by
    unfold orderPrimitiveCostEnvelope fixedPAOrderPayloadEnvelope
    omega
  unfold shiftedZeroOneStructuralPayloadBound
  omega

theorem ltTransportStructuralPayloadBound_le_primitive
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEqualityBound secondEqualityBound relationBound termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    ltTransportStructuralPayloadBound leftFirst leftSecond
        rightFirst rightSecond firstEqualityBound secondEqualityBound
        relationBound <=
      firstEqualityBound + secondEqualityBound + relationBound +
        2 * orderPrimitiveCostEnvelope termBound := by
  have htransport := binaryRelationTransportFullPayloadBound_le_primitive
    leftFirst leftSecond rightFirst rightSecond
    firstEqualityBound secondEqualityBound termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hmp := lessThanMPSyntaxBudget_le_derived
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hmpPrimitive := (hmp.trans
    (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have hfinalCost :
      240 + 34 * modusPonensSyntaxBudget
          (“!!leftFirst < !!leftSecond” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!rightFirst < !!rightSecond” :
            LO.FirstOrder.ArithmeticProposition) <=
        orderPrimitiveCostEnvelope termBound := by
    unfold orderPrimitiveCostEnvelope
    omega
  unfold ltTransportStructuralPayloadBound
  omega

def termLtSuccessorPayloadEnvelope (termBound : Nat) : Nat :=
  8 * (paPrimitiveCostEnvelope termBound +
    orderPrimitiveCostEnvelope termBound + 1)

theorem termLtSuccessorStructuralPayloadBound_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hzero : (binaryTermCode paZeroTerm).length <= termBound)
    (hone : (binaryTermCode paOneTerm).length <= termBound)
    (hterm : (binaryTermCode term).length <= termBound)
    (hzeroAdd :
      (binaryTermCode (paAddTerm paZeroTerm term)).length <= termBound)
    (honeAdd :
      (binaryTermCode (paAddTerm paOneTerm term)).length <= termBound)
    (haddZero :
      (binaryTermCode (paAddTerm term paZeroTerm)).length <= termBound)
    (haddOne :
      (binaryTermCode (paAddTerm term paOneTerm)).length <= termBound) :
    termLtSuccessorStructuralPayloadBound term <=
      termLtSuccessorPayloadEnvelope termBound := by
  have hzeroEquality :=
    zeroAddTermEqualsTermStructuralPayloadBound_le_primitive
      term termBound hzero hterm hzeroAdd haddZero
  have hcommutativity :=
    addCommutativityStructuralPayloadBound_le_primitive
      paOneTerm term termBound hone hterm
  have hshifted := shiftedZeroOneStructuralPayloadBound_le_primitive
    term termBound hzero hone hterm hzeroAdd honeAdd
  have htransport := ltTransportStructuralPayloadBound_le_primitive
    (paAddTerm paZeroTerm term) (paAddTerm paOneTerm term)
    term (paAddTerm term paOneTerm)
    (zeroAddTermEqualsTermStructuralPayloadBound term)
    (addCommutativityStructuralPayloadBound paOneTerm term)
    (shiftedZeroOneStructuralPayloadBound term) termBound
    hzeroAdd honeAdd hterm haddOne
  unfold termLtSuccessorStructuralPayloadBound
    termLtSuccessorPayloadEnvelope
  omega

theorem ltTransImplicationStructuralPayloadBound_le_primitive
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    ltTransImplicationStructuralPayloadBound left middle right <=
      orderPrimitiveCostEnvelope termBound := by
  have houter := (fixedOrderFormulaCode_le_stage0
    ltTransOuterBody (Or.inr (Or.inl rfl))).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hmiddleFormula := (ltTransMiddleBody_code_le_stage1
    left termBound hleft).trans
      (orderFormulaStage_le_envelope (orderFormulaStage1 termBound)
        termBound (Or.inr (Or.inl rfl)))
  have hinner := (ltTransInnerBody_code_le_stage2
    left middle termBound hleft hmiddle).trans
      (orderFormulaStage_le_envelope (orderFormulaStage2 termBound)
        termBound (Or.inr (Or.inr (Or.inl rfl))))
  have hfirst := specializationCost_le_orderEnvelope
    ltTransOuterBody left termBound houter hleft
  have hsecond := specializationCost_le_orderEnvelope
    (ltTransMiddleBody left) middle termBound hmiddleFormula hmiddle
  have hthird := specializationCost_le_orderEnvelope
    (ltTransInnerBody left middle) right termBound hinner hright
  have haxiom : 10 * axiomSyntaxBudget .ltTrans <=
      fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  unfold ltTransImplicationStructuralPayloadBound orderPrimitiveCostEnvelope
  omega

def finiteSuccessorReasoningTermEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  32 * (finiteClosedTermEnvelope subject bound +
    (binaryTermCode paZeroTerm).length +
    (binaryTermCode paOneTerm).length +
    (binaryTermCode (paAddTerm paZeroTerm subject)).length +
    (binaryTermCode (paAddTerm paOneTerm subject)).length +
    (binaryTermCode (paAddTerm subject paZeroTerm)).length +
    (binaryTermCode (paAddTerm subject paOneTerm)).length + 1)

def finiteSuccessorImplicationPayloadEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  let termBound := finiteSuccessorReasoningTermEnvelope subject bound
  let formulaBound := orderPrimitiveFormulaCodeEnvelope termBound
  16 * (termLtSuccessorPayloadEnvelope termBound +
    orderPrimitiveCostEnvelope termBound +
    smallContextAssemblyEnvelope formulaBound + 1)

theorem successorLessThanImpliesLessThanStructuralPayloadBound_le_polynomial
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (index bound : Nat) (hindex : index <= bound + 3) :
    successorLessThanImpliesLessThanStructuralPayloadBound subject
        (iteratedSuccessorTerm 0 index) <=
      finiteSuccessorImplicationPayloadEnvelope subject bound := by
  let boundTerm := iteratedSuccessorTerm 0 index
  let successorTerm := successorOf subject
  let termBound := finiteSuccessorReasoningTermEnvelope subject bound
  let formulaBound := orderPrimitiveFormulaCodeEnvelope termBound
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼successorLessThanFormula subject boundTerm}
  let termSuccessor :=
    (“!!subject < !!successorTerm” : LO.FirstOrder.ArithmeticProposition)
  let antecedent := successorLessThanFormula subject boundTerm
  let consequent := termLessThanFormula subject boundTerm
  let conjunctionFormula := termSuccessor ⋏ antecedent
  let transitivity := conjunctionFormula 🡒 consequent
  let implication := antecedent 🡒 consequent
  have hclosedToTerm : finiteClosedTermEnvelope subject bound <=
      termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have hsubject : (binaryTermCode subject).length <= termBound :=
    (subject_code_le_finiteClosedTermEnvelope subject bound).trans
      hclosedToTerm
  have hsuccessor : (binaryTermCode successorTerm).length <= termBound := by
    dsimp only [successorTerm]
    exact (successorSubject_code_le_finiteClosedTermEnvelope
      subject bound).trans hclosedToTerm
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [boundTerm]
    exact (iteratedSuccessorTerm_code_le_finiteClosedTermEnvelope
      subject index bound hindex).trans hclosedToTerm
  have hzero : (binaryTermCode paZeroTerm).length <= termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have hone : (binaryTermCode paOneTerm).length <= termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have hzeroAdd :
      (binaryTermCode (paAddTerm paZeroTerm subject)).length <= termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have honeAdd :
      (binaryTermCode (paAddTerm paOneTerm subject)).length <= termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have haddZero :
      (binaryTermCode (paAddTerm subject paZeroTerm)).length <= termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have haddOne :
      (binaryTermCode (paAddTerm subject paOneTerm)).length <= termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have htermSuccessorStructural :=
    termLtSuccessorStructuralPayloadBound_le_primitive
      subject termBound hzero hone hsubject hzeroAdd honeAdd haddZero haddOne
  have htransitivityStructural :=
    ltTransImplicationStructuralPayloadBound_le_primitive
      subject successorTerm boundTerm termBound
      hsubject hsuccessor hboundTerm
  have htermSuccessorAtomic :
      (binaryFormulaCode termSuccessor).length <=
        orderAtomicFormulaCodeEnvelope termBound := by
    dsimp only [termSuccessor]
    exact lessThanFormula_code_le_orderAtomic
      subject successorTerm termBound hsubject hsuccessor
  have hantecedentAtomic :
      (binaryFormulaCode antecedent).length <=
        orderAtomicFormulaCodeEnvelope termBound := by
    dsimp only [antecedent, successorLessThanFormula]
    exact lessThanFormula_code_le_orderAtomic
      successorTerm boundTerm termBound hsuccessor hboundTerm
  have hconsequentAtomic :
      (binaryFormulaCode consequent).length <=
        orderAtomicFormulaCodeEnvelope termBound := by
    dsimp only [consequent, termLessThanFormula]
    exact lessThanFormula_code_le_orderAtomic
      subject boundTerm termBound hsubject hboundTerm
  have hconjunctionDerived :
      (binaryFormulaCode conjunctionFormula).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_and_length_le_local
      termSuccessor antecedent
    dsimp only [conjunctionFormula]
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have himplicationDerived :
      (binaryFormulaCode implication).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_implication_length_le
      antecedent consequent
    dsimp only [implication]
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hnegatedAntecedentDerived :
      (binaryFormulaCode (∼antecedent)).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_neg_length_le antecedent
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hnegatedConsequentDerived :
      (binaryFormulaCode (∼consequent)).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_neg_length_le consequent
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have htransitivityLocal :
      (binaryFormulaCode transitivity).length <=
        orderLocalFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_implication_length_le
      conjunctionFormula consequent
    have hconsequentDerived := hconsequentAtomic.trans
      (orderAtomic_le_derived termBound)
    dsimp only [transitivity]
    unfold orderLocalFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hnegatedTransitivityPrimitive :
      (binaryFormulaCode (∼transitivity)).length <= formulaBound := by
    have hraw := binaryFormulaCode_neg_length_le transitivity
    have hlocalToPrimitive := orderLocal_le_primitive termBound
    dsimp only [formulaBound]
    unfold orderPrimitiveFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have htermSuccessor := htermSuccessorAtomic.trans
    ((orderAtomic_le_derived termBound).trans
      ((orderDerived_le_local termBound).trans
        (orderLocal_le_primitive termBound)))
  have hantecedent := hantecedentAtomic.trans
    ((orderAtomic_le_derived termBound).trans
      ((orderDerived_le_local termBound).trans
        (orderLocal_le_primitive termBound)))
  have hconsequent := hconsequentAtomic.trans
    ((orderAtomic_le_derived termBound).trans
      ((orderDerived_le_local termBound).trans
        (orderLocal_le_primitive termBound)))
  have hconjunction := hconjunctionDerived.trans
    ((orderDerived_le_local termBound).trans
      (orderLocal_le_primitive termBound))
  have himplication := himplicationDerived.trans
    ((orderDerived_le_local termBound).trans
      (orderLocal_le_primitive termBound))
  have hnegatedAntecedent := hnegatedAntecedentDerived.trans
    ((orderDerived_le_local termBound).trans
      (orderLocal_le_primitive termBound))
  have hnegatedConsequent := hnegatedConsequentDerived.trans
    ((orderDerived_le_local termBound).trans
      (orderLocal_le_primitive termBound))
  have htransitivity := htransitivityLocal.trans
    (orderLocal_le_primitive termBound)
  have hGamma : FormulaCodeBound Gamma formulaBound := by
    intro formula hformula
    simp only [Gamma, Finset.mem_singleton] at hformula
    subst formula
    exact hnegatedAntecedent
  have hGammaCard : Gamma.card <= 4 := by
    dsimp only [Gamma]
    simp
  have hassumption := assumptionFullPayloadCost_le_small
    Gamma antecedent formulaBound hGammaCard hGamma hantecedent
  have htermSuccessorContext := hGamma.insert htermSuccessor
  have htermSuccessorCard : (insert termSuccessor Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le termSuccessor Gamma
    omega
  have htermSuccessorWeakening := weakeningFullAssemblyCost_le_small
    (insert termSuccessor Gamma) formulaBound
    htermSuccessorCard htermSuccessorContext
  have hconjunctionCost := conjunctionFullAssemblyCost_le_small
    Gamma termSuccessor antecedent formulaBound hGammaCard hGamma
    htermSuccessor hantecedent hconjunction
  have htransitivityContext := hGamma.insert htransitivity
  have htransitivityCard : (insert transitivity Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le transitivity Gamma
    omega
  have htransitivityWeakening := weakeningFullAssemblyCost_le_small
    (insert transitivity Gamma) formulaBound
    htransitivityCard htransitivityContext
  have hmp := contextualModusPonensFullAssemblyCost_le_small
    Gamma conjunctionFormula consequent formulaBound hGammaCard hGamma
    hconjunction hconsequent htransitivity hnegatedTransitivityPrimitive
    hnegatedConsequent
  have hdischarge := dischargeFullAssemblyCost_le_small
    antecedent consequent formulaBound hantecedent hconsequent
    himplication hnegatedAntecedent
  unfold successorLessThanImpliesLessThanStructuralPayloadBound
    finiteSuccessorImplicationPayloadEnvelope
  dsimp only [boundTerm, successorTerm, termBound, formulaBound, Gamma,
    termSuccessor, antecedent, consequent, conjunctionFormula,
    transitivity, implication] at *
  omega

/-! ## Polynomial compression of the preserved lower-bound branch -/

def finitePreserveFormulaEnvelope
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  let termBound := finiteSuccessorReasoningTermEnvelope subject bound
  4 * (finiteAdvanceFormulaEnvelope subject bound +
    orderPrimitiveFormulaCodeEnvelope termBound + 1)

def preserveLowerBoundBranchPayloadPolynomial
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  8 * (finiteSuccessorImplicationPayloadEnvelope subject bound +
    smallContextAssemblyEnvelope
      (finitePreserveFormulaEnvelope subject bound) + 1)

theorem preserveLowerBoundBranchStructuralPayloadBound_le_polynomial
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    preserveLowerBoundBranchStructuralPayloadBound bound subject <=
      preserveLowerBoundBranchPayloadPolynomial subject bound := by
  let boundTerm := iteratedSuccessorTerm 0 bound
  let successorTerm := successorOf subject
  let termBound := finiteSuccessorReasoningTermEnvelope subject bound
  let formulaBound := finitePreserveFormulaEnvelope subject bound
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼finiteLowerBoundFormula bound subject}
  let lowerFormula := finiteLowerBoundFormula bound subject
  let antecedent := successorLessThanFormula subject boundTerm
  let consequent := termLessThanFormula subject boundTerm
  let implication := antecedent 🡒 consequent
  have hclosedToTerm : finiteClosedTermEnvelope subject bound <=
      termBound := by
    dsimp only [termBound]
    unfold finiteSuccessorReasoningTermEnvelope
    omega
  have hsubject : (binaryTermCode subject).length <= termBound :=
    (subject_code_le_finiteClosedTermEnvelope subject bound).trans
      hclosedToTerm
  have hsuccessor : (binaryTermCode successorTerm).length <= termBound := by
    dsimp only [successorTerm]
    exact (successorSubject_code_le_finiteClosedTermEnvelope
      subject bound).trans hclosedToTerm
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [boundTerm]
    exact (iteratedSuccessorTerm_code_le_finiteClosedTermEnvelope
      subject bound bound (by omega)).trans hclosedToTerm
  have hadvance : finiteAdvanceFormulaEnvelope subject bound <=
      formulaBound := by
    dsimp only [formulaBound]
    unfold finitePreserveFormulaEnvelope
    dsimp only
    omega
  have horder : orderPrimitiveFormulaCodeEnvelope termBound <=
      formulaBound := by
    dsimp only [termBound, formulaBound]
    unfold finitePreserveFormulaEnvelope
    dsimp only
    omega
  have hlowerAdvance := (finiteLowerBoundFormula_code_le_caseEnvelope
    subject bound bound (by omega)).trans
      (finiteCaseFormulaEnvelope_le_advance subject bound)
  have hlower := hlowerAdvance.trans hadvance
  have hnegatedLowerRaw := binaryFormulaCode_neg_length_le lowerFormula
  have hnegatedLower : (binaryFormulaCode (∼lowerFormula)).length <=
      formulaBound := by
    dsimp only [lowerFormula] at hnegatedLowerRaw ⊢
    dsimp only [formulaBound]
    unfold finitePreserveFormulaEnvelope
    dsimp only
    omega
  have hGamma : FormulaCodeBound Gamma formulaBound := by
    intro formula hformula
    simp only [Gamma, Finset.mem_singleton] at hformula
    subst formula
    exact hnegatedLower
  have hGammaCard : Gamma.card <= 4 := by
    dsimp only [Gamma]
    simp
  have hlowerAssumption := assumptionFullPayloadCost_le_small
    Gamma lowerFormula formulaBound hGammaCard hGamma hlower
  have hantecedentAtomic :
      (binaryFormulaCode antecedent).length <=
        orderAtomicFormulaCodeEnvelope termBound := by
    dsimp only [antecedent, successorLessThanFormula]
    exact lessThanFormula_code_le_orderAtomic
      successorTerm boundTerm termBound hsuccessor hboundTerm
  have hconsequentAtomic :
      (binaryFormulaCode consequent).length <=
        orderAtomicFormulaCodeEnvelope termBound := by
    dsimp only [consequent, termLessThanFormula]
    exact lessThanFormula_code_le_orderAtomic
      subject boundTerm termBound hsubject hboundTerm
  have himplicationDerived :
      (binaryFormulaCode implication).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_implication_length_le
      antecedent consequent
    dsimp only [implication]
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hnegatedImplicationLocal :
      (binaryFormulaCode (∼implication)).length <=
        orderLocalFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_neg_length_le implication
    unfold orderLocalFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hnegatedAntecedentDerived :
      (binaryFormulaCode (∼antecedent)).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_neg_length_le antecedent
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hnegatedConsequentDerived :
      (binaryFormulaCode (∼consequent)).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_neg_length_le consequent
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hantecedent := (hantecedentAtomic.trans
    ((orderAtomic_le_derived termBound).trans
      ((orderDerived_le_local termBound).trans
        (orderLocal_le_primitive termBound)))).trans horder
  have hconsequent := (hconsequentAtomic.trans
    ((orderAtomic_le_derived termBound).trans
      ((orderDerived_le_local termBound).trans
        (orderLocal_le_primitive termBound)))).trans horder
  have himplication := (himplicationDerived.trans
    ((orderDerived_le_local termBound).trans
      (orderLocal_le_primitive termBound))).trans horder
  have hnegatedImplication :=
    (hnegatedImplicationLocal.trans
      (orderLocal_le_primitive termBound)).trans horder
  have hnegatedAntecedent := (hnegatedAntecedentDerived.trans
    ((orderDerived_le_local termBound).trans
      (orderLocal_le_primitive termBound))).trans horder
  have hnegatedConsequent := (hnegatedConsequentDerived.trans
    ((orderDerived_le_local termBound).trans
      (orderLocal_le_primitive termBound))).trans horder
  have himplicationContext := hGamma.insert himplication
  have himplicationCard : (insert implication Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le implication Gamma
    omega
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert implication Gamma) formulaBound
    himplicationCard himplicationContext
  have htollens := modusTollensFullAssemblyCost_le_small
    Gamma antecedent consequent formulaBound hGammaCard hGamma
    hantecedent hconsequent himplication hnegatedImplication
    hnegatedAntecedent hnegatedConsequent
  have hsuccessorImplication :=
    successorLessThanImpliesLessThanStructuralPayloadBound_le_polynomial
      subject bound bound (by omega)
  have hlift :
      liftLowerBoundThroughSuccessorStructuralPayloadBound Gamma subject
          boundTerm
          (CertifiedPAContextProof.assumptionFullPayloadCost
            Gamma lowerFormula) <=
        finiteSuccessorImplicationPayloadEnvelope subject bound +
          3 * smallContextAssemblyEnvelope formulaBound := by
    unfold liftLowerBoundThroughSuccessorStructuralPayloadBound
    dsimp only [Gamma, boundTerm, lowerFormula, antecedent, consequent,
      implication] at hweakening
    dsimp only [Gamma, boundTerm, lowerFormula, antecedent, consequent,
      implication] at htollens
    dsimp only [Gamma, boundTerm, lowerFormula, antecedent, consequent,
      implication] at hlowerAssumption
    dsimp only [Gamma, boundTerm, lowerFormula, antecedent, consequent,
      implication]
    omega
  have hleft := (finiteEqualityCases_code_le_caseEnvelope
    (successorOf subject) bound bound (by omega)).trans
      ((successorFiniteCaseFormulaEnvelope_le_advance
        subject bound).trans hadvance)
  have hright := (finiteLowerBoundFormula_code_le_caseEnvelope
    (successorOf subject) bound bound (by omega)).trans
      ((successorFiniteCaseFormulaEnvelope_le_advance
        subject bound).trans hadvance)
  have hdisjunctionRaw := (finiteExhaustionFormula_code_le_caseEnvelope
    (successorOf subject) bound bound (by omega)).trans
      ((successorFiniteCaseFormulaEnvelope_le_advance
        subject bound).trans hadvance)
  have hdisjunctionFormula :
      (binaryFormulaCode
        (finiteEqualityCases (successorOf subject) bound ⋎
          finiteLowerBoundFormula bound (successorOf subject))).length <=
        formulaBound := by
    simpa [finiteExhaustionFormula, finiteLowerBoundFormula] using
      hdisjunctionRaw
  have hdisjunction := disjunctionFullAssemblyCost_le_small
    Gamma (finiteEqualityCases (successorOf subject) bound)
    (finiteLowerBoundFormula bound (successorOf subject))
    formulaBound hGammaCard hGamma hleft hright hdisjunctionFormula
  unfold preserveLowerBoundBranchStructuralPayloadBound
    preserveLowerBoundBranchPayloadPolynomial
  dsimp only [boundTerm, successorTerm, termBound, formulaBound, Gamma,
    lowerFormula, antecedent, consequent, implication] at hlift hdisjunction ⊢
  omega

/-! ## Assembly of the complete successor implication -/

def finiteExhaustionSuccessorUnderAssumptionPayloadPolynomial
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  advanceFiniteCasePrefixPayloadPolynomial subject bound bound +
    preserveLowerBoundBranchPayloadPolynomial subject bound +
    smallContextAssemblyEnvelope
      (finitePreserveFormulaEnvelope subject bound)

theorem finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound_le_polynomial
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound
        bound subject <=
      finiteExhaustionSuccessorUnderAssumptionPayloadPolynomial
        subject bound := by
  let formulaBound := finitePreserveFormulaEnvelope subject bound
  have hadvance :=
    advanceFiniteCasePrefixStructuralPayloadBound_le_polynomial
      subject bound 0 bound (by omega)
  have hpreserve :=
    preserveLowerBoundBranchStructuralPayloadBound_le_polynomial
      bound subject
  have hformulaAdvance : finiteAdvanceFormulaEnvelope subject bound <=
      formulaBound := by
    dsimp only [formulaBound]
    unfold finitePreserveFormulaEnvelope
    dsimp only
    omega
  have htarget := (finiteExhaustionFormula_code_le_caseEnvelope
    (successorOf subject) bound bound (by omega)).trans
      ((successorFiniteCaseFormulaEnvelope_le_advance
        subject bound).trans hformulaAdvance)
  have hnegatedLeft := (negatedFiniteEqualityCases_code_le_caseEnvelope
    subject bound bound (by omega)).trans
      ((finiteCaseFormulaEnvelope_le_advance
        subject bound).trans hformulaAdvance)
  have hrightRaw := (finiteLowerBoundFormula_code_le_caseEnvelope
    subject bound bound (by omega)).trans
      (finiteCaseFormulaEnvelope_le_advance subject bound)
  have hnegatedRightRaw := binaryFormulaCode_neg_length_le
    (finiteLowerBoundFormula bound subject)
  have hnegatedRight :
      (binaryFormulaCode
        (∼finiteLowerBoundFormula bound subject)).length <= formulaBound := by
    dsimp only [formulaBound]
    unfold finitePreserveFormulaEnvelope
    dsimp only
    omega
  have hnegatedDisjunction :=
    (negatedFiniteExhaustionFormula_code_le_caseEnvelope
      subject bound bound (by omega)).trans
        ((finiteCaseFormulaEnvelope_le_advance
          subject bound).trans hformulaAdvance)
  have hGamma : FormulaCodeBound
      (∅ : Finset LO.FirstOrder.ArithmeticProposition) formulaBound := by
    intro formula hformula
    simp at hformula
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    (∅ : Finset LO.FirstOrder.ArithmeticProposition)
    (finiteExhaustionFormula bound (successorOf subject))
    (finiteEqualityCases subject bound)
    (finiteLowerBoundFormula bound subject) formulaBound
    (by simp) hGamma htarget hnegatedLeft hnegatedRight
    hnegatedDisjunction
  unfold finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound
    advanceAllFiniteCasesStructuralPayloadBound
    finiteExhaustionSuccessorUnderAssumptionPayloadPolynomial
  dsimp only [formulaBound] at heliminate ⊢
  omega

def finiteExhaustionSuccessorImplicationPayloadPolynomial
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bound : Nat) : Nat :=
  finiteExhaustionSuccessorUnderAssumptionPayloadPolynomial subject bound +
    smallContextAssemblyEnvelope
      (finitePreserveFormulaEnvelope subject bound)

theorem finiteExhaustionSuccessorImplicationStructuralPayloadBound_le_polynomial
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    finiteExhaustionSuccessorImplicationStructuralPayloadBound
        bound subject <=
      finiteExhaustionSuccessorImplicationPayloadPolynomial
        subject bound := by
  let antecedent := finiteExhaustionFormula bound subject
  let consequent := finiteExhaustionFormula bound (successorOf subject)
  let formulaBound := finitePreserveFormulaEnvelope subject bound
  have hunder :=
    finiteExhaustionSuccessorUnderAssumptionStructuralPayloadBound_le_polynomial
      bound subject
  have hantecedentAdvance := (finiteExhaustionFormula_code_le_caseEnvelope
    subject bound bound (by omega)).trans
      (finiteCaseFormulaEnvelope_le_advance subject bound)
  have hconsequentAdvance := (finiteExhaustionFormula_code_le_caseEnvelope
    (successorOf subject) bound bound (by omega)).trans
      (successorFiniteCaseFormulaEnvelope_le_advance subject bound)
  have hformulaAdvance : finiteAdvanceFormulaEnvelope subject bound <=
      formulaBound := by
    dsimp only [formulaBound]
    unfold finitePreserveFormulaEnvelope
    dsimp only
    omega
  have hantecedent := hantecedentAdvance.trans hformulaAdvance
  have hconsequent := hconsequentAdvance.trans hformulaAdvance
  have hformulaBase : 16 <= finiteAdvanceFormulaEnvelope subject bound := by
    unfold finiteAdvanceFormulaEnvelope finiteCaseFormulaEnvelope
    omega
  have himplicationRaw := binaryFormulaCode_implication_length_le
    antecedent consequent
  have himplicationTag : (binaryNatCode 5).length <= 16 := by decide
  have himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        formulaBound := by
    dsimp only [antecedent, consequent] at himplicationRaw
    dsimp only [antecedent, consequent, formulaBound]
    unfold finitePreserveFormulaEnvelope
    dsimp only
    omega
  have hnegatedAntecedent :=
    (negatedFiniteExhaustionFormula_code_le_caseEnvelope
      subject bound bound (by omega)).trans
        ((finiteCaseFormulaEnvelope_le_advance
          subject bound).trans hformulaAdvance)
  have hdischarge := dischargeFullAssemblyCost_le_small
    antecedent consequent formulaBound hantecedent hconsequent
    himplication hnegatedAntecedent
  have hdischargeExact :
      CertifiedPAContextProof.dischargeFullAssemblyCost
          (finiteExhaustionFormula bound subject)
          (finiteExhaustionFormula bound (successorOf subject)) <=
        smallContextAssemblyEnvelope formulaBound := by
    simpa only [antecedent, consequent] using hdischarge
  unfold finiteExhaustionSuccessorImplicationStructuralPayloadBound
    finiteExhaustionSuccessorImplicationPayloadPolynomial
  dsimp only [formulaBound] at hdischargeExact ⊢
  omega

/-! ## Open substitution and the quantified induction step -/

theorem iteratedSuccessorTerm_substitution_open
    (value : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    (Rew.subst ![witness]) (iteratedSuccessorTerm 1 value) =
      iteratedSuccessorTerm 1 value := by
  induction value with
  | zero =>
      simp [iteratedSuccessorTerm, finiteCaseZeroTerm, Rew.func]
  | succ value ih =>
      simp only [iteratedSuccessorTerm_succ]
      simp [finiteCaseAddTerm, finiteCaseOneTerm, Rew.func, ih]

theorem finiteCaseEqualityFormula_substitution_open
    (value : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    (finiteCaseEqualityFormula
      (iteratedSuccessorTerm 1 value) (#0))/[witness] =
      finiteCaseEqualityFormula
        (iteratedSuccessorTerm 1 value) witness := by
  unfold finiteCaseEqualityFormula
  simp only [Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness])
      (![iteratedSuccessorTerm 1 value,
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)] index))]
  simp [iteratedSuccessorTerm_substitution_open]

theorem finiteCaseLessThanFormula_substitution_open
    (bound : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    (finiteCaseLessThanFormula (#0)
      (iteratedSuccessorTerm 1 bound))/[witness] =
      finiteCaseLessThanFormula witness
        (iteratedSuccessorTerm 1 bound) := by
  unfold finiteCaseLessThanFormula
  simp only [Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two
    (fun index => (Rew.subst ![witness])
      (![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
        iteratedSuccessorTerm 1 bound] index))]
  simp [iteratedSuccessorTerm_substitution_open]

theorem finiteEqualityCases_substitution_open
    (bound : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    (finiteEqualityCases (#0 :
      LO.FirstOrder.ArithmeticSemiterm Nat 1) bound)/[witness] =
      finiteEqualityCases witness bound := by
  induction bound with
  | zero =>
      simp [finiteEqualityCases]
  | succ bound ih =>
      calc
        (finiteEqualityCases (#0 :
            LO.FirstOrder.ArithmeticSemiterm Nat 1) (bound + 1))/[witness] =
            (finiteEqualityCases (#0 :
              LO.FirstOrder.ArithmeticSemiterm Nat 1) bound)/[witness] ⋎
              (finiteCaseEqualityFormula
                (iteratedSuccessorTerm 1 bound) (#0))/[witness] := by
          simp only [finiteEqualityCases_succ,
            LogicalConnective.HomClass.map_or]
        _ = finiteEqualityCases witness bound ⋎
              finiteCaseEqualityFormula
                (iteratedSuccessorTerm 1 bound) witness := by
          rw [ih, finiteCaseEqualityFormula_substitution_open]
        _ = finiteEqualityCases witness (bound + 1) := by rfl

theorem finiteExhaustionBody_substitution_open
    (bound : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    (finiteExhaustionBody bound)/[witness] =
      finiteEqualityCases witness bound ⋎
        ∼finiteCaseLessThanFormula witness
          (iteratedSuccessorTerm 1 bound) := by
  unfold finiteExhaustionBody
  simp only [LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg]
  change
    (finiteEqualityCases (#0 :
      LO.FirstOrder.ArithmeticSemiterm Nat 1) bound)/[witness] ⋎
      ∼((finiteCaseLessThanFormula (#0)
        (iteratedSuccessorTerm 1 bound))/[witness]) = _
  rw [finiteEqualityCases_substitution_open,
    finiteCaseLessThanFormula_substitution_open]

def finiteExhaustionStepBodyCodePolynomial (bound : Nat) : Nat :=
  let leftBound := finiteExhaustionFormulaCodePolynomial
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bound
  let rightBound := finiteExhaustionFormulaCodePolynomial
    finiteExhaustionStepWitness bound
  2 * leftBound + rightBound + (binaryNatCode 5).length

theorem binarySemiformulaCode_implication_length_le
    {arity : Nat}
    (antecedent consequent :
      LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (antecedent 🡒 consequent)).length <=
      2 * (binaryFormulaCode antecedent).length +
        (binaryFormulaCode consequent).length + (binaryNatCode 5).length := by
  have hnegated := binaryFormulaCode_neg_length_le antecedent
  have hnegatedExact := hnegated
  change (binaryFormulaCode (Semiformula.neg antecedent)).length <=
    2 * (binaryFormulaCode antecedent).length at hnegatedExact
  simp [binaryFormulaCode]
  omega

theorem finiteExhaustionStepBody_code_length_le_polynomial
    (bound : Nat) :
    (binaryFormulaCode (finiteExhaustionStepBody bound)).length <=
      finiteExhaustionStepBodyCodePolynomial bound := by
  let leftFormula :=
    finiteEqualityCases (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bound ⋎
      ∼finiteCaseLessThanFormula (#0)
        (iteratedSuccessorTerm 1 bound)
  let rightFormula := finiteEqualityCases finiteExhaustionStepWitness bound ⋎
    ∼finiteCaseLessThanFormula finiteExhaustionStepWitness
      (iteratedSuccessorTerm 1 bound)
  have hleft := finiteExhaustionLike_code_length_le_polynomial
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bound
  have hright := finiteExhaustionLike_code_length_le_polynomial
    finiteExhaustionStepWitness bound
  have himplication := binarySemiformulaCode_implication_length_le
    leftFormula rightFormula
  unfold finiteExhaustionStepBody
  rw [finiteExhaustionBody_substitution_open,
    finiteExhaustionBody_substitution_open]
  dsimp only [leftFormula, rightFormula] at himplication
  unfold finiteExhaustionStepBodyCodePolynomial
  dsimp only
  omega

theorem universalIntroductionPayloadPolynomial_mono_local
    {small large : Nat} (h : small <= large) :
    universalIntroductionPayloadPolynomial small <=
      universalIntroductionPayloadPolynomial large := by
  unfold universalIntroductionPayloadPolynomial
    universalIntroductionSequentCodeEnvelope
    universalIntroductionFormulaCodeEnvelope
  omega

def finiteExhaustionStepPayloadPolynomial (bound : Nat) : Nat :=
  finiteExhaustionSuccessorImplicationPayloadPolynomial
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) bound +
    universalIntroductionPayloadPolynomial
      (finiteExhaustionStepBodyCodePolynomial bound)

theorem finiteExhaustionStepStructuralPayloadBound_le_polynomial
    (bound : Nat) :
    finiteExhaustionStepStructuralPayloadBound bound <=
      finiteExhaustionStepPayloadPolynomial bound := by
  have hopen :=
    finiteExhaustionSuccessorImplicationStructuralPayloadBound_le_polynomial
      bound (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  have huniversalRaw := universalIntroductionFullAssemblyCost_le_polynomial
    (finiteExhaustionStepBody bound)
  have hbody := finiteExhaustionStepBody_code_length_le_polynomial bound
  have hmono := universalIntroductionPayloadPolynomial_mono_local hbody
  have huniversal := huniversalRaw.trans hmono
  unfold finiteExhaustionStepStructuralPayloadBound
    finiteExhaustionStepOpenStructuralPayloadBound
    finiteExhaustionStepPayloadPolynomial
  omega

/-! ## The final induction-axiom assembly -/

theorem binaryFormulaCode_all_length_le_polynomial
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode
      (∀⁰ body : LO.FirstOrder.ArithmeticProposition)).length <=
      (binaryFormulaCode body).length + (binaryNatCode 6).length := by
  simp [binaryFormulaCode]
  omega

def finiteInductionZeroFormulaCodePolynomial (bound : Nat) : Nat :=
  finiteExhaustionFormulaCodePolynomial inductionZeroTerm bound

def finiteInductionStepFormulaCodePolynomial (bound : Nat) : Nat :=
  finiteExhaustionStepBodyCodePolynomial bound + (binaryNatCode 6).length

def finiteInductionConclusionCodePolynomial (bound : Nat) : Nat :=
  finiteExhaustionFormulaCodePolynomial
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bound +
    (binaryNatCode 6).length

def finiteInductionIntermediateCodePolynomial (bound : Nat) : Nat :=
  2 * finiteInductionStepFormulaCodePolynomial bound +
    finiteInductionConclusionCodePolynomial bound +
    (binaryNatCode 5).length

def finiteInductionAxiomFormulaCodePolynomial (bound : Nat) : Nat :=
  2 * finiteInductionZeroFormulaCodePolynomial bound +
    finiteInductionIntermediateCodePolynomial bound +
    (binaryNatCode 5).length

def finiteInductionFormulaEnvelope (bound : Nat) : Nat :=
  finiteInductionZeroFormulaCodePolynomial bound +
    finiteInductionStepFormulaCodePolynomial bound +
    finiteInductionConclusionCodePolynomial bound +
    finiteInductionIntermediateCodePolynomial bound +
    finiteInductionAxiomFormulaCodePolynomial bound + 1

theorem finiteInductionZeroFormula_code_le_polynomial
    (bound : Nat) :
    (binaryFormulaCode
      ((finiteExhaustionBody bound)/[inductionZeroTerm])).length <=
      finiteInductionZeroFormulaCodePolynomial bound := by
  rw [finiteExhaustionBody_substitution]
  exact finiteExhaustionFormula_code_length_le_polynomial
    bound inductionZeroTerm

theorem finiteInductionStepFormula_code_le_polynomial
    (bound : Nat) :
    (binaryFormulaCode
      (inductionStepFormula (finiteExhaustionBody bound))).length <=
      finiteInductionStepFormulaCodePolynomial bound := by
  rw [← finiteExhaustionStepBody_all_eq_inductionStepFormula]
  have hall := binaryFormulaCode_all_length_le_polynomial
    (finiteExhaustionStepBody bound)
  have hbody := finiteExhaustionStepBody_code_length_le_polynomial bound
  unfold finiteInductionStepFormulaCodePolynomial
  omega

theorem finiteInductionConclusion_code_le_polynomial
    (bound : Nat) :
    (binaryFormulaCode
      (∀⁰ finiteExhaustionBody bound :
        LO.FirstOrder.ArithmeticProposition)).length <=
      finiteInductionConclusionCodePolynomial bound := by
  have hall := binaryFormulaCode_all_length_le_polynomial
    (finiteExhaustionBody bound)
  have hbody := finiteExhaustionBody_code_length_le_polynomial bound
  unfold finiteInductionConclusionCodePolynomial
  omega

theorem finiteInductionIntermediate_code_le_polynomial
    (bound : Nat) :
    let stepFormula := inductionStepFormula (finiteExhaustionBody bound)
    let conclusionFormula :=
      (∀⁰ finiteExhaustionBody bound :
        LO.FirstOrder.ArithmeticProposition)
    (binaryFormulaCode (stepFormula 🡒 conclusionFormula)).length <=
      finiteInductionIntermediateCodePolynomial bound := by
  let stepFormula := inductionStepFormula (finiteExhaustionBody bound)
  let conclusionFormula :=
    (∀⁰ finiteExhaustionBody bound :
      LO.FirstOrder.ArithmeticProposition)
  have hstep := finiteInductionStepFormula_code_le_polynomial bound
  have hconclusion := finiteInductionConclusion_code_le_polynomial bound
  have hraw := binaryFormulaCode_implication_length_le
    stepFormula conclusionFormula
  dsimp only [stepFormula, conclusionFormula] at hraw ⊢
  unfold finiteInductionIntermediateCodePolynomial
  omega

theorem finiteInductionAxiomFormula_code_le_polynomial
    (bound : Nat) :
    let zeroFormula := (finiteExhaustionBody bound)/[inductionZeroTerm]
    let stepFormula := inductionStepFormula (finiteExhaustionBody bound)
    let conclusionFormula :=
      (∀⁰ finiteExhaustionBody bound :
        LO.FirstOrder.ArithmeticProposition)
    (binaryFormulaCode
      (zeroFormula 🡒 stepFormula 🡒 conclusionFormula)).length <=
      finiteInductionAxiomFormulaCodePolynomial bound := by
  let zeroFormula := (finiteExhaustionBody bound)/[inductionZeroTerm]
  let stepFormula := inductionStepFormula (finiteExhaustionBody bound)
  let conclusionFormula :=
    (∀⁰ finiteExhaustionBody bound :
      LO.FirstOrder.ArithmeticProposition)
  let intermediateFormula := stepFormula 🡒 conclusionFormula
  have hzero := finiteInductionZeroFormula_code_le_polynomial bound
  have hintermediate := finiteInductionIntermediate_code_le_polynomial bound
  have hraw := binaryFormulaCode_implication_length_le
    zeroFormula intermediateFormula
  dsimp only [zeroFormula, stepFormula, conclusionFormula,
    intermediateFormula] at hraw hintermediate ⊢
  unfold finiteInductionAxiomFormulaCodePolynomial
  omega

theorem finiteInductionFormula_components_le_envelope
    (bound : Nat) :
    finiteInductionZeroFormulaCodePolynomial bound <=
        finiteInductionFormulaEnvelope bound ∧
      finiteInductionStepFormulaCodePolynomial bound <=
        finiteInductionFormulaEnvelope bound ∧
      finiteInductionConclusionCodePolynomial bound <=
        finiteInductionFormulaEnvelope bound ∧
      finiteInductionIntermediateCodePolynomial bound <=
        finiteInductionFormulaEnvelope bound ∧
      finiteInductionAxiomFormulaCodePolynomial bound <=
        finiteInductionFormulaEnvelope bound := by
  unfold finiteInductionFormulaEnvelope
  omega

def finiteInductionAxiomSyntaxPolynomial (bound : Nat) : Nat :=
  finiteInductionAxiomFormulaCodePolynomial bound +
    (binaryNatCode 1).length + (binaryNatCode 22).length +
    finiteExhaustionFormulaCodePolynomial
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bound + 1

theorem finiteInductionAxiomSyntaxBudget_le_polynomial
    (bound : Nat) :
    axiomSyntaxBudget
        (.induction (finiteExhaustionBody bound)) <=
      finiteInductionAxiomSyntaxPolynomial bound := by
  let body := finiteExhaustionBody bound
  have hclosed := finiteExhaustionBody_freeVariables_eq_empty bound
  have hformulaEq := inductionAxiom_formula body hclosed
  have hformula :
      (binaryFormulaCode
        (Rewriting.emb (PAAxiomCertificate.induction body).sentence :
          LO.FirstOrder.ArithmeticProposition)).length <=
        finiteInductionAxiomFormulaCodePolynomial bound := by
    rw [hformulaEq]
    simpa only [body] using
      finiteInductionAxiomFormula_code_le_polynomial bound
  have hbody := finiteExhaustionBody_code_length_le_polynomial bound
  have hcertificate :
      (binaryStructuralValidityCertificateCode
        (.axiomCert (.induction body))).length <=
        (binaryNatCode 1).length + (binaryNatCode 22).length +
          finiteExhaustionFormulaCodePolynomial
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bound := by
    simp only [binaryStructuralValidityCertificateCode,
      binaryPAAxiomCertificateCode, List.length_append]
    dsimp only [body]
    omega
  unfold axiomSyntaxBudget
    finiteInductionAxiomSyntaxPolynomial
  dsimp only [body] at hformula hcertificate ⊢
  omega

def finiteInductionAssemblyPolynomial (bound : Nat) : Nat :=
  32 + 10 * finiteInductionAxiomSyntaxPolynomial bound +
    480 + 68 * paAssemblySyntaxEnvelope
      (finiteInductionFormulaEnvelope bound)

theorem inductionStructuralPayloadBound_le_polynomial
    (bound zeroPayloadLength stepPayloadLength : Nat) :
    inductionStructuralPayloadBound (finiteExhaustionBody bound)
        zeroPayloadLength stepPayloadLength <=
      zeroPayloadLength + stepPayloadLength +
        finiteInductionAssemblyPolynomial bound := by
  let body := finiteExhaustionBody bound
  let zeroFormula := body/[inductionZeroTerm]
  let stepFormula := inductionStepFormula body
  let conclusionFormula :=
    (∀⁰ body : LO.FirstOrder.ArithmeticProposition)
  let intermediateFormula := stepFormula 🡒 conclusionFormula
  have hcomponents := finiteInductionFormula_components_le_envelope bound
  have hzero := (finiteInductionZeroFormula_code_le_polynomial bound).trans
    hcomponents.1
  have hstep := (finiteInductionStepFormula_code_le_polynomial bound).trans
    hcomponents.2.1
  have hconclusion := (finiteInductionConclusion_code_le_polynomial bound).trans
    hcomponents.2.2.1
  have hintermediate :=
    (finiteInductionIntermediate_code_le_polynomial bound).trans
      hcomponents.2.2.2.1
  have hmpFirst := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    zeroFormula intermediateFormula (finiteInductionFormulaEnvelope bound)
    hzero hintermediate
  have hmpSecond := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    stepFormula conclusionFormula (finiteInductionFormulaEnvelope bound)
    hstep hconclusion
  have haxiom := finiteInductionAxiomSyntaxBudget_le_polynomial bound
  unfold inductionStructuralPayloadBound finiteInductionAssemblyPolynomial
  dsimp only [body, zeroFormula, stepFormula, conclusionFormula,
    intermediateFormula] at hmpFirst hmpSecond haxiom ⊢
  omega

def finiteExhaustionPayloadPolynomial (bound : Nat) : Nat :=
  finiteExhaustionZeroPayloadPolynomial bound +
    finiteExhaustionStepPayloadPolynomial bound +
    finiteInductionAssemblyPolynomial bound

theorem finiteExhaustionStructuralPayloadBound_le_polynomial
    (bound : Nat) :
    finiteExhaustionStructuralPayloadBound bound <=
      finiteExhaustionPayloadPolynomial bound := by
  have hzero := finiteExhaustionZeroStructuralPayloadBound_le_polynomial bound
  have hstep := finiteExhaustionStepStructuralPayloadBound_le_polynomial bound
  have hinduction := inductionStructuralPayloadBound_le_polynomial bound
    (finiteExhaustionZeroStructuralPayloadBound bound)
    (finiteExhaustionStepStructuralPayloadBound bound)
  unfold finiteExhaustionStructuralPayloadBound
    finiteExhaustionPayloadPolynomial
  omega

theorem proveFiniteExhaustion_payloadLength_le_polynomial
    (bound : Nat) :
    (proveFiniteExhaustion bound).payloadLength <=
      finiteExhaustionPayloadPolynomial bound := by
  exact (proveFiniteExhaustion_payloadLength_le_structural bound).trans
    (finiteExhaustionStructuralPayloadBound_le_polynomial bound)

#print axioms finiteExhaustionFormula_code_le_caseEnvelope
#print axioms negatedFiniteCaseEqualityFormula_code_le_caseEnvelope
#print axioms successorEqualityUnderCaseStructuralPayloadBound_le_polynomial
#print axioms finalLowerBoundUnderCaseStructuralPayloadBound_le_polynomial
#print axioms advanceInjectEqualityCaseStructuralPayloadBound_le_polynomial
#print axioms advanceFiniteCasePrefixStructuralPayloadBound_le_polynomial
#print axioms finiteExhaustionZeroStructuralPayloadBound_le_polynomial
#print axioms successorLessThanImpliesLessThanStructuralPayloadBound_le_polynomial
#print axioms preserveLowerBoundBranchStructuralPayloadBound_le_polynomial
#print axioms finiteExhaustionSuccessorImplicationStructuralPayloadBound_le_polynomial
#print axioms finiteExhaustionStepBody_code_length_le_polynomial
#print axioms finiteInductionAxiomSyntaxBudget_le_polynomial
#print axioms finiteExhaustionStructuralPayloadBound_le_polynomial
#print axioms proveFiniteExhaustion_payloadLength_le_polynomial

end FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
