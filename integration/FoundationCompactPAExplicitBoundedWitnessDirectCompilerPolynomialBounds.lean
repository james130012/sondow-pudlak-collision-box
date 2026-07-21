import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-!
# Public syntax bounds for direct bounded-witness installation

One witness layer is charged only to its guard bit width and to the codes of
the formulas that occur in its three small valuation contexts.  No generated
proof or certificate payload is an input to this envelope.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

def formulaCodeSum
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) : Nat :=
  Gamma.sum fun formula => (binaryFormulaCode formula).length

theorem formulaCode_le_formulaCodeSum
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hformula : formula ∈ Gamma) :
    (binaryFormulaCode formula).length ≤ formulaCodeSum Gamma := by
  unfold formulaCodeSum
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (binaryFormulaCode candidate).length)
    hformula

def explicitBoundedWitnessDirectHeadSyntaxResource
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) : Nat :=
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let guard := boundedWitnessGuardFormula (values 0) bound
  let installedFormula := witnessBody/[witnessTerm]
  let matrix := guard ⋏ installedFormula
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
      witnessBody
  let instantiated := boundedMatrix/[witnessTerm]
  let existential := (∃⁰ boundedMatrix : ValuationFormula)
  let guardContext := valuationContext guard.freeVariables valuation
  let matrixContext := valuationContext matrix.freeVariables valuation
  let existentialContext :=
    valuationContext existential.freeVariables valuation
  1 + formulaCodeSum guardContext + formulaCodeSum matrixContext +
    formulaCodeSum existentialContext +
    (binaryFormulaCode guard).length +
    (binaryFormulaCode installedFormula).length +
    (binaryFormulaCode matrix).length +
    (binaryFormulaCode boundedMatrix).length +
    (binaryFormulaCode instantiated).length +
    (binaryFormulaCode existential).length +
    (binaryTermCode witnessTerm).length

def explicitBoundedWitnessDirectHeadPayloadPolynomial
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) : Nat :=
  boundedWitnessGuardPayloadPolynomial
      (boundedWitnessGuardBitWidth (values 0) bound) +
    6 * smallContextAssemblyEnvelope
      (explicitBoundedWitnessDirectHeadSyntaxResource
        valuation bound body values)

theorem explicitBoundedWitnessDirectHeadPayloadEnvelope_le_polynomial
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (hguardCard :
      (valuationContext
        (boundedWitnessGuardFormula (values 0) bound).freeVariables
        valuation).card ≤ 4)
    (hmatrixCard :
      (valuationContext
        ((boundedWitnessGuardFormula (values 0) bound) ⋏
          ((explicitWitnessBodyAfterTail body values)/[
            shortBinaryNumeralTerm (values 0)])).freeVariables
        valuation).card ≤ 4)
    (hexistentialCard :
      (valuationContext
        (∃⁰
          (Semiformula.Operator.LT.lt.operator
              ![(#0 : ArithmeticSemiterm Nat 1),
                Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
            explicitWitnessBodyAfterTail body values) :
          ValuationFormula).freeVariables valuation).card ≤ 4) :
    explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound body values ≤
      explicitBoundedWitnessDirectHeadPayloadPolynomial
        valuation bound body values := by
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let guard := boundedWitnessGuardFormula (values 0) bound
  let installedFormula := witnessBody/[witnessTerm]
  let matrix := guard ⋏ installedFormula
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
      witnessBody
  let instantiated := boundedMatrix/[witnessTerm]
  let existential := (∃⁰ boundedMatrix : ValuationFormula)
  let guardContext := valuationContext guard.freeVariables valuation
  let matrixContext := valuationContext matrix.freeVariables valuation
  let existentialContext :=
    valuationContext existential.freeVariables valuation
  let resource := explicitBoundedWitnessDirectHeadSyntaxResource
    valuation bound body values
  have hguardContext : FormulaCodeBound guardContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext] at hsum ⊢
    omega
  have hmatrixContext : FormulaCodeBound matrixContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext] at hsum ⊢
    omega
  have hexistentialContext : FormulaCodeBound existentialContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext] at hsum ⊢
    omega
  have hguardCode : (binaryFormulaCode guard).length ≤ resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hinstalledCode :
      (binaryFormulaCode installedFormula).length ≤ resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hmatrixCode : (binaryFormulaCode matrix).length ≤ resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hboundedMatrixCode :
      (binaryFormulaCode boundedMatrix).length ≤ resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hinstantiatedCode :
      (binaryFormulaCode instantiated).length ≤ resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hexistentialCode :
      (binaryFormulaCode existential).length ≤ resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hwitnessCode : (binaryTermCode witnessTerm).length ≤ resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hguardInsertCard : (insert guard guardContext).card ≤ 8 := by
    have hinsert := Finset.card_insert_le guard guardContext
    dsimp only [guardContext, guard] at hinsert hguardCard ⊢
    omega
  have hmatrixGuardCard : (insert guard matrixContext).card ≤ 8 := by
    have hinsert := Finset.card_insert_le guard matrixContext
    dsimp only [matrixContext, matrix, guard, installedFormula, witnessBody,
      witnessTerm] at hinsert hmatrixCard ⊢
    omega
  have hmatrixInstalledCard :
      (insert installedFormula matrixContext).card ≤ 8 := by
    have hinsert := Finset.card_insert_le installedFormula matrixContext
    dsimp only [matrixContext, matrix, guard, installedFormula, witnessBody,
      witnessTerm] at hinsert hmatrixCard ⊢
    omega
  have hexistentialInsertCard :
      (insert instantiated existentialContext).card ≤ 8 := by
    have hinsert := Finset.card_insert_le instantiated existentialContext
    dsimp only [existentialContext, existential, boundedMatrix, instantiated,
      witnessBody, witnessTerm] at hinsert hexistentialCard ⊢
    omega
  have hweakGuard := weakeningFullAssemblyCost_le_small
    (insert guard guardContext) resource hguardInsertCard
      (hguardContext.insert hguardCode)
  have hweakGuardMatrix := weakeningFullAssemblyCost_le_small
    (insert guard matrixContext) resource hmatrixGuardCard
      (hmatrixContext.insert hguardCode)
  have hweakInstalled := weakeningFullAssemblyCost_le_small
    (insert installedFormula matrixContext) resource hmatrixInstalledCard
      (hmatrixContext.insert hinstalledCode)
  have hconjunction := conjunctionFullAssemblyCost_le_small
    matrixContext guard installedFormula resource hmatrixCard
      hmatrixContext hguardCode hinstalledCode hmatrixCode
  have hweakInstantiated := weakeningFullAssemblyCost_le_small
    (insert instantiated existentialContext) resource hexistentialInsertCard
      (hexistentialContext.insert hinstantiatedCode)
  have hexists := existsIntroFullAssemblyCost_le_small
    existentialContext boundedMatrix witnessTerm resource hexistentialCard
      hexistentialContext hboundedMatrixCode hwitnessCode hinstantiatedCode
      hexistentialCode
  unfold explicitBoundedWitnessDirectHeadPayloadEnvelope
  unfold explicitBoundedWitnessDirectHeadPayloadPolynomial
  dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
    boundedMatrix, instantiated, existential, guardContext, matrixContext,
    existentialContext, resource]
    at hweakGuard hweakGuardMatrix hweakInstalled hconjunction
      hweakInstantiated hexists ⊢
  omega

structure ExplicitBoundedWitnessDirectHeadSmallContexts
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) : Prop where
  guard :
    (valuationContext
      (boundedWitnessGuardFormula (values 0) bound).freeVariables
      valuation).card ≤ 4
  matrix :
    (valuationContext
      ((boundedWitnessGuardFormula (values 0) bound) ⋏
        ((explicitWitnessBodyAfterTail body values)/[
          shortBinaryNumeralTerm (values 0)])).freeVariables
      valuation).card ≤ 4
  existential :
    (valuationContext
      (∃⁰
        (Semiformula.Operator.LT.lt.operator
            ![(#0 : ArithmeticSemiterm Nat 1),
              Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
          explicitWitnessBodyAfterTail body values) :
        ValuationFormula).freeVariables valuation).card ≤ 4

theorem explicitBoundedWitnessDirectHeadPayloadEnvelope_le_polynomial_of_profile
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (profile : ExplicitBoundedWitnessDirectHeadSmallContexts
      valuation bound body values) :
    explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound body values ≤
      explicitBoundedWitnessDirectHeadPayloadPolynomial
        valuation bound body values :=
  explicitBoundedWitnessDirectHeadPayloadEnvelope_le_polynomial
    valuation bound body values profile.guard profile.matrix
      profile.existential

def directWitnessBody3
    (bound : Nat)
    (body4 : ArithmeticSemiformula Nat 4) :
    ArithmeticSemiformula Nat 3 :=
  body4.bexsLTSucc (closedShift 3 (shortBinaryNumeralTerm bound))

def directWitnessBody2
    (bound : Nat)
    (body4 : ArithmeticSemiformula Nat 4) :
    ArithmeticSemiformula Nat 2 :=
  (directWitnessBody3 bound body4).bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm bound))

def directWitnessBody1
    (bound : Nat)
    (body4 : ArithmeticSemiformula Nat 4) :
    ArithmeticSemiformula Nat 1 :=
  (directWitnessBody2 bound body4).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm bound))

def directWitnessValues3
    (values4 : Fin 4 -> Nat) : Fin 3 -> Nat :=
  fun index => values4 index.succ

def directWitnessValues2
    (values4 : Fin 4 -> Nat) : Fin 2 -> Nat :=
  fun index => values4 index.succ.succ

def directWitnessValues1
    (values4 : Fin 4 -> Nat) : Fin 1 -> Nat :=
  fun index => values4 index.succ.succ.succ

def explicitBoundedWitnessDirectHeadEnvelopeSumArity4
    (valuation : Nat -> Nat)
    (bound : Nat)
    (body4 : ArithmeticSemiformula Nat 4)
    (values4 : Fin 4 -> Nat)
    (terminalResource : Nat) : Nat :=
  terminalResource +
    explicitBoundedWitnessDirectHeadPayloadEnvelope
      valuation bound body4 values4 +
    explicitBoundedWitnessDirectHeadPayloadEnvelope
      valuation bound (directWitnessBody3 bound body4)
        (directWitnessValues3 values4) +
    explicitBoundedWitnessDirectHeadPayloadEnvelope
      valuation bound (directWitnessBody2 bound body4)
        (directWitnessValues2 values4) +
    explicitBoundedWitnessDirectHeadPayloadEnvelope
      valuation bound (directWitnessBody1 bound body4)
        (directWitnessValues1 values4)

/-- Fixed four-coordinate public envelope used by the binary-Nat status
compiler.  The terminal resource is independent; every witness layer is
charged only to its formula/term syntax and guard bit width. -/
def explicitBoundedWitnessDirectPayloadPolynomialArity4
    (valuation : Nat -> Nat)
    (bound : Nat)
    (body4 : ArithmeticSemiformula Nat 4)
    (values4 : Fin 4 -> Nat)
    (terminalResource : Nat) : Nat :=
  terminalResource +
    explicitBoundedWitnessDirectHeadPayloadPolynomial
      valuation bound body4 values4 +
    explicitBoundedWitnessDirectHeadPayloadPolynomial
      valuation bound (directWitnessBody3 bound body4)
        (directWitnessValues3 values4) +
    explicitBoundedWitnessDirectHeadPayloadPolynomial
      valuation bound (directWitnessBody2 bound body4)
        (directWitnessValues2 values4) +
    explicitBoundedWitnessDirectHeadPayloadPolynomial
      valuation bound (directWitnessBody1 bound body4)
        (directWitnessValues1 values4)

theorem explicitBoundedWitnessDirectPayloadEnvelope_arity4_eq
    (valuation : Nat -> Nat)
    (bound : Nat)
    (body4 : ArithmeticSemiformula Nat 4)
    (values4 : Fin 4 -> Nat)
    (terminalResource : Nat) :
    explicitBoundedWitnessDirectPayloadEnvelope
        valuation bound body4 values4 terminalResource =
      explicitBoundedWitnessDirectHeadEnvelopeSumArity4
        valuation bound body4 values4 terminalResource := by
  rfl

theorem explicitBoundedWitnessDirectHeadEnvelopeSumArity4_le_polynomial
    (valuation : Nat -> Nat)
    (bound : Nat)
    (body4 : ArithmeticSemiformula Nat 4)
    (values4 : Fin 4 -> Nat)
    (terminalResource : Nat)
    (h4 : explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound body4 values4 ≤
      explicitBoundedWitnessDirectHeadPayloadPolynomial
        valuation bound body4 values4)
    (h3 : explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound (directWitnessBody3 bound body4)
          (directWitnessValues3 values4) ≤
      explicitBoundedWitnessDirectHeadPayloadPolynomial
        valuation bound (directWitnessBody3 bound body4)
          (directWitnessValues3 values4))
    (h2 : explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound (directWitnessBody2 bound body4)
          (directWitnessValues2 values4) ≤
      explicitBoundedWitnessDirectHeadPayloadPolynomial
        valuation bound (directWitnessBody2 bound body4)
          (directWitnessValues2 values4))
    (h1 : explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound (directWitnessBody1 bound body4)
          (directWitnessValues1 values4) ≤
      explicitBoundedWitnessDirectHeadPayloadPolynomial
        valuation bound (directWitnessBody1 bound body4)
          (directWitnessValues1 values4)) :
    explicitBoundedWitnessDirectHeadEnvelopeSumArity4
        valuation bound body4 values4 terminalResource ≤
      explicitBoundedWitnessDirectPayloadPolynomialArity4
        valuation bound body4 values4 terminalResource := by
  unfold explicitBoundedWitnessDirectHeadEnvelopeSumArity4
  unfold explicitBoundedWitnessDirectPayloadPolynomialArity4
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add_left h4 terminalResource) h3) h2) h1

#print axioms formulaCode_le_formulaCodeSum
#print axioms explicitBoundedWitnessDirectHeadPayloadEnvelope_le_polynomial
#print axioms explicitBoundedWitnessDirectPayloadEnvelope_arity4_eq
#print axioms
  explicitBoundedWitnessDirectHeadEnvelopeSumArity4_le_polynomial

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
