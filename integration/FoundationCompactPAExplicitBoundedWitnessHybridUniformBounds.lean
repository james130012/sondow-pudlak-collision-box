import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Witness-value-free bounds for explicit bounded hybrid witnesses

The real hybrid witness recursion is compared with the audited direct witness
compiler one layer at a time.  Concrete witness values disappear from the
public resource once their checked bounds are supplied.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 50000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessHybridUniformBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

def explicitBoundedWitnessHybridGuardTermCodeEnvelope (bound : Nat) : Nat :=
  boundedWitnessNumeralTermCodeEnvelope bound +
    boundedWitnessSuccessorTermCodeEnvelope bound + 1

def explicitBoundedWitnessHybridGuardUniformPayloadPolynomial
    (numericBound bound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (explicitBoundedWitnessHybridGuardTermCodeEnvelope bound)

theorem boundedWitnessGuardHybridPayloadResource_le_uniform
    (valuation : Nat -> Nat) (value bound numericBound : Nat)
    (hvalue : value <= bound)
    (hvaluation : valuation 0 <= numericBound) :
    compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm value,
          (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)] <=
      explicitBoundedWitnessHybridGuardUniformPayloadPolynomial
        numericBound bound := by
  let firstTerm := shortBinaryNumeralTerm value
  let secondTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let args : Fin 2 -> ValuationTerm := ![firstTerm, secondTerm]
  have hfirstCode : (binaryTermCode firstTerm).length <=
      explicitBoundedWitnessHybridGuardTermCodeEnvelope bound := by
    have hraw := shortBinaryNumeralTerm_code_length_le_bound value bound hvalue
    dsimp only [firstTerm]
    unfold explicitBoundedWitnessHybridGuardTermCodeEnvelope
    omega
  have hsecondCode : (binaryTermCode secondTerm).length <=
      explicitBoundedWitnessHybridGuardTermCodeEnvelope bound := by
    have hraw := boundedWitnessSuccessorTerm_code_length_le bound
    dsimp only [secondTerm] at hraw ⊢
    unfold explicitBoundedWitnessHybridGuardTermCodeEnvelope
    omega
  have hfirstVariables : firstTerm.freeVariables ⊆ {0} := by
    rw [show firstTerm.freeVariables = ∅ by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty value]
    simp
  have hsecondVariables : secondTerm.freeVariables ⊆ {0} := by
    rw [show secondTerm.freeVariables = ∅ by
      dsimp only [secondTerm]
      exact boundedWitnessSuccessorTerm_freeVariables_eq_empty bound]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    valuation Language.ORing.Rel.lt args hfirstVariables hsecondVariables
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed valuation
    Language.ORing.Rel.lt args numericBound
      (explicitBoundedWitnessHybridGuardTermCodeEnvelope bound)
      hfirstVariables hsecondVariables hvaluation hfirstCode hsecondCode
  simpa only [explicitBoundedWitnessHybridGuardUniformPayloadPolynomial,
    args, firstTerm, secondTerm] using hpublic.trans hfixed

def explicitBoundedWitnessHybridHeadUniformPayloadPolynomial
    (valuation : Nat -> Nat) {arity : Nat}
    (numericBound bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  explicitBoundedWitnessHybridGuardUniformPayloadPolynomial numericBound bound +
    explicitBoundedWitnessDirectHeadUniformPayloadPolynomial
      valuation bound body

private theorem fiveTermTail_le_twoPrefix
    (prefixOne prefixTwo first second third fourth fifth : Nat) :
    first + second + third + fourth + fifth <=
      prefixOne + prefixTwo + first + second + third + fourth + fifth := by
  omega

private theorem hybridHeadArithmetic
    (guard guardUniform weakGuard terminal weakInstalled conjunctionCost
      weakInstantiated existsCost directUniform : Nat)
    (hguard : guard <= guardUniform)
    (htail : weakGuard + weakInstalled + conjunctionCost + weakInstantiated +
        existsCost <= directUniform) :
    guard + weakGuard + terminal + weakInstalled + conjunctionCost +
        weakInstantiated + existsCost <=
      terminal + (guardUniform + directUniform) := by
  omega

theorem explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_le_uniform
    (valuation : Nat -> Nat) {arity : Nat}
    (numericBound bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (terminalResource : Nat)
    (hvalues : forall index, values index <= bound)
    (hvaluation : valuation 0 <= numericBound) :
    explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
        body values terminalResource <=
      terminalResource +
        explicitBoundedWitnessHybridHeadUniformPayloadPolynomial valuation
          numericBound bound body := by
  have hguard := boundedWitnessGuardHybridPayloadResource_le_uniform valuation
    (values 0) bound numericBound (hvalues 0) hvaluation
  have hdirect := explicitBoundedWitnessDirectHeadPayloadEnvelope_le_uniform
    valuation bound body values hvalues
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let guardFormula := boundedWitnessGuardFormula (values 0) bound
  let installedFormula := witnessBody/[witnessTerm]
  let matrix := guardFormula ⋏ installedFormula
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
      witnessBody
  let instantiated := boundedMatrix/[witnessTerm]
  let existential := (∃⁰ boundedMatrix : ValuationFormula)
  let guardContext := valuationContext guardFormula.freeVariables valuation
  let matrixContext := valuationContext matrix.freeVariables valuation
  let existentialContext := valuationContext existential.freeVariables valuation
  let weakGuard := weakeningFullAssemblyCost (insert guardFormula matrixContext)
  let weakInstalled :=
    weakeningFullAssemblyCost (insert installedFormula matrixContext)
  let conjunctionCost :=
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.conjunctionFullAssemblyCost
      matrixContext guardFormula installedFormula
  let weakInstantiated :=
    weakeningFullAssemblyCost (insert instantiated existentialContext)
  let existsCost :=
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.existsIntroFullAssemblyCost
      existentialContext boundedMatrix witnessTerm
  have htail : weakGuard + weakInstalled + conjunctionCost + weakInstantiated +
      existsCost <=
        explicitBoundedWitnessDirectHeadPayloadEnvelope valuation bound body
          values := by
    change weakGuard + weakInstalled + conjunctionCost + weakInstantiated +
        existsCost <=
      boundedWitnessGuardPayloadPolynomial
          (boundedWitnessGuardBitWidth (values 0) bound) +
        weakeningFullAssemblyCost (insert guardFormula guardContext) +
        weakGuard + weakInstalled + conjunctionCost + weakInstantiated +
        existsCost
    exact fiveTermTail_le_twoPrefix _ _ _ _ _ _ _
  change
    compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
          ![shortBinaryNumeralTerm (values 0),
            (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)] +
        weakGuard + terminalResource + weakInstalled + conjunctionCost +
          weakInstantiated + existsCost <=
      terminalResource +
        (explicitBoundedWitnessHybridGuardUniformPayloadPolynomial
            numericBound bound +
          explicitBoundedWitnessDirectHeadUniformPayloadPolynomial valuation
            bound body)
  exact hybridHeadArithmetic _ _ _ _ _ _ _ _ _ hguard (htail.trans hdirect)

/-- Recursive public resource for a complete hybrid bounded-witness vector.
The recursion follows the real compiler but contains no concrete witness
coordinate. -/
def explicitBoundedWitnessHybridUniformPayloadEnvelope :
    {arity : Nat} ->
    (valuation : Nat -> Nat) ->
    (numericBound bound : Nat) ->
    (body : ArithmeticSemiformula Nat arity) ->
    (terminalResource : Nat) -> Nat
  | 0, _, _, _, _, terminalResource => terminalResource
  | arity + 1, valuation, numericBound, bound, body, terminalResource =>
      explicitBoundedWitnessHybridUniformPayloadEnvelope valuation numericBound
        bound
        (body.bexsLTSucc
          (closedShift arity (shortBinaryNumeralTerm bound)))
        (terminalResource +
          explicitBoundedWitnessHybridHeadUniformPayloadPolynomial valuation
            numericBound bound body)

theorem explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_uniform :
    forall {arity : Nat}
      (valuation : Nat -> Nat) (numericBound bound : Nat)
      (body : ArithmeticSemiformula Nat arity)
      (values : Fin arity -> Nat)
      {terminalSmall terminalLarge : Nat},
      (forall index, values index <= bound) ->
      valuation 0 <= numericBound ->
      terminalSmall <= terminalLarge ->
      explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation bound
          body values terminalSmall <=
        explicitBoundedWitnessHybridUniformPayloadEnvelope valuation
          numericBound bound body terminalLarge
  | 0, _, _, _, _, _, _, _, _, _, hterminal => hterminal
  | arity + 1, valuation, numericBound, bound, body, values,
      terminalSmall, terminalLarge, hvalues, hvaluation, hterminal => by
      let tailValues : Fin arity -> Nat := fun index => values index.succ
      let recursiveBody := body.bexsLTSucc
        (closedShift arity (shortBinaryNumeralTerm bound))
      have hheadMono :=
        explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_mono
          valuation bound body values hterminal
      have hheadUniform :=
        explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_le_uniform
          valuation numericBound bound body values terminalLarge hvalues
          hvaluation
      have hnext :
          explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation
              bound body values terminalSmall <=
            terminalLarge +
              explicitBoundedWitnessHybridHeadUniformPayloadPolynomial valuation
                numericBound bound body :=
        hheadMono.trans hheadUniform
      simpa only [explicitBoundedWitnessHybridStructuralPayloadEnvelope,
        explicitBoundedWitnessHybridUniformPayloadEnvelope, tailValues,
        recursiveBody] using
        explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_uniform
          valuation numericBound bound recursiveBody tailValues
          (fun index => hvalues index.succ) hvaluation hnext

#print axioms boundedWitnessGuardHybridPayloadResource_le_uniform
#print axioms
  explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_le_uniform
#print axioms explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_uniform

end FoundationCompactPAExplicitBoundedWitnessHybridUniformBounds
