import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAUnaryAtomicTransportPolynomialBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fully public fixed bounds for hybrid bounded witnesses

The transparent hybrid witness compiler follows the same audited assembly
recursion as the direct compiler, but additionally compiles each closed guard.
This file removes the concrete witness bound and the concrete witness vector
from that recursion.  The resulting resource depends only on a common numeric
ceiling, a valuation-context code ceiling, an open-body code ceiling, and the
independently bounded terminal resource.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

private theorem boundedWitnessNumeralTermCodeEnvelope_mono_hybridFixed
    {small large : Nat} (hbound : small <= large) :
    boundedWitnessNumeralTermCodeEnvelope small <=
      boundedWitnessNumeralTermCodeEnvelope large := by
  unfold boundedWitnessNumeralTermCodeEnvelope
  exact
    FoundationCompactPAExponentialShortNumeralCompilerBounds.binaryNumeralTermCodeEnvelope_mono_short
      (Nat.size_le_size hbound)

private theorem uniformRewritingFormulaCodeEnvelope_mono_hybridFixed
    {smallImage largeImage smallFormula largeFormula : Nat}
    (himage : smallImage <= largeImage)
    (hformula : smallFormula <= largeFormula) :
    uniformRewritingFormulaCodeEnvelope smallImage smallFormula <=
      uniformRewritingFormulaCodeEnvelope largeImage largeFormula := by
  unfold uniformRewritingFormulaCodeEnvelope
  gcongr

private theorem
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_hybridFixed
    (contextCodeBound : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        smallBound smallBody <=
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        largeBound largeBody := by
  have hnumeral :=
    boundedWitnessNumeralTermCodeEnvelope_mono_hybridFixed hbound
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
    exact uniformRewritingFormulaCodeEnvelope_mono_hybridFixed hlifted hbody
  have hinstalled : explicitWitnessInstalledPublicCodeEnvelope smallBound
        smallBody <=
      explicitWitnessInstalledPublicCodeEnvelope largeBound largeBody := by
    unfold explicitWitnessInstalledPublicCodeEnvelope
    exact uniformRewritingFormulaCodeEnvelope_mono_hybridFixed hnumeral hbody
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
  have hopenGuard :
      boundedWitnessOpenGuardFormulaCodeEnvelope smallBound <=
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

private theorem
    closedShiftShortBinaryNumeralPublicCodeEnvelope_mono_hybridFixed
    (arity : Nat) {smallBound largeBound : Nat}
    (hbound : smallBound <= largeBound) :
    closedShiftShortBinaryNumeralPublicCodeEnvelope arity smallBound <=
      closedShiftShortBinaryNumeralPublicCodeEnvelope arity largeBound := by
  induction arity with
  | zero =>
      simpa only [closedShiftShortBinaryNumeralPublicCodeEnvelope] using
        boundedWitnessNumeralTermCodeEnvelope_mono_hybridFixed hbound
  | succ arity ih =>
      simp only [closedShiftShortBinaryNumeralPublicCodeEnvelope]
      have hnumeral :=
        boundedWitnessNumeralTermCodeEnvelope_mono_hybridFixed hbound
      omega

theorem explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
    (arity : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity smallBound
        smallBody <=
      explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity largeBound
        largeBody := by
  have hclosed :=
    closedShiftShortBinaryNumeralPublicCodeEnvelope_mono_hybridFixed arity
      hbound
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
  have hguard :
      explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity
          smallBound <=
        explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity
          largeBound := by
    unfold explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope
    omega
  unfold explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
  omega

def explicitBoundedWitnessHybridGuardFullyFixedTermCodeEnvelope
    (numericBound : Nat) : Nat :=
  boundedWitnessNumeralTermCodeEnvelope numericBound +
    boundedWitnessSuccessorTermCodeEnvelope numericBound + 1

def explicitBoundedWitnessHybridGuardFullyFixedPayloadPolynomial
    (numericBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (explicitBoundedWitnessHybridGuardFullyFixedTermCodeEnvelope numericBound)

theorem boundedWitnessGuardHybridPayloadResource_le_fullyFixed
    (valuation : Nat -> Nat) (value bound numericBound : Nat)
    (hvalue : value <= bound)
    (hbound : bound <= numericBound) :
    compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm value,
          (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)] <=
      explicitBoundedWitnessHybridGuardFullyFixedPayloadPolynomial
        numericBound := by
  let firstTerm : ValuationTerm := shortBinaryNumeralTerm value
  let secondTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  have hvalueGlobal : value <= numericBound := hvalue.trans hbound
  have hfirstCode :
      (binaryTermCode firstTerm).length <=
        explicitBoundedWitnessHybridGuardFullyFixedTermCodeEnvelope
          numericBound := by
    have hraw := shortBinaryNumeralTerm_code_length_le_bound value
      numericBound hvalueGlobal
    dsimp only [firstTerm]
    unfold explicitBoundedWitnessHybridGuardFullyFixedTermCodeEnvelope
    omega
  have hboundNumeral :
      (binaryTermCode (shortBinaryNumeralTerm bound)).length <=
        boundedWitnessNumeralTermCodeEnvelope numericBound :=
    shortBinaryNumeralTerm_code_length_le_bound bound numericBound hbound
  have hsecondRaw := arithmeticAddTerm_code_length_le
    (shortBinaryNumeralTerm bound) (‘1’ : ValuationTerm)
  have hsecondCode :
      (binaryTermCode secondTerm).length <=
        explicitBoundedWitnessHybridGuardFullyFixedTermCodeEnvelope
          numericBound := by
    dsimp only [secondTerm]
    unfold explicitBoundedWitnessHybridGuardFullyFixedTermCodeEnvelope
      boundedWitnessSuccessorTermCodeEnvelope
    omega
  have hfirstClosed : firstTerm.freeVariables = ∅ := by
    dsimp only [firstTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty value
  have hsecondClosed : secondTerm.freeVariables = ∅ := by
    dsimp only [secondTerm]
    exact boundedWitnessSuccessorTerm_freeVariables_eq_empty bound
  simpa only [explicitBoundedWitnessHybridGuardFullyFixedPayloadPolynomial,
    firstTerm, secondTerm] using
    compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.ORing.Rel.lt firstTerm secondTerm numericBound
      (explicitBoundedWitnessHybridGuardFullyFixedTermCodeEnvelope
        numericBound)
      hfirstClosed hsecondClosed hfirstCode hsecondCode

def explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
    (contextCodeBound numericBound bodyCodeBound : Nat) : Nat :=
  explicitBoundedWitnessHybridGuardFullyFixedPayloadPolynomial numericBound +
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
      numericBound bodyCodeBound

private theorem fiveTermTail_le_twoPrefix_hybridFixed
    (prefixOne prefixTwo first second third fourth fifth : Nat) :
    first + second + third + fourth + fifth <=
      prefixOne + prefixTwo + first + second + third + fourth + fifth := by
  omega

private theorem hybridHeadArithmetic_hybridFixed
    (guard guardFixed weakGuard terminal weakInstalled conjunctionCost
      weakInstantiated existsCost directFixed : Nat)
    (hguard : guard <= guardFixed)
    (htail : weakGuard + weakInstalled + conjunctionCost + weakInstantiated +
        existsCost <= directFixed) :
    guard + weakGuard + terminal + weakInstalled + conjunctionCost +
        weakInstantiated + existsCost <=
      terminal + (guardFixed + directFixed) := by
  omega

theorem
    explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_le_fullyFixed
    (valuation : Nat -> Nat) {arity : Nat}
    (contextCodeBound bound numericBound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (terminalResource : Nat)
    (hvalues : forall index, values index <= bound)
    (hbound : bound <= numericBound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound)
    (hcontext : formulaCodeSum
        (valuationContext body.freeVariables valuation) <= contextCodeBound) :
    explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
        body values terminalResource <=
      terminalResource +
        explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
          contextCodeBound numericBound bodyCodeBound := by
  have hguard :=
    boundedWitnessGuardHybridPayloadResource_le_fullyFixed valuation
      (values 0) bound numericBound (hvalues 0) hbound
  have hdirectPublic :=
    explicitBoundedWitnessDirectHeadPayloadEnvelope_le_public valuation
      contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
  have hdirectMono :=
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_hybridFixed
      contextCodeBound hbound (Nat.le_refl bodyCodeBound)
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
  let existentialContext := valuationContext existential.freeVariables
    valuation
  let weakGuard := weakeningFullAssemblyCost
    (insert guardFormula matrixContext)
  let weakInstalled :=
    weakeningFullAssemblyCost (insert installedFormula matrixContext)
  let conjunctionCost :=
    CertifiedPAContextProof.conjunctionFullAssemblyCost matrixContext
      guardFormula installedFormula
  let weakInstantiated :=
    weakeningFullAssemblyCost (insert instantiated existentialContext)
  let existsCost :=
    CertifiedPAContextProof.existsIntroFullAssemblyCost existentialContext
      boundedMatrix witnessTerm
  have htail : weakGuard + weakInstalled + conjunctionCost +
      weakInstantiated + existsCost <=
        explicitBoundedWitnessDirectHeadPayloadEnvelope valuation bound body
          values := by
    change weakGuard + weakInstalled + conjunctionCost + weakInstantiated +
        existsCost <=
      boundedWitnessGuardPayloadPolynomial
          (boundedWitnessGuardBitWidth (values 0) bound) +
        weakeningFullAssemblyCost (insert guardFormula guardContext) +
        weakGuard + weakInstalled + conjunctionCost + weakInstantiated +
        existsCost
    exact fiveTermTail_le_twoPrefix_hybridFixed _ _ _ _ _ _ _
  have hdirect :
      explicitBoundedWitnessDirectHeadPayloadEnvelope valuation bound body
          values <=
        explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
          contextCodeBound numericBound bodyCodeBound :=
    hdirectPublic.trans hdirectMono
  change
    compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
          ![shortBinaryNumeralTerm (values 0),
            (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)] +
        weakGuard + terminalResource + weakInstalled + conjunctionCost +
          weakInstantiated + existsCost <=
      terminalResource +
        (explicitBoundedWitnessHybridGuardFullyFixedPayloadPolynomial
            numericBound +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
            contextCodeBound numericBound bodyCodeBound)
  exact hybridHeadArithmetic_hybridFixed _ _ _ _ _ _ _ _ _ hguard
    (htail.trans hdirect)

#print axioms boundedWitnessGuardHybridPayloadResource_le_fullyFixed
#print axioms
  explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_le_fullyFixed

end FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
