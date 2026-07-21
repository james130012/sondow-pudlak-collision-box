import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Public scalar bounds for one direct bounded-witness layer

Every formula emitted by one witness layer is charged to three public
coordinates: the witness bound, a bound for the open body code, and a bound
for the valuation-context code sum.  Concrete witness values and generated
proof payloads do not occur in these coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds

def explicitWitnessBodyAfterTailPublicCodeEnvelope
    (bound bodyCodeBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (liftedRewritingImageCodeBound
      (boundedWitnessNumeralTermCodeEnvelope bound)) bodyCodeBound

theorem explicitWitnessBodyAfterTail_code_length_le_public
    {arity : Nat}
    (bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (explicitWitnessBodyAfterTail body values)).length <=
        explicitWitnessBodyAfterTailPublicCodeEnvelope bound bodyCodeBound := by
  let rewriting : Rew ℒₒᵣ Nat arity Nat 0 :=
    Rew.subst (fun index : Fin arity =>
      shortBinaryNumeralTerm (values index.succ))
  have hrewriting : RewritingImageCodeBound rewriting
      (boundedWitnessNumeralTermCodeEnvelope bound) := by
    constructor
    · intro index
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      exact shortBinaryNumeralTerm_code_length_le_bound
        (values index.succ) bound (hvalues index.succ)
    · intro index
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting.q
    (liftedRewritingImageCodeBound
      (boundedWitnessNumeralTermCodeEnvelope bound)) hrewriting.q body
  have hwiden := uniformRewritingFormulaCodeEnvelope_mono_formula
    (liftedRewritingImageCodeBound
      (boundedWitnessNumeralTermCodeEnvelope bound)) hbody
  simpa only [explicitWitnessBodyAfterTailPublicCodeEnvelope,
    explicitWitnessBodyAfterTail, rewriting] using hraw.trans hwiden

def explicitWitnessInstalledPublicCodeEnvelope
    (bound bodyCodeBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (boundedWitnessNumeralTermCodeEnvelope bound) bodyCodeBound

theorem explicitWitnessInstalledFormula_code_length_le_public
    {arity : Nat}
    (bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat arity)
    (values : Fin arity -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))).length <=
        explicitWitnessInstalledPublicCodeEnvelope bound bodyCodeBound := by
  let rewriting : Rew ℒₒᵣ Nat arity Nat 0 :=
    Rew.subst (fun index : Fin arity =>
      shortBinaryNumeralTerm (values index))
  have hrewriting : RewritingImageCodeBound rewriting
      (boundedWitnessNumeralTermCodeEnvelope bound) := by
    constructor
    · intro index
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      exact shortBinaryNumeralTerm_code_length_le_bound
        (values index) bound (hvalues index)
    · intro index
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (boundedWitnessNumeralTermCodeEnvelope bound) hrewriting body
  have hwiden := uniformRewritingFormulaCodeEnvelope_mono_formula
    (boundedWitnessNumeralTermCodeEnvelope bound) hbody
  simpa only [explicitWitnessInstalledPublicCodeEnvelope, rewriting] using
    hraw.trans hwiden

def explicitBoundedWitnessMatrixPublicCodeEnvelope
    (bound bodyCodeBound : Nat) : Nat :=
  boundedWitnessGuardFormulaCodeEnvelope bound +
    explicitWitnessInstalledPublicCodeEnvelope bound bodyCodeBound +
    (binaryNatCode 4).length

theorem explicitBoundedWitnessMatrixFormula_code_length_le_public
    {arity : Nat}
    (bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      ((boundedWitnessGuardFormula (values 0) bound) ⋏
        ((explicitWitnessBodyAfterTail body values)/[
          shortBinaryNumeralTerm (values 0)]))).length <=
      explicitBoundedWitnessMatrixPublicCodeEnvelope bound bodyCodeBound := by
  have hguard := boundedWitnessGuardFormula_code_length_le
    (values 0) bound (hvalues 0)
  have hinstalled := explicitWitnessInstalledFormula_code_length_le_public
    bound bodyCodeBound body values hvalues hbody
  rw [explicitWitnessBodyAfterTail_subst_head]
  have hconjunction := andSemiformula_code_length_le
    (boundedWitnessGuardFormula (values 0) bound)
    (body ⇜ fun index => shortBinaryNumeralTerm (values index))
  unfold explicitBoundedWitnessMatrixPublicCodeEnvelope
  omega

def explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope
    (bound bodyCodeBound : Nat) : Nat :=
  boundedWitnessOpenGuardFormulaCodeEnvelope bound +
    explicitWitnessBodyAfterTailPublicCodeEnvelope bound bodyCodeBound +
    (binaryNatCode 4).length

theorem explicitBoundedWitnessBoundedMatrixFormula_code_length_le_public
    {arity : Nat}
    (bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (Semiformula.Operator.LT.lt.operator
          ![(#0 : ArithmeticSemiterm Nat 1),
            Rew.bShift
              (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                ArithmeticSemiterm Nat 0)] ⋏
        explicitWitnessBodyAfterTail body values)).length <=
      explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope bound
        bodyCodeBound := by
  have hopen := boundedWitnessOpenGuardFormula_code_length_le bound
  have hbodyCode := explicitWitnessBodyAfterTail_code_length_le_public
    bound bodyCodeBound body values hvalues hbody
  have hconjunction := andSemiformula_code_length_le
    (Semiformula.Operator.LT.lt.operator
      ![(#0 : ArithmeticSemiterm Nat 1),
        Rew.bShift
          (‘!!(shortBinaryNumeralTerm bound) + 1’ :
            ArithmeticSemiterm Nat 0)])
    (explicitWitnessBodyAfterTail body values)
  unfold explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope
  omega

def explicitBoundedWitnessInstantiatedPublicCodeEnvelope
    (bound bodyCodeBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope bound
      bodyCodeBound)
    (boundedWitnessNumeralTermCodeEnvelope bound)

theorem explicitBoundedWitnessInstantiatedFormula_code_length_le_public
    {arity : Nat}
    (bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      ((Semiformula.Operator.LT.lt.operator
            ![(#0 : ArithmeticSemiterm Nat 1),
              Rew.bShift
                (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                  ArithmeticSemiterm Nat 0)] ⋏
          explicitWitnessBodyAfterTail body values)/[
            shortBinaryNumeralTerm (values 0)])).length <=
      explicitBoundedWitnessInstantiatedPublicCodeEnvelope bound
        bodyCodeBound := by
  have hmatrix :=
    explicitBoundedWitnessBoundedMatrixFormula_code_length_le_public
      bound bodyCodeBound body values hvalues hbody
  have hwitness := shortBinaryNumeralTerm_code_length_le_bound
    (values 0) bound (hvalues 0)
  exact binaryFormulaCode_substitution_one_length_le_envelope
    (Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift
            (‘!!(shortBinaryNumeralTerm bound) + 1’ :
              ArithmeticSemiterm Nat 0)] ⋏
      explicitWitnessBodyAfterTail body values)
    (shortBinaryNumeralTerm (values 0))
    (explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope bound
      bodyCodeBound)
    (boundedWitnessNumeralTermCodeEnvelope bound) hmatrix hwitness

def explicitBoundedWitnessExistentialPublicCodeEnvelope
    (bound bodyCodeBound : Nat) : Nat :=
  (binaryNatCode 7).length +
    explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope bound
      bodyCodeBound

theorem explicitBoundedWitnessExistentialFormula_code_length_le_public
    {arity : Nat}
    (bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (∃⁰
        (Semiformula.Operator.LT.lt.operator
            ![(#0 : ArithmeticSemiterm Nat 1),
              Rew.bShift
                (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                  ArithmeticSemiterm Nat 0)] ⋏
          explicitWitnessBodyAfterTail body values))).length <=
      explicitBoundedWitnessExistentialPublicCodeEnvelope bound
        bodyCodeBound := by
  have hmatrix :=
    explicitBoundedWitnessBoundedMatrixFormula_code_length_le_public
      bound bodyCodeBound body values hvalues hbody
  unfold explicitBoundedWitnessExistentialPublicCodeEnvelope
  change
    (binaryNatCode 7 ++
      binaryFormulaCode
        (Semiformula.Operator.LT.lt.operator
            ![(#0 : ArithmeticSemiterm Nat 1),
              Rew.bShift
                (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                  ArithmeticSemiterm Nat 0)] ⋏
          explicitWitnessBodyAfterTail body values)).length <= _
  rw [List.length_append]
  exact Nat.add_le_add_left hmatrix _

def explicitBoundedWitnessDirectHeadPublicSyntaxResource
    (contextCodeBound bound bodyCodeBound : Nat) : Nat :=
  1 + 3 * contextCodeBound +
    boundedWitnessGuardFormulaCodeEnvelope bound +
    explicitWitnessInstalledPublicCodeEnvelope bound bodyCodeBound +
    explicitBoundedWitnessMatrixPublicCodeEnvelope bound bodyCodeBound +
    explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope bound bodyCodeBound +
    explicitBoundedWitnessInstantiatedPublicCodeEnvelope bound bodyCodeBound +
    explicitBoundedWitnessExistentialPublicCodeEnvelope bound bodyCodeBound +
    boundedWitnessNumeralTermCodeEnvelope bound

theorem explicitBoundedWitnessDirectHeadSyntaxResource_le_public
    (valuation : Nat -> Nat) {arity : Nat}
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound)
    (hcontext : formulaCodeSum
        (valuationContext body.freeVariables valuation) <= contextCodeBound) :
    explicitBoundedWitnessDirectHeadSyntaxResource
        valuation bound body values <=
      explicitBoundedWitnessDirectHeadPublicSyntaxResource
        contextCodeBound bound bodyCodeBound := by
  have hguardContextSubset :
      valuationContext
          (boundedWitnessGuardFormula (values 0) bound).freeVariables
          valuation ⊆
        valuationContext body.freeVariables valuation :=
    valuationContext_mono valuation (by
      rw [boundedWitnessGuardFormula_freeVariables_eq_empty]
      exact Finset.empty_subset _)
  have hmatrixContextSubset :
      valuationContext
          ((boundedWitnessGuardFormula (values 0) bound) ⋏
            ((explicitWitnessBodyAfterTail body values)/[
              shortBinaryNumeralTerm (values 0)])).freeVariables valuation ⊆
        valuationContext body.freeVariables valuation :=
    valuationContext_mono valuation
      (explicitBoundedWitnessMatrix_freeVariables_subset bound body values)
  have hexistentialContextSubset :
      valuationContext
          (∃⁰
            (Semiformula.Operator.LT.lt.operator
                ![(#0 : ArithmeticSemiterm Nat 1),
                  Rew.bShift
                    (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                      ArithmeticSemiterm Nat 0)] ⋏
              explicitWitnessBodyAfterTail body values)).freeVariables
          valuation ⊆
        valuationContext body.freeVariables valuation :=
    valuationContext_mono valuation
      (explicitBoundedWitnessExistential_freeVariables_subset
        bound body values)
  have hguardContext :=
    (formulaCodeSum_mono hguardContextSubset).trans hcontext
  have hmatrixContext :=
    (formulaCodeSum_mono hmatrixContextSubset).trans hcontext
  have hexistentialContext :=
    (formulaCodeSum_mono hexistentialContextSubset).trans hcontext
  have hguard := boundedWitnessGuardFormula_code_length_le
    (values 0) bound (hvalues 0)
  have hinstalled :
      (binaryFormulaCode
        ((explicitWitnessBodyAfterTail body values)/[
          shortBinaryNumeralTerm (values 0)])).length <=
        explicitWitnessInstalledPublicCodeEnvelope bound bodyCodeBound := by
    rw [explicitWitnessBodyAfterTail_subst_head]
    exact explicitWitnessInstalledFormula_code_length_le_public
      bound bodyCodeBound body values hvalues hbody
  have hmatrix := explicitBoundedWitnessMatrixFormula_code_length_le_public
    bound bodyCodeBound body values hvalues hbody
  have hbounded :=
    explicitBoundedWitnessBoundedMatrixFormula_code_length_le_public
      bound bodyCodeBound body values hvalues hbody
  have hinstantiated :=
    explicitBoundedWitnessInstantiatedFormula_code_length_le_public
      bound bodyCodeBound body values hvalues hbody
  have hexistential :=
    explicitBoundedWitnessExistentialFormula_code_length_le_public
      bound bodyCodeBound body values hvalues hbody
  have hwitness := shortBinaryNumeralTerm_code_length_le_bound
    (values 0) bound (hvalues 0)
  unfold explicitBoundedWitnessDirectHeadSyntaxResource
    explicitBoundedWitnessDirectHeadPublicSyntaxResource
  dsimp only
  omega

def explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
    (contextCodeBound bound bodyCodeBound : Nat) : Nat :=
  boundedWitnessGuardPayloadPolynomial
      (boundedWitnessGuardUniformBitWidth bound) +
    6 * generalContextAssemblyEnvelope
      (explicitBoundedWitnessDirectHeadPublicSyntaxResource
        contextCodeBound bound bodyCodeBound)

theorem explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_context
    {smallContextCodeBound largeContextCodeBound : Nat}
    (hcontext : smallContextCodeBound <= largeContextCodeBound)
    (bound bodyCodeBound : Nat) :
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
        smallContextCodeBound bound bodyCodeBound <=
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
        largeContextCodeBound bound bodyCodeBound := by
  have hsyntax :
      explicitBoundedWitnessDirectHeadPublicSyntaxResource
          smallContextCodeBound bound bodyCodeBound <=
        explicitBoundedWitnessDirectHeadPublicSyntaxResource
          largeContextCodeBound bound bodyCodeBound := by
    unfold explicitBoundedWitnessDirectHeadPublicSyntaxResource
    omega
  have hassembly := generalContextAssemblyEnvelope_mono_uniform hsyntax
  unfold explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
  omega

theorem explicitBoundedWitnessDirectHeadPayloadEnvelope_le_public
    (valuation : Nat -> Nat) {arity : Nat}
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound)
    (hcontext : formulaCodeSum
        (valuationContext body.freeVariables valuation) <= contextCodeBound) :
    explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound body values <=
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
        contextCodeBound bound bodyCodeBound := by
  have hexact := explicitBoundedWitnessDirectHeadPayloadEnvelope_le_general
    valuation bound body values
  have hbit := boundedWitnessGuardBitWidth_le_uniform
    (values 0) bound (hvalues 0)
  have hguard := boundedWitnessGuardPayloadPolynomial_mono_uniform hbit
  have hsyntax := explicitBoundedWitnessDirectHeadSyntaxResource_le_public
    valuation contextCodeBound bound bodyCodeBound body values hvalues hbody
      hcontext
  have hcontextAssembly := generalContextAssemblyEnvelope_mono_uniform hsyntax
  apply hexact.trans
  unfold explicitBoundedWitnessDirectHeadGeneralPayloadPolynomial
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
  omega

#print axioms explicitWitnessBodyAfterTail_code_length_le_public
#print axioms explicitWitnessInstalledFormula_code_length_le_public
#print axioms explicitBoundedWitnessDirectHeadSyntaxResource_le_public
#print axioms
  explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_context
#print axioms explicitBoundedWitnessDirectHeadPayloadEnvelope_le_public

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
