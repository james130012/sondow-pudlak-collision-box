import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Code bounds for bounded-endpoint source substitutions

Public parameters are substituted through a fixed stack of bounded witness
binders.  This file bounds every lifted substitution image by the sum of the
source-term codes and then bounds the rewritten fixed source formula itself.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

def sourceTermCodeSum
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity) : Nat :=
  Finset.univ.sum fun index => (binaryTermCode (terms index)).length

theorem sourceTermCode_length_le_sum
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (index : Fin sourceArity) :
    (binaryTermCode (terms index)).length <= sourceTermCodeSum terms := by
  unfold sourceTermCodeSum
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (binaryTermCode (terms candidate)).length)
    (Finset.mem_univ index)

def sourceSubstitutionQpowUniformCodeBound : Nat -> Nat -> Nat
  | 0, termBound => termBound + 4
  | depth + 1, termBound =>
      sourceSubstitutionQpowUniformCodeBound depth termBound +
        2 * (termBound + 1)

theorem four_le_sourceSubstitutionQpowUniformCodeBound
    (depth termBound : Nat) :
    4 <= sourceSubstitutionQpowUniformCodeBound depth termBound := by
  induction depth with
  | zero =>
      simp [sourceSubstitutionQpowUniformCodeBound]
  | succ depth ih =>
      simp only [sourceSubstitutionQpowUniformCodeBound]
      omega

theorem sourceSubstitutionQpow_uniformRewritingImageBound
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (termBound : Nat)
    (hterms : forall index,
      (binaryTermCode (terms index)).length <= termBound) :
    forall depth,
      UniformRewritingImageBound (sourceSubstitutionQpow terms depth)
        (sourceSubstitutionQpowUniformCodeBound depth termBound)
        (termBound + 1)
  | 0 => by
      have hbase : RewritingImageCodeBound (Rew.subst terms) termBound := by
        constructor
        · intro index
          simpa only [Rew.subst_bvar] using hterms index
        · intro index
          simp
      simpa only [sourceSubstitutionQpow,
        sourceSubstitutionQpowUniformCodeBound] using
          UniformRewritingImageBound.ofCodeBound hbase
  | depth + 1 => by
      simpa only [sourceSubstitutionQpow,
        sourceSubstitutionQpowUniformCodeBound] using
          (sourceSubstitutionQpow_uniformRewritingImageBound terms termBound
            hterms depth).q
              (four_le_sourceSubstitutionQpowUniformCodeBound depth termBound)
              (by omega)

def sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound
    (depth termBound formulaCodeBound : Nat) : Nat :=
  uniformRewritingFormulaFactor
      (sourceSubstitutionQpowUniformCodeBound depth termBound)
      (termBound + 1) formulaCodeBound * formulaCodeBound

theorem binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
    {sourceArity targetArity : Nat}
    (depth termBound formulaCodeBound : Nat)
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (source : ArithmeticSemiformula Nat (sourceArity + depth))
    (hterms : forall index,
      (binaryTermCode (terms index)).length <= termBound)
    (hsource : (binaryFormulaCode source).length <= formulaCodeBound) :
    (binaryFormulaCode
      (sourceSubstitutionQpow terms depth ▹ source)).length <=
        sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound depth
          termBound formulaCodeBound := by
  have himages := sourceSubstitutionQpow_uniformRewritingImageBound terms
    termBound hterms depth
  have hraw := binaryFormulaCode_rewriting_length_le_factor source
    (sourceSubstitutionQpow terms depth)
    (four_le_sourceSubstitutionQpowUniformCodeBound depth termBound)
    (show 1 <= termBound + 1 by omega) himages
  have hsymbols := formulaSymbolCount_le_binaryFormulaCode_length source
  have hsymbolBound : formulaSymbolCount source <= formulaCodeBound :=
    hsymbols.trans hsource
  unfold sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound
  exact hraw.trans (Nat.mul_le_mul
    (by
      unfold uniformRewritingFormulaFactor
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right (termBound + 1)
          (Nat.mul_le_mul_left 2 hsymbolBound))
        (sourceSubstitutionQpowUniformCodeBound depth termBound))
    hsource)

def iteratedLiftedRewritingImageCodeBound : Nat -> Nat -> Nat
  | 0, termBound => termBound
  | depth + 1, termBound =>
      liftedRewritingImageCodeBound
        (iteratedLiftedRewritingImageCodeBound depth termBound)

theorem sourceSubstitutionQpow_rewritingImageCodeBound
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (termBound : Nat)
    (hterms : forall index,
      (binaryTermCode (terms index)).length <= termBound) :
    forall depth,
      RewritingImageCodeBound (sourceSubstitutionQpow terms depth)
        (iteratedLiftedRewritingImageCodeBound depth termBound)
  | 0 => by
      have hbase : RewritingImageCodeBound (Rew.subst terms) termBound := by
        constructor
        · intro index
          simpa only [Rew.subst_bvar] using hterms index
        · intro index
          simp
      simpa only [sourceSubstitutionQpow,
        iteratedLiftedRewritingImageCodeBound] using hbase
  | depth + 1 => by
      simpa only [sourceSubstitutionQpow,
        iteratedLiftedRewritingImageCodeBound] using
          (sourceSubstitutionQpow_rewritingImageCodeBound terms termBound
            hterms depth).q

def sourceSubstitutionFormulaCodeEnvelopeOfTermBound
    {sourceArity : Nat}
    (depth : Nat)
    (termBound : Nat)
    (source : ArithmeticSemiformula Nat (sourceArity + depth)) : Nat :=
  boundedRewritingFormulaCodeEnvelope
    (iteratedLiftedRewritingImageCodeBound depth termBound) source

def sourceSubstitutionFormulaCodeEnvelope
    {sourceArity targetArity : Nat}
    (depth : Nat)
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (source : ArithmeticSemiformula Nat (sourceArity + depth)) : Nat :=
  sourceSubstitutionFormulaCodeEnvelopeOfTermBound depth
    (sourceTermCodeSum terms) source

theorem binaryFormulaCode_sourceSubstitutionQpow_length_le_of_termBound
    {sourceArity targetArity : Nat}
    (depth termBound : Nat)
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (source : ArithmeticSemiformula Nat (sourceArity + depth))
    (hterms : forall index,
      (binaryTermCode (terms index)).length <= termBound) :
    (binaryFormulaCode
      (sourceSubstitutionQpow terms depth ▹ source)).length <=
        sourceSubstitutionFormulaCodeEnvelopeOfTermBound depth termBound
          source := by
  have himages := sourceSubstitutionQpow_rewritingImageCodeBound terms
    termBound hterms depth
  exact binaryFormulaCode_rewriting_length_le_envelope source
    (targetArity + depth) (sourceSubstitutionQpow terms depth)
    (iteratedLiftedRewritingImageCodeBound depth termBound) himages

theorem binaryFormulaCode_sourceSubstitutionQpow_length_le
    {sourceArity targetArity : Nat}
    (depth : Nat)
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (source : ArithmeticSemiformula Nat (sourceArity + depth)) :
    (binaryFormulaCode
      (sourceSubstitutionQpow terms depth ▹ source)).length <=
        sourceSubstitutionFormulaCodeEnvelope depth terms source := by
  exact binaryFormulaCode_sourceSubstitutionQpow_length_le_of_termBound depth
    (sourceTermCodeSum terms) terms source (sourceTermCode_length_le_sum terms)

#print axioms sourceTermCode_length_le_sum
#print axioms sourceSubstitutionQpow_uniformRewritingImageBound
#print axioms
  binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
#print axioms sourceSubstitutionQpow_rewritingImageCodeBound
#print axioms
  binaryFormulaCode_sourceSubstitutionQpow_length_le_of_termBound
#print axioms binaryFormulaCode_sourceSubstitutionQpow_length_le

end FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
