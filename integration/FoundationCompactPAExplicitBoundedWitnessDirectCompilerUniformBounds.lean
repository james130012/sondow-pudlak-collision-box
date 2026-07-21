import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds
import integration.FoundationCompactPAValuationTermCompilerUniformBounds

/-!
# Uniform syntax bounds for direct bounded-witness compilation

The exact witness compiler substitutes a fixed vector of closed binary
numerals into an open arithmetic matrix.  This file bounds the emitted syntax
from a common code bound for the rewriting images; no proof object or concrete
witness vector enters the public coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactCanonicalDecodeLength
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAClosedAtomicCompilerBounds
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

def liftedRewritingImageCodeBound (imageBound : Nat) : Nat :=
  3 * imageBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length + 1

def RewritingImageCodeBound
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (imageBound : Nat) : Prop :=
  (forall index,
    (binaryTermCode
      (rewriting (#index : ArithmeticSemiterm Nat sourceArity))).length <=
        imageBound) ∧
  (forall index,
    rewriting (&index : ArithmeticSemiterm Nat sourceArity) =
      (&index : ArithmeticSemiterm Nat targetArity))

theorem RewritingImageCodeBound.q
    {sourceArity targetArity : Nat}
    {rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity}
    {imageBound : Nat}
    (hbound : RewritingImageCodeBound rewriting imageBound) :
    RewritingImageCodeBound rewriting.q
      (liftedRewritingImageCodeBound imageBound) := by
  constructor
  · intro index
    cases index using Fin.cases with
    | zero =>
        simp [liftedRewritingImageCodeBound, binaryTermCode]
        omega
    | succ index =>
        rw [Rew.q_bvar_succ]
        have hshift := binaryTermCode_bShift_length_le_add_symbols
          (rewriting (#index : ArithmeticSemiterm Nat sourceArity))
        have hsymbols := termSymbolCount_le_binaryTermCode_length
          (rewriting (#index : ArithmeticSemiterm Nat sourceArity))
        have himage := hbound.1 index
        unfold liftedRewritingImageCodeBound
        omega
  · intro index
    rw [Rew.q_fvar, hbound.2 index]
    simp

def boundedRewritingTermCodeEnvelope (imageBound : Nat) :
    {arity : Nat} -> ArithmeticSemiterm Nat arity -> Nat
  | _, #_ => imageBound
  | _, &index =>
      (binaryNatCode 1).length + (binaryNatCode index).length
  | _, .func (arity := functionArity) functionSymbol arguments =>
      (binaryNatCode 2).length +
        (binaryNatCode functionArity).length +
        (binaryNatCode (Encodable.encode functionSymbol)).length +
        Finset.univ.sum (fun index =>
          (binaryTermCode (arguments index)).length +
            boundedRewritingTermCodeEnvelope imageBound (arguments index))
termination_by arity term => term.complexity
decreasing_by
  all_goals exact Semiterm.complexity_func_lt _ _ _

theorem binaryTermCode_rewriting_length_le_envelope
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (imageBound : Nat)
    (hbound : RewritingImageCodeBound rewriting imageBound) :
    (term : ArithmeticSemiterm Nat sourceArity) ->
      (binaryTermCode (rewriting term)).length <=
        boundedRewritingTermCodeEnvelope imageBound term
  | #index => by
      simpa only [boundedRewritingTermCodeEnvelope] using hbound.1 index
  | &index => by
      rw [hbound.2 index]
      simp [boundedRewritingTermCodeEnvelope, binaryTermCode]
  | .func functionSymbol arguments => by
      have hchildren :
          Finset.univ.sum (fun index =>
              (binaryTermCode (rewriting (arguments index))).length) <=
            Finset.univ.sum (fun index =>
              boundedRewritingTermCodeEnvelope imageBound
                (arguments index)) :=
        Finset.sum_le_sum (fun index _ =>
          binaryTermCode_rewriting_length_le_envelope rewriting imageBound
            hbound (arguments index))
      have hchildrenWiden :
          Finset.univ.sum (fun index =>
              boundedRewritingTermCodeEnvelope imageBound
                (arguments index)) <=
            Finset.univ.sum (fun index =>
              (binaryTermCode (arguments index)).length +
                boundedRewritingTermCodeEnvelope imageBound
                  (arguments index)) :=
        Finset.sum_le_sum (fun index _ => by omega)
      simp only [Rew.func, binaryTermCode,
        boundedRewritingTermCodeEnvelope, List.length_append]
      rw [length_flatten_ofFn]
      simpa only [Function.comp_apply, Nat.add_assoc] using
        Nat.add_le_add_left (hchildren.trans hchildrenWiden)
          ((binaryNatCode 2).length +
            (binaryNatCode _).length +
            (binaryNatCode (Encodable.encode functionSymbol)).length)

def boundedRewritingFormulaCodeEnvelope (imageBound : Nat) :
    {arity : Nat} -> ArithmeticSemiformula Nat arity -> Nat
  | _, ⊤ => (binaryNatCode 2).length
  | _, ⊥ => (binaryNatCode 3).length
  | _, .rel (arity := relationArity) relationSymbol arguments =>
      (binaryNatCode 0).length +
        (binaryNatCode relationArity).length +
        (binaryNatCode (Encodable.encode relationSymbol)).length +
        Finset.univ.sum (fun index =>
          (binaryTermCode (arguments index)).length +
            boundedRewritingTermCodeEnvelope imageBound (arguments index))
  | _, .nrel (arity := relationArity) relationSymbol arguments =>
      (binaryNatCode 1).length +
        (binaryNatCode relationArity).length +
        (binaryNatCode (Encodable.encode relationSymbol)).length +
        Finset.univ.sum (fun index =>
          (binaryTermCode (arguments index)).length +
            boundedRewritingTermCodeEnvelope imageBound (arguments index))
  | _, left ⋏ right =>
      (binaryNatCode 4).length +
        (binaryFormulaCode left).length +
        (binaryFormulaCode right).length +
        boundedRewritingFormulaCodeEnvelope imageBound left +
        boundedRewritingFormulaCodeEnvelope imageBound right
  | _, left ⋎ right =>
      (binaryNatCode 5).length +
        (binaryFormulaCode left).length +
        (binaryFormulaCode right).length +
        boundedRewritingFormulaCodeEnvelope imageBound left +
        boundedRewritingFormulaCodeEnvelope imageBound right
  | _, ∀⁰ body =>
      (binaryNatCode 6).length + (binaryFormulaCode body).length +
        boundedRewritingFormulaCodeEnvelope
          (liftedRewritingImageCodeBound imageBound) body
  | _, ∃⁰ body =>
      (binaryNatCode 7).length + (binaryFormulaCode body).length +
        boundedRewritingFormulaCodeEnvelope
          (liftedRewritingImageCodeBound imageBound) body

theorem binaryFormulaCode_rewriting_length_le_envelope
    {sourceArity : Nat}
    (formula : ArithmeticSemiformula Nat sourceArity) :
    forall (targetArity : Nat)
      (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
      (imageBound : Nat),
      RewritingImageCodeBound rewriting imageBound ->
      (binaryFormulaCode (rewriting ▹ formula)).length <=
        boundedRewritingFormulaCodeEnvelope imageBound formula := by
  induction formula using Semiformula.rec' with
  | hverum =>
      intro targetArity rewriting imageBound hbound
      simp [boundedRewritingFormulaCodeEnvelope, binaryFormulaCode]
  | hfalsum =>
      intro targetArity rewriting imageBound hbound
      simp [boundedRewritingFormulaCodeEnvelope, binaryFormulaCode]
  | hrel relationSymbol arguments =>
      intro targetArity rewriting imageBound hbound
      have hchildren :
          Finset.univ.sum (fun index =>
              (binaryTermCode (rewriting (arguments index))).length) <=
            Finset.univ.sum (fun index =>
              boundedRewritingTermCodeEnvelope imageBound
                (arguments index)) :=
        Finset.sum_le_sum (fun index _ =>
          binaryTermCode_rewriting_length_le_envelope rewriting imageBound
            hbound (arguments index))
      have hchildrenWiden :
          Finset.univ.sum (fun index =>
              boundedRewritingTermCodeEnvelope imageBound
                (arguments index)) <=
            Finset.univ.sum (fun index =>
              (binaryTermCode (arguments index)).length +
                boundedRewritingTermCodeEnvelope imageBound
                  (arguments index)) :=
        Finset.sum_le_sum (fun index _ => by omega)
      simp only [Semiformula.rew_rel, binaryFormulaCode,
        boundedRewritingFormulaCodeEnvelope, List.length_append]
      rw [length_flatten_ofFn]
      exact Nat.add_le_add_left (hchildren.trans hchildrenWiden) _
  | hnrel relationSymbol arguments =>
      intro targetArity rewriting imageBound hbound
      have hchildren :
          Finset.univ.sum (fun index =>
              (binaryTermCode (rewriting (arguments index))).length) <=
            Finset.univ.sum (fun index =>
              boundedRewritingTermCodeEnvelope imageBound
                (arguments index)) :=
        Finset.sum_le_sum (fun index _ =>
          binaryTermCode_rewriting_length_le_envelope rewriting imageBound
            hbound (arguments index))
      have hchildrenWiden :
          Finset.univ.sum (fun index =>
              boundedRewritingTermCodeEnvelope imageBound
                (arguments index)) <=
            Finset.univ.sum (fun index =>
              (binaryTermCode (arguments index)).length +
                boundedRewritingTermCodeEnvelope imageBound
                  (arguments index)) :=
        Finset.sum_le_sum (fun index _ => by omega)
      simp only [Semiformula.rew_nrel, binaryFormulaCode,
        boundedRewritingFormulaCodeEnvelope, List.length_append]
      rw [length_flatten_ofFn]
      exact Nat.add_le_add_left (hchildren.trans hchildrenWiden) _
  | hand left right ihLeft ihRight =>
      intro targetArity rewriting imageBound hbound
      have hleft := ihLeft targetArity rewriting imageBound hbound
      have hright := ihRight targetArity rewriting imageBound hbound
      simp only [LogicalConnective.HomClass.map_and, binaryFormulaCode,
        boundedRewritingFormulaCodeEnvelope, List.length_append]
      omega
  | hor left right ihLeft ihRight =>
      intro targetArity rewriting imageBound hbound
      have hleft := ihLeft targetArity rewriting imageBound hbound
      have hright := ihRight targetArity rewriting imageBound hbound
      simp only [LogicalConnective.HomClass.map_or, binaryFormulaCode,
        boundedRewritingFormulaCodeEnvelope, List.length_append]
      omega
  | hall body ih =>
      intro targetArity rewriting imageBound hbound
      have hbody := ih (targetArity + 1) rewriting.q
        (liftedRewritingImageCodeBound imageBound) hbound.q
      simp only [Rewriting.app_all, binaryFormulaCode,
        boundedRewritingFormulaCodeEnvelope, List.length_append]
      omega
  | hexs body ih =>
      intro targetArity rewriting imageBound hbound
      have hbody := ih (targetArity + 1) rewriting.q
        (liftedRewritingImageCodeBound imageBound) hbound.q
      simp only [Rewriting.app_exs, binaryFormulaCode,
        boundedRewritingFormulaCodeEnvelope, List.length_append]
      omega

/-- Public code coordinate for every short-binary numeral bounded by `bound`. -/
def boundedWitnessNumeralTermCodeEnvelope (bound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope (Nat.size bound)

theorem shortBinaryNumeralTerm_code_length_le_bound
    (value bound : Nat) (hvalue : value <= bound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      boundedWitnessNumeralTermCodeEnvelope bound := by
  exact binaryNumeralTerm_code_length_le_envelope value (Nat.size bound)
    (Nat.size_le_size hvalue)

/-- Syntax-only envelope for the one-variable body left after installing every
tail witness.  Concrete witness values do not occur in this coordinate. -/
def explicitWitnessBodyAfterTailFormulaCodeEnvelope
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  boundedRewritingFormulaCodeEnvelope
    (liftedRewritingImageCodeBound
      (boundedWitnessNumeralTermCodeEnvelope bound)) body

theorem explicitWitnessBodyAfterTail_code_length_le_uniform
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound) :
    (binaryFormulaCode
      (explicitWitnessBodyAfterTail body values)).length <=
        explicitWitnessBodyAfterTailFormulaCodeEnvelope bound body := by
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
  have hbound := binaryFormulaCode_rewriting_length_le_envelope
    body 1 rewriting.q
      (liftedRewritingImageCodeBound
        (boundedWitnessNumeralTermCodeEnvelope bound)) hrewriting.q
  simpa only [explicitWitnessBodyAfterTailFormulaCodeEnvelope,
    explicitWitnessBodyAfterTail, rewriting] using hbound

def boundedWitnessSuccessorTermCodeEnvelope (bound : Nat) : Nat :=
  boundedWitnessNumeralTermCodeEnvelope bound +
    (binaryTermCode (‘1’ : ArithmeticSemiterm Nat 0)).length +
    binaryFunctionTermCodeOverhead Language.Add.add

theorem arithmeticAddTerm_code_length_le
    {arity : Nat}
    (left right : ArithmeticSemiterm Nat arity) :
    (binaryTermCode ‘!!left + !!right’).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Matrix.fun_eq_vec_two, binaryTermCode,
    binaryFunctionTermCodeOverhead]
  omega

theorem boundedWitnessSuccessorTerm_code_length_le (bound : Nat) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm bound) + 1’ :
        ArithmeticSemiterm Nat 0)).length <=
      boundedWitnessSuccessorTermCodeEnvelope bound := by
  have hshort := shortBinaryNumeralTerm_code_length_le_bound
    bound bound le_rfl
  have hadd := arithmeticAddTerm_code_length_le
    (shortBinaryNumeralTerm bound)
    (‘1’ : ArithmeticSemiterm Nat 0)
  unfold boundedWitnessSuccessorTermCodeEnvelope
  omega

def boundedWitnessShiftedSuccessorTermCodeEnvelope (bound : Nat) : Nat :=
  3 * boundedWitnessSuccessorTermCodeEnvelope bound

theorem boundedWitnessShiftedSuccessorTerm_code_length_le (bound : Nat) :
    (binaryTermCode
      (Rew.bShift
        (‘!!(shortBinaryNumeralTerm bound) + 1’ :
          ArithmeticSemiterm Nat 0))).length <=
      boundedWitnessShiftedSuccessorTermCodeEnvelope bound := by
  let source : ArithmeticSemiterm Nat 0 :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  have hshift := binaryTermCode_bShift_length_le_add_symbols source
  have hsymbols := termSymbolCount_le_binaryTermCode_length source
  have hsource := boundedWitnessSuccessorTerm_code_length_le bound
  unfold boundedWitnessShiftedSuccessorTermCodeEnvelope
  dsimp only [source] at hshift hsymbols
  omega

theorem lessThanSemiformula_code_length_le
    {arity : Nat}
    (left right : ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode
      (Semiformula.Operator.LT.lt.operator ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        lessThanFormulaCodeOverhead := by
  simp [Semiformula.Operator.operator,
    Semiformula.Operator.LT.sentence_eq, Matrix.fun_eq_vec_two,
    binaryFormulaCode, lessThanFormulaCodeOverhead]
  omega

def boundedWitnessGuardFormulaCodeEnvelope (bound : Nat) : Nat :=
  boundedWitnessNumeralTermCodeEnvelope bound +
    boundedWitnessSuccessorTermCodeEnvelope bound +
    lessThanFormulaCodeOverhead

theorem boundedWitnessGuardFormula_code_length_le
    (value bound : Nat) (hvalue : value <= bound) :
    (binaryFormulaCode
      (boundedWitnessGuardFormula value bound)).length <=
        boundedWitnessGuardFormulaCodeEnvelope bound := by
  have hleft := shortBinaryNumeralTerm_code_length_le_bound
    value bound hvalue
  have hright := boundedWitnessSuccessorTerm_code_length_le bound
  have hformula := lessThanSemiformula_code_length_le
    (shortBinaryNumeralTerm value)
    (‘!!(shortBinaryNumeralTerm bound) + 1’ :
      ArithmeticSemiterm Nat 0)
  unfold boundedWitnessGuardFormulaCodeEnvelope
  simpa only [boundedWitnessGuardFormula,
    Semiformula.Operator.lt_def] using hformula.trans (by omega)

def boundedWitnessOpenGuardFormulaCodeEnvelope (bound : Nat) : Nat :=
  (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length +
    boundedWitnessShiftedSuccessorTermCodeEnvelope bound +
    lessThanFormulaCodeOverhead

theorem boundedWitnessOpenGuardFormula_code_length_le (bound : Nat) :
    (binaryFormulaCode
      (Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift
            (‘!!(shortBinaryNumeralTerm bound) + 1’ :
              ArithmeticSemiterm Nat 0)])).length <=
      boundedWitnessOpenGuardFormulaCodeEnvelope bound := by
  have hright := boundedWitnessShiftedSuccessorTerm_code_length_le bound
  have hformula := lessThanSemiformula_code_length_le
    (#0 : ArithmeticSemiterm Nat 1)
    (Rew.bShift
      (‘!!(shortBinaryNumeralTerm bound) + 1’ :
        ArithmeticSemiterm Nat 0))
  unfold boundedWitnessOpenGuardFormulaCodeEnvelope
  omega

theorem andSemiformula_code_length_le
    {arity : Nat}
    (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (left ⋏ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + (binaryNatCode 4).length := by
  simp [binaryFormulaCode]
  omega

def explicitWitnessInstalledFormulaCodeEnvelope
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat arity) : Nat :=
  boundedRewritingFormulaCodeEnvelope
    (boundedWitnessNumeralTermCodeEnvelope bound) body

theorem explicitWitnessInstalledFormula_code_length_le_uniform
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat arity)
    (values : Fin arity -> Nat)
    (hvalues : forall index, values index <= bound) :
    (binaryFormulaCode
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))).length <=
        explicitWitnessInstalledFormulaCodeEnvelope bound body := by
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
  have hbound := binaryFormulaCode_rewriting_length_le_envelope
    body 0 rewriting (boundedWitnessNumeralTermCodeEnvelope bound) hrewriting
  simpa only [explicitWitnessInstalledFormulaCodeEnvelope, rewriting] using hbound

def explicitBoundedWitnessMatrixFormulaCodeEnvelope
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  boundedWitnessGuardFormulaCodeEnvelope bound +
    explicitWitnessInstalledFormulaCodeEnvelope bound body +
    (binaryNatCode 4).length

theorem explicitBoundedWitnessMatrixFormula_code_length_le_uniform
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound) :
    (binaryFormulaCode
      ((boundedWitnessGuardFormula (values 0) bound) ⋏
        ((explicitWitnessBodyAfterTail body values)/[
          shortBinaryNumeralTerm (values 0)]))).length <=
      explicitBoundedWitnessMatrixFormulaCodeEnvelope bound body := by
  have hguard := boundedWitnessGuardFormula_code_length_le
    (values 0) bound (hvalues 0)
  have hinstalled := explicitWitnessInstalledFormula_code_length_le_uniform
    bound body values hvalues
  rw [explicitWitnessBodyAfterTail_subst_head]
  have hconjunction := andSemiformula_code_length_le
    (boundedWitnessGuardFormula (values 0) bound)
    (body ⇜ fun index => shortBinaryNumeralTerm (values index))
  unfold explicitBoundedWitnessMatrixFormulaCodeEnvelope
  omega

def explicitBoundedWitnessBoundedMatrixFormulaCodeEnvelope
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  boundedWitnessOpenGuardFormulaCodeEnvelope bound +
    explicitWitnessBodyAfterTailFormulaCodeEnvelope bound body +
    (binaryNatCode 4).length

theorem explicitBoundedWitnessBoundedMatrixFormula_code_length_le_uniform
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound) :
    (binaryFormulaCode
      (Semiformula.Operator.LT.lt.operator
          ![(#0 : ArithmeticSemiterm Nat 1),
            Rew.bShift
              (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                ArithmeticSemiterm Nat 0)] ⋏
        explicitWitnessBodyAfterTail body values)).length <=
      explicitBoundedWitnessBoundedMatrixFormulaCodeEnvelope bound body := by
  have hopen := boundedWitnessOpenGuardFormula_code_length_le bound
  have hbody := explicitWitnessBodyAfterTail_code_length_le_uniform
    bound body values hvalues
  have hconjunction := andSemiformula_code_length_le
    (Semiformula.Operator.LT.lt.operator
      ![(#0 : ArithmeticSemiterm Nat 1),
        Rew.bShift
          (‘!!(shortBinaryNumeralTerm bound) + 1’ :
            ArithmeticSemiterm Nat 0)])
    (explicitWitnessBodyAfterTail body values)
  unfold explicitBoundedWitnessBoundedMatrixFormulaCodeEnvelope
  omega

def explicitBoundedWitnessInstantiatedFormulaCodeEnvelope
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  substitutionFormulaCodeEnvelope
    (explicitBoundedWitnessBoundedMatrixFormulaCodeEnvelope bound body)
    (boundedWitnessNumeralTermCodeEnvelope bound)

theorem explicitBoundedWitnessInstantiatedFormula_code_length_le_uniform
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound) :
    (binaryFormulaCode
      ((Semiformula.Operator.LT.lt.operator
            ![(#0 : ArithmeticSemiterm Nat 1),
              Rew.bShift
                (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                  ArithmeticSemiterm Nat 0)] ⋏
          explicitWitnessBodyAfterTail body values)/[
            shortBinaryNumeralTerm (values 0)])).length <=
      explicitBoundedWitnessInstantiatedFormulaCodeEnvelope bound body := by
  have hmatrix :=
    explicitBoundedWitnessBoundedMatrixFormula_code_length_le_uniform
      bound body values hvalues
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
    (explicitBoundedWitnessBoundedMatrixFormulaCodeEnvelope bound body)
    (boundedWitnessNumeralTermCodeEnvelope bound) hmatrix hwitness

def explicitBoundedWitnessExistentialFormulaCodeEnvelope
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  (binaryNatCode 7).length +
    explicitBoundedWitnessBoundedMatrixFormulaCodeEnvelope bound body

theorem explicitBoundedWitnessExistentialFormula_code_length_le_uniform
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound) :
    (binaryFormulaCode
      (∃⁰
        (Semiformula.Operator.LT.lt.operator
            ![(#0 : ArithmeticSemiterm Nat 1),
              Rew.bShift
                (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                  ArithmeticSemiterm Nat 0)] ⋏
          explicitWitnessBodyAfterTail body values))).length <=
      explicitBoundedWitnessExistentialFormulaCodeEnvelope bound body := by
  have hmatrix :=
    explicitBoundedWitnessBoundedMatrixFormula_code_length_le_uniform
      bound body values hvalues
  unfold explicitBoundedWitnessExistentialFormulaCodeEnvelope
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

theorem explicitWitnessInstalledFormula_freeVariables_subset
    {arity : Nat}
    (body : ArithmeticSemiformula Nat arity)
    (values : Fin arity -> Nat) :
    (body ⇜ fun index =>
      shortBinaryNumeralTerm (values index)).freeVariables ⊆
        body.freeVariables := by
  intro index hindex
  have hrewritten :
      (Rew.subst (fun sourceIndex : Fin arity =>
        shortBinaryNumeralTerm (values sourceIndex)) ▹ body).FVar? index :=
    hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, himage⟩
    rw [Rew.subst_bvar] at himage
    have himpossible : index ∈
        (shortBinaryNumeralTerm (values boundIndex)).freeVariables := himage
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at himpossible
    simp at himpossible
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    have hsame : index = sourceIndex := by
      simpa [LO.FirstOrder.Semiterm.FVar?] using himage
    subst index
    exact hsource

theorem explicitWitnessBodyAfterTail_freeVariables_subset
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    (explicitWitnessBodyAfterTail body values).freeVariables ⊆
      body.freeVariables := by
  let rewriting : Rew ℒₒᵣ Nat arity Nat 0 :=
    Rew.subst (fun sourceIndex : Fin arity =>
      shortBinaryNumeralTerm (values sourceIndex.succ))
  intro index hindex
  have hrewritten : (rewriting.q ▹ body).FVar? index := by
    simpa only [explicitWitnessBodyAfterTail, rewriting] using hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, himage⟩
    cases boundIndex using Fin.cases with
    | zero =>
        simp [rewriting, LO.FirstOrder.Semiterm.FVar?] at himage
    | succ tailIndex =>
        rw [Rew.q_bvar_succ] at himage
        have himpossible : index ∈
            (Rew.bShift
              (shortBinaryNumeralTerm
                (values tailIndex.succ))).freeVariables := himage
        have himpossible' : index ∈
            (shortBinaryNumeralTerm
              (values tailIndex.succ)).freeVariables := by
          simpa using himpossible
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at himpossible'
        simp at himpossible'
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    rw [Rew.q_fvar] at himage
    dsimp only [rewriting] at himage
    have hsame : index = sourceIndex := by
      simpa [LO.FirstOrder.Semiterm.FVar?] using himage
    subst index
    exact hsource

theorem arithmeticAddTerm_freeVariables_eq_union
    {arity : Nat}
    (left right : ArithmeticSemiterm Nat arity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Nat arity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  ext candidate
  constructor
  · intro hcandidate
    rw [Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

theorem lessThanSemiformula_freeVariables_eq_union
    {arity : Nat}
    (left right : ArithmeticSemiterm Nat arity) :
    (Semiformula.Operator.LT.lt.operator
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  change
    (Semiformula.rel Language.LT.lt ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  ext candidate
  constructor
  · intro hcandidate
    rw [Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [Semiformula.freeVariables_rel]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

theorem boundedWitnessSuccessorTerm_freeVariables_eq_empty
    (bound : Nat) :
    (‘!!(shortBinaryNumeralTerm bound) + 1’ :
      ArithmeticSemiterm Nat 0).freeVariables = ∅ := by
  rw [arithmeticAddTerm_freeVariables_eq_union,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  have hone : (‘1’ : ArithmeticSemiterm Nat 0).freeVariables = ∅ := by
    simp [Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
      Semiterm.Operator.One.term_eq]
  rw [hone]
  simp

theorem boundedWitnessGuardFormula_freeVariables_eq_empty
    (value bound : Nat) :
    (boundedWitnessGuardFormula value bound).freeVariables = ∅ := by
  rw [boundedWitnessGuardFormula,
    lessThanSemiformula_freeVariables_eq_union,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    boundedWitnessSuccessorTerm_freeVariables_eq_empty]
  simp

theorem boundedWitnessOpenGuardFormula_freeVariables_eq_empty
    (bound : Nat) :
    (Semiformula.Operator.LT.lt.operator
      ![(#0 : ArithmeticSemiterm Nat 1),
        Rew.bShift
          (‘!!(shortBinaryNumeralTerm bound) + 1’ :
            ArithmeticSemiterm Nat 0)]).freeVariables = ∅ := by
  rw [lessThanSemiformula_freeVariables_eq_union]
  have hshift := bShift_freeVariables_eq_empty_of_empty
    (‘!!(shortBinaryNumeralTerm bound) + 1’ :
      ArithmeticSemiterm Nat 0)
    (boundedWitnessSuccessorTerm_freeVariables_eq_empty bound)
  rw [hshift]
  simp

theorem explicitBoundedWitnessMatrix_freeVariables_subset
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    ((boundedWitnessGuardFormula (values 0) bound) ⋏
      ((explicitWitnessBodyAfterTail body values)/[
        shortBinaryNumeralTerm (values 0)])).freeVariables ⊆
      body.freeVariables := by
  intro index hindex
  rw [Semiformula.freeVariables_and] at hindex
  rcases Finset.mem_union.mp hindex with hguard | hinstalled
  · rw [boundedWitnessGuardFormula_freeVariables_eq_empty] at hguard
    simp at hguard
  · rw [explicitWitnessBodyAfterTail_subst_head] at hinstalled
    exact explicitWitnessInstalledFormula_freeVariables_subset
      body values hinstalled

theorem explicitBoundedWitnessBoundedMatrix_freeVariables_subset
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    (Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift
            (‘!!(shortBinaryNumeralTerm bound) + 1’ :
              ArithmeticSemiterm Nat 0)] ⋏
      explicitWitnessBodyAfterTail body values).freeVariables ⊆
        body.freeVariables := by
  intro index hindex
  rw [Semiformula.freeVariables_and] at hindex
  rcases Finset.mem_union.mp hindex with hopen | hbody
  · rw [boundedWitnessOpenGuardFormula_freeVariables_eq_empty] at hopen
    simp at hopen
  · exact explicitWitnessBodyAfterTail_freeVariables_subset
      body values hbody

theorem explicitBoundedWitnessExistential_freeVariables_subset
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    (∃⁰
      (Semiformula.Operator.LT.lt.operator
          ![(#0 : ArithmeticSemiterm Nat 1),
            Rew.bShift
              (‘!!(shortBinaryNumeralTerm bound) + 1’ :
                ArithmeticSemiterm Nat 0)] ⋏
        explicitWitnessBodyAfterTail body values)).freeVariables ⊆
      body.freeVariables := by
  simpa only [Semiformula.freeVariables_exs] using
    explicitBoundedWitnessBoundedMatrix_freeVariables_subset
      bound body values

theorem formulaCodeSum_mono
    {small large : Finset LO.FirstOrder.ArithmeticProposition}
    (hsubset : small ⊆ large) :
    formulaCodeSum small <= formulaCodeSum large := by
  unfold formulaCodeSum
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun _ _ _ => Nat.zero_le _)

def explicitBoundedWitnessDirectHeadUniformSyntaxResource
    (valuation : Nat -> Nat) {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  let bodyContext := valuationContext body.freeVariables valuation
  1 + 3 * formulaCodeSum bodyContext +
    boundedWitnessGuardFormulaCodeEnvelope bound +
    explicitWitnessInstalledFormulaCodeEnvelope bound body +
    explicitBoundedWitnessMatrixFormulaCodeEnvelope bound body +
    explicitBoundedWitnessBoundedMatrixFormulaCodeEnvelope bound body +
    explicitBoundedWitnessInstantiatedFormulaCodeEnvelope bound body +
    explicitBoundedWitnessExistentialFormulaCodeEnvelope bound body +
    boundedWitnessNumeralTermCodeEnvelope bound

theorem explicitBoundedWitnessDirectHeadSyntaxResource_le_uniform
    (valuation : Nat -> Nat) {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound) :
    explicitBoundedWitnessDirectHeadSyntaxResource
        valuation bound body values <=
      explicitBoundedWitnessDirectHeadUniformSyntaxResource
        valuation bound body := by
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
  have hguardContext := formulaCodeSum_mono hguardContextSubset
  have hmatrixContext := formulaCodeSum_mono hmatrixContextSubset
  have hexistentialContext := formulaCodeSum_mono hexistentialContextSubset
  have hguard := boundedWitnessGuardFormula_code_length_le
    (values 0) bound (hvalues 0)
  have hinstalled :
      (binaryFormulaCode
        ((explicitWitnessBodyAfterTail body values)/[
          shortBinaryNumeralTerm (values 0)])).length <=
        explicitWitnessInstalledFormulaCodeEnvelope bound body := by
    rw [explicitWitnessBodyAfterTail_subst_head]
    exact explicitWitnessInstalledFormula_code_length_le_uniform
      bound body values hvalues
  have hmatrix := explicitBoundedWitnessMatrixFormula_code_length_le_uniform
    bound body values hvalues
  have hboundedMatrix :=
    explicitBoundedWitnessBoundedMatrixFormula_code_length_le_uniform
      bound body values hvalues
  have hinstantiated :=
    explicitBoundedWitnessInstantiatedFormula_code_length_le_uniform
      bound body values hvalues
  have hexistential :=
    explicitBoundedWitnessExistentialFormula_code_length_le_uniform
      bound body values hvalues
  have hwitness := shortBinaryNumeralTerm_code_length_le_bound
    (values 0) bound (hvalues 0)
  unfold explicitBoundedWitnessDirectHeadSyntaxResource
  unfold explicitBoundedWitnessDirectHeadUniformSyntaxResource
  dsimp only
  omega

/-! ## Monotonicity of the guard and context ledgers -/

theorem paTermCodeBaseEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paTermCodeBaseEnvelope small <= paTermCodeBaseEnvelope large := by
  have hnumeral := binaryNumeralTermCodeEnvelope_mono_short hbound
  unfold paTermCodeBaseEnvelope
  omega

theorem paGeneratedTermAtomEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paGeneratedTermAtomEnvelope small <=
      paGeneratedTermAtomEnvelope large := by
  have hbase := paTermCodeBaseEnvelope_mono_uniform hbound
  unfold paGeneratedTermAtomEnvelope
  omega

theorem compilerTermCodeEnvelope_mono_uniform
    (nodeBudget : Nat) {small large : Nat} (hbound : small <= large) :
    compilerTermCodeEnvelope nodeBudget small <=
      compilerTermCodeEnvelope nodeBudget large := by
  have hatom := paGeneratedTermAtomEnvelope_mono_uniform hbound
  unfold compilerTermCodeEnvelope
  exact Nat.mul_le_mul_left _ hatom

theorem compilerLocalCostEnvelope_mono_uniform
    (nodeBudget : Nat) {small large : Nat} (hbound : small <= large) :
    compilerLocalCostEnvelope nodeBudget small <=
      compilerLocalCostEnvelope nodeBudget large := by
  have hterm := compilerTermCodeEnvelope_mono_uniform nodeBudget hbound
  have hprimitive := paPrimitiveCostEnvelope_mono_local hterm
  have haddition := binaryNumeralAdditionPayloadPolynomial_mono_uniform hbound
  have hmultiplication :=
    binaryNumeralMultiplicationPayloadPolynomial_mono_uniform hbound
  unfold compilerLocalCostEnvelope
  omega

theorem orderFormulaCodeEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    orderFormulaCodeEnvelope small <= orderFormulaCodeEnvelope large := by
  have hstageOne := substitutionFormulaCodeEnvelope_mono_short
    (smallFormula := orderFormulaStage0)
    (largeFormula := orderFormulaStage0) le_rfl hbound
  change orderFormulaStage1 small <= orderFormulaStage1 large at hstageOne
  have hstageTwo := substitutionFormulaCodeEnvelope_mono_short
    hstageOne hbound
  change orderFormulaStage2 small <= orderFormulaStage2 large at hstageTwo
  have hstageThree := substitutionFormulaCodeEnvelope_mono_short
    hstageTwo hbound
  change orderFormulaStage3 small <= orderFormulaStage3 large at hstageThree
  have hstageFour := substitutionFormulaCodeEnvelope_mono_short
    hstageThree hbound
  change orderFormulaStage4 small <= orderFormulaStage4 large at hstageFour
  unfold orderFormulaCodeEnvelope
  omega

theorem orderSpecializationCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    orderSpecializationCostEnvelope small <=
      orderSpecializationCostEnvelope large := by
  have hformula := orderFormulaCodeEnvelope_mono_uniform hbound
  have hscale : orderSpecializationScaleEnvelope small <=
      orderSpecializationScaleEnvelope large := by
    unfold orderSpecializationScaleEnvelope
    omega
  unfold orderSpecializationCostEnvelope
  gcongr

theorem orderPrimitiveCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    orderPrimitiveCostEnvelope small <=
      orderPrimitiveCostEnvelope large := by
  have hspecialization := orderSpecializationCostEnvelope_mono_uniform hbound
  have hformula := orderPrimitiveFormulaCodeEnvelope_mono_local hbound
  unfold orderPrimitiveCostEnvelope
  omega

theorem cumulativeBinaryAdditionPayloadPolynomial_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    cumulativeBinaryAdditionPayloadPolynomial small <=
      cumulativeBinaryAdditionPayloadPolynomial large := by
  unfold cumulativeBinaryAdditionPayloadPolynomial
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hbound))
    (fun _ _ _ => Nat.zero_le _)

theorem cumulativeBinaryMultiplicationPayloadPolynomial_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    cumulativeBinaryMultiplicationPayloadPolynomial small <=
      cumulativeBinaryMultiplicationPayloadPolynomial large := by
  unfold cumulativeBinaryMultiplicationPayloadPolynomial
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hbound))
    (fun _ _ _ => Nat.zero_le _)

theorem orderTermCodeEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    orderTermCodeEnvelope small <= orderTermCodeEnvelope large := by
  have hwork : orderTermWorkWidth small <= orderTermWorkWidth large := by
    unfold orderTermWorkWidth
    omega
  unfold orderTermCodeEnvelope
  exact paGeneratedTermCodeEnvelope_mono_short hwork

theorem orderStepCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    orderStepCostEnvelope small <= orderStepCostEnvelope large := by
  have hterm := orderTermCodeEnvelope_mono_uniform hbound
  have hprimitive := orderPrimitiveCostEnvelope_mono_uniform hterm
  have haddition := cumulativeBinaryAdditionPayloadPolynomial_mono_uniform
    (show 2 * small <= 2 * large from Nat.mul_le_mul_left 2 hbound)
  unfold orderStepCostEnvelope
  omega

theorem orderDoubleTermCodeEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    orderDoubleTermCodeEnvelope small <=
      orderDoubleTermCodeEnvelope large := by
  have hwork : orderDoubleTermWorkWidth small <=
      orderDoubleTermWorkWidth large := by
    unfold orderDoubleTermWorkWidth
    omega
  unfold orderDoubleTermCodeEnvelope
  exact paGeneratedTermCodeEnvelope_mono_short hwork

theorem orderDoubleStepCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    orderDoubleStepCostEnvelope small <=
      orderDoubleStepCostEnvelope large := by
  have hterm := orderDoubleTermCodeEnvelope_mono_uniform hbound
  have hprimitive := orderPrimitiveCostEnvelope_mono_uniform hterm
  have hmultiplication :=
    cumulativeBinaryMultiplicationPayloadPolynomial_mono_uniform
      (show small + 2 <= large + 2 from Nat.add_le_add_right hbound 2)
  unfold orderDoubleStepCostEnvelope
  omega

theorem positiveBinaryLocalCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    positiveBinaryLocalCostEnvelope small <=
      positiveBinaryLocalCostEnvelope large := by
  have hdouble := orderDoubleStepCostEnvelope_mono_uniform hbound
  have hstep := orderStepCostEnvelope_mono_uniform
    (show 2 * small + 1 <= 2 * large + 1 by omega)
  unfold positiveBinaryLocalCostEnvelope
  omega

theorem positiveBinaryNumeralPayloadPolynomial_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    positiveBinaryNumeralPayloadPolynomial small <=
      positiveBinaryNumeralPayloadPolynomial large := by
  have hlocal := positiveBinaryLocalCostEnvelope_mono_uniform hbound
  unfold positiveBinaryNumeralPayloadPolynomial
  exact Nat.add_le_add_left (Nat.mul_le_mul hbound hlocal) _

theorem boundedWitnessGuardTermCodeEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    boundedWitnessGuardTermCodeEnvelope small <=
      boundedWitnessGuardTermCodeEnvelope large := by
  unfold boundedWitnessGuardTermCodeEnvelope
  exact compilerTermCodeEnvelope_mono_uniform 5 hbound

theorem boundedWitnessGuardSourcePayloadPolynomial_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    boundedWitnessGuardSourcePayloadPolynomial small <=
      boundedWitnessGuardSourcePayloadPolynomial large := by
  have hlocal := compilerLocalCostEnvelope_mono_uniform 5 hbound
  have hpositive := positiveBinaryNumeralPayloadPolynomial_mono_uniform hbound
  have hstep := orderStepCostEnvelope_mono_uniform hbound
  have hterm := boundedWitnessGuardTermCodeEnvelope_mono_uniform hbound
  have hprimitive := paPrimitiveCostEnvelope_mono_local hterm
  have horder := orderPrimitiveCostEnvelope_mono_uniform hterm
  unfold boundedWitnessGuardSourcePayloadPolynomial
  omega

theorem boundedWitnessGuardPayloadPolynomial_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    boundedWitnessGuardPayloadPolynomial small <=
      boundedWitnessGuardPayloadPolynomial large := by
  have hsource :=
    boundedWitnessGuardSourcePayloadPolynomial_mono_uniform hbound
  have hmultiplication := paMultiplicationLocalCostEnvelope_mono_uniform hbound
  have hterm := boundedWitnessGuardTermCodeEnvelope_mono_uniform hbound
  have hprimitive := paPrimitiveCostEnvelope_mono_local hterm
  have horder := orderPrimitiveCostEnvelope_mono_uniform hterm
  unfold boundedWitnessGuardPayloadPolynomial
  omega

theorem smallContextAssemblyEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    smallContextAssemblyEnvelope small <=
      smallContextAssemblyEnvelope large := by
  unfold smallContextAssemblyEnvelope smallSequentCodeEnvelope
  omega

theorem generalContextCoordinate_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    generalContextCoordinate small <= generalContextCoordinate large := by
  unfold generalContextCoordinate
  omega

theorem generalSequentCodeEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    generalSequentCodeEnvelope small <= generalSequentCodeEnvelope large := by
  have hcoordinate := generalContextCoordinate_mono_uniform hbound
  have hheader := binaryNatCode_length_mono hcoordinate
  unfold generalSequentCodeEnvelope
  exact Nat.add_le_add hheader (Nat.mul_le_mul hcoordinate hcoordinate)

theorem generalContextAssemblyEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    generalContextAssemblyEnvelope small <=
      generalContextAssemblyEnvelope large := by
  have hsequent := generalSequentCodeEnvelope_mono_uniform hbound
  have hcoordinate := generalContextCoordinate_mono_uniform hbound
  unfold generalContextAssemblyEnvelope
  omega

def boundedWitnessGuardUniformBitWidth (bound : Nat) : Nat :=
  boundedWitnessGuardBitWidth bound bound

theorem boundedWitnessGuardBitWidth_le_uniform
    (value bound : Nat) (hvalue : value <= bound) :
    boundedWitnessGuardBitWidth value bound <=
      boundedWitnessGuardUniformBitWidth bound := by
  have hsize := Nat.size_le_size hvalue
  unfold boundedWitnessGuardUniformBitWidth boundedWitnessGuardBitWidth
  omega

theorem explicitBoundedWitnessDirectHeadSmallContexts_of_bodyContext
    (valuation : Nat -> Nat) {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hbodyCard :
      (valuationContext body.freeVariables valuation).card <= 4) :
    ExplicitBoundedWitnessDirectHeadSmallContexts
      valuation bound body values := by
  constructor
  · have hsubset :
        valuationContext
            (boundedWitnessGuardFormula (values 0) bound).freeVariables
            valuation ⊆
          valuationContext body.freeVariables valuation :=
      valuationContext_mono valuation (by
        rw [boundedWitnessGuardFormula_freeVariables_eq_empty]
        exact Finset.empty_subset _)
    exact (Finset.card_le_card hsubset).trans hbodyCard
  · have hsubset :
        valuationContext
            ((boundedWitnessGuardFormula (values 0) bound) ⋏
              ((explicitWitnessBodyAfterTail body values)/[
                shortBinaryNumeralTerm (values 0)])).freeVariables valuation ⊆
          valuationContext body.freeVariables valuation :=
      valuationContext_mono valuation
        (explicitBoundedWitnessMatrix_freeVariables_subset bound body values)
    exact (Finset.card_le_card hsubset).trans hbodyCard
  · have hsubset :
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
    exact (Finset.card_le_card hsubset).trans hbodyCard

def explicitBoundedWitnessDirectHeadUniformPayloadPolynomial
    (valuation : Nat -> Nat) {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) : Nat :=
  boundedWitnessGuardPayloadPolynomial
      (boundedWitnessGuardUniformBitWidth bound) +
    6 * generalContextAssemblyEnvelope
      (explicitBoundedWitnessDirectHeadUniformSyntaxResource
        valuation bound body)

theorem explicitBoundedWitnessDirectHeadPayloadEnvelope_le_uniform
    (valuation : Nat -> Nat) {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    (hvalues : forall index, values index <= bound) :
    explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound body values <=
      explicitBoundedWitnessDirectHeadUniformPayloadPolynomial
        valuation bound body := by
  have hexact :=
    explicitBoundedWitnessDirectHeadPayloadEnvelope_le_general
      valuation bound body values
  have hbit := boundedWitnessGuardBitWidth_le_uniform
    (values 0) bound (hvalues 0)
  have hguard := boundedWitnessGuardPayloadPolynomial_mono_uniform hbit
  have hsyntax := explicitBoundedWitnessDirectHeadSyntaxResource_le_uniform
    valuation bound body values hvalues
  have hcontext := generalContextAssemblyEnvelope_mono_uniform hsyntax
  apply hexact.trans
  unfold explicitBoundedWitnessDirectHeadGeneralPayloadPolynomial
  unfold explicitBoundedWitnessDirectHeadUniformPayloadPolynomial
  omega

/-! ## Complete fixed-arity witness vectors -/

theorem closedShift_shortBinaryNumeralTerm_freeVariables_eq_empty
    (bound : Nat) :
    forall arity,
      (closedShift arity
        (shortBinaryNumeralTerm bound)).freeVariables = ∅
  | 0 => shortBinaryNumeralTerm_freeVariables_eq_empty bound
  | arity + 1 => by
      change
        (Rew.bShift
          (closedShift arity
            (shortBinaryNumeralTerm bound))).freeVariables = ∅
      exact bShift_freeVariables_eq_empty_of_empty _
        (closedShift_shortBinaryNumeralTerm_freeVariables_eq_empty
          bound arity)

theorem explicitBoundedWitnessRecursiveBody_freeVariables_subset
    {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1)) :
    (body.bexsLTSucc
      (closedShift arity
        (shortBinaryNumeralTerm bound))).freeVariables ⊆
      body.freeVariables := by
  let boundTerm : ArithmeticSemiterm Nat arity :=
    closedShift arity (shortBinaryNumeralTerm bound)
  have hboundTerm : boundTerm.freeVariables = ∅ := by
    exact closedShift_shortBinaryNumeralTerm_freeVariables_eq_empty
      bound arity
  have hsuccessor :
      (‘!!boundTerm + 1’ :
        ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables_eq_union, hboundTerm]
    have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
      simp [Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
        Semiterm.Operator.One.term_eq]
    rw [hone]
    simp
  have hshiftedSuccessor :
      (Rew.bShift
        (‘!!boundTerm + 1’ :
          ArithmeticSemiterm Nat arity)).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty _ hsuccessor
  have hguard :
      (Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat (arity + 1)),
          Rew.bShift
            (‘!!boundTerm + 1’ :
              ArithmeticSemiterm Nat arity)]).freeVariables = ∅ := by
    rw [lessThanSemiformula_freeVariables_eq_union,
      hshiftedSuccessor]
    simp
  intro index hindex
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT at hindex
  rw [Semiformula.bexs_eq] at hindex
  rw [Semiformula.freeVariables_exs,
    Semiformula.freeVariables_and] at hindex
  rcases Finset.mem_union.mp hindex with hguardIndex | hbodyIndex
  · dsimp only [boundTerm] at hguard
    rw [hguard] at hguardIndex
    simp at hguardIndex
  · exact hbodyIndex

/-- Recursive public resource for a complete bounded-witness vector.  It has
the same fixed arity recursion as the real compiler, but no concrete witness
value occurs in the coordinate. -/
def explicitBoundedWitnessDirectUniformPayloadEnvelope :
    {arity : Nat} ->
    (valuation : Nat -> Nat) ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat arity) ->
    (terminalResource : Nat) -> Nat
  | 0, _, _, _, terminalResource => terminalResource
  | arity + 1, valuation, bound, body, terminalResource =>
      explicitBoundedWitnessDirectUniformPayloadEnvelope valuation bound
        (body.bexsLTSucc
          (closedShift arity (shortBinaryNumeralTerm bound)))
        (terminalResource +
          explicitBoundedWitnessDirectHeadUniformPayloadPolynomial
            valuation bound body)

#print axioms RewritingImageCodeBound.q
#print axioms binaryTermCode_rewriting_length_le_envelope
#print axioms binaryFormulaCode_rewriting_length_le_envelope
#print axioms shortBinaryNumeralTerm_code_length_le_bound
#print axioms explicitWitnessBodyAfterTail_code_length_le_uniform
#print axioms boundedWitnessSuccessorTerm_code_length_le
#print axioms boundedWitnessShiftedSuccessorTerm_code_length_le
#print axioms lessThanSemiformula_code_length_le
#print axioms boundedWitnessGuardFormula_code_length_le
#print axioms boundedWitnessOpenGuardFormula_code_length_le
#print axioms andSemiformula_code_length_le
#print axioms explicitWitnessInstalledFormula_code_length_le_uniform
#print axioms explicitBoundedWitnessMatrixFormula_code_length_le_uniform
#print axioms explicitBoundedWitnessBoundedMatrixFormula_code_length_le_uniform
#print axioms explicitBoundedWitnessInstantiatedFormula_code_length_le_uniform
#print axioms explicitBoundedWitnessExistentialFormula_code_length_le_uniform
#print axioms explicitWitnessInstalledFormula_freeVariables_subset
#print axioms explicitWitnessBodyAfterTail_freeVariables_subset
#print axioms arithmeticAddTerm_freeVariables_eq_union
#print axioms lessThanSemiformula_freeVariables_eq_union
#print axioms boundedWitnessSuccessorTerm_freeVariables_eq_empty
#print axioms boundedWitnessGuardFormula_freeVariables_eq_empty
#print axioms boundedWitnessOpenGuardFormula_freeVariables_eq_empty
#print axioms explicitBoundedWitnessMatrix_freeVariables_subset
#print axioms explicitBoundedWitnessBoundedMatrix_freeVariables_subset
#print axioms explicitBoundedWitnessExistential_freeVariables_subset
#print axioms formulaCodeSum_mono
#print axioms explicitBoundedWitnessDirectHeadSyntaxResource_le_uniform
#print axioms compilerLocalCostEnvelope_mono_uniform
#print axioms orderPrimitiveCostEnvelope_mono_uniform
#print axioms orderStepCostEnvelope_mono_uniform
#print axioms positiveBinaryNumeralPayloadPolynomial_mono_uniform
#print axioms boundedWitnessGuardPayloadPolynomial_mono_uniform
#print axioms smallContextAssemblyEnvelope_mono_uniform
#print axioms boundedWitnessGuardBitWidth_le_uniform
#print axioms
  explicitBoundedWitnessDirectHeadSmallContexts_of_bodyContext
#print axioms explicitBoundedWitnessDirectHeadPayloadEnvelope_le_uniform
#print axioms
  closedShift_shortBinaryNumeralTerm_freeVariables_eq_empty
#print axioms explicitBoundedWitnessRecursiveBody_freeVariables_subset
#print axioms explicitBoundedWitnessDirectUniformPayloadEnvelope

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
