import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectGraph

/-!
# Complete adjacent-row graph at the exact parser fuel term

The original eight-argument adjacent-row graph is instantiated with the
composite parser fuel term itself.  Its exponential and bounded-universal
children are compiled independently and joined by a checked PA conjunction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal

def compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentRowsBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      compactParserSyntaxExactFuelTerm inputCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactParserSyntaxAdjacentRowsBoundedExactFuelExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound : Nat) : ValuationFormula :=
  compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
      tableWidth valueBound ⋏
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound).ballLT
        (compactParserSyntaxExactFuelTerm inputCount)

private theorem rewriting_ballLT_exactFuel
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have rewriting_formulaOperator
      {operatorArity : Nat}
      (operator : Semiformula.Operator ℒₒᵣ operatorArity)
      (terms : Fin operatorArity ->
        ArithmeticSemiterm sourceVariables (sourceArity + 1)) :
      rewriting.q ▹ operator.operator terms =
        operator.operator (rewriting.q ∘ terms) := by
    unfold Semiformula.Operator.operator
    exact
      FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution
        rewriting.q operator.sentence terms
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)),
            Rew.bShift bound] =
        ![(#0 : ArithmeticSemiterm targetVariables (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold Semiformula.ballLT
  rw [Rewriting.smul_ball,
    rewriting_formulaOperator,
    hguardTerms]

theorem compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound : Nat) :
    compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound =
      compactParserSyntaxAdjacentRowsBoundedExactFuelExplicitFormula tokenTable
        width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound := by
  unfold compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula
  unfold compactParserSyntaxAdjacentRowsBoundedExactFuelExplicitFormula
  unfold compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
  unfold compactParserSyntaxAdjacentRowsBoundedUniversalBody
  unfold compactParserSyntaxAdjacentRowsBoundedGraphDef
  simp [rewriting_ballLT_exactFuel, ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

def compactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedResource
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat) : Nat :=
  let exponentialFormula :=
    compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula tableWidth
      valueBound
  let universalFormula :=
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound).ballLT
        (compactParserSyntaxExactFuelTerm inputCount)
  compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource tableWidth
      valueBound +
    compactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalResource
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
        numericBound bitBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ exponentialFormula
      universalFormula

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth valueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueNumeric : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CertifiedPAContextProof ∅
      (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound) := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputCount
        tableWidth valueBound).symm
    raw

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth valueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueNumeric : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound hgraph hfuel hvalueNumeric hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hnumericSize hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedResource
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound numericBound bitBound := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource
        tableWidth valueBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalResource
        tokenTable width tokenCount stateBoundary stateCount inputCount
          valueBound numericBound bitBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  exact hraw.trans (by
    unfold
      compactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedResource
    dsimp only
    omega)

#print axioms
  compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula_alignment
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
