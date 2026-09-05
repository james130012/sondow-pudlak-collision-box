import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate

/-! # Direct closed syntax for the 28-coordinate total transform endpoint -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointDirectSyntax

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint

def compactFormulaTransformTotalExactBoundedGraphClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount inputBoundary inputCount outputBoundary
      outputCount emptyBoundary binderArity tableWidth valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformTotalExactBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm mode,
      shortBinaryNumeralTerm witnessStart,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm witnessCount,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      shortBinaryNumeralTerm outputBoundary,
      shortBinaryNumeralTerm outputCount,
      shortBinaryNumeralTerm emptyBoundary,
      shortBinaryNumeralTerm binderArity,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactFormulaTransformTotalExactEndpointDirectClosedFormula
    (tokenTable width tokenCount mode binderArity witnessStart witnessFinish
      witnessBoundary witnessCount witnessBoundarySize inputStart inputFinish
      inputBoundary inputCount inputBoundarySize outputStart outputFinish
      outputBoundary outputCount outputBoundarySize emptyStart emptyFinish
      emptyBoundary emptyBoundarySize stateBoundary stateCount tableWidth
      valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformTotalExactEndpointDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm mode,
      shortBinaryNumeralTerm binderArity,
      shortBinaryNumeralTerm witnessStart,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm witnessBoundary,
      shortBinaryNumeralTerm witnessCount,
      shortBinaryNumeralTerm witnessBoundarySize,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      shortBinaryNumeralTerm inputBoundarySize,
      shortBinaryNumeralTerm outputStart,
      shortBinaryNumeralTerm outputFinish,
      shortBinaryNumeralTerm outputBoundary,
      shortBinaryNumeralTerm outputCount,
      shortBinaryNumeralTerm outputBoundarySize,
      shortBinaryNumeralTerm emptyStart,
      shortBinaryNumeralTerm emptyFinish,
      shortBinaryNumeralTerm emptyBoundary,
      shortBinaryNumeralTerm emptyBoundarySize,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactFormulaTransformTotalExactEndpointDirectExplicitFormula
    (tokenTable width tokenCount mode binderArity witnessStart witnessFinish
      witnessBoundary witnessCount witnessBoundarySize inputStart inputFinish
      inputBoundary inputCount inputBoundarySize outputStart outputFinish
      outputBoundary outputCount outputBoundarySize emptyStart emptyFinish
      emptyBoundary emptyBoundarySize stateBoundary stateCount tableWidth
      valueBound : Nat) : ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      witnessStart witnessCount witnessFinish witnessBoundary
      witnessBoundarySize ⋏
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        inputStart inputCount inputFinish inputBoundary inputBoundarySize ⋏
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
          tokenCount outputStart outputCount outputFinish outputBoundary
          outputBoundarySize ⋏
        (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
            tokenCount emptyStart 0 emptyFinish emptyBoundary
            emptyBoundarySize ⋏
          compactFormulaTransformTotalExactBoundedGraphClosedFormula tokenTable
            width tokenCount stateBoundary stateCount mode witnessStart
            witnessFinish witnessCount inputBoundary inputCount outputBoundary
            outputCount emptyBoundary binderArity tableWidth valueBound)))

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

theorem compactFormulaTransformTotalExactEndpointDirectClosedFormula_alignment
    (tokenTable width tokenCount mode binderArity witnessStart witnessFinish
      witnessBoundary witnessCount witnessBoundarySize inputStart inputFinish
      inputBoundary inputCount inputBoundarySize outputStart outputFinish
      outputBoundary outputCount outputBoundarySize emptyStart emptyFinish
      emptyBoundary emptyBoundarySize stateBoundary stateCount tableWidth
      valueBound : Nat) :
    compactFormulaTransformTotalExactEndpointDirectClosedFormula tokenTable
        width tokenCount mode binderArity witnessStart witnessFinish
        witnessBoundary witnessCount witnessBoundarySize inputStart inputFinish
        inputBoundary inputCount inputBoundarySize outputStart outputFinish
        outputBoundary outputCount outputBoundarySize emptyStart emptyFinish
        emptyBoundary emptyBoundarySize stateBoundary stateCount tableWidth
        valueBound =
      compactFormulaTransformTotalExactEndpointDirectExplicitFormula tokenTable
        width tokenCount mode binderArity witnessStart witnessFinish
        witnessBoundary witnessCount witnessBoundarySize inputStart inputFinish
        inputBoundary inputCount inputBoundarySize outputStart outputFinish
        outputBoundary outputCount outputBoundarySize emptyStart emptyFinish
        emptyBoundary emptyBoundarySize stateBoundary stateCount tableWidth
        valueBound := by
  unfold compactFormulaTransformTotalExactEndpointDirectClosedFormula
    compactFormulaTransformTotalExactEndpointDirectExplicitFormula
    compactFormulaTransformTotalExactEndpointDef
    compactAdditiveNatListWitnessRowsClosedFormula
    compactFormulaTransformTotalExactBoundedGraphClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm,
          Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
          Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate

#print axioms
  compactFormulaTransformTotalExactEndpointDirectClosedFormula_alignment

end FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointDirectSyntax
