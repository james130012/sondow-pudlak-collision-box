import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFormulaFixedBounds

/-! # Common complete syntax budget for every term-output-row branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFormulaFixedBounds

def termRowsOuterSyntaxPolynomial (bitBound : Nat) : Nat :=
  compactFormulaTransformTermOutputRowsFullFormulaCodePolynomial bitBound + 1

theorem termRowsOuterSyntaxPolynomial_positive (bitBound : Nat) :
    1 <= termRowsOuterSyntaxPolynomial bitBound := by
  unfold termRowsOuterSyntaxPolynomial
  omega

theorem compactFormulaTransformTermOutputRowsExplicitFormula_code_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount bitBound : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount)).length <=
      termRowsOuterSyntaxPolynomial bitBound := by
  have hraw :=
    compactFormulaTransformTermOutputRowsClosedFormula_code_length_le_fixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount bitBound witnessStart witnessFinish witnessCount
      henvironmentSize
  rw [compactFormulaTransformTermOutputRowsClosedFormula_alignment] at hraw
  unfold termRowsOuterSyntaxPolynomial
  omega

theorem compactFormulaTransformTermOutputRowsExplicitFormula_closed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    (compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
      tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount).freeVariables = ∅ := by
  rw [← compactFormulaTransformTermOutputRowsClosedFormula_alignment]
  exact compactFormulaTransformTermOutputRowsClosedFormula_closed tokenTable
    width tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount

theorem termRowsConjunction_left_closed
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

theorem termRowsConjunction_right_closed
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

theorem termRowsDisjunction_left_closed
    (left right : ValuationFormula)
    (hclosed : (left ⋎ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

theorem termRowsDisjunction_right_closed
    (left right : ValuationFormula)
    (hclosed : (left ⋎ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

theorem termRowsConjunction_left_code_le
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem termRowsConjunction_right_code_le
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem termRowsDisjunction_left_code_le
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem termRowsDisjunction_right_code_le
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp [binaryFormulaCode]
  omega

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
