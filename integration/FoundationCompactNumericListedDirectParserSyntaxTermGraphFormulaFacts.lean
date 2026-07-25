import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds

/-! # Closedness and code bounds for the complete syntax-term graph formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphFormulaFacts

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds

theorem compactUnifiedParserSyntaxTermExplicitFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    (compactUnifiedParserSyntaxTermExplicitFormula tokenTable width tokenCount
      current next binderArity witness).freeVariables = ∅ := by
  have hclosed :
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current next binderArity witness).freeVariables = ∅ := by
    unfold compactUnifiedParserSyntaxTermClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  rw [compactUnifiedParserSyntaxTermClosedFormula_alignment] at hclosed
  exact hclosed

theorem compactUnifiedParserSyntaxTermExplicitFormula_code_length_le_graph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (bitBound : Nat)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxTermExplicitFormula tokenTable width tokenCount
        current next binderArity witness)).length <=
      compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound :=
  compactUnifiedParserSyntaxTermExplicitFormula_code_length_le_fixed tokenTable
    width tokenCount current next binderArity witness bitBound hsize

end FoundationCompactNumericListedDirectParserSyntaxTermGraphFormulaFacts
