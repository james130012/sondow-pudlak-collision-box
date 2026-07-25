import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds

/-!
# Graph-independent syntax bound for the syntax-term failure formula

The twenty-one-coordinate closed formula is bounded directly as one finite
substitution.  Its syntax cost therefore does not require the represented
failure graph to hold.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerUniformMonotoneBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate

def syntaxTermFailureSubstitutionFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxTermFailureRowsDef.val)).length

theorem syntaxTermFailureClosedFormula_code_length_le_substitutionFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (htailCountSize : Nat.size tailCount <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next tailBoundary tailCount)).length <=
      syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound := by
  let values :=
    compactUnifiedParserSyntaxTermFailureEnvironment tokenTable width
      tokenCount current next tailBoundary tailCount
  have hsizes : ∀ coordinate, Nat.size (values coordinate) <= bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableSize
    · exact hwidthSize
    · exact htokenCountSize
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (0 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (1 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (2 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (3 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (4 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (5 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (6 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (7 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (0 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (1 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (2 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (3 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (4 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (5 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (6 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFailureEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (7 : Fin 8)
    · exact htailBoundarySize
    · exact htailCountSize
  have hraw := shortNumeralRewritingFormula_code_length_le_uniform
    compactUnifiedParserSyntaxTermFailureRowsDef.val values bitBound hsizes
  have hterms :
      (fun coordinate => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm current.start,
          shortBinaryNumeralTerm current.finish,
          shortBinaryNumeralTerm current.tokensFinish,
          shortBinaryNumeralTerm current.tasksFinish,
          shortBinaryNumeralTerm current.tokensBoundary,
          shortBinaryNumeralTerm current.tokensCount,
          shortBinaryNumeralTerm current.tasksBoundary,
          shortBinaryNumeralTerm current.tasksCount,
          shortBinaryNumeralTerm next.start,
          shortBinaryNumeralTerm next.finish,
          shortBinaryNumeralTerm next.tokensFinish,
          shortBinaryNumeralTerm next.tasksFinish,
          shortBinaryNumeralTerm next.tokensBoundary,
          shortBinaryNumeralTerm next.tokensCount,
          shortBinaryNumeralTerm next.tasksBoundary,
          shortBinaryNumeralTerm next.tasksCount,
          shortBinaryNumeralTerm tailBoundary,
          shortBinaryNumeralTerm tailCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  unfold compactUnifiedParserSyntaxTermFailureClosedFormula
    syntaxTermFailureSubstitutionFormulaCodePolynomial
  rw [← hterms]
  exact hraw

theorem
    syntaxTermFailureClosedFormula_freeVariables_eq_empty_substitutionFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) :
    (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next tailBoundary tailCount).freeVariables = ∅ := by
  unfold compactUnifiedParserSyntaxTermFailureClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  syntaxTermFailureClosedFormula_code_length_le_substitutionFixed
#print axioms
  syntaxTermFailureClosedFormula_freeVariables_eq_empty_substitutionFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
