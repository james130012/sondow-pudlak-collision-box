import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds

/-!
# Fixed syntax bound for the syntax-term function formula

The original formula has twenty-three numeric coordinates.  Treating the
closed instance as one finite rewriting gives a code bound from the common bit
coordinate alone; no proof resource for the represented graph is used here.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate

def syntaxTermFunctionClosedFormulaCodePolynomial (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxTermFunctionRowsDef.val)).length

theorem syntaxTermFunctionClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (htailCountSize : Nat.size tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hfunctionAritySize : Nat.size functionArity <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
        tokenTable width tokenCount current next tailBoundary tailCount
        binderArity functionArity)).length <=
      syntaxTermFunctionClosedFormulaCodePolynomial bitBound := by
  let values :=
    compactUnifiedParserSyntaxTermFunctionEnvironment tokenTable width
      tokenCount current next tailBoundary tailCount binderArity functionArity
  have hsizes : ∀ coordinate, Nat.size (values coordinate) <= bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableSize
    · exact hwidthSize
    · exact htokenCountSize
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (0 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (1 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (2 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (3 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (4 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (5 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (6 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (7 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (0 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (1 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (2 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (3 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (4 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (5 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (6 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermFunctionEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (7 : Fin 8)
    · exact htailBoundarySize
    · exact htailCountSize
    · exact hbinderAritySize
    · exact hfunctionAritySize
  have hraw := shortNumeralRewritingFormula_code_length_le_uniform
    compactUnifiedParserSyntaxTermFunctionRowsDef.val values bitBound hsizes
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
          shortBinaryNumeralTerm tailCount,
          shortBinaryNumeralTerm binderArity,
          shortBinaryNumeralTerm functionArity] := by
    funext coordinate
    fin_cases coordinate <;>
      rfl
  unfold compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
    syntaxTermFunctionClosedFormulaCodePolynomial
  rw [← hterms]
  exact hraw

theorem syntaxTermFunctionClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) :
    (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity functionArity).freeVariables = ∅ := by
  unfold compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms syntaxTermFunctionClosedFormula_code_length_le_fixed
#print axioms syntaxTermFunctionClosedFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds
