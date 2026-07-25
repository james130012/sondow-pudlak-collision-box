import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds

/-!
# Graph-independent syntax bounds for binary and quantifier parser formulas

Both genuine closed formulas are substitutions of a fixed twenty-two-variable
template by short binary numerals.  Their code lengths therefore depend only
on the shared bit coordinate, not on either represented parser graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaTaskSubstitutionSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate

private theorem parserFormulaTaskEnvironment_sizes
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (htailCountSize : Nat.size tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound) :
    ∀ coordinate,
      Nat.size
          (compactUnifiedParserSyntaxFormulaBinaryEnvironment tokenTable width
            tokenCount current next tailBoundary tailCount binderArity
            coordinate) <= bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact htokenTableSize
  · exact hwidthSize
  · exact htokenCountSize
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrentSize (7 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnextSize (7 : Fin 8)
  · exact htailBoundarySize
  · exact htailCountSize
  · exact hbinderAritySize

def syntaxFormulaBinarySubstitutionFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxFormulaBinaryRowsDef.val)).length

theorem syntaxFormulaBinaryClosedFormula_code_length_le_substitutionFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (htailCountSize : Nat.size tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width
        tokenCount current next tailBoundary tailCount binderArity)).length <=
      syntaxFormulaBinarySubstitutionFormulaCodePolynomial bitBound := by
  let values :=
    compactUnifiedParserSyntaxFormulaBinaryEnvironment tokenTable width
      tokenCount current next tailBoundary tailCount binderArity
  have hsizes := parserFormulaTaskEnvironment_sizes tokenTable width tokenCount
    current next tailBoundary tailCount binderArity bitBound htokenTableSize
    hwidthSize htokenCountSize hcurrentSize hnextSize htailBoundarySize
    htailCountSize hbinderAritySize
  have hraw := shortNumeralRewritingFormula_code_length_le_uniform
    compactUnifiedParserSyntaxFormulaBinaryRowsDef.val values bitBound hsizes
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
          shortBinaryNumeralTerm binderArity] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  unfold compactUnifiedParserSyntaxFormulaBinaryClosedFormula
    syntaxFormulaBinarySubstitutionFormulaCodePolynomial
  rw [← hterms]
  exact hraw

def syntaxFormulaQuantifierSubstitutionFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxFormulaQuantifierRowsDef.val)).length

theorem syntaxFormulaQuantifierClosedFormula_code_length_le_substitutionFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (htailCountSize : Nat.size tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable
        width tokenCount current next tailBoundary tailCount binderArity)).length <=
      syntaxFormulaQuantifierSubstitutionFormulaCodePolynomial bitBound := by
  let values :=
    compactUnifiedParserSyntaxFormulaQuantifierEnvironment tokenTable width
      tokenCount current next tailBoundary tailCount binderArity
  have hsizes :
      ∀ coordinate, Nat.size (values coordinate) <= bitBound := by
    simpa only [values, compactUnifiedParserSyntaxFormulaQuantifierEnvironment,
      compactUnifiedParserSyntaxFormulaBinaryEnvironment] using
      (parserFormulaTaskEnvironment_sizes tokenTable width tokenCount current
        next tailBoundary tailCount binderArity bitBound htokenTableSize
        hwidthSize htokenCountSize hcurrentSize hnextSize htailBoundarySize
        htailCountSize hbinderAritySize)
  have hraw := shortNumeralRewritingFormula_code_length_le_uniform
    compactUnifiedParserSyntaxFormulaQuantifierRowsDef.val values bitBound
      hsizes
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
          shortBinaryNumeralTerm binderArity] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  unfold compactUnifiedParserSyntaxFormulaQuantifierClosedFormula
    syntaxFormulaQuantifierSubstitutionFormulaCodePolynomial
  rw [← hterms]
  exact hraw

#print axioms syntaxFormulaBinaryClosedFormula_code_length_le_substitutionFixed
#print axioms
  syntaxFormulaQuantifierClosedFormula_code_length_le_substitutionFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaTaskSubstitutionSyntaxFixedBounds
