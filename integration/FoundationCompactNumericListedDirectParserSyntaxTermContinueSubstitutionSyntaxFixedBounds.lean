import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds

/-!
# Graph-independent syntax bound for the syntax-term continue formula

The complete twenty-two-coordinate formula is bounded directly as a finite
substitution.  The final coordinate is the fixed numeral `consumed = 1`;
no continue-row graph is required.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermContinueSubstitutionSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

def syntaxTermContinueSubstitutionFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound +
      (binaryTermCode (fixedNumeralTerm 1)).length)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxTermContinueRowsDef.val)).length

theorem
    syntaxTermContinueFixedOneClosedFormula_code_length_le_substitutionFixed
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
    (htailCountSize : Nat.size tailCount <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next tailBoundary tailCount 1)).length <=
      syntaxTermContinueSubstitutionFormulaCodePolynomial bitBound := by
  let values :=
    compactUnifiedParserSyntaxTermContinueEnvironment tokenTable width
      tokenCount current next tailBoundary tailCount 1
  have hsizes : ∀ coordinate, Nat.size (values coordinate) <= bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableSize
    · exact hwidthSize
    · exact htokenCountSize
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (0 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (1 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (2 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (3 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (4 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (5 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (6 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hcurrentSize (7 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (0 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (1 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (2 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (3 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (4 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (5 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (6 : Fin 8)
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment,
        compactUnifiedParserStateCoordinateValues] using hnextSize (7 : Fin 8)
    · exact htailBoundarySize
    · exact htailCountSize
    · simpa [values, compactUnifiedParserSyntaxTermContinueEnvironment] using
        hbitPositive
  let terms : Fin 22 -> ValuationTerm :=
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
          fixedNumeralTerm 1]
  let imageBound :=
    binaryNumeralTermCodeEnvelope bitBound +
      (binaryTermCode (fixedNumeralTerm 1)).length
  let rewriting : Rew ℒₒᵣ Nat 22 Nat 0 := Rew.subst terms
  have hrewriting : RewritingImageCodeBound rewriting imageBound := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      by_cases hlast : coordinate = (21 : Fin 22)
      · subst coordinate
        dsimp only [terms, imageBound]
        exact Nat.le_add_left _ _
      · have hterm :
            terms coordinate =
              shortBinaryNumeralTerm (values coordinate) := by
          fin_cases coordinate <;>
            simp [terms, values,
              compactUnifiedParserSyntaxTermContinueEnvironment] at hlast ⊢
        rw [hterm]
        exact
          (binaryNumeralTerm_code_length_le_envelope
            (values coordinate) bitBound (hsizes coordinate)).trans
            (Nat.le_add_right _ _)
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    imageBound hrewriting
    (Rewriting.emb (ξ := Nat)
      compactUnifiedParserSyntaxTermContinueRowsDef.val)
  unfold compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
    syntaxTermContinueSubstitutionFormulaCodePolynomial
  simpa only [rewriting, terms, imageBound] using hraw

#print axioms
  syntaxTermContinueFixedOneClosedFormula_code_length_le_substitutionFixed

end FoundationCompactNumericListedDirectParserSyntaxTermContinueSubstitutionSyntaxFixedBounds
