import integration.FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Graph-free fixed syntax bound for the original 26-coordinate SyntaxStep formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

namespace FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate

def compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxStepRowsDef.val)).length

theorem compactUnifiedParserSyntaxStepClosedFormula_environment_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
        current next witness =
      (Rew.subst (fun coordinate =>
        shortBinaryNumeralTerm
          (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
            tokenCount current next witness coordinate))) ▹
        (Rewriting.emb (ξ := Nat)
          compactUnifiedParserSyntaxStepRowsDef.val) := by
  unfold compactUnifiedParserSyntaxStepClosedFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [compactUnifiedParserSyntaxStepFormulaEnvironment]

theorem compactUnifiedParserSyntaxStepClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (bitBound : Nat)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
        current next witness)).length <=
      compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound := by
  let environment :=
    compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width tokenCount
      current next witness
  let rewriting : Rew ℒₒᵣ Nat 26 Nat 0 :=
    Rew.subst (fun coordinate =>
      shortBinaryNumeralTerm (environment coordinate))
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro coordinate
      rw [show rewriting (#coordinate : ArithmeticSemiterm Nat 26) =
          shortBinaryNumeralTerm (environment coordinate) by
        simp [rewriting]]
      exact binaryNumeralTerm_code_length_le_envelope
        (environment coordinate) bitBound (by
          simpa only [environment] using hsize coordinate)
    · intro coordinate
      simp [rewriting]
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxStepRowsDef.val)
  unfold compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial
  rw [compactUnifiedParserSyntaxStepClosedFormula_environment_alignment
    tokenTable width tokenCount current next witness]
  simpa only [rewriting, environment] using hraw

theorem compactUnifiedParserSyntaxStepExplicitFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (bitBound : Nat)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)).length <=
      compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound := by
  rw [← compactUnifiedParserSyntaxStepClosedFormula_alignment tokenTable width
    tokenCount current next witness]
  exact compactUnifiedParserSyntaxStepClosedFormula_code_length_le_fixed
    tokenTable width tokenCount current next witness bitBound hsize

theorem compactUnifiedParserSyntaxStepClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
      current next witness).freeVariables = ∅ := by
  unfold compactUnifiedParserSyntaxStepClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem compactUnifiedParserSyntaxStepExplicitFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
      current next witness).freeVariables = ∅ := by
  rw [← compactUnifiedParserSyntaxStepClosedFormula_alignment tokenTable width
    tokenCount current next witness]
  exact compactUnifiedParserSyntaxStepClosedFormula_freeVariables_eq_empty
    tokenTable width tokenCount current next witness

end FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
