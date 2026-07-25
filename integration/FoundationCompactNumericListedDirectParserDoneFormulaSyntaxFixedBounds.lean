import integration.FoundationCompactNumericListedDirectParserDoneFormulaEnvironmentAlignment
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

/-! # Graph-free fixed syntax bound for the original 26-coordinate Done formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneFormulaEnvironmentAlignment

def compactUnifiedParserDoneFormulaSyntaxFixedPolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactUnifiedParserDoneGraphRowsDef.val)).length

def compactUnifiedParserDoneWitnessCoordinateValues
    (witness : CompactUnifiedParserDoneWitnessCoordinates) : Fin 7 -> Nat :=
  ![witness.sourceOutputStart, witness.sourceOutputBoundary,
    witness.sourceOutputBoundarySize, witness.targetOutputStart,
    witness.targetOutputBoundary, witness.targetOutputBoundarySize,
    witness.outputCount]

def CompactUnifiedParserDoneWitnessCoordinateSizeBound
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (bitBound : Nat) : Prop :=
  forall coordinate,
    Nat.size (compactUnifiedParserDoneWitnessCoordinateValues witness
      coordinate) <= bitBound

theorem compactUnifiedParserDoneFormulaEnvironmentOf_size_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hcurrent :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnext :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hwitness :
      CompactUnifiedParserDoneWitnessCoordinateSizeBound witness bitBound) :
    ∀ coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserDoneFormulaEnvironmentOf tokenTable width
          tokenCount current next witness coordinate) <= bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact htokenTable
  · exact hwidth
  · exact htokenCount
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (0 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (1 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (2 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (3 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (4 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (5 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (6 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hcurrent (7 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (0 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (1 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (2 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (3 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (4 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (5 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (6 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using
      hnext (7 : Fin 8)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserDoneWitnessCoordinateValues] using
      hwitness (0 : Fin 7)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserDoneWitnessCoordinateValues] using
      hwitness (1 : Fin 7)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserDoneWitnessCoordinateValues] using
      hwitness (2 : Fin 7)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserDoneWitnessCoordinateValues] using
      hwitness (3 : Fin 7)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserDoneWitnessCoordinateValues] using
      hwitness (4 : Fin 7)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserDoneWitnessCoordinateValues] using
      hwitness (5 : Fin 7)
  · simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment,
      compactUnifiedParserDoneWitnessCoordinateValues] using
      hwitness (6 : Fin 7)

theorem compactUnifiedParserDoneClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (bitBound : Nat)
    (hsize : ∀ coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserDoneFormulaEnvironmentOf tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
        current next witness)).length <=
      compactUnifiedParserDoneFormulaSyntaxFixedPolynomial bitBound := by
  let environment := compactUnifiedParserDoneFormulaEnvironmentOf tokenTable
    width tokenCount current next witness
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
    (Rewriting.emb (ξ := Nat) compactUnifiedParserDoneGraphRowsDef.val)
  unfold compactUnifiedParserDoneFormulaSyntaxFixedPolynomial
  rw [compactUnifiedParserDoneClosedFormula_environment_alignment tokenTable
    width tokenCount current next witness]
  simpa only [rewriting, environment] using hraw

theorem compactUnifiedParserDoneExplicitFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (bitBound : Nat)
    (hsize : ∀ coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserDoneFormulaEnvironmentOf tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserDoneExplicitFormula tokenTable width tokenCount
        current next witness)).length <=
      compactUnifiedParserDoneFormulaSyntaxFixedPolynomial bitBound := by
  rw [← compactUnifiedParserDoneClosedFormula_alignment tokenTable width
    tokenCount current next witness]
  exact compactUnifiedParserDoneClosedFormula_code_length_le_fixed tokenTable
    width tokenCount current next witness bitBound hsize

end FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
