import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaEnvironmentAlignment
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

/-! # Graph-free fixed syntax bound for the original 25-coordinate Repeat formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaEnvironmentAlignment

def compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxRepeatRowsDef.val)).length

def compactUnifiedParserSyntaxRepeatWitnessCoordinateValues
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : Fin 4 -> Nat :=
  ![witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
    witness.decrementedCount]

def CompactUnifiedParserSyntaxRepeatWitnessCoordinateSizeBound
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (bitBound : Nat) : Prop :=
  forall coordinate,
    Nat.size
      (compactUnifiedParserSyntaxRepeatWitnessCoordinateValues witness
        coordinate) <= bitBound

theorem compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf_size_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hcurrent :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnext :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hbinderArity : Nat.size binderArity <= bitBound)
    (hrepeatCount : Nat.size repeatCount <= bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxRepeatWitnessCoordinateSizeBound witness
        bitBound) :
    forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact htokenTable
  · exact hwidth
  · exact htokenCount
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (7 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (7 : Fin 8)
  · exact hbinderArity
  · exact hrepeatCount
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues] using
      hwitness (0 : Fin 4)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues] using
      hwitness (1 : Fin 4)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues] using
      hwitness (2 : Fin 4)
  · simpa [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues] using
      hwitness (3 : Fin 4)

theorem compactUnifiedParserSyntaxRepeatClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (bitBound : Nat)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
        tokenCount current next binderArity repeatCount witness)).length <=
      compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound := by
  let environment :=
    compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
      tokenCount current next binderArity repeatCount witness
  let rewriting : Rew ℒₒᵣ Nat 25 Nat 0 :=
    Rew.subst (fun coordinate =>
      shortBinaryNumeralTerm (environment coordinate))
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro coordinate
      rw [show rewriting (#coordinate : ArithmeticSemiterm Nat 25) =
          shortBinaryNumeralTerm (environment coordinate) by
        simp [rewriting]]
      exact binaryNumeralTerm_code_length_le_envelope
        (environment coordinate) bitBound (by
          simpa only [environment] using hsize coordinate)
    · intro coordinate
      simp [rewriting]
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxRepeatRowsDef.val)
  unfold compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial
  rw [compactUnifiedParserSyntaxRepeatClosedFormula_environment_alignment
    tokenTable width tokenCount current next binderArity repeatCount witness]
  simpa only [rewriting, environment] using hraw

theorem compactUnifiedParserSyntaxRepeatExplicitFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (bitBound : Nat)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxRepeatExplicitFormula tokenTable width
        tokenCount current next binderArity repeatCount witness)).length <=
      compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound := by
  rw [← compactUnifiedParserSyntaxRepeatClosedFormula_alignment tokenTable
    width tokenCount current next binderArity repeatCount witness]
  exact compactUnifiedParserSyntaxRepeatClosedFormula_code_length_le_fixed
    tokenTable width tokenCount current next binderArity repeatCount witness
    bitBound hsize

end FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
