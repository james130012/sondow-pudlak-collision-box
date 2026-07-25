import integration.FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

/-! # Graph-free fixed syntax bound for the original 26-coordinate Term formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

namespace FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate

def compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserSyntaxTermRowsDef.val)).length

def compactUnifiedParserSyntaxTermWitnessCoordinateValues
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : Fin 6 -> Nat :=
  ![witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
    witness.tag, witness.argument, witness.functionCode]

def CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (bitBound : Nat) : Prop :=
  forall coordinate,
    Nat.size
      (compactUnifiedParserSyntaxTermWitnessCoordinateValues witness
        coordinate) <= bitBound

def compactUnifiedParserSyntaxTermFormulaEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : Fin 26 -> Nat :=
  ![tokenTable, width, tokenCount, current.start, current.finish,
    current.tokensFinish, current.tasksFinish, current.tokensBoundary,
    current.tokensCount, current.tasksBoundary, current.tasksCount, next.start,
    next.finish, next.tokensFinish, next.tasksFinish, next.tokensBoundary,
    next.tokensCount, next.tasksBoundary, next.tasksCount, binderArity,
    witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
    witness.tag, witness.argument, witness.functionCode]

theorem compactUnifiedParserSyntaxTermClosedFormula_environment_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current next binderArity witness =
      (Rew.subst (fun coordinate =>
        shortBinaryNumeralTerm
          (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
            tokenCount current next binderArity witness coordinate))) ▹
        (Rewriting.emb (ξ := Nat)
          compactUnifiedParserSyntaxTermRowsDef.val) := by
  unfold compactUnifiedParserSyntaxTermClosedFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [compactUnifiedParserSyntaxTermFormulaEnvironment]

theorem compactUnifiedParserSyntaxTermFormulaEnvironment_size_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hcurrent :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnext :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hbinderArity : Nat.size binderArity <= bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness
        bitBound) :
    forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact htokenTable
  · exact hwidth
  · exact htokenCount
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (7 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (7 : Fin 8)
  · exact hbinderArity
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (0 : Fin 6)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (1 : Fin 6)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (2 : Fin 6)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (3 : Fin 6)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (4 : Fin 6)
  · simpa [compactUnifiedParserSyntaxTermFormulaEnvironment,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues] using
      hwitness (5 : Fin 6)

theorem compactUnifiedParserSyntaxTermClosedFormula_code_length_le_fixed
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
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current next binderArity witness)).length <=
      compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound := by
  let environment :=
    compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
      tokenCount current next binderArity witness
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
    (Rewriting.emb (ξ := Nat) compactUnifiedParserSyntaxTermRowsDef.val)
  unfold compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial
  rw [compactUnifiedParserSyntaxTermClosedFormula_environment_alignment
    tokenTable width tokenCount current next binderArity witness]
  simpa only [rewriting, environment] using hraw

theorem compactUnifiedParserSyntaxTermExplicitFormula_code_length_le_fixed
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
      (compactUnifiedParserSyntaxTermExplicitFormula tokenTable width
        tokenCount current next binderArity witness)).length <=
      compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound := by
  rw [← compactUnifiedParserSyntaxTermClosedFormula_alignment tokenTable width
    tokenCount current next binderArity witness]
  exact compactUnifiedParserSyntaxTermClosedFormula_code_length_le_fixed
    tokenTable width tokenCount current next binderArity witness bitBound hsize

#print axioms compactUnifiedParserSyntaxTermClosedFormula_code_length_le_fixed
#print axioms compactUnifiedParserSyntaxTermExplicitFormula_code_length_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
