import integration.FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepDoneDirectSelectedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepEmptyDirectSelectedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepRepeatGraphFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepTermGraphFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanFormulaBranchFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanInvalidBranchFixedBounds

/-! # Common data for the six closed fixed SyntaxStep branch bounds -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserEmptyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepRepeatGraphFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsClosedGeneralBounds
open FoundationCompactNumericListedDirectParserSyntaxInvalidFullyFixedBounds
open FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

def syntaxStepDoneClosedFixedResource
    (numericBound bitBound : Nat) : Nat :=
  sixRightDisjunctionPathZeroPayloadEnvelope
    (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
    (compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
      numericBound bitBound)

def syntaxStepEmptyClosedFixedResource
    (numericBound bitBound : Nat) : Nat :=
  sixRightDisjunctionPathOnePayloadEnvelope
    (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
    (parserEmptyUniformDirectFixedPayloadPolynomial numericBound bitBound)

def syntaxStepRepeatClosedFixedResource
    (tokenCount numericBound bitBound : Nat) : Nat :=
  sixRightDisjunctionPathTwoPayloadEnvelope
    (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
    (syntaxStepRepeatGraphSelectedResource tokenCount numericBound bitBound)

def syntaxStepTermClosedFixedResource
    (tokenCount numericBound bitBound : Nat) : Nat :=
  sixRightDisjunctionPathThreePayloadEnvelope
    (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
    (syntaxTermGraphFullyFixedPayloadPolynomial tokenCount numericBound bitBound)

def syntaxStepFormulaClosedFixedResource
    (tokenCount numericBound bitBound : Nat) : Nat :=
  sixRightDisjunctionPathFourPayloadEnvelope
    (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
    (cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
      bitBound)

def syntaxStepInvalidClosedFixedResource
    (tokenCount numericBound bitBound : Nat) : Nat :=
  sixRightDisjunctionPathFivePayloadEnvelope
    (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
    (syntaxInvalidFullyFixedPayloadPolynomial tokenCount numericBound bitBound)

def syntaxStepAllBranchesClosedFixedResource
    (tokenCount numericBound bitBound : Nat) : Nat :=
  max (syntaxStepDoneClosedFixedResource numericBound bitBound)
    (max (syntaxStepEmptyClosedFixedResource numericBound bitBound)
      (max (syntaxStepRepeatClosedFixedResource tokenCount numericBound bitBound)
        (max (syntaxStepTermClosedFixedResource tokenCount numericBound bitBound)
          (max
            (syntaxStepFormulaClosedFixedResource tokenCount numericBound
              bitBound)
            (syntaxStepInvalidClosedFixedResource tokenCount numericBound
              bitBound)))))

structure CompactUnifiedParserSyntaxStepClosedFixedContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat) : Prop where
  width_le : width <= numericBound
  width_le_bit : width <= bitBound
  tokenCount_le : tokenCount <= numericBound
  currentValue :
    CompactUnifiedParserStateCoordinateValueBound current numericBound
  nextValue :
    CompactUnifiedParserStateCoordinateValueBound next numericBound
  tokenTableSize : Nat.size tokenTable <= bitBound
  currentSize :
    CompactUnifiedParserStateCoordinateSizeBound current bitBound
  nextSize :
    CompactUnifiedParserStateCoordinateSizeBound next bitBound
  witnessValue :
    CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound witness
      numericBound
  witnessSize :
    CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness bitBound
  numericSize : Nat.size numericBound <= bitBound
  bitPositive : 1 <= bitBound

namespace CompactUnifiedParserSyntaxStepClosedFixedContext

variable
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {witness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    {numericBound bitBound : Nat}

theorem widthSize
    (context : CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
      tokenCount current next witness numericBound bitBound) :
    Nat.size width <= bitBound :=
  (Nat.size_le_size context.width_le).trans context.numericSize

theorem tokenCountSize
    (context : CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
      tokenCount current next witness numericBound bitBound) :
    Nat.size tokenCount <= bitBound :=
  (Nat.size_le_size context.tokenCount_le).trans context.numericSize

theorem stepSize
    (context : CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
      tokenCount current next witness numericBound bitBound) :
    forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound :=
  compactUnifiedParserSyntaxStepFormulaEnvironment_size_le tokenTable width
    tokenCount current next witness bitBound context.tokenTableSize
    context.widthSize context.tokenCountSize context.currentSize
    context.nextSize context.witnessSize

theorem doneWitnessSize
    (context : CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
      tokenCount current next witness numericBound bitBound) :
    CompactUnifiedParserDoneWitnessCoordinateSizeBound witness.done bitBound :=
  compactUnifiedParserSyntaxStepDoneWitness_size_le witness bitBound
    context.witnessSize

theorem repeatWitnessSize
    (context : CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
      tokenCount current next witness numericBound bitBound) :
    CompactUnifiedParserSyntaxRepeatWitnessCoordinateSizeBound witness.repeat
      bitBound :=
  compactUnifiedParserSyntaxStepRepeatWitness_size_le witness bitBound
    context.witnessSize

theorem termWitnessSize
    (context : CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
      tokenCount current next witness numericBound bitBound) :
    CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness.term
      bitBound :=
  compactUnifiedParserSyntaxStepTermWitness_size_le witness bitBound
    context.witnessSize

end CompactUnifiedParserSyntaxStepClosedFixedContext

end FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase
