import integration.FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRouteCompleteness
import integration.FoundationCompactNumericListedDirectSuccIndBaseNegationRouteCompleteness
import integration.FoundationCompactNumericListedDirectSuccIndStepAssemblyRouteCompleteness
import integration.FoundationCompactNumericListedDirectSuccIndOuterAssemblyRouteCompleteness
import integration.FoundationCompactNumericListedDirectFormulaFvSupTotalEndpointCompleteness
import integration.FoundationCompactNumericListedDirectFixedAllClosureTotalEndpointCompleteness
import integration.FoundationCompactNumericListedDirectGuardedInductionSentenceRoute

/-!
# Canonical completeness for the guarded induction route

All formula values and all twelve executable transform traces are packed into
one fixed-width table.  Extra chunks may be appended so later rule-check and
sequent witnesses can use exactly the same table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericAllClosure
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectLiteralNatListFormula
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
open FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute
open FoundationCompactNumericListedDirectSuccIndOuterAssemblyRoute
open FoundationCompactNumericListedDirectSuccIndSentenceRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
open FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRouteCompleteness
open FoundationCompactNumericListedDirectSuccIndBaseNegationRouteCompleteness
open FoundationCompactNumericListedDirectSuccIndStepAssemblyRouteCompleteness
open FoundationCompactNumericListedDirectSuccIndOuterAssemblyRouteCompleteness
open FoundationCompactNumericListedDirectFormulaFvSupTotalEndpointCompleteness
open FoundationCompactNumericListedDirectFixedAllClosureTotalEndpointCompleteness

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def compactGuardedInductionExactTransform
    (mode : Nat) (witness : List Nat) (binderArity : Nat)
    (input : List Nat) : List Nat :=
  (compactExactFormulaTransformResult
    (compactFormulaTransformResult
      (mode, witness) (binderArity, input))).getD []

def compactGuardedInductionTransformStates
    (mode : Nat) (witness : List Nat) (binderArity : Nat)
    (input : List Nat) : List CompactFormulaTransformState :=
  compactFormulaTransformStateTrace (mode, witness)
    (compactSyntaxRunFuelBound input)
    (compactFormulaTransformInitialState binderArity input)

structure CompactGuardedInductionExecutableData where
  body : List Nat
  zeroWitness : List Nat
  openZeroWitness : List Nat
  openSuccessorWitness : List Nat
  captureOne : List Nat
  empty : List Nat
  base : List Nat
  negatedBase : List Nat
  openZeroShifted : List Nat
  openZeroSubstituted : List Nat
  stepZero : List Nat
  openSuccessorShifted : List Nat
  openSuccessorSubstituted : List Nat
  stepSuccessor : List Nat
  negatedStepZero : List Nat
  stepDisjunction : List Nat
  quantifiedStep : List Nat
  negatedQuantifiedStep : List Nat
  quantifiedFinal : List Nat
  innerDisjunction : List Nat
  sentence : List Nat
  fvarList : List Nat
  depth : Nat
  depthCapture : List Nat
  fixed : List Nat
  generated : List Nat

def compactGuardedInductionZeroWitness : List Nat :=
  compactSuccIndZeroWitnessTokens

def compactGuardedInductionOpenZeroWitness : List Nat :=
  compactSuccIndOpenZeroWitnessTokens

def compactGuardedInductionOpenSuccessorWitness : List Nat :=
  compactSuccIndOpenSuccessorWitnessTokens

def compactGuardedInductionCaptureOne : List Nat := [0]

def compactGuardedInductionEmpty : List Nat := []

def compactGuardedInductionBase (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    2 compactGuardedInductionZeroWitness 1 bodyTokens

def compactGuardedInductionNegatedBase (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform 3 compactGuardedInductionEmpty 0
    (compactGuardedInductionBase bodyTokens)

def compactGuardedInductionOpenZeroShifted
    (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    1 compactGuardedInductionEmpty 1 bodyTokens

def compactGuardedInductionOpenZeroSubstituted
    (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    2 compactGuardedInductionOpenZeroWitness 1
      (compactGuardedInductionOpenZeroShifted bodyTokens)

def compactGuardedInductionStepZero (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    5 compactGuardedInductionCaptureOne 0
      (compactGuardedInductionOpenZeroSubstituted bodyTokens)

def compactGuardedInductionOpenSuccessorShifted
    (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    1 compactGuardedInductionEmpty 1 bodyTokens

def compactGuardedInductionOpenSuccessorSubstituted
    (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    2 compactGuardedInductionOpenSuccessorWitness 1
      (compactGuardedInductionOpenSuccessorShifted bodyTokens)

def compactGuardedInductionStepSuccessor
    (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    5 compactGuardedInductionCaptureOne 0
      (compactGuardedInductionOpenSuccessorSubstituted bodyTokens)

def compactGuardedInductionNegatedStepZero
    (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    3 compactGuardedInductionEmpty 1
      (compactGuardedInductionStepZero bodyTokens)

def compactGuardedInductionStepDisjunction
    (bodyTokens : List Nat) : List Nat :=
  tokenFormulaOr
    (compactGuardedInductionNegatedStepZero bodyTokens)
    (compactGuardedInductionStepSuccessor bodyTokens)

def compactGuardedInductionQuantifiedStep
    (bodyTokens : List Nat) : List Nat :=
  tokenFormulaAll (compactGuardedInductionStepDisjunction bodyTokens)

def compactGuardedInductionNegatedQuantifiedStep
    (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    3 compactGuardedInductionEmpty 0
      (compactGuardedInductionQuantifiedStep bodyTokens)

def compactGuardedInductionQuantifiedFinal
    (bodyTokens : List Nat) : List Nat :=
  tokenFormulaAll (compactGuardedInductionStepZero bodyTokens)

def compactGuardedInductionInnerDisjunction
    (bodyTokens : List Nat) : List Nat :=
  tokenFormulaOr
    (compactGuardedInductionNegatedQuantifiedStep bodyTokens)
    (compactGuardedInductionQuantifiedFinal bodyTokens)

def compactGuardedInductionSentence (bodyTokens : List Nat) : List Nat :=
  tokenFormulaOr
    (compactGuardedInductionNegatedBase bodyTokens)
    (compactGuardedInductionInnerDisjunction bodyTokens)

def compactGuardedInductionFvarList (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    4 compactGuardedInductionEmpty 0
      (compactGuardedInductionSentence bodyTokens)

def compactGuardedInductionDepth (bodyTokens : List Nat) : Nat :=
  listFvSup (compactGuardedInductionFvarList bodyTokens)

def compactGuardedInductionDepthCapture
    (bodyTokens : List Nat) : List Nat :=
  List.replicate (compactGuardedInductionDepth bodyTokens) 0

def compactGuardedInductionFixed (bodyTokens : List Nat) : List Nat :=
  compactGuardedInductionExactTransform
    5 (compactGuardedInductionDepthCapture bodyTokens) 0
      (compactGuardedInductionSentence bodyTokens)

def compactGuardedInductionGenerated (bodyTokens : List Nat) : List Nat :=
  compactAllClosureTokens
    (compactGuardedInductionDepth bodyTokens)
    (compactGuardedInductionFixed bodyTokens)

def compactGuardedInductionExecutableData
    (bodyTokens : List Nat) : CompactGuardedInductionExecutableData :=
  { body := bodyTokens
    zeroWitness := compactGuardedInductionZeroWitness
    openZeroWitness := compactGuardedInductionOpenZeroWitness
    openSuccessorWitness := compactGuardedInductionOpenSuccessorWitness
    captureOne := compactGuardedInductionCaptureOne
    empty := compactGuardedInductionEmpty
    base := compactGuardedInductionBase bodyTokens
    negatedBase := compactGuardedInductionNegatedBase bodyTokens
    openZeroShifted := compactGuardedInductionOpenZeroShifted bodyTokens
    openZeroSubstituted :=
      compactGuardedInductionOpenZeroSubstituted bodyTokens
    stepZero := compactGuardedInductionStepZero bodyTokens
    openSuccessorShifted :=
      compactGuardedInductionOpenSuccessorShifted bodyTokens
    openSuccessorSubstituted :=
      compactGuardedInductionOpenSuccessorSubstituted bodyTokens
    stepSuccessor := compactGuardedInductionStepSuccessor bodyTokens
    negatedStepZero := compactGuardedInductionNegatedStepZero bodyTokens
    stepDisjunction := compactGuardedInductionStepDisjunction bodyTokens
    quantifiedStep := compactGuardedInductionQuantifiedStep bodyTokens
    negatedQuantifiedStep :=
      compactGuardedInductionNegatedQuantifiedStep bodyTokens
    quantifiedFinal := compactGuardedInductionQuantifiedFinal bodyTokens
    innerDisjunction := compactGuardedInductionInnerDisjunction bodyTokens
    sentence := compactGuardedInductionSentence bodyTokens
    fvarList := compactGuardedInductionFvarList bodyTokens
    depth := compactGuardedInductionDepth bodyTokens
    depthCapture := compactGuardedInductionDepthCapture bodyTokens
    fixed := compactGuardedInductionFixed bodyTokens
    generated := compactGuardedInductionGenerated bodyTokens }

@[simp] theorem compactGuardedInductionCaptureOne_length :
    compactGuardedInductionCaptureOne.length = 1 := by
  rfl

@[simp] theorem compactGuardedInductionDepthCapture_length
    (bodyTokens : List Nat) :
    (compactGuardedInductionDepthCapture bodyTokens).length =
      compactGuardedInductionDepth bodyTokens := by
  simp [compactGuardedInductionDepthCapture]

theorem compactGuardedInductionBase_eq (bodyTokens : List Nat) :
    compactGuardedInductionBase bodyTokens =
      compactGuardedInductionExactTransform
        2 compactGuardedInductionZeroWitness 1 bodyTokens := by
  rfl

theorem compactGuardedInductionNegatedBase_eq (bodyTokens : List Nat) :
    compactGuardedInductionNegatedBase bodyTokens =
      compactGuardedInductionExactTransform
        3 compactGuardedInductionEmpty 0
          (compactGuardedInductionBase bodyTokens) := by
  rfl

theorem compactGuardedInductionOpenZeroShifted_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionOpenZeroShifted bodyTokens =
      compactGuardedInductionExactTransform
        1 compactGuardedInductionEmpty 1 bodyTokens := by
  rfl

theorem compactGuardedInductionOpenZeroSubstituted_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionOpenZeroSubstituted bodyTokens =
      compactGuardedInductionExactTransform
        2 compactGuardedInductionOpenZeroWitness 1
          (compactGuardedInductionOpenZeroShifted bodyTokens) := by
  rfl

theorem compactGuardedInductionStepZero_eq (bodyTokens : List Nat) :
    compactGuardedInductionStepZero bodyTokens =
      compactGuardedInductionExactTransform
        5 compactGuardedInductionCaptureOne 0
          (compactGuardedInductionOpenZeroSubstituted bodyTokens) := by
  rfl

theorem compactGuardedInductionOpenSuccessorShifted_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionOpenSuccessorShifted bodyTokens =
      compactGuardedInductionExactTransform
        1 compactGuardedInductionEmpty 1 bodyTokens := by
  rfl

theorem compactGuardedInductionOpenSuccessorSubstituted_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionOpenSuccessorSubstituted bodyTokens =
      compactGuardedInductionExactTransform
        2 compactGuardedInductionOpenSuccessorWitness 1
          (compactGuardedInductionOpenSuccessorShifted bodyTokens) := by
  rfl

theorem compactGuardedInductionStepSuccessor_eq (bodyTokens : List Nat) :
    compactGuardedInductionStepSuccessor bodyTokens =
      compactGuardedInductionExactTransform
        5 compactGuardedInductionCaptureOne 0
          (compactGuardedInductionOpenSuccessorSubstituted bodyTokens) := by
  rfl

theorem compactGuardedInductionNegatedStepZero_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionNegatedStepZero bodyTokens =
      compactGuardedInductionExactTransform
        3 compactGuardedInductionEmpty 1
          (compactGuardedInductionStepZero bodyTokens) := by
  rfl

theorem compactGuardedInductionStepDisjunction_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionStepDisjunction bodyTokens =
      tokenFormulaOr
        (compactGuardedInductionNegatedStepZero bodyTokens)
        (compactGuardedInductionStepSuccessor bodyTokens) := by
  rfl

theorem compactGuardedInductionQuantifiedStep_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionQuantifiedStep bodyTokens =
      tokenFormulaAll
        (compactGuardedInductionStepDisjunction bodyTokens) := by
  rfl

theorem compactGuardedInductionNegatedQuantifiedStep_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionNegatedQuantifiedStep bodyTokens =
      compactGuardedInductionExactTransform
        3 compactGuardedInductionEmpty 0
          (compactGuardedInductionQuantifiedStep bodyTokens) := by
  rfl

theorem compactGuardedInductionQuantifiedFinal_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionQuantifiedFinal bodyTokens =
      tokenFormulaAll (compactGuardedInductionStepZero bodyTokens) := by
  rfl

theorem compactGuardedInductionInnerDisjunction_eq
    (bodyTokens : List Nat) :
    compactGuardedInductionInnerDisjunction bodyTokens =
      tokenFormulaOr
        (compactGuardedInductionNegatedQuantifiedStep bodyTokens)
        (compactGuardedInductionQuantifiedFinal bodyTokens) := by
  rfl

theorem compactGuardedInductionSentence_eq (bodyTokens : List Nat) :
    compactGuardedInductionSentence bodyTokens =
      tokenFormulaOr
        (compactGuardedInductionNegatedBase bodyTokens)
        (compactGuardedInductionInnerDisjunction bodyTokens) := by
  rfl

theorem compactGuardedInductionFvarList_eq (bodyTokens : List Nat) :
    compactGuardedInductionFvarList bodyTokens =
      compactGuardedInductionExactTransform
        4 compactGuardedInductionEmpty 0
          (compactGuardedInductionSentence bodyTokens) := by
  rfl

theorem compactGuardedInductionDepth_eq (bodyTokens : List Nat) :
    compactGuardedInductionDepth bodyTokens =
      listFvSup (compactGuardedInductionFvarList bodyTokens) := by
  rfl

theorem compactGuardedInductionFixed_eq (bodyTokens : List Nat) :
    compactGuardedInductionFixed bodyTokens =
      compactGuardedInductionExactTransform
        5 (compactGuardedInductionDepthCapture bodyTokens) 0
          (compactGuardedInductionSentence bodyTokens) := by
  rfl

theorem compactGuardedInductionGenerated_eq (bodyTokens : List Nat) :
    compactGuardedInductionGenerated bodyTokens =
      compactAllClosureTokens
        (compactGuardedInductionDepth bodyTokens)
        (compactGuardedInductionFixed bodyTokens) := by
  rfl
def compactGuardedInductionRouteChunks
    (data : CompactGuardedInductionExecutableData) : List (List Nat) :=
  [compactAdditiveEncode data.body,
    compactAdditiveEncode data.zeroWitness,
    compactAdditiveEncode data.openZeroWitness,
    compactAdditiveEncode data.openSuccessorWitness,
    compactAdditiveEncode data.captureOne,
    compactAdditiveEncode data.empty,
    compactAdditiveEncode data.base,
    compactAdditiveEncode data.negatedBase,
    compactAdditiveEncode data.openZeroShifted,
    compactAdditiveEncode data.openZeroSubstituted,
    compactAdditiveEncode data.stepZero,
    compactAdditiveEncode data.openSuccessorShifted,
    compactAdditiveEncode data.openSuccessorSubstituted,
    compactAdditiveEncode data.stepSuccessor,
    compactAdditiveEncode data.negatedStepZero,
    compactAdditiveEncode data.stepDisjunction,
    compactAdditiveEncode data.quantifiedStep,
    compactAdditiveEncode data.negatedQuantifiedStep,
    compactAdditiveEncode data.quantifiedFinal,
    compactAdditiveEncode data.innerDisjunction,
    compactAdditiveEncode data.sentence,
    compactAdditiveEncode data.fvarList,
    compactAdditiveEncode data.depthCapture,
    compactAdditiveEncode data.fixed,
    compactAdditiveEncode data.generated,
    compactAdditiveEncode (compactGuardedInductionTransformStates
      2 data.zeroWitness 1 data.body),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      3 data.empty 0 data.base),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      1 data.empty 1 data.body),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      2 data.openZeroWitness 1 data.openZeroShifted),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      5 data.captureOne 0 data.openZeroSubstituted),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      1 data.empty 1 data.body),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      2 data.openSuccessorWitness 1 data.openSuccessorShifted),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      5 data.captureOne 0 data.openSuccessorSubstituted),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      3 data.empty 1 data.stepZero),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      3 data.empty 0 data.quantifiedStep),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      4 data.empty 0 data.sentence),
    compactAdditiveEncode (compactGuardedInductionTransformStates
      5 data.depthCapture 0 data.sentence)]

structure CompactGuardedInductionPackedNatRows
    (tokenTable width tokenCount : Nat) (chunks : List (List Nat))
    (data : CompactGuardedInductionExecutableData) : Prop where
  body : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 0 data.body) data.body
  zeroWitness : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 1 data.zeroWitness) data.zeroWitness
  openZeroWitness : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 2 data.openZeroWitness)
    data.openZeroWitness
  openSuccessorWitness : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
    data.openSuccessorWitness
  captureOne : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 4 data.captureOne) data.captureOne
  empty : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 5 data.empty) data.empty
  base : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 6 data.base) data.base
  negatedBase : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 7 data.negatedBase) data.negatedBase
  openZeroShifted : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 8 data.openZeroShifted)
    data.openZeroShifted
  openZeroSubstituted : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 9 data.openZeroSubstituted)
    data.openZeroSubstituted
  stepZero : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 10 data.stepZero) data.stepZero
  openSuccessorShifted : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 11 data.openSuccessorShifted)
    data.openSuccessorShifted
  openSuccessorSubstituted : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 12 data.openSuccessorSubstituted)
    data.openSuccessorSubstituted
  stepSuccessor : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 13 data.stepSuccessor)
    data.stepSuccessor
  negatedStepZero : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 14 data.negatedStepZero)
    data.negatedStepZero
  stepDisjunction : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 15 data.stepDisjunction)
    data.stepDisjunction
  quantifiedStep : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 16 data.quantifiedStep)
    data.quantifiedStep
  negatedQuantifiedStep : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
    data.negatedQuantifiedStep
  quantifiedFinal : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
    data.quantifiedFinal
  innerDisjunction : CompactPackedNatListSlotCanonical
    tokenTable width tokenCount
    (compactPackedNatListSlot chunks 19 data.innerDisjunction)
    data.innerDisjunction
  sentence : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 20 data.sentence) data.sentence
  fvarList : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 21 data.fvarList) data.fvarList
  depthCapture : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 22 data.depthCapture) data.depthCapture
  fixed : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 23 data.fixed) data.fixed
  generated : CompactPackedNatListSlotCanonical tokenTable width tokenCount
    (compactPackedNatListSlot chunks 24 data.generated) data.generated

structure CompactGuardedInductionPackedStateRows
    (tokenTable width tokenCount : Nat) (chunks : List (List Nat))
    (data : CompactGuardedInductionExecutableData) : Prop where
  base : CompactFormulaTransformStateListRowLayouts tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 25
      (compactGuardedInductionTransformStates
        2 data.zeroWitness 1 data.body))
    (compactGuardedInductionTransformStates 2 data.zeroWitness 1 data.body)
  baseNegation : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 26
      (compactGuardedInductionTransformStates 3 data.empty 0 data.base))
    (compactGuardedInductionTransformStates 3 data.empty 0 data.base)
  openZeroShift : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 27
      (compactGuardedInductionTransformStates 1 data.empty 1 data.body))
    (compactGuardedInductionTransformStates 1 data.empty 1 data.body)
  openZeroSubstitution : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 28
      (compactGuardedInductionTransformStates
        2 data.openZeroWitness 1 data.openZeroShifted))
    (compactGuardedInductionTransformStates
      2 data.openZeroWitness 1 data.openZeroShifted)
  openZeroFixitr : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 29
      (compactGuardedInductionTransformStates
        5 data.captureOne 0 data.openZeroSubstituted))
    (compactGuardedInductionTransformStates
      5 data.captureOne 0 data.openZeroSubstituted)
  openSuccessorShift : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 30
      (compactGuardedInductionTransformStates 1 data.empty 1 data.body))
    (compactGuardedInductionTransformStates 1 data.empty 1 data.body)
  openSuccessorSubstitution : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 31
      (compactGuardedInductionTransformStates
        2 data.openSuccessorWitness 1 data.openSuccessorShifted))
    (compactGuardedInductionTransformStates
      2 data.openSuccessorWitness 1 data.openSuccessorShifted)
  openSuccessorFixitr : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 32
      (compactGuardedInductionTransformStates
        5 data.captureOne 0 data.openSuccessorSubstituted))
    (compactGuardedInductionTransformStates
      5 data.captureOne 0 data.openSuccessorSubstituted)
  stepNegation : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 33
      (compactGuardedInductionTransformStates
        3 data.empty 1 data.stepZero))
    (compactGuardedInductionTransformStates 3 data.empty 1 data.stepZero)
  quantifiedStepNegation : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 34
      (compactGuardedInductionTransformStates
        3 data.empty 0 data.quantifiedStep))
    (compactGuardedInductionTransformStates
      3 data.empty 0 data.quantifiedStep)
  fvarList : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 35
      (compactGuardedInductionTransformStates
        4 data.empty 0 data.sentence))
    (compactGuardedInductionTransformStates 4 data.empty 0 data.sentence)
  closure : CompactFormulaTransformStateListRowLayouts
    tokenTable width tokenCount
    (compactPackedFormulaTransformStateBoundary chunks 36
      (compactGuardedInductionTransformStates
        5 data.depthCapture 0 data.sentence))
    (compactGuardedInductionTransformStates
      5 data.depthCapture 0 data.sentence)

set_option maxHeartbeats 600000 in
theorem compactGuardedInductionPackedNatRows_canonical
    (data : CompactGuardedInductionExecutableData)
    (extraChunks : List (List Nat)) :
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokens.length chunks data
  have hlength : 37 <= chunks.length := by
    simp [chunks, compactGuardedInductionRouteChunks]
  have slotCanonical (index : Nat) (values : List Nat)
      (hindex : index < chunks.length)
      (hchunk : chunks[index] = compactAdditiveEncode values) :
      CompactPackedNatListSlotCanonical tokenTable width tokens.length
        (compactPackedNatListSlot chunks index values) values := by
    simpa [tokenTable, width, tokens] using
      compactPackedNatListSlot_canonical chunks index values hindex hchunk
  refine
    { body := slotCanonical 0 data.body (by omega) ?_
      zeroWitness := slotCanonical 1 data.zeroWitness (by omega) ?_
      openZeroWitness := slotCanonical 2 data.openZeroWitness (by omega) ?_
      openSuccessorWitness := slotCanonical 3 data.openSuccessorWitness
        (by omega) ?_
      captureOne := slotCanonical 4 data.captureOne (by omega) ?_
      empty := slotCanonical 5 data.empty (by omega) ?_
      base := slotCanonical 6 data.base (by omega) ?_
      negatedBase := slotCanonical 7 data.negatedBase (by omega) ?_
      openZeroShifted := slotCanonical 8 data.openZeroShifted (by omega) ?_
      openZeroSubstituted := slotCanonical 9 data.openZeroSubstituted
        (by omega) ?_
      stepZero := slotCanonical 10 data.stepZero (by omega) ?_
      openSuccessorShifted := slotCanonical 11 data.openSuccessorShifted
        (by omega) ?_
      openSuccessorSubstituted := slotCanonical 12
        data.openSuccessorSubstituted (by omega) ?_
      stepSuccessor := slotCanonical 13 data.stepSuccessor (by omega) ?_
      negatedStepZero := slotCanonical 14 data.negatedStepZero (by omega) ?_
      stepDisjunction := slotCanonical 15 data.stepDisjunction (by omega) ?_
      quantifiedStep := slotCanonical 16 data.quantifiedStep (by omega) ?_
      negatedQuantifiedStep := slotCanonical 17 data.negatedQuantifiedStep
        (by omega) ?_
      quantifiedFinal := slotCanonical 18 data.quantifiedFinal (by omega) ?_
      innerDisjunction := slotCanonical 19 data.innerDisjunction
        (by omega) ?_
      sentence := slotCanonical 20 data.sentence (by omega) ?_
      fvarList := slotCanonical 21 data.fvarList (by omega) ?_
      depthCapture := slotCanonical 22 data.depthCapture (by omega) ?_
      fixed := slotCanonical 23 data.fixed (by omega) ?_
      generated := slotCanonical 24 data.generated (by omega) ?_ } <;>
    simp [chunks, compactGuardedInductionRouteChunks]

set_option maxHeartbeats 600000 in
theorem compactGuardedInductionPackedStateRows_canonical
    (data : CompactGuardedInductionExecutableData)
    (extraChunks : List (List Nat)) :
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokens.length chunks data
  have hlength : 37 <= chunks.length := by
    simp [chunks, compactGuardedInductionRouteChunks]
  have stateRowsCanonical (index : Nat)
      (states : List CompactFormulaTransformState)
      (hindex : index < chunks.length)
      (hchunk : chunks[index] = compactAdditiveEncode states) :
      CompactFormulaTransformStateListRowLayouts tokenTable width
        tokens.length
        (compactPackedFormulaTransformStateBoundary chunks index states)
        states := by
    simpa [tokenTable, width, tokens] using
      compactPackedFormulaTransformStateRows_canonical
        chunks index states hindex hchunk
  refine
    { base := stateRowsCanonical 25
        (compactGuardedInductionTransformStates
          2 data.zeroWitness 1 data.body) (by omega) ?_
      baseNegation := stateRowsCanonical 26
        (compactGuardedInductionTransformStates
          3 data.empty 0 data.base) (by omega) ?_
      openZeroShift := stateRowsCanonical 27
        (compactGuardedInductionTransformStates
          1 data.empty 1 data.body) (by omega) ?_
      openZeroSubstitution := stateRowsCanonical 28
        (compactGuardedInductionTransformStates
          2 data.openZeroWitness 1 data.openZeroShifted) (by omega) ?_
      openZeroFixitr := stateRowsCanonical 29
        (compactGuardedInductionTransformStates
          5 data.captureOne 0 data.openZeroSubstituted) (by omega) ?_
      openSuccessorShift := stateRowsCanonical 30
        (compactGuardedInductionTransformStates
          1 data.empty 1 data.body) (by omega) ?_
      openSuccessorSubstitution := stateRowsCanonical 31
        (compactGuardedInductionTransformStates
          2 data.openSuccessorWitness 1 data.openSuccessorShifted)
        (by omega) ?_
      openSuccessorFixitr := stateRowsCanonical 32
        (compactGuardedInductionTransformStates
          5 data.captureOne 0 data.openSuccessorSubstituted) (by omega) ?_
      stepNegation := stateRowsCanonical 33
        (compactGuardedInductionTransformStates
          3 data.empty 1 data.stepZero) (by omega) ?_
      quantifiedStepNegation := stateRowsCanonical 34
        (compactGuardedInductionTransformStates
          3 data.empty 0 data.quantifiedStep) (by omega) ?_
      fvarList := stateRowsCanonical 35
        (compactGuardedInductionTransformStates
          4 data.empty 0 data.sentence) (by omega) ?_
      closure := stateRowsCanonical 36
        (compactGuardedInductionTransformStates
          5 data.depthCapture 0 data.sentence) (by omega) ?_ } <;>
    simp [chunks, compactGuardedInductionRouteChunks]

set_option maxHeartbeats 250000 in
theorem exists_compactGuardedInductionBaseRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactSuccIndBaseNegationRouteCoordinates,
      CompactSuccIndBaseNegationRoute tokenTable width tokenCount
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactSuccIndBaseNegationRouteCoordinates,
    CompactSuccIndBaseNegationRoute tokenTable width tokenCount
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates
  exact exists_compactSuccIndBaseNegationRoute_of_executable_outputs
    hnat.body hnat.zeroWitness hnat.base hnat.negatedBase hnat.empty
    (by rfl) hstates.base hstates.baseNegation
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform] using
      compactGuardedInductionBase_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform,
        compactGuardedInductionEmpty] using
      compactGuardedInductionNegatedBase_eq bodyTokens)

set_option maxHeartbeats 250000 in
theorem exists_compactGuardedInductionOpenZeroRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
      CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
    CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates
  exact exists_compactSuccIndOpenSubstitutionRoute_of_executable_outputs
    hnat.body hnat.openZeroWitness hnat.captureOne hnat.stepZero hnat.empty
    hnat.openZeroShifted hnat.openZeroSubstituted
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionCaptureOne_length)
    hstates.openZeroShift hstates.openZeroSubstitution hstates.openZeroFixitr
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform,
        compactGuardedInductionEmpty] using
      compactGuardedInductionOpenZeroShifted_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform] using
      compactGuardedInductionOpenZeroSubstituted_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform] using
      compactGuardedInductionStepZero_eq bodyTokens)

set_option maxHeartbeats 250000 in
theorem exists_compactGuardedInductionOpenSuccessorRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
      CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
    CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates
  exact exists_compactSuccIndOpenSubstitutionRoute_of_executable_outputs
    hnat.body hnat.openSuccessorWitness hnat.captureOne hnat.stepSuccessor
    hnat.empty hnat.openSuccessorShifted hnat.openSuccessorSubstituted
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionCaptureOne_length)
    hstates.openSuccessorShift hstates.openSuccessorSubstitution
    hstates.openSuccessorFixitr
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform,
        compactGuardedInductionEmpty] using
      compactGuardedInductionOpenSuccessorShifted_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform] using
      compactGuardedInductionOpenSuccessorSubstituted_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform] using
      compactGuardedInductionStepSuccessor_eq bodyTokens)

set_option maxHeartbeats 250000 in
theorem exists_compactGuardedInductionStepRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactSuccIndStepAssemblyRouteCoordinates,
      CompactSuccIndStepAssemblyRoute tokenTable width tokenCount
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactSuccIndStepAssemblyRouteCoordinates,
    CompactSuccIndStepAssemblyRoute tokenTable width tokenCount
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates
  exact exists_compactSuccIndStepAssemblyRoute_of_executable_outputs
    hnat.stepZero hnat.stepSuccessor hnat.negatedStepZero
    hnat.stepDisjunction hnat.quantifiedStep hnat.negatedQuantifiedStep
    hnat.quantifiedFinal hnat.empty hstates.stepNegation
    hstates.quantifiedStepNegation
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform,
        compactGuardedInductionEmpty] using
      compactGuardedInductionNegatedStepZero_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionStepDisjunction_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionQuantifiedStep_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform,
        compactGuardedInductionEmpty] using
      compactGuardedInductionNegatedQuantifiedStep_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionQuantifiedFinal_eq bodyTokens)

set_option maxHeartbeats 250000 in
theorem compactGuardedInductionOuterRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    CompactSuccIndOuterAssemblyRoute tokenTable width tokenCount
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence) := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactSuccIndOuterAssemblyRoute tokenTable width tokenCount
    (compactPackedNatListSlot chunks 7 data.negatedBase)
    (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
    (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
    (compactPackedNatListSlot chunks 19 data.innerDisjunction)
    (compactPackedNatListSlot chunks 20 data.sentence)
  exact compactSuccIndOuterAssemblyRoute_of_constructor_outputs
    hnat.negatedBase hnat.negatedQuantifiedStep hnat.quantifiedFinal
    hnat.innerDisjunction hnat.sentence
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionInnerDisjunction_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionSentence_eq bodyTokens)

set_option maxHeartbeats 350000 in
theorem exists_compactGuardedInductionSuccIndRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactSuccIndSentenceRouteCoordinates,
      CompactSuccIndSentenceRoute tokenTable width tokenCount
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactSuccIndSentenceRouteCoordinates,
    CompactSuccIndSentenceRoute tokenTable width tokenCount
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      coordinates
  rcases exists_compactGuardedInductionBaseRoute_of_packed_rows
      bodyTokens hnat hstates with
    ⟨baseCoordinates, hbaseRoute⟩
  rcases exists_compactGuardedInductionOpenZeroRoute_of_packed_rows
      bodyTokens hnat hstates with
    ⟨openZeroCoordinates, hopenZeroRoute⟩
  rcases exists_compactGuardedInductionOpenSuccessorRoute_of_packed_rows
      bodyTokens hnat hstates with
    ⟨openSuccessorCoordinates, hopenSuccessorRoute⟩
  rcases exists_compactGuardedInductionStepRoute_of_packed_rows
      bodyTokens hnat hstates with
    ⟨stepCoordinates, hstepRoute⟩
  have houterRoute :=
    compactGuardedInductionOuterRoute_of_packed_rows bodyTokens hnat
  have hopenZeroLiteral : CompactAdditiveLiteralNatListRows
      tokenTable width tokenCount
        (compactPackedNatListSlot chunks 2 data.openZeroWitness).start
        (compactPackedNatListSlot chunks 2 data.openZeroWitness).count
        compactSuccIndOpenZeroWitnessTokens := by
    apply (compactAdditiveLiteralNatListRows_iff_eq
      hnat.openZeroWitness.layout hnat.openZeroWitness.1).2
    rfl
  have hopenSuccessorLiteral : CompactAdditiveLiteralNatListRows
      tokenTable width tokenCount
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness).start
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness).count
        compactSuccIndOpenSuccessorWitnessTokens := by
    apply (compactAdditiveLiteralNatListRows_iff_eq
      hnat.openSuccessorWitness.layout hnat.openSuccessorWitness.1).2
    rfl
  let coordinates : CompactSuccIndSentenceRouteCoordinates :=
    { base := baseCoordinates
      openZero := openZeroCoordinates
      openSuccessor := openSuccessorCoordinates
      step := stepCoordinates }
  exact ⟨coordinates, hbaseRoute, hopenZeroLiteral, hopenZeroRoute,
    hopenSuccessorLiteral, hopenSuccessorRoute, hstepRoute, houterRoute⟩

set_option maxHeartbeats 250000 in
theorem exists_compactGuardedInductionFvSupRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactFormulaFvSupTotalEndpointCoordinates,
      CompactFormulaFvSupTotalEndpoint tokenTable width tokenCount
        0 data.depth
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactFormulaFvSupTotalEndpointCoordinates,
    CompactFormulaFvSupTotalEndpoint tokenTable width tokenCount
      0 data.depth
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList)
      coordinates
  exact exists_compactFormulaFvSupTotalEndpoint_of_executable_output
    hnat.empty hnat.sentence hnat.fvarList hstates.fvarList
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform,
        compactGuardedInductionEmpty] using
      compactGuardedInductionFvarList_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionDepth_eq bodyTokens)

set_option maxHeartbeats 250000 in
theorem exists_compactGuardedInductionClosureRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactFixedAllClosureTotalEndpointCoordinates,
      CompactFixedAllClosureTotalEndpoint tokenTable width tokenCount
        data.depth
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated)
        coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactFixedAllClosureTotalEndpointCoordinates,
    CompactFixedAllClosureTotalEndpoint tokenTable width tokenCount
      data.depth
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated)
      coordinates
  exact exists_compactFixedAllClosureTotalEndpoint_of_executable_output
    hnat.empty hnat.depthCapture hnat.sentence hnat.fixed hnat.generated
    hstates.closure
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionDepthCapture_length bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData,
        compactGuardedInductionExactTransform] using
      compactGuardedInductionFixed_eq bodyTokens)
    (by simpa only [data, compactGuardedInductionExecutableData] using
      compactGuardedInductionGenerated_eq bodyTokens)

set_option maxHeartbeats 300000 in
theorem exists_compactGuardedInductionSentenceRoute_of_packed_rows
    (bodyTokens : List Nat)
    {tokenTable width tokenCount : Nat} {chunks : List (List Nat)}
    (hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens))
    (hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokenCount chunks
        (compactGuardedInductionExecutableData bodyTokens)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    ∃ coordinates : CompactGuardedInductionSentenceRouteCoordinates,
      CompactGuardedInductionSentenceRoute
        tokenTable width tokenCount data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated)
        coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  change CompactGuardedInductionPackedNatRows
    tokenTable width tokenCount chunks data at hnat
  change CompactGuardedInductionPackedStateRows
    tokenTable width tokenCount chunks data at hstates
  change ∃ coordinates : CompactGuardedInductionSentenceRouteCoordinates,
    CompactGuardedInductionSentenceRoute
      tokenTable width tokenCount data.depth
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated)
      coordinates
  rcases exists_compactGuardedInductionSuccIndRoute_of_packed_rows
      bodyTokens hnat hstates with
    ⟨sentenceCoordinates, hsentenceRoute⟩
  rcases exists_compactGuardedInductionFvSupRoute_of_packed_rows
      bodyTokens hnat hstates with
    ⟨fvSupCoordinates, hfvSupRoute⟩
  rcases exists_compactGuardedInductionClosureRoute_of_packed_rows
      bodyTokens hnat hstates with
    ⟨closureCoordinates, hclosureRoute⟩
  let coordinates : CompactGuardedInductionSentenceRouteCoordinates :=
    { sentence := sentenceCoordinates
      fvSup := fvSupCoordinates
      closure := closureCoordinates }
  exact ⟨coordinates, hsentenceRoute, hfvSupRoute, hclosureRoute⟩
set_option maxHeartbeats 600000 in
theorem exists_compactGuardedInductionSentenceRoute_of_executable_body
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∃ coordinates : CompactGuardedInductionSentenceRouteCoordinates,
      CompactGuardedInductionSentenceRoute
        tokenTable width tokens.length data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated)
        coordinates := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∃ coordinates : CompactGuardedInductionSentenceRouteCoordinates,
    CompactGuardedInductionSentenceRoute
      tokenTable width tokens.length data.depth
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated)
      coordinates
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedStateRows_canonical data extraChunks
  exact exists_compactGuardedInductionSentenceRoute_of_packed_rows
    bodyTokens hnat hstates
#print axioms
  exists_compactGuardedInductionSentenceRoute_of_executable_body

end FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness
