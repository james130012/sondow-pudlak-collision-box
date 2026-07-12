import integration.FoundationCompactNumericListedDirectAtomicListRowRealization
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepRows

/-!
# Pure numeric core formula for one binary-natural stream state

The state row is split into its Boolean list, natural-number list, and status
interval using only numeric coordinates.  The status payload is checked by the
step formula; this module realizes the two list fields and all structural
boundaries without taking a typed state as input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStateFormula

open FoundationCompactBinaryNatStreamMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows

structure CompactBinaryNatStreamStateCoreSizeWitness where
  bitsBoundarySize : Nat
  decodedBoundarySize : Nat

def compactBinaryNatStreamStateRowCoordinatesOf
    (start finish bitsFinish decodedFinish bitsBoundary bitsCount
      decodedBoundary decodedCount : Nat) :
    CompactBinaryNatStreamRowCoordinates where
  start := start
  finish := finish
  bitsFinish := bitsFinish
  decodedFinish := decodedFinish
  bitsBoundary := bitsBoundary
  bitsCount := bitsCount
  decodedBoundary := decodedBoundary
  decodedCount := decodedCount

def CompactBinaryNatStreamStateCoreGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactBinaryNatStreamRowCoordinates)
    (sizeWitness : CompactBinaryNatStreamStateCoreSizeWitness) : Prop :=
  CompactAdditiveProductSplit
      tokenCount coordinates.start coordinates.bitsFinish
        coordinates.finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.start coordinates.bitsCount
        coordinates.bitsFinish coordinates.bitsBoundary ∧
    CompactAdditiveBoolListRowsWellFormed
      tokenTable width tokenCount coordinates.bitsBoundary
        coordinates.bitsCount ∧
    CompactAdditiveProductSplit
      tokenCount coordinates.bitsFinish coordinates.decodedFinish
        coordinates.finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.bitsFinish
        coordinates.decodedCount coordinates.decodedFinish
        coordinates.decodedBoundary ∧
    CompactAdditiveUnitBoundaryRows
      tokenCount coordinates.decodedCount coordinates.decodedBoundary ∧
    sizeWitness.bitsBoundarySize = Nat.size coordinates.bitsBoundary ∧
    sizeWitness.bitsBoundarySize ≤
      (coordinates.bitsCount + 1) * tokenCount ∧
    sizeWitness.decodedBoundarySize = Nat.size coordinates.decodedBoundary ∧
    sizeWitness.decodedBoundarySize ≤
      (coordinates.decodedCount + 1) * tokenCount

def compactBinaryNatStreamStateCoreGraphDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount
      start finish bitsFinish decodedFinish
      bitsBoundary bitsCount decodedBoundary decodedCount
      bitsBoundarySize decodedBoundarySize.
    !(compactAdditiveProductSplitDef)
      tokenCount start bitsFinish finish ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount start bitsCount bitsFinish bitsBoundary ∧
    !(compactAdditiveBoolListRowsWellFormedDef)
      tokenTable width tokenCount bitsBoundary bitsCount ∧
    !(compactAdditiveProductSplitDef)
      tokenCount bitsFinish decodedFinish finish ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount bitsFinish decodedCount
        decodedFinish decodedBoundary ∧
    !(compactAdditiveUnitBoundaryRowsDef)
      tokenCount decodedCount decodedBoundary ∧
    !(compactNatSizeDef) bitsBoundarySize bitsBoundary ∧
    bitsBoundarySize ≤ (bitsCount + 1) * tokenCount ∧
    !(compactNatSizeDef) decodedBoundarySize decodedBoundary ∧
    decodedBoundarySize ≤ (decodedCount + 1) * tokenCount”

def compactBinaryNatStreamStateCoreFormulaEnvironment
    (tokenTable width tokenCount
      start finish bitsFinish decodedFinish
      bitsBoundary bitsCount decodedBoundary decodedCount
      bitsBoundarySize decodedBoundarySize : Nat) : Fin 13 → Nat :=
  ![tokenTable, width, tokenCount,
    start, finish, bitsFinish, decodedFinish,
    bitsBoundary, bitsCount, decodedBoundary, decodedCount,
    bitsBoundarySize, decodedBoundarySize]

@[simp] theorem compactBinaryNatStreamStateCoreGraphDef_spec
    (tokenTable width tokenCount
      start finish bitsFinish decodedFinish
      bitsBoundary bitsCount decodedBoundary decodedCount
      bitsBoundarySize decodedBoundarySize : Nat) :
    compactBinaryNatStreamStateCoreGraphDef.val.Evalb
        (compactBinaryNatStreamStateCoreFormulaEnvironment
          tokenTable width tokenCount
          start finish bitsFinish decodedFinish
          bitsBoundary bitsCount decodedBoundary decodedCount
          bitsBoundarySize decodedBoundarySize) ↔
      CompactBinaryNatStreamStateCoreGraph tokenTable width tokenCount
        (compactBinaryNatStreamStateRowCoordinatesOf
          start finish bitsFinish decodedFinish
          bitsBoundary bitsCount decodedBoundary decodedCount)
        { bitsBoundarySize := bitsBoundarySize
          decodedBoundarySize := decodedBoundarySize } := by
  let env := compactBinaryNatStreamStateCoreFormulaEnvironment
    tokenTable width tokenCount
    start finish bitsFinish decodedFinish
    bitsBoundary bitsCount decodedBoundary decodedCount
    bitsBoundarySize decodedBoundarySize
  change compactBinaryNatStreamStateCoreGraphDef.val.Evalb env ↔ _
  have houterEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 13), #3, #5, #4]) =
        ![tokenCount, start, bitsFinish, finish] := by
    funext index
    fin_cases index <;> rfl
  have hbitsLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #3, #8, #5, #7]) =
        ![tokenTable, width, tokenCount,
          start, bitsCount, bitsFinish, bitsBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hbitsRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #7, #8]) =
        ![tokenTable, width, tokenCount, bitsBoundary, bitsCount] := by
    funext index
    fin_cases index <;> rfl
  have hinnerEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 13), #5, #6, #4]) =
        ![tokenCount, bitsFinish, decodedFinish, finish] := by
    funext index
    fin_cases index <;> rfl
  have hdecodedLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #5, #10, #6, #9]) =
        ![tokenTable, width, tokenCount,
          bitsFinish, decodedCount, decodedFinish, decodedBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hdecodedRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 13), #10, #9]) =
        ![tokenCount, decodedCount, decodedBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hbitsSizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#11 : Semiterm ℒₒᵣ Empty 13), #7]) =
        ![bitsBoundarySize, bitsBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hdecodedSizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#12 : Semiterm ℒₒᵣ Empty 13), #9]) =
        ![decodedBoundarySize, decodedBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have hbitsCountValue : env 8 = bitsCount := rfl
  have hdecodedCountValue : env 10 = decodedCount := rfl
  have hbitsBoundarySizeValue : env 11 = bitsBoundarySize := rfl
  have hdecodedBoundarySizeValue : env 12 = decodedBoundarySize := rfl
  simp [compactBinaryNatStreamStateCoreGraphDef,
    compactBinaryNatStreamStateRowCoordinatesOf,
    CompactBinaryNatStreamStateCoreGraph,
    houterEnv, hbitsLayoutEnv, hbitsRowsEnv,
    hinnerEnv, hdecodedLayoutEnv, hdecodedRowsEnv,
    hbitsSizeEnv, hdecodedSizeEnv,
    htokenCountValue, hbitsCountValue, hdecodedCountValue,
    hbitsBoundarySizeValue, hdecodedBoundarySizeValue]

theorem compactBinaryNatStreamStateCoreGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamStateCoreGraphDef.val := by
  simp [compactBinaryNatStreamStateCoreGraphDef]

structure CompactBinaryNatStreamStateCoreFixedLayout
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactBinaryNatStreamRowCoordinates)
    (bits : List Bool) (decoded : List Nat) : Prop where
  bitsCount_eq : coordinates.bitsCount = bits.length
  decodedCount_eq : coordinates.decodedCount = decoded.length
  outerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.start coordinates.bitsFinish coordinates.finish
  bitsLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.start coordinates.bitsCount
      coordinates.bitsFinish coordinates.bitsBoundary
  bitsRows : CompactAdditiveStructuredListElementRowLayouts
    CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      coordinates.bitsBoundary bits
  innerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.bitsFinish coordinates.decodedFinish
      coordinates.finish
  decodedLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.bitsFinish
      coordinates.decodedCount coordinates.decodedFinish
      coordinates.decodedBoundary
  decodedRows : CompactAdditiveStructuredListElementRowLayouts
    CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      coordinates.decodedBoundary decoded
  bitsBoundarySize : Nat.size coordinates.bitsBoundary ≤
    (coordinates.bitsCount + 1) * tokenCount
  decodedBoundarySize : Nat.size coordinates.decodedBoundary ≤
    (coordinates.decodedCount + 1) * tokenCount

theorem CompactBinaryNatStreamStateFixedLayout.coreFixedLayout
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactBinaryNatStreamRowCoordinates}
    {state : BinaryNatStreamState}
    (hlayout : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount coordinates state) :
    CompactBinaryNatStreamStateCoreFixedLayout
      tokenTable width tokenCount coordinates state.1 state.2.1 where
  bitsCount_eq := hlayout.bitsCount_eq
  decodedCount_eq := hlayout.decodedCount_eq
  outerSplit := hlayout.outerSplit
  bitsLayout := hlayout.bitsLayout
  bitsRows := hlayout.bitsRows
  innerSplit := hlayout.innerSplit
  decodedLayout := hlayout.decodedLayout
  decodedRows := hlayout.decodedRows
  bitsBoundarySize := hlayout.bitsBoundarySize
  decodedBoundarySize := hlayout.decodedBoundarySize

theorem CompactBinaryNatStreamStateCoreFixedLayout.toCoreGraph
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactBinaryNatStreamRowCoordinates}
    {bits : List Bool} {decoded : List Nat}
    (hlayout : CompactBinaryNatStreamStateCoreFixedLayout
      tokenTable width tokenCount coordinates bits decoded) :
    ∃ sizeWitness,
      CompactBinaryNatStreamStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  let sizeWitness : CompactBinaryNatStreamStateCoreSizeWitness :=
    { bitsBoundarySize := Nat.size coordinates.bitsBoundary
      decodedBoundarySize := Nat.size coordinates.decodedBoundary }
  refine ⟨sizeWitness, hlayout.outerSplit, hlayout.bitsLayout, ?_,
    hlayout.innerSplit, hlayout.decodedLayout, ?_, rfl,
    hlayout.bitsBoundarySize, rfl, hlayout.decodedBoundarySize⟩
  · simpa only [hlayout.bitsCount_eq] using
      CompactAdditiveStructuredListElementRowLayouts.boolRowsWellFormed
        hlayout.bitsRows
  · simpa only [hlayout.decodedCount_eq] using
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hlayout.decodedRows

theorem CompactBinaryNatStreamStateCoreGraph.realize
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactBinaryNatStreamRowCoordinates}
    {sizeWitness : CompactBinaryNatStreamStateCoreSizeWitness}
    (hgraph : CompactBinaryNatStreamStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ bits decoded,
      CompactBinaryNatStreamStateCoreFixedLayout
        tokenTable width tokenCount coordinates bits decoded := by
  let bits := compactAdditiveBoolListRowValues
    tokenTable width tokenCount
      coordinates.bitsBoundary coordinates.bitsCount
  let decoded := compactAdditiveNatListRowValues
    tokenTable width tokenCount
      coordinates.decodedBoundary coordinates.decodedCount
  rcases hgraph with
    ⟨houter, hbitsLayout, hbitsRows,
      hinner, hdecodedLayout, hdecodedRows,
      hbitsSizeEq, hbitsSize,
      hdecodedSizeEq, hdecodedSize⟩
  refine ⟨bits, decoded,
    { bitsCount_eq := by simp [bits]
      decodedCount_eq := by simp [decoded]
      outerSplit := houter
      bitsLayout := hbitsLayout
      bitsRows := ?_
      innerSplit := hinner
      decodedLayout := hdecodedLayout
      decodedRows := ?_
      bitsBoundarySize := ?_
      decodedBoundarySize := ?_ }⟩
  · exact CompactAdditiveBoolListRowsWellFormed.realizedRows hbitsRows
  · exact CompactAdditiveUnitBoundaryRows.realizedNatRows hdecodedRows
  · rw [← hbitsSizeEq]
    exact hbitsSize
  · rw [← hdecodedSizeEq]
    exact hdecodedSize

theorem CompactBinaryNatStreamStateCoreFixedLayout.withStatus
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactBinaryNatStreamRowCoordinates}
    {bits : List Bool} {decoded : List Nat}
    {status : Option (Option (List Nat))}
    (hcore : CompactBinaryNatStreamStateCoreFixedLayout
      tokenTable width tokenCount coordinates bits decoded)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount coordinates.decodedFinish
        coordinates.finish status) :
    CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount coordinates (bits, decoded, status) where
  bitsCount_eq := hcore.bitsCount_eq
  decodedCount_eq := hcore.decodedCount_eq
  outerSplit := hcore.outerSplit
  bitsLayout := hcore.bitsLayout
  bitsRows := hcore.bitsRows
  innerSplit := hcore.innerSplit
  decodedLayout := hcore.decodedLayout
  decodedRows := hcore.decodedRows
  statusLayout := hstatus
  bitsBoundarySize := hcore.bitsBoundarySize
  decodedBoundarySize := hcore.decodedBoundarySize

#print axioms compactBinaryNatStreamStateCoreGraphDef_spec
#print axioms compactBinaryNatStreamStateCoreGraphDef_sigmaZero
#print axioms CompactBinaryNatStreamStateFixedLayout.coreFixedLayout
#print axioms CompactBinaryNatStreamStateCoreFixedLayout.toCoreGraph
#print axioms CompactBinaryNatStreamStateCoreGraph.realize
#print axioms CompactBinaryNatStreamStateCoreFixedLayout.withStatus

end FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
