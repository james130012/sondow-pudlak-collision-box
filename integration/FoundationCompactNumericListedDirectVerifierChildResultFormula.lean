import integration.FoundationCompactNumericListedDirectVerifierStateLayout
import integration.FoundationCompactNumericListedDirectNatListListRowsFormula

/-!
# Bounded arithmetic core for one verifier child result

A child result is a nested context list followed by one Boolean.  The formula
uses the same context-row graph as verifier tasks and exposes the Boolean as
an exact additive token cell.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierChildResultFormula

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula

structure CompactNumericChildResultRowCoordinates where
  start : Nat
  finish : Nat
  gammaFinish : Nat
  gammaCount : Nat
  gammaBoundary : Nat
  boolValue : Nat

structure CompactNumericChildResultSizeWitness where
  gammaBoundarySize : Nat

def compactNumericChildResultRowCoordinatesOf
    (start finish gammaFinish gammaCount gammaBoundary boolValue : Nat) :
    CompactNumericChildResultRowCoordinates where
  start := start
  finish := finish
  gammaFinish := gammaFinish
  gammaCount := gammaCount
  gammaBoundary := gammaBoundary
  boolValue := boolValue

def CompactNumericChildResultCoreGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericChildResultRowCoordinates)
    (sizeWitness : CompactNumericChildResultSizeWitness) : Prop :=
  CompactAdditiveStructuredListLayout tokenTable width tokenCount
      coordinates.start coordinates.gammaCount
      coordinates.gammaFinish coordinates.gammaBoundary ∧
    CompactAdditiveNatListListRowsWellFormed tokenTable width tokenCount
      coordinates.gammaBoundary coordinates.gammaCount ∧
    sizeWitness.gammaBoundarySize = Nat.size coordinates.gammaBoundary ∧
    sizeWitness.gammaBoundarySize ≤
      (coordinates.gammaCount + 1) * tokenCount ∧
    CompactAdditiveBoolSlice tokenTable width tokenCount
      coordinates.gammaFinish coordinates.boolValue coordinates.finish

def compactNumericChildResultCoreGraphDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount start finish
      gammaFinish gammaCount gammaBoundary boolValue gammaBoundarySize.
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount start gammaCount
        gammaFinish gammaBoundary ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount gammaBoundary gammaCount ∧
    !(compactNatSizeDef) gammaBoundarySize gammaBoundary ∧
    gammaBoundarySize ≤ (gammaCount + 1) * tokenCount ∧
    !(compactAdditiveBoolSliceDef)
      tokenTable width tokenCount gammaFinish boolValue finish”

def compactNumericChildResultCoreFormulaEnvironment
    (tokenTable width tokenCount start finish
      gammaFinish gammaCount gammaBoundary boolValue gammaBoundarySize : Nat) :
    Fin 10 → Nat :=
  ![tokenTable, width, tokenCount, start, finish,
    gammaFinish, gammaCount, gammaBoundary, boolValue, gammaBoundarySize]

@[simp] theorem compactNumericChildResultCoreGraphDef_spec
    (tokenTable width tokenCount start finish
      gammaFinish gammaCount gammaBoundary boolValue gammaBoundarySize : Nat) :
    compactNumericChildResultCoreGraphDef.val.Evalb
        (compactNumericChildResultCoreFormulaEnvironment
          tokenTable width tokenCount start finish
          gammaFinish gammaCount gammaBoundary boolValue gammaBoundarySize) ↔
      CompactNumericChildResultCoreGraph tokenTable width tokenCount
        (compactNumericChildResultRowCoordinatesOf
          start finish gammaFinish gammaCount gammaBoundary boolValue)
        { gammaBoundarySize := gammaBoundarySize } := by
  let env := compactNumericChildResultCoreFormulaEnvironment
    tokenTable width tokenCount start finish
    gammaFinish gammaCount gammaBoundary boolValue gammaBoundarySize
  change compactNumericChildResultCoreGraphDef.val.Evalb env ↔ _
  have hgammaLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, #2, #3, #6, #5, #7]) =
        ![tokenTable, width, tokenCount, start,
          gammaCount, gammaFinish, gammaBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hgammaRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, #2, #7, #6]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount] := by
    funext index
    fin_cases index <;> rfl
  have hsizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#9 : Semiterm ℒₒᵣ Empty 10), #7]) =
        ![gammaBoundarySize, gammaBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hboolEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, #2, #5, #8, #4]) =
        ![tokenTable, width, tokenCount, gammaFinish, boolValue, finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have hgammaCountValue : env 6 = gammaCount := rfl
  have hgammaBoundarySizeValue : env 9 = gammaBoundarySize := rfl
  simp [compactNumericChildResultCoreGraphDef,
    compactNumericChildResultRowCoordinatesOf,
    CompactNumericChildResultCoreGraph,
    hgammaLayoutEnv, hgammaRowsEnv, hsizeEnv, hboolEnv,
    htokenCountValue, hgammaCountValue, hgammaBoundarySizeValue]

theorem compactNumericChildResultCoreGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultCoreGraphDef.val := by
  simp [compactNumericChildResultCoreGraphDef]

theorem CompactNumericChildResultDirectLayout.toCoreGraph
    {tokenTable width tokenCount start finish : Nat}
    {value : CompactNumericChildResult}
    (hlayout : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount start finish value) :
    ∃ coordinates sizeWitness,
      coordinates.start = start ∧
      coordinates.finish = finish ∧
      coordinates.boolValue = compactAdditiveBoolTag value.2 ∧
      CompactNumericChildResultCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases hlayout with
    ⟨gammaFinish, gammaBoundary, boolValue,
      _hproduct, hgammaLayout, hgammaRows,
      hboolValue, hbool, hgammaSize⟩
  let coordinates : CompactNumericChildResultRowCoordinates :=
    { start := start
      finish := finish
      gammaFinish := gammaFinish
      gammaCount := value.1.length
      gammaBoundary := gammaBoundary
      boolValue := boolValue }
  let sizeWitness : CompactNumericChildResultSizeWitness :=
    { gammaBoundarySize := Nat.size gammaBoundary }
  refine ⟨coordinates, sizeWitness, rfl, rfl, hboolValue, ?_⟩
  exact ⟨hgammaLayout,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hgammaRows,
    rfl, hgammaSize, hbool⟩

structure CompactNumericChildResultCoreBounds
    (tokenCount : Nat)
    (coordinates : CompactNumericChildResultRowCoordinates)
    (sizeWitness : CompactNumericChildResultSizeWitness) : Prop where
  start_le : coordinates.start ≤ tokenCount
  finish_le : coordinates.finish ≤ tokenCount
  gammaFinish_le : coordinates.gammaFinish ≤ tokenCount
  gammaCount_le : coordinates.gammaCount ≤ tokenCount
  gammaBoundary_size_le :
    Nat.size coordinates.gammaBoundary ≤
      (coordinates.gammaCount + 1) * tokenCount
  gammaBoundarySize_le :
    sizeWitness.gammaBoundarySize ≤
      (coordinates.gammaCount + 1) * tokenCount
  boolValue_le_one : coordinates.boolValue ≤ 1

theorem CompactNumericChildResultCoreGraph.bounds
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericChildResultRowCoordinates}
    {sizeWitness : CompactNumericChildResultSizeWitness}
    (hgraph : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    CompactNumericChildResultCoreBounds
      tokenCount coordinates sizeWitness := by
  rcases hgraph with
    ⟨hgamma, _hgammaRows, hgammaSizeEq, hgammaSize, hbool⟩
  rcases hgamma with
    ⟨gammaBodyStart, _hgammaBodyStart, hgammaHeader,
      hgammaBoundary⟩
  have hstartLt : coordinates.start < tokenCount := hgammaHeader.1.1
  have hgammaCountBound :
      gammaBodyStart + coordinates.gammaCount ≤ tokenCount :=
    hgammaHeader.2
  have hfinishEq : coordinates.finish = coordinates.gammaFinish + 1 :=
    hbool.1.2.1
  have hgammaFinishLt : coordinates.gammaFinish < tokenCount := hbool.1.1
  exact
    { start_le := by omega
      finish_le := by omega
      gammaFinish_le := hgammaBoundary.2.1
      gammaCount_le := by omega
      gammaBoundary_size_le := by
        rw [← hgammaSizeEq]
        exact hgammaSize
      gammaBoundarySize_le := hgammaSize
      boolValue_le_one := by
        rcases hbool.2 with hzero | hone <;> omega }

#print axioms compactNumericChildResultCoreGraphDef_spec
#print axioms compactNumericChildResultCoreGraphDef_sigmaZero
#print axioms CompactNumericChildResultDirectLayout.toCoreGraph
#print axioms CompactNumericChildResultCoreGraph.bounds

end FoundationCompactNumericListedDirectVerifierChildResultFormula
