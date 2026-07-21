import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactPABitMembershipValuationContextCompilerBounds
import integration.FoundationCompactPABitMembershipTraceBudgetBounds
import integration.FoundationCompactPAContextCostPolynomialBounds
import integration.FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds

/-!
# Public bounds for valuation-term fixed-width entries

The first layer removes dependence on the proof of the bit equality.  A
uniform leaf envelope charges both truth values of the two bit literals and
every context connector that can occur in either Boolean branch.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipRuleCompilerBounds
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPABitMembershipTraceBudgetBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds

def fixedWidthBitLeafUniformStructuralEnvelope
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let leftTrue := binaryBitAtValuationFormula true
    leftIndexTerm leftValueTerm
  let leftFalse := binaryBitAtValuationFormula false
    leftIndexTerm leftValueTerm
  let rightTrue := binaryBitAtValuationFormula true
    rightIndexTerm rightValueTerm
  let rightFalse := binaryBitAtValuationFormula false
    rightIndexTerm rightValueTerm
  let forward := (∼leftAtom ⋎ rightAtom)
  let backward := (∼rightAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let leftTrueContext := valuationContext leftTrue.freeVariables branchValuation
  let leftFalseContext := valuationContext leftFalse.freeVariables branchValuation
  let rightTrueContext := valuationContext rightTrue.freeVariables branchValuation
  let rightFalseContext := valuationContext rightFalse.freeVariables branchValuation
  let forwardContext := valuationContext forward.freeVariables branchValuation
  let backwardContext := valuationContext backward.freeVariables branchValuation
  let targetContext := valuationContext target.freeVariables branchValuation
  compileBinaryBitLiteralAtValuationPayloadResource true branchValuation
      leftIndexTerm leftValueTerm +
    compileBinaryBitLiteralAtValuationPayloadResource false branchValuation
      leftIndexTerm leftValueTerm +
    compileBinaryBitLiteralAtValuationPayloadResource true branchValuation
      rightIndexTerm rightValueTerm +
    compileBinaryBitLiteralAtValuationPayloadResource false branchValuation
      rightIndexTerm rightValueTerm +
    weakeningFullAssemblyCost (insert leftTrue leftTrueContext) +
    weakeningFullAssemblyCost (insert leftFalse leftFalseContext) +
    weakeningFullAssemblyCost (insert rightTrue rightTrueContext) +
    weakeningFullAssemblyCost (insert rightFalse rightFalseContext) +
    weakeningFullAssemblyCost (insert leftFalse forwardContext) +
    weakeningFullAssemblyCost (insert rightTrue forwardContext) +
    weakeningFullAssemblyCost (insert rightFalse backwardContext) +
    weakeningFullAssemblyCost (insert leftTrue backwardContext) +
    disjunctionFullAssemblyCost forwardContext (∼leftAtom) rightAtom +
    disjunctionFullAssemblyCost backwardContext (∼rightAtom) leftAtom +
    weakeningFullAssemblyCost (insert forward targetContext) +
    weakeningFullAssemblyCost (insert backward targetContext) +
    conjunctionFullAssemblyCost targetContext forward backward

theorem fixedWidthBitHybridCertificate_structuralPayloadBound_le_uniform
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hbit : (termValue valuation tableTerm).testBit
        (termValue valuation indexTerm * termValue valuation widthTerm +
          bitIndex) =
      (termValue valuation valueTerm).testBit bitIndex) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthBitHybridCertificate valuation tableTerm widthTerm
          indexTerm valueTerm bitIndex hbit) <=
      fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex := by
  let expected := (termValue valuation valueTerm).testBit bitIndex
  cases hexpected : expected with
  | false =>
      dsimp only [expected] at hexpected
      simp only [fixedWidthBitHybridCertificate, hexpected]
      rw [dif_neg (show ¬(false = true) by simp)]
      simp only [hybridFormulaStructuralPayloadBound]
      dsimp only [fixedWidthBitLeafUniformStructuralEnvelope]
      simp only [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
        Bool.false_eq_true, ↓reduceIte]
      omega
  | true =>
      dsimp only [expected] at hexpected
      simp only [fixedWidthBitHybridCertificate, hexpected]
      rw [dif_pos (show True by trivial)]
      simp only [hybridFormulaStructuralPayloadBound]
      dsimp only [fixedWidthBitLeafUniformStructuralEnvelope]
      simp only [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
        Bool.false_eq_true, ↓reduceIte]
      omega

#print axioms
  fixedWidthBitHybridCertificate_structuralPayloadBound_le_uniform

/-- Public numeric scale for one fixed-width bit branch.  The numeric width
charges the unary branch variable; all other coordinates enter only through
their binary widths. -/
def fixedWidthBitPublicScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  termValue valuation widthTerm +
    Nat.size (termValue valuation tableTerm) +
    2 * Nat.size (termValue valuation widthTerm) +
    Nat.size (termValue valuation indexTerm) +
    Nat.size (termValue valuation valueTerm) + 2

theorem fixedWidthBitTermValues_size_le_publicScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hindex : bitIndex < termValue valuation widthTerm) :
    Nat.size (termValue (extendValuation bitIndex valuation)
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)) <=
        fixedWidthBitPublicScale valuation tableTerm widthTerm indexTerm
          valueTerm ∧
      Nat.size (termValue (extendValuation bitIndex valuation)
        (fixedWidthLeftBitValueTerm tableTerm)) <=
        fixedWidthBitPublicScale valuation tableTerm widthTerm indexTerm
          valueTerm ∧
      Nat.size (termValue (extendValuation bitIndex valuation)
        fixedWidthRightBitIndexTerm) <=
        fixedWidthBitPublicScale valuation tableTerm widthTerm indexTerm
          valueTerm ∧
      Nat.size (termValue (extendValuation bitIndex valuation)
        (fixedWidthRightBitValueTerm valueTerm)) <=
        fixedWidthBitPublicScale valuation tableTerm widthTerm indexTerm
          valueTerm := by
  have hmul :=
    FoundationCompactPABinaryNumeralMultiplicationBounds.natSize_mul_le
      (termValue valuation indexTerm) (termValue valuation widthTerm)
  have hadd :=
    FoundationCompactPABinaryNumeralAdditionBounds.natSize_add_le
      (termValue valuation indexTerm * termValue valuation widthTerm)
      bitIndex
  have hbitSize : Nat.size bitIndex <=
      Nat.size (termValue valuation widthTerm) :=
    Nat.size_le_size (Nat.le_of_lt hindex)
  rw [termValue_fixedWidthLeftBitIndexTerm,
    termValue_fixedWidthLeftBitValueTerm,
    termValue_fixedWidthRightBitIndexTerm,
    termValue_fixedWidthRightBitValueTerm]
  unfold fixedWidthBitPublicScale
  omega

#print axioms fixedWidthBitTermValues_size_le_publicScale

/-- Exclusive bound for both table and value bit positions in one row. -/
def fixedWidthBitSourceIndexBound
    (valuation : Nat -> Nat)
    (widthTerm indexTerm : ValuationTerm) : Nat :=
  termValue valuation indexTerm * termValue valuation widthTerm +
    termValue valuation widthTerm

def fixedWidthBitSourceCoordinateBound
    (valuation : Nat -> Nat)
    (tableTerm valueTerm : ValuationTerm) : Nat :=
  Nat.size (termValue valuation tableTerm) +
    Nat.size (termValue valuation valueTerm)

def fixedWidthBitSourcePayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  binaryBitTraceBudgetPayloadPolynomial
    (fixedWidthBitSourceCoordinateBound valuation tableTerm valueTerm)
    (fixedWidthBitSourceIndexBound valuation widthTerm indexTerm)

theorem fixedWidthLeftBitSourcePayload_le_publicPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hindex : bitIndex < termValue valuation widthTerm) :
    binaryBitLiteralPayloadPolynomial
        (termValue (extendValuation bitIndex valuation)
          (fixedWidthLeftBitIndexTerm widthTerm indexTerm))
        (termValue (extendValuation bitIndex valuation)
          (fixedWidthLeftBitValueTerm tableTerm)) <=
      fixedWidthBitSourcePayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm := by
  have hposition :
      termValue valuation indexTerm * termValue valuation widthTerm +
          bitIndex <
        fixedWidthBitSourceIndexBound valuation widthTerm indexTerm := by
    unfold fixedWidthBitSourceIndexBound
    omega
  have hvalue : Nat.size (termValue valuation tableTerm) <=
      fixedWidthBitSourceCoordinateBound valuation tableTerm valueTerm := by
    unfold fixedWidthBitSourceCoordinateBound
    omega
  rw [termValue_fixedWidthLeftBitIndexTerm,
    termValue_fixedWidthLeftBitValueTerm]
  exact binaryBitLiteralPayloadPolynomial_le_traceBudget hposition hvalue

theorem fixedWidthRightBitSourcePayload_le_publicPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hindex : bitIndex < termValue valuation widthTerm) :
    binaryBitLiteralPayloadPolynomial
        (termValue (extendValuation bitIndex valuation)
          fixedWidthRightBitIndexTerm)
        (termValue (extendValuation bitIndex valuation)
          (fixedWidthRightBitValueTerm valueTerm)) <=
      fixedWidthBitSourcePayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm := by
  have hposition : bitIndex <
      fixedWidthBitSourceIndexBound valuation widthTerm indexTerm := by
    unfold fixedWidthBitSourceIndexBound
    omega
  have hvalue : Nat.size (termValue valuation valueTerm) <=
      fixedWidthBitSourceCoordinateBound valuation tableTerm valueTerm := by
    unfold fixedWidthBitSourceCoordinateBound
    omega
  rw [termValue_fixedWidthRightBitIndexTerm,
    termValue_fixedWidthRightBitValueTerm]
  exact binaryBitLiteralPayloadPolynomial_le_traceBudget hposition hvalue

#print axioms fixedWidthLeftBitSourcePayload_le_publicPolynomial
#print axioms fixedWidthRightBitSourcePayload_le_publicPolynomial

theorem fixedWidthBitHybridBranches_leafPayloadBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitCount leafBound : Nat)
    (hbits : ∀ bitIndex < bitCount,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex)
    (hleaf : ∀ bitIndex (_hindex : bitIndex < bitCount),
      fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
          indexTerm valueTerm bitIndex <= leafBound) :
    HybridBranchesLeafPayloadBound leafBound
      (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
        valueTerm bitCount hbits) := by
  induction bitCount with
  | zero =>
      simp [fixedWidthBitHybridBranches, HybridBranchesLeafPayloadBound]
  | succ previous inductionHypothesis =>
      simp only [fixedWidthBitHybridBranches,
        HybridBranchesLeafPayloadBound]
      constructor
      · exact inductionHypothesis
          (fun bitIndex hindex =>
            hbits bitIndex
              (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
          (fun bitIndex hindex =>
            hleaf bitIndex
              (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
      · exact
          (fixedWidthBitHybridCertificate_structuralPayloadBound_le_uniform
              valuation tableTerm widthTerm indexTerm valueTerm previous
              (hbits previous (Nat.lt_succ_self previous))).trans
            (hleaf previous (Nat.lt_succ_self previous))

#print axioms fixedWidthBitHybridBranches_leafPayloadBound

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerBounds
