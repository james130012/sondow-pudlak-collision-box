import integration.FoundationCompactNumericListedDirectParserSyntaxStepDoneClosedFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxStepEmptyClosedFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxStepRepeatClosedFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxStepTermClosedFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaClosedFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxStepInvalidClosedFixedBound

/-! # One closed fixed resource for all six SyntaxStep branches -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBounds

open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase
open FoundationCompactNumericListedDirectParserSyntaxStepDoneClosedFixedBound
open FoundationCompactNumericListedDirectParserSyntaxStepEmptyClosedFixedBound
open FoundationCompactNumericListedDirectParserSyntaxStepRepeatClosedFixedBound
open FoundationCompactNumericListedDirectParserSyntaxStepTermClosedFixedBound
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaClosedFixedBound
open FoundationCompactNumericListedDirectParserSyntaxStepInvalidClosedFixedBound

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

noncomputable def compactUnifiedParserSyntaxStepFullyFixedBoundFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (data : CompactUnifiedParserSyntaxStepCheckedBranchData tokenTable width
      tokenCount current next witness)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hwitnessValue :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound witness
        numericBound)
    (hwitnessSize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound stepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepAllBranchesClosedFixedResource tokenCount numericBound
        bitBound) := by
  let context :
      CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
        tokenCount current next witness numericBound bitBound :=
    { width_le := hwidth
      width_le_bit := hwidthBit
      tokenCount_le := htokenCount
      currentValue := hcurrentValue
      nextValue := hnextValue
      tokenTableSize := htokenTableSize
      currentSize := hcurrentSize
      nextSize := hnextSize
      witnessValue := hwitnessValue
      witnessSize := hwitnessSize
      numericSize := hnumericSize
      bitPositive := hbitPositive }
  cases data with
  | done hgraph =>
      let bound :=
        compactUnifiedParserSyntaxStepDoneClosedFixedBound tokenTable width
          tokenCount current next witness numericBound bitBound context hgraph
      exact ⟨bound.proof, bound.payloadLength_le.trans (by
        simp [syntaxStepAllBranchesClosedFixedResource])⟩
  | empty hgraph =>
      let bound :=
        compactUnifiedParserSyntaxStepEmptyClosedFixedBound tokenTable width
          tokenCount current next witness numericBound bitBound context hgraph
      exact ⟨bound.proof, bound.payloadLength_le.trans (by
        simp [syntaxStepAllBranchesClosedFixedResource])⟩
  | repeatBranch hgraph =>
      let bound :=
        compactUnifiedParserSyntaxStepRepeatClosedFixedBound tokenTable width
          tokenCount current next witness numericBound bitBound context hgraph
      exact ⟨bound.proof, bound.payloadLength_le.trans (by
        simp [syntaxStepAllBranchesClosedFixedResource])⟩
  | term hgraph =>
      let bound :=
        compactUnifiedParserSyntaxStepTermClosedFixedBound tokenTable width
          tokenCount current next witness numericBound bitBound context hgraph
      exact ⟨bound.proof, bound.payloadLength_le.trans (by
        simp [syntaxStepAllBranchesClosedFixedResource])⟩
  | formula hgraph =>
      let bound :=
        compactUnifiedParserSyntaxStepFormulaClosedFixedBound tokenTable width
          tokenCount current next witness numericBound bitBound context hgraph
      exact ⟨bound.proof, bound.payloadLength_le.trans (by
        simp [syntaxStepAllBranchesClosedFixedResource])⟩
  | invalid hgraph =>
      let bound :=
        compactUnifiedParserSyntaxStepInvalidClosedFixedBound tokenTable width
          tokenCount current next witness numericBound bitBound context hgraph
      exact ⟨bound.proof, bound.payloadLength_le.trans (by
        simp [syntaxStepAllBranchesClosedFixedResource])⟩

noncomputable def compactUnifiedParserSyntaxStepFullyFixedBoundOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount
      current next witness)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hwitnessValue :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound witness
        numericBound)
    (hwitnessSize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound stepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepAllBranchesClosedFixedResource tokenCount numericBound
        bitBound) :=
  compactUnifiedParserSyntaxStepFullyFixedBoundFromData tokenTable width
    tokenCount current next witness numericBound bitBound
    (compactUnifiedParserSyntaxStepCheckedBranchDataOfGraph tokenTable width
      tokenCount current next witness hgraph)
    hwidth hwidthBit htokenCount hcurrentValue hnextValue htokenTableSize
    hcurrentSize hnextSize hwitnessValue hwitnessSize hnumericSize hbitPositive

end FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBounds
