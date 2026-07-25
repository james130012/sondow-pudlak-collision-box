import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds

/-!
# Graph-free syntax bounds for the outer syntax-formula branch

This closes the complete `empty ⋎ enough` formula syntax independently of
which execution branch is selected.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds

def syntaxFormulaEmptyFullyFixedCodePolynomial (bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 8

def syntaxFormulaEnoughFullyFixedCodePolynomial (bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    (natListAtRowsFixedIndexFormulaCodePolynomial bitBound +
      syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound + 8) + 8

def syntaxFormulaOuterFullyFixedCodePolynomial (bitBound : Nat) : Nat :=
  syntaxFormulaEmptyFullyFixedCodePolynomial bitBound +
    syntaxFormulaEnoughFullyFixedCodePolynomial bitBound + 8

private theorem syntaxFormulaAddCodeBounds
    {left right leftBound rightBound : Nat}
    (hleft : left <= leftBound) (hright : right <= rightBound) :
    left + right + 8 <= leftBound + rightBound + 8 := by
  omega

def syntaxFormulaEmptyFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  nativeEqFormula current.tokensCount 0 ⋏
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount

def syntaxFormulaEnoughFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  nativeShortLeFormula 1 current.tokensCount ⋏
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount witness.tag
        (fixedNumeralTerm 0) ⋏
      compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness

theorem syntaxFormulaOuterFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness =
      syntaxFormulaEmptyFormula tokenTable width tokenCount current next
          witness ⋎
        syntaxFormulaEnoughFormula tokenTable width tokenCount current next
          binderArity witness := by
  rfl

theorem syntaxFormulaEmptyFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htailCountSize : Nat.size witness.tailCount <= bitBound) :
    (binaryFormulaCode
      (syntaxFormulaEmptyFormula tokenTable width tokenCount current next
        witness)).length <=
      syntaxFormulaEmptyFullyFixedCodePolynomial bitBound := by
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hcountLeaf :=
    nativeEqFormula_code_length_le_fixed current.tokensCount 0 bitBound
      hcurrentTokensCountSize (by omega)
  have hcount :
      (binaryFormulaCode (nativeEqFormula current.tokensCount 0)).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound :=
    hcountLeaf.trans (by
      unfold parserFormulaAtomicFormulaCodePolynomial
      omega)
  have hfailure :=
    syntaxTermFailureClosedFormula_code_length_le_substitutionFixed tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      bitBound htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize
  unfold syntaxFormulaEmptyFormula
  exact
    (binaryFormulaCode_and_length_le
      (nativeEqFormula current.tokensCount 0)
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)).trans
      (by
        unfold syntaxFormulaEmptyFullyFixedCodePolynomial
        exact syntaxFormulaAddCodeBounds hcount hfailure)

theorem syntaxFormulaEnoughFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htailCountSize : Nat.size witness.tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (binaryFormulaCode
      (syntaxFormulaEnoughFormula tokenTable width tokenCount current next
        binderArity witness)).length <=
      syntaxFormulaEnoughFullyFixedCodePolynomial bitBound := by
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hcount :=
    nativeShortLeFormula_code_length_le_fixed 1 current.tokensCount bitBound
      (by omega) hcurrentTokensCountSize
  have hatTag :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_code_length_le_fixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      witness.tag 0 bitBound htokenTableSize hwidthSize htokenCountSize
      hcurrentTokensBoundarySize hcurrentTokensCountSize htagSize (by omega)
  have htagBranch :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  have htail :=
    (binaryFormulaCode_and_length_le
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount witness.tag
        (fixedNumeralTerm 0))
      (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
        width tokenCount current next binderArity witness)).trans
      (syntaxFormulaAddCodeBounds hatTag htagBranch)
  unfold syntaxFormulaEnoughFormula
  exact
    (binaryFormulaCode_and_length_le
      (nativeShortLeFormula 1 current.tokensCount)
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
          tokenCount current.tokensBoundary current.tokensCount witness.tag
          (fixedNumeralTerm 0) ⋏
        compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
          width tokenCount current next binderArity witness)).trans
      (by
        unfold syntaxFormulaEnoughFullyFixedCodePolynomial
        exact syntaxFormulaAddCodeBounds hcount htail)

theorem syntaxFormulaOuterFormula_code_length_le_of_parts
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (bitBound : Nat)
    (hempty :
      (binaryFormulaCode
        (syntaxFormulaEmptyFormula tokenTable width tokenCount current next
          witness)).length <=
        syntaxFormulaEmptyFullyFixedCodePolynomial bitBound)
    (henough :
      (binaryFormulaCode
        (syntaxFormulaEnoughFormula tokenTable width tokenCount current next
          binderArity witness)).length <=
        syntaxFormulaEnoughFullyFixedCodePolynomial bitBound) :
    (binaryFormulaCode
      (syntaxFormulaEmptyFormula tokenTable width tokenCount current next
          witness ⋎
        syntaxFormulaEnoughFormula tokenTable width tokenCount current next
          binderArity witness)).length <=
      syntaxFormulaOuterFullyFixedCodePolynomial bitBound := by
  exact
    (binaryFormulaCode_or_length_le
      (syntaxFormulaEmptyFormula tokenTable width tokenCount current next
        witness)
      (syntaxFormulaEnoughFormula tokenTable width tokenCount current next
        binderArity witness)).trans
      (by
        unfold syntaxFormulaOuterFullyFixedCodePolynomial
        exact syntaxFormulaAddCodeBounds hempty henough)

theorem
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htailCountSize : Nat.size witness.tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness)).length <=
      syntaxFormulaOuterFullyFixedCodePolynomial bitBound := by
  rw [syntaxFormulaOuterFormula_alignment]
  apply syntaxFormulaOuterFormula_code_length_le_of_parts tokenTable width
    tokenCount current next binderArity witness bitBound
  · exact syntaxFormulaEmptyFormula_code_length_le_fullyFixed tokenTable width
      tokenCount current next witness bitBound htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize htailCountSize
  · exact syntaxFormulaEnoughFormula_code_length_le_fullyFixed tokenTable width
      tokenCount current next binderArity witness bitBound htokenTableSize
      hwidthSize htokenCountSize hcurrentSize hnextSize htailBoundarySize
      htailCountSize hbinderAritySize hrelationAritySize hrelationCodeSize
      htagSize hbitPositive

theorem
    syntaxFormulaEmptyFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    (syntaxFormulaEmptyFormula tokenTable width tokenCount current next
      witness).freeVariables = ∅ := by
  unfold syntaxFormulaEmptyFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    nativeEqFormula_freeVariables_eq_empty_fixed,
    syntaxTermFailureClosedFormula_freeVariables_eq_empty_substitutionFixed]
  simp

theorem
    syntaxFormulaEnoughFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    (syntaxFormulaEnoughFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅ := by
  unfold syntaxFormulaEnoughFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    nativeShortLeFormula_freeVariables_eq_empty_fixed,
    LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed]
  simp

theorem
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
      tokenCount current next binderArity witness).freeVariables = ∅ := by
  rw [syntaxFormulaOuterFormula_alignment,
    LO.FirstOrder.Semiformula.freeVariables_or,
    syntaxFormulaEmptyFormula_freeVariables_eq_empty_fullyFixed,
    syntaxFormulaEnoughFormula_freeVariables_eq_empty_fullyFixed]
  simp

end FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds
