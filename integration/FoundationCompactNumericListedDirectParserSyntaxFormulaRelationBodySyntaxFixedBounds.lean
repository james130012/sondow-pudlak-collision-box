import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds

/-!
# Fixed syntax bound for the complete syntax-formula relation body

Every leaf of the selected and unselected branches is charged by a common
coordinate bit bound.  The result is independent of which semantic branch is
true and therefore can be shared by relation-short, relation-valid, and
relation-invalid certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds

def syntaxFormulaRelationBodyCodePolynomial
    (bitBound : Nat) : Nat :=
  2 * parserFormulaAtomicFormulaCodePolynomial bitBound +
    2 * syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound +
    syntaxTermFunctionClosedFormulaCodePolynomial bitBound +
    2 * natListAtRowsFixedIndexFormulaCodePolynomial bitBound +
    arithmeticRelCodeValidFormulaCodePolynomial bitBound +
    arithmeticRelCodeInvalidFormulaCodePolynomial bitBound + 4096

theorem
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_code_length_le_fixed
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
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
        width tokenCount current next binderArity witness)).length <=
      syntaxFormulaRelationBodyCodePolynomial bitBound := by
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let functionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity
  let atArityFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1)
  let atCodeFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationCode (fixedNumeralTerm 2)
  let validFormula :=
    compactAdditiveArithmeticRelCodeValidClosedFormula witness.relationArity
      witness.relationCode
  let invalidFormula :=
    compactAdditiveArithmeticRelCodeInvalidClosedFormula witness.relationArity
      witness.relationCode
  let shortFormula := shortNativeLeFormula current.tokensCount 2
  let longFormula := nativeShortLeFormula 3 current.tokensCount
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hshort :
      (binaryFormulaCode shortFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [shortFormula]
    exact shortNativeLeFormula_code_length_le_fixed current.tokensCount 2
      bitBound hcurrentTokensCountSize (by omega)
  have hlong :
      (binaryFormulaCode longFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [longFormula]
    exact nativeShortLeFormula_code_length_le_fixed 3 current.tokensCount
      bitBound (by omega) hcurrentTokensCountSize
  have hfailure :
      (binaryFormulaCode failureFormula).length <=
        syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound := by
    dsimp only [failureFormula]
    exact syntaxTermFailureClosedFormula_code_length_le_substitutionFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount bitBound htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize htailCountSize
  have hfunction :
      (binaryFormulaCode functionFormula).length <=
        syntaxTermFunctionClosedFormulaCodePolynomial bitBound := by
    dsimp only [functionFormula]
    exact syntaxTermFunctionClosedFormula_code_length_le_fixed tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity bitBound htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize htailCountSize
      hbinderAritySize hrelationAritySize
  have hatArity :
      (binaryFormulaCode atArityFormula).length <=
        natListAtRowsFixedIndexFormulaCodePolynomial bitBound := by
    dsimp only [atArityFormula]
    exact
      compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_code_length_le_fixed
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount witness.relationArity 1 bitBound htokenTableSize
        hwidthSize htokenCountSize hcurrentTokensBoundarySize
        hcurrentTokensCountSize hrelationAritySize (by omega)
  have hatCode :
      (binaryFormulaCode atCodeFormula).length <=
        natListAtRowsFixedIndexFormulaCodePolynomial bitBound := by
    dsimp only [atCodeFormula]
    exact
      compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_code_length_le_fixed
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount witness.relationCode 2 bitBound htokenTableSize
        hwidthSize htokenCountSize hcurrentTokensBoundarySize
        hcurrentTokensCountSize hrelationCodeSize (by omega)
  have hvalid :
      (binaryFormulaCode validFormula).length <=
        arithmeticRelCodeValidFormulaCodePolynomial bitBound := by
    dsimp only [validFormula]
    exact
      compactAdditiveArithmeticRelCodeValidClosedFormula_code_length_le_fixed
        witness.relationArity witness.relationCode bitBound
        hrelationAritySize hrelationCodeSize
  have hinvalid :
      (binaryFormulaCode invalidFormula).length <=
        arithmeticRelCodeInvalidFormulaCodePolynomial bitBound := by
    dsimp only [invalidFormula]
    exact
      compactAdditiveArithmeticRelCodeInvalidClosedFormula_code_length_le_fixed
        witness.relationArity witness.relationCode bitBound
        hrelationAritySize hrelationCodeSize
  let validPair := validFormula ⋏ functionFormula
  let invalidPair := invalidFormula ⋏ failureFormula
  let codeBranch := validPair ⋎ invalidPair
  let codeTail := atCodeFormula ⋏ codeBranch
  let arityTail := atArityFormula ⋏ codeTail
  let longBranch := longFormula ⋏ arityTail
  let shortBranch := shortFormula ⋏ failureFormula
  have hvalidPairRaw := binaryFormulaCode_and_length_le validFormula
    functionFormula
  have hvalidPair :
      (binaryFormulaCode validPair).length <=
        arithmeticRelCodeValidFormulaCodePolynomial bitBound +
          syntaxTermFunctionClosedFormulaCodePolynomial bitBound + 8 := by
    simpa only [validPair] using hvalidPairRaw.trans (by omega)
  have hinvalidPairRaw := binaryFormulaCode_and_length_le invalidFormula
    failureFormula
  have hinvalidPair :
      (binaryFormulaCode invalidPair).length <=
        arithmeticRelCodeInvalidFormulaCodePolynomial bitBound +
          syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 8 := by
    simpa only [invalidPair] using hinvalidPairRaw.trans (by omega)
  have hcodeBranchRaw := binaryFormulaCode_or_length_le validPair invalidPair
  have hcodeBranch :
      (binaryFormulaCode codeBranch).length <=
        arithmeticRelCodeValidFormulaCodePolynomial bitBound +
          syntaxTermFunctionClosedFormulaCodePolynomial bitBound +
          arithmeticRelCodeInvalidFormulaCodePolynomial bitBound +
          syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 24 := by
    simpa only [codeBranch] using hcodeBranchRaw.trans (by omega)
  have hcodeTailRaw := binaryFormulaCode_and_length_le atCodeFormula codeBranch
  have hcodeTail :
      (binaryFormulaCode codeTail).length <=
        natListAtRowsFixedIndexFormulaCodePolynomial bitBound +
          arithmeticRelCodeValidFormulaCodePolynomial bitBound +
          syntaxTermFunctionClosedFormulaCodePolynomial bitBound +
          arithmeticRelCodeInvalidFormulaCodePolynomial bitBound +
          syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 40 := by
    simpa only [codeTail] using hcodeTailRaw.trans (by omega)
  have harityTailRaw := binaryFormulaCode_and_length_le atArityFormula codeTail
  have harityTail :
      (binaryFormulaCode arityTail).length <=
        2 * natListAtRowsFixedIndexFormulaCodePolynomial bitBound +
          arithmeticRelCodeValidFormulaCodePolynomial bitBound +
          syntaxTermFunctionClosedFormulaCodePolynomial bitBound +
          arithmeticRelCodeInvalidFormulaCodePolynomial bitBound +
          syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 56 := by
    simpa only [arityTail] using harityTailRaw.trans (by omega)
  have hlongBranchRaw := binaryFormulaCode_and_length_le longFormula arityTail
  have hlongBranch :
      (binaryFormulaCode longBranch).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound +
          2 * natListAtRowsFixedIndexFormulaCodePolynomial bitBound +
          arithmeticRelCodeValidFormulaCodePolynomial bitBound +
          syntaxTermFunctionClosedFormulaCodePolynomial bitBound +
          arithmeticRelCodeInvalidFormulaCodePolynomial bitBound +
          syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 72 := by
    simpa only [longBranch] using hlongBranchRaw.trans (by omega)
  have hshortBranchRaw := binaryFormulaCode_and_length_le shortFormula
    failureFormula
  have hshortBranch :
      (binaryFormulaCode shortBranch).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound +
          syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 8 := by
    simpa only [shortBranch] using hshortBranchRaw.trans (by omega)
  have hfullRaw := binaryFormulaCode_or_length_le shortBranch longBranch
  have hfull :
      (binaryFormulaCode (shortBranch ⋎ longBranch)).length <=
        syntaxFormulaRelationBodyCodePolynomial bitBound := by
    unfold syntaxFormulaRelationBodyCodePolynomial
    exact hfullRaw.trans (by omega)
  unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
  simpa only [failureFormula, functionFormula, atArityFormula, atCodeFormula,
    validFormula, invalidFormula, shortFormula, longFormula, validPair,
    invalidPair, codeBranch, codeTail, arityTail, longBranch, shortBranch] using
      hfull

@[simp] theorem
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
      width tokenCount current next binderArity witness).freeVariables = ∅ := by
  unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
  simp [
    shortNativeLeFormula_freeVariables_eq_empty_fixed,
    nativeShortLeFormula_freeVariables_eq_empty_fixed,
    syntaxTermFailureClosedFormula_freeVariables_eq_empty_substitutionFixed,
    syntaxTermFunctionClosedFormula_freeVariables_eq_empty,
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
    compactAdditiveArithmeticRelCodeValidClosedFormula_freeVariables_eq_empty_fixed,
    compactAdditiveArithmeticRelCodeInvalidClosedFormula_freeVariables_eq_empty_fixed]

#print axioms
  compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_code_length_le_fixed
#print axioms
  compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
