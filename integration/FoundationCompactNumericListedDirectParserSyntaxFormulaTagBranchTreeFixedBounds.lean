import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueSubstitutionSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTaskSubstitutionSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierFullyFixedBounds
import integration.FoundationCompactListedLocalCostPrimitives

/-!
# Fixed assembly bounds for the syntax-formula tag tree

This module isolates the right-associated five-way disjunction used by the
genuine parser formula.  It only accounts for connective syntax.  Bounds for
the five named leaves remain explicit obligations for the graph-free syntax
modules that follow.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinueSubstitutionSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskSubstitutionSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierFullyFixedBounds

def fiveRightDisjunctionCodePolynomial
    (first second third fourth fifth : Nat) : Nat :=
  first + second + third + fourth + fifth + 32

theorem binaryFormulaCode_fiveRightDisjunction_length_le
    (first second third fourth fifth : ValuationFormula)
    (firstResource secondResource thirdResource fourthResource
      fifthResource : Nat)
    (hfirst : (binaryFormulaCode first).length <= firstResource)
    (hsecond : (binaryFormulaCode second).length <= secondResource)
    (hthird : (binaryFormulaCode third).length <= thirdResource)
    (hfourth : (binaryFormulaCode fourth).length <= fourthResource)
    (hfifth : (binaryFormulaCode fifth).length <= fifthResource) :
    (binaryFormulaCode
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
        fiveRightDisjunctionCodePolynomial firstResource secondResource
          thirdResource fourthResource fifthResource := by
  have h45 := binaryFormulaCode_or_length_le fourth fifth
  have h345 := binaryFormulaCode_or_length_le third (fourth ⋎ fifth)
  have h2345 :=
    binaryFormulaCode_or_length_le second (third ⋎ fourth ⋎ fifth)
  have h12345 :=
    binaryFormulaCode_or_length_le first
      (second ⋎ third ⋎ fourth ⋎ fifth)
  unfold fiveRightDisjunctionCodePolynomial
  omega

theorem fiveRightDisjunction_freeVariables_eq_empty
    (first second third fourth fifth : ValuationFormula)
    (hfirst : first.freeVariables = ∅)
    (hsecond : second.freeVariables = ∅)
    (hthird : third.freeVariables = ∅)
    (hfourth : fourth.freeVariables = ∅)
    (hfifth : fifth.freeVariables = ∅) :
    (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅ := by
  simp only [LO.FirstOrder.Semiformula.freeVariables_or, hfirst, hsecond,
    hthird, hfourth, hfifth, Finset.union_empty]

def syntaxFormulaTagBranchCodePolynomial
    (relationResource logicalResource binaryResource quantifierResource
      invalidResource : Nat) : Nat :=
  fiveRightDisjunctionCodePolynomial relationResource logicalResource
    binaryResource quantifierResource invalidResource

def syntaxFormulaRelationSelectedFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxFormulaRelationBodyCodePolynomial bitBound + 8

theorem syntaxFormulaRelationSelectedFormula_code_length_le_fixed
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
    (htagSize : Nat.size witness.tag <= bitBound) :
    (binaryFormulaCode
      (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
        current next binderArity witness)).length <=
      syntaxFormulaRelationSelectedFormulaCodePolynomial bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 0 ⋎ nativeEqFormula witness.tag 1
  let bodyFormula :=
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
      width tokenCount current next binderArity witness
  have htag :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 0 1 bitBound
      htagSize (by omega) (by omega)
  have hbody :
      (binaryFormulaCode bodyFormula).length <=
        syntaxFormulaRelationBodyCodePolynomial bitBound := by
    dsimp only [bodyFormula]
    exact
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_code_length_le_fixed
        tokenTable width tokenCount current next binderArity witness bitBound
        htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
        htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
        hrelationCodeSize
  have hraw := binaryFormulaCode_and_length_le tagFormula bodyFormula
  unfold syntaxFormulaRelationSelectedFormula
  change
    (binaryFormulaCode (tagFormula ⋏ bodyFormula)).length <=
      syntaxFormulaRelationSelectedFormulaCodePolynomial bitBound
  unfold syntaxFormulaRelationSelectedFormulaCodePolynomial
  omega

def syntaxFormulaInvalidTagSelectedFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  8 * parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound + 72

theorem syntaxFormulaInvalidTagSelectedFormula_code_length_le_fixed
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
    (htailCountSize : Nat.size witness.tailCount <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound) :
    (binaryFormulaCode
      (syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
        current next witness)).length <=
      syntaxFormulaInvalidTagSelectedFormulaCodePolynomial bitBound := by
  have h0 := nativeNeFormula_code_length_le_fixed witness.tag 0 bitBound
    htagSize (by omega)
  have h1 := nativeNeFormula_code_length_le_fixed witness.tag 1 bitBound
    htagSize (by omega)
  have h2 := nativeNeFormula_code_length_le_fixed witness.tag 2 bitBound
    htagSize (by omega)
  have h3 := nativeNeFormula_code_length_le_fixed witness.tag 3 bitBound
    htagSize (by omega)
  have h4 := nativeNeFormula_code_length_le_fixed witness.tag 4 bitBound
    htagSize (by omega)
  have h5 := nativeNeFormula_code_length_le_fixed witness.tag 5 bitBound
    htagSize (by omega)
  have h6 := nativeNeFormula_code_length_le_fixed witness.tag 6 bitBound
    htagSize (by omega)
  have h7 := nativeNeFormula_code_length_le_fixed witness.tag 7 bitBound
    htagSize (by omega)
  have hfailure :=
    syntaxTermFailureClosedFormula_code_length_le_substitutionFixed tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      bitBound htokenTableSize hwidthSize htokenCountSize hcurrentSize
      hnextSize htailBoundarySize htailCountSize
  have hconjunctionTag : (binaryNatCode 4).length <= 8 := by decide
  unfold syntaxFormulaInvalidTagSelectedFormula
  simp only [binaryFormulaCode, List.length_append] at *
  unfold syntaxFormulaInvalidTagSelectedFormulaCodePolynomial
  omega

def syntaxFormulaLogicalSelectedFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxTermContinueSubstitutionFormulaCodePolynomial bitBound + 8

theorem syntaxFormulaLogicalSelectedFormula_code_length_le_fixed
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
    (htailCountSize : Nat.size witness.tailCount <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (binaryFormulaCode
      (syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
        current next witness)).length <=
      syntaxFormulaLogicalSelectedFormulaCodePolynomial bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 2 ⋎ nativeEqFormula witness.tag 3
  let continueFormula :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 1
  have htag :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 2 3 bitBound
      htagSize (by omega) (by omega)
  have hcontinue :
      (binaryFormulaCode continueFormula).length <=
        syntaxTermContinueSubstitutionFormulaCodePolynomial bitBound := by
    dsimp only [continueFormula]
    exact
      syntaxTermContinueFixedOneClosedFormula_code_length_le_substitutionFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount bitBound htokenTableSize hwidthSize htokenCountSize
        hcurrentSize hnextSize htailBoundarySize htailCountSize hbitPositive
  have hraw := binaryFormulaCode_and_length_le tagFormula continueFormula
  unfold syntaxFormulaLogicalSelectedFormula
  change
    (binaryFormulaCode (tagFormula ⋏ continueFormula)).length <=
      syntaxFormulaLogicalSelectedFormulaCodePolynomial bitBound
  unfold syntaxFormulaLogicalSelectedFormulaCodePolynomial
  omega

def syntaxFormulaBinarySelectedFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxFormulaBinarySubstitutionFormulaCodePolynomial bitBound + 8

theorem syntaxFormulaBinarySelectedFormula_code_length_le_fixed
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
    (htagSize : Nat.size witness.tag <= bitBound) :
    (binaryFormulaCode
      (syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
        next binderArity witness)).length <=
      syntaxFormulaBinarySelectedFormulaCodePolynomial bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 4 ⋎ nativeEqFormula witness.tag 5
  let binaryFormula :=
    compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity
  have htag :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 4 5 bitBound
      htagSize (by omega) (by omega)
  have hbinary :
      (binaryFormulaCode binaryFormula).length <=
        syntaxFormulaBinarySubstitutionFormulaCodePolynomial bitBound := by
    dsimp only [binaryFormula]
    exact syntaxFormulaBinaryClosedFormula_code_length_le_substitutionFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity bitBound htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize htailCountSize
      hbinderAritySize
  have hraw := binaryFormulaCode_and_length_le tagFormula binaryFormula
  unfold syntaxFormulaBinarySelectedFormula
  change
    (binaryFormulaCode (tagFormula ⋏ binaryFormula)).length <=
      syntaxFormulaBinarySelectedFormulaCodePolynomial bitBound
  unfold syntaxFormulaBinarySelectedFormulaCodePolynomial
  omega

def syntaxFormulaQuantifierSelectedFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxFormulaQuantifierSubstitutionFormulaCodePolynomial bitBound + 8

theorem syntaxFormulaQuantifierSelectedFormula_code_length_le_fixed
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
    (htagSize : Nat.size witness.tag <= bitBound) :
    (binaryFormulaCode
      (syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
        current next binderArity witness)).length <=
      syntaxFormulaQuantifierSelectedFormulaCodePolynomial bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 6 ⋎ nativeEqFormula witness.tag 7
  let quantifierFormula :=
    compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity
  have htag :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 6 7 bitBound
      htagSize (by omega) (by omega)
  have hquantifier :
      (binaryFormulaCode quantifierFormula).length <=
        syntaxFormulaQuantifierSubstitutionFormulaCodePolynomial bitBound := by
    dsimp only [quantifierFormula]
    exact syntaxFormulaQuantifierClosedFormula_code_length_le_substitutionFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity bitBound htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize htailCountSize
      hbinderAritySize
  have hraw := binaryFormulaCode_and_length_le tagFormula quantifierFormula
  unfold syntaxFormulaQuantifierSelectedFormula
  change
    (binaryFormulaCode (tagFormula ⋏ quantifierFormula)).length <=
      syntaxFormulaQuantifierSelectedFormulaCodePolynomial bitBound
  unfold syntaxFormulaQuantifierSelectedFormulaCodePolynomial
  omega

def syntaxFormulaTagBranchFullyFixedCodePolynomial
    (bitBound : Nat) : Nat :=
  syntaxFormulaTagBranchCodePolynomial
    (syntaxFormulaRelationSelectedFormulaCodePolynomial bitBound)
    (syntaxFormulaLogicalSelectedFormulaCodePolynomial bitBound)
    (syntaxFormulaBinarySelectedFormulaCodePolynomial bitBound)
    (syntaxFormulaQuantifierSelectedFormulaCodePolynomial bitBound)
    (syntaxFormulaInvalidTagSelectedFormulaCodePolynomial bitBound)

theorem
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
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
      (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
        width tokenCount current next binderArity witness)).length <=
      syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound := by
  unfold syntaxFormulaTagBranchFullyFixedCodePolynomial
    syntaxFormulaTagBranchCodePolynomial
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment]
  apply binaryFormulaCode_fiveRightDisjunction_length_le
  · exact syntaxFormulaRelationSelectedFormula_code_length_le_fixed tokenTable
      width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize
  · exact syntaxFormulaLogicalSelectedFormula_code_length_le_fixed tokenTable
      width tokenCount current next witness bitBound htokenTableSize
      hwidthSize htokenCountSize hcurrentSize hnextSize htailBoundarySize
      htailCountSize htagSize hbitPositive
  · exact syntaxFormulaBinarySelectedFormula_code_length_le_fixed tokenTable
      width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize htagSize
  · exact syntaxFormulaQuantifierSelectedFormula_code_length_le_fixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize htagSize
  · exact syntaxFormulaInvalidTagSelectedFormula_code_length_le_fixed
      tokenTable width tokenCount current next witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize htagSize

theorem
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
      width tokenCount current next binderArity witness).freeVariables = ∅ := by
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment]
  apply fiveRightDisjunction_freeVariables_eq_empty
  · unfold syntaxFormulaRelationSelectedFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      nativeEqEitherFormula_freeVariables_eq_empty_fixed,
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed]
    simp
  · unfold syntaxFormulaLogicalSelectedFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      nativeEqEitherFormula_freeVariables_eq_empty_fixed,
      compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed]
    simp
  · unfold syntaxFormulaBinarySelectedFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      nativeEqEitherFormula_freeVariables_eq_empty_fixed,
      compactUnifiedParserSyntaxFormulaBinaryClosedFormula_freeVariables_eq_empty_fullyFixed]
    simp
  · unfold syntaxFormulaQuantifierSelectedFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      nativeEqEitherFormula_freeVariables_eq_empty_fixed,
      compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_freeVariables_eq_empty_fullyFixed]
    simp
  · unfold syntaxFormulaInvalidTagSelectedFormula
    simp only [LO.FirstOrder.Semiformula.freeVariables_and,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      nativeNeFormula_freeVariables_eq_empty_fixed,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty_substitutionFixed]
    simp

theorem compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_of_leaves
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (relationResource logicalResource binaryResource quantifierResource
      invalidResource : Nat)
    (hrelation :
      (binaryFormulaCode
        (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
          current next binderArity witness)).length <= relationResource)
    (hlogical :
      (binaryFormulaCode
        (syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
          current next witness)).length <= logicalResource)
    (hbinary :
      (binaryFormulaCode
        (syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
          current next binderArity witness)).length <= binaryResource)
    (hquantifier :
      (binaryFormulaCode
        (syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
          current next binderArity witness)).length <= quantifierResource)
    (hinvalid :
      (binaryFormulaCode
        (syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
          current next witness)).length <= invalidResource) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
        width tokenCount current next binderArity witness)).length <=
      syntaxFormulaTagBranchCodePolynomial relationResource logicalResource
        binaryResource quantifierResource invalidResource := by
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment]
  exact binaryFormulaCode_fiveRightDisjunction_length_le _ _ _ _ _
    relationResource logicalResource binaryResource quantifierResource
    invalidResource hrelation hlogical hbinary hquantifier hinvalid

#print axioms binaryFormulaCode_fiveRightDisjunction_length_le
#print axioms fiveRightDisjunction_freeVariables_eq_empty
#print axioms
  syntaxFormulaRelationSelectedFormula_code_length_le_fixed
#print axioms
  syntaxFormulaInvalidTagSelectedFormula_code_length_le_fixed
#print axioms
  syntaxFormulaLogicalSelectedFormula_code_length_le_fixed
#print axioms
  syntaxFormulaBinarySelectedFormula_code_length_le_fixed
#print axioms
  syntaxFormulaQuantifierSelectedFormula_code_length_le_fixed
#print axioms
  compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
#print axioms
  compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_of_leaves

end FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
