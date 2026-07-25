import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaLogicalSelectedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinarySelectedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierSelectedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaInvalidSelectedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
import integration.FoundationCompactPAHybridFiveRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactListedProofHonestWeight

/-!
# Fully fixed remaining paths in the syntax-formula tag branch

Each selected certificate is inserted into the genuine right-associated
five-way tag formula.  Unselected leaves contribute only graph-free syntax.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRemainingTagBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactListedProofHonestWeight
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridFiveRightDisjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaLogicalSelectedFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinarySelectedFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierSelectedFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaInvalidSelectedFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows

def syntaxFormulaLogicalTagBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  fiveRightDisjunctionPathOnePayloadEnvelope
    (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
    (syntaxFormulaLogicalSelectedFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaLogicalTagBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (htag : NativeEqEitherCheckedData witness.tag 2 3)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : witness.tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left :=
            syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
              current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right :=
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
              (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount 1 hcontinue)))) <=
      syntaxFormulaLogicalTagBranchFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let first :=
    syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let second :=
    syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current next
      witness
  let third :=
    syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let fourth :=
    syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount current
      next binderArity witness
  let fifth :=
    syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount current
      next witness
  let selected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
      (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 1 hcontinue)
  have hselected :
      hybridFormulaStructuralPayloadBound selected <=
        syntaxFormulaLogicalSelectedFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [selected]
    exact
      syntaxFormulaLogicalSelectedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness numericBound bitBound
        htag hcontinue hwidth htokenCount htailCount hcurrentValue hnextValue
        htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
        htailBoundarySize htagSize hnumericSize
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  have hclosed :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hclosed
  change (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅ at hclosed
  have hcode :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hcode
  change
    (binaryFormulaCode
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
        syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound at hcode
  have hsyntaxPositive :
      1 <= syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).trans hcode
  unfold syntaxFormulaLogicalTagBranchFullyFixedPayloadPolynomial
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := third ⋎ fourth ⋎ fifth) selected)) <=
      fiveRightDisjunctionPathOnePayloadEnvelope
        (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
        (syntaxFormulaLogicalSelectedFullyFixedPayloadPolynomial numericBound
          bitBound)
  exact
    fiveRightDisjunctionPathOnePayloadBound_le_closedGeneral first second third
      fourth fifth selected
      (syntaxFormulaLogicalSelectedFullyFixedPayloadPolynomial numericBound
        bitBound)
      (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound) hselected
      hsyntaxPositive hclosed hcode

def syntaxFormulaBinaryTagBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  fiveRightDisjunctionPathTwoPayloadEnvelope
    (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
    (syntaxFormulaBinarySelectedFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaBinaryTagBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 4 5)
    (hbinary : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity)
    (hwidth : width <= numericBound)
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
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left :=
            syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
              current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left :=
              syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right :=
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
                (compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
                  tokenTable width tokenCount current next
                  witness.tailBoundary witness.tailCount binderArity
                  hbinary))))) <=
      syntaxFormulaBinaryTagBranchFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let first :=
    syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let second :=
    syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current next
      witness
  let third :=
    syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let fourth :=
    syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount current
      next binderArity witness
  let fifth :=
    syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount current
      next witness
  let selected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
      (compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity hbinary)
  have hselected :
      hybridFormulaStructuralPayloadBound selected <=
        syntaxFormulaBinarySelectedFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [selected]
    exact
      syntaxFormulaBinarySelectedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness binderArity numericBound
        bitBound htag hbinary hwidth htokenCount hcurrentValue hnextValue
        htokenTableSize hcurrentSize hnextSize htailBoundarySize
        hbinderAritySize htagSize hnumericSize
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have htailCount : witness.tailCount <= numericBound := by
    have hdrop := hbinary.2.2.1
    unfold CompactAdditiveSyntaxTaskListDropRows at hdrop
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hnextValue (7 : Fin 8)
    omega
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  have hbitPositive : 1 <= bitBound := by
    have htagPositive : 0 < witness.tag := by
      cases htag with
      | left hleft =>
          omega
      | right hright =>
          omega
    have hsizePositive : 0 < Nat.size witness.tag :=
      Nat.size_pos.mpr htagPositive
    omega
  have hclosed :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hclosed
  change (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅ at hclosed
  have hcode :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hcode
  change
    (binaryFormulaCode
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
        syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound at hcode
  have hsyntaxPositive :
      1 <= syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).trans hcode
  unfold syntaxFormulaBinaryTagBranchFullyFixedPayloadPolynomial
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := second)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := fourth ⋎ fifth) selected))) <=
      fiveRightDisjunctionPathTwoPayloadEnvelope
        (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
        (syntaxFormulaBinarySelectedFullyFixedPayloadPolynomial numericBound
          bitBound)
  exact
    fiveRightDisjunctionPathTwoPayloadBound_le_closedGeneral first second third
      fourth fifth selected
      (syntaxFormulaBinarySelectedFullyFixedPayloadPolynomial numericBound
        bitBound)
      (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound) hselected
      hsyntaxPositive hclosed hcode

def syntaxFormulaQuantifierTagBranchFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  fiveRightDisjunctionPathThreePayloadEnvelope
    (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
    (syntaxFormulaQuantifierSelectedFullyFixedPayloadPolynomial tokenCount
      numericBound bitBound)

theorem
    syntaxFormulaQuantifierTagBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 6 7)
    (hquantifier : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity)
    (hwidth : width <= numericBound)
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
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left :=
            syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
              current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left :=
              syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left :=
                syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right :=
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
                  (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
                    tokenTable width tokenCount current next
                    witness.tailBoundary witness.tailCount binderArity
                    hquantifier)))))) <=
      syntaxFormulaQuantifierTagBranchFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let first :=
    syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let second :=
    syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current next
      witness
  let third :=
    syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let fourth :=
    syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount current
      next binderArity witness
  let fifth :=
    syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount current
      next witness
  let selected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
      (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity hquantifier)
  have hselected :
      hybridFormulaStructuralPayloadBound selected <=
        syntaxFormulaQuantifierSelectedFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    dsimp only [selected]
    exact
      syntaxFormulaQuantifierSelectedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness binderArity numericBound
        bitBound htag hquantifier hwidth htokenCount hcurrentValue hnextValue
        htokenTableSize hcurrentSize hnextSize htailBoundarySize
        hbinderAritySize htagSize hnumericSize
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have htailCount : witness.tailCount <= numericBound := by
    have htasks := hquantifier.2.2
    unfold CompactAdditiveSyntaxTaskListConsRows at htasks
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hnextValue (7 : Fin 8)
    omega
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  have hbitPositive : 1 <= bitBound := by
    have htagPositive : 0 < witness.tag := by
      cases htag with
      | left hleft =>
          omega
      | right hright =>
          omega
    have hsizePositive : 0 < Nat.size witness.tag :=
      Nat.size_pos.mpr htagPositive
    omega
  have hclosed :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hclosed
  change (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅ at hclosed
  have hcode :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hcode
  change
    (binaryFormulaCode
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
        syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound at hcode
  have hsyntaxPositive :
      1 <= syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).trans hcode
  unfold syntaxFormulaQuantifierTagBranchFullyFixedPayloadPolynomial
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := second)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := third)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := fifth) selected)))) <=
      fiveRightDisjunctionPathThreePayloadEnvelope
        (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
        (syntaxFormulaQuantifierSelectedFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound)
  exact
    fiveRightDisjunctionPathThreeLeftPayloadBound_le_closedGeneral first second
      third fourth fifth selected
      (syntaxFormulaQuantifierSelectedFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound) hselected
      hsyntaxPositive hclosed hcode

noncomputable def syntaxFormulaInvalidSelectedCertificateOfData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (htag0 : witness.tag ≠ 0)
    (htag1 : witness.tag ≠ 1)
    (htag2 : witness.tag ≠ 2)
    (htag3 : witness.tag ≠ 3)
    (htag4 : witness.tag ≠ 4)
    (htag5 : witness.tag ≠ 5)
    (htag6 : witness.tag ≠ 6)
    (htag7 : witness.tag ≠ 7) :
    CheckedHybridValuationBoundedFormulaCertificate (fun _ => 0)
      (syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
        current next witness) := by
  unfold syntaxFormulaInvalidTagSelectedFormula
  exact
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeNeCertificate witness.tag 0 htag0)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeNeCertificate witness.tag 1 htag1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeNeCertificate witness.tag 2 htag2)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeNeCertificate witness.tag 3 htag3)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeNeCertificate witness.tag 4 htag4)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (nativeNeCertificate witness.tag 5 htag5)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeNeCertificate witness.tag 6 htag6)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (nativeNeCertificate witness.tag 7 htag7)
                    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount hfailure))))))))

def syntaxFormulaInvalidTagBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  fiveRightDisjunctionPathThreePayloadEnvelope
    (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
    (syntaxFormulaInvalidSelectedFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaInvalidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (htag0 : witness.tag ≠ 0)
    (htag1 : witness.tag ≠ 1)
    (htag2 : witness.tag ≠ 2)
    (htag3 : witness.tag ≠ 3)
    (htag4 : witness.tag ≠ 4)
    (htag5 : witness.tag ≠ 5)
    (htag6 : witness.tag ≠ 6)
    (htag7 : witness.tag ≠ 7)
    (hwidth : width <= numericBound)
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
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left :=
            syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
              current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left :=
              syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left :=
                syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left :=
                  syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness)
                (syntaxFormulaInvalidSelectedCertificateOfData tokenTable width
                  tokenCount current next witness hfailure htag0 htag1 htag2
                  htag3 htag4 htag5 htag6 htag7))))) <=
      syntaxFormulaInvalidTagBranchFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let first :=
    syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let second :=
    syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current next
      witness
  let third :=
    syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current next
      binderArity witness
  let fourth :=
    syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount current
      next binderArity witness
  let fifth :=
    syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount current
      next witness
  let selected :=
    syntaxFormulaInvalidSelectedCertificateOfData tokenTable width tokenCount
      current next witness hfailure htag0 htag1 htag2 htag3 htag4 htag5 htag6
      htag7
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have htailCount : witness.tailCount <= numericBound := by
    have htasks := hfailure.2.2
    unfold CompactAdditiveSyntaxTaskListSameRows at htasks
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hnextValue (7 : Fin 8)
    omega
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  have hbitPositive : 1 <= bitBound := by
    have htagPositive : 0 < witness.tag := Nat.pos_of_ne_zero htag0
    have hsizePositive : 0 < Nat.size witness.tag :=
      Nat.size_pos.mpr htagPositive
    omega
  have hselected :
      hybridFormulaStructuralPayloadBound selected <=
        syntaxFormulaInvalidSelectedFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [selected, syntaxFormulaInvalidSelectedCertificateOfData]
    exact
      syntaxFormulaInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness numericBound bitBound
        hfailure htag0 htag1 htag2 htag3 htag4 htag5 htag6 htag7 hwidth
        htokenCount htailCount hcurrentValue hnextValue htokenTableSize
        hwidthSize htokenCountSize hcurrentSize hnextSize htailBoundarySize
        htagSize hnumericSize hbitPositive
  have hclosed :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hclosed
  change (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅ at hclosed
  have hcode :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hcode
  change
    (binaryFormulaCode
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
        syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound at hcode
  have hsyntaxPositive :
      1 <= syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).trans hcode
  unfold syntaxFormulaInvalidTagBranchFullyFixedPayloadPolynomial
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := second)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := third)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := fourth) selected)))) <=
      fiveRightDisjunctionPathThreePayloadEnvelope
        (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound)
        (syntaxFormulaInvalidSelectedFullyFixedPayloadPolynomial numericBound
          bitBound)
  exact
    fiveRightDisjunctionPathThreeRightPayloadBound_le_closedGeneral first second
      third fourth fifth selected
      (syntaxFormulaInvalidSelectedFullyFixedPayloadPolynomial numericBound
        bitBound)
      (syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound) hselected
      hsyntaxPositive hclosed hcode

#print axioms
  syntaxFormulaLogicalTagBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaBinaryTagBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaQuantifierTagBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaInvalidTagBranchCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaRemainingTagBranchesFullyFixedBounds
