import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaOuterCertificateGeneralBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationTagBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRemainingTagBranchesFullyFixedBounds

/-!
# Concrete fully fixed outer syntax-formula branches

Each theorem inserts one genuine tag-branch certificate into the common enough
wrapper.  No abstract certificate remains in these concrete endpoints.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaOuterConcreteBranchesFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationShortFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongCertificates
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationSelectedFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationTagBranchFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRemainingTagBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterCertificateGeneralBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactArithmeticSymbolCode

def syntaxFormulaOuterRelationShortFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
    (syntaxFormulaRelationShortTagBranchFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaOuterRelationShortCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hshort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
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
            FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds.syntaxFormulaEmptyFormula
              tokenTable width tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right :=
                  syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                      current next witness ⋎
                    syntaxFormulaBinarySelectedFormula tokenTable width
                        tokenCount current next binderArity witness ⋎
                      syntaxFormulaQuantifierSelectedFormula tokenTable width
                          tokenCount current next binderArity witness ⋎
                        syntaxFormulaInvalidTagSelectedFormula tokenTable width
                          tokenCount current next witness)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
                  (syntaxFormulaRelationShortBodyCertificate tokenTable width
                    tokenCount current next binderArity witness hshort
                    hfailure)))))) <=
      syntaxFormulaOuterRelationShortFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let branchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right :=
        syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
            next witness ⋎
          syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
              next binderArity witness ⋎
            syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
                current next binderArity witness ⋎
              syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
                current next witness)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
        (syntaxFormulaRelationShortBodyCertificate tokenTable width tokenCount
          current next binderArity witness hshort hfailure))
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
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr (by omega)
    omega
  have hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaRelationShortTagBranchFullyFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [branchCertificate]
    exact
      syntaxFormulaRelationShortTagBranchCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness numericBound
        bitBound htag hshort hfailure hwidth htokenCount htailCount hcurrentValue
        hnextValue htokenTableSize hwidthSize htokenCountSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize htagSize hnumericSize hbitPositive
  unfold syntaxFormulaOuterRelationShortFullyFixedPayloadPolynomial
  exact
    syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      (syntaxFormulaRelationShortTagBranchFullyFixedPayloadPolynomial numericBound
        bitBound)
      witness hcount hatTag branchCertificate hbranch hwidth htokenCount
      hcurrentValue htailCount htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive

def syntaxFormulaOuterLogicalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
    (syntaxFormulaLogicalTagBranchFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaOuterLogicalCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 2 3)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1)
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
            FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds.syntaxFormulaEmptyFormula
              tokenTable width tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left :=
                  syntaxFormulaRelationSelectedFormula tokenTable width
                    tokenCount current next binderArity witness)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (right :=
                    syntaxFormulaBinarySelectedFormula tokenTable width
                        tokenCount current next binderArity witness ⋎
                      syntaxFormulaQuantifierSelectedFormula tokenTable width
                          tokenCount current next binderArity witness ⋎
                        syntaxFormulaInvalidTagSelectedFormula tokenTable width
                          tokenCount current next witness)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
                    (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount 1
                      hcontinue))))))) <=
      syntaxFormulaOuterLogicalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let branchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left :=
        syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
          next binderArity witness)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right :=
          syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
              next binderArity witness ⋎
            syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
                current next binderArity witness ⋎
              syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
                current next witness)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
          (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount 1 hcontinue)))
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have htailCount : witness.tailCount <= numericBound := by
    have htasks := hcontinue.2.2
    unfold CompactAdditiveSyntaxTaskListSameRows at htasks
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hnextValue (7 : Fin 8)
    omega
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr (by omega)
    omega
  have hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaLogicalTagBranchFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchCertificate]
    exact
      syntaxFormulaLogicalTagBranchCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness numericBound
        bitBound htag hcontinue hwidth htokenCount htailCount hcurrentValue
        hnextValue htokenTableSize hwidthSize htokenCountSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize htagSize hnumericSize hbitPositive
  unfold syntaxFormulaOuterLogicalFullyFixedPayloadPolynomial
  exact
    syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      (syntaxFormulaLogicalTagBranchFullyFixedPayloadPolynomial numericBound
        bitBound)
      witness hcount hatTag branchCertificate hbranch hwidth htokenCount
      hcurrentValue htailCount htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive

def syntaxFormulaOuterBinaryFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
    (syntaxFormulaBinaryTagBranchFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaOuterBinaryCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
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
            FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds.syntaxFormulaEmptyFormula
              tokenTable width tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left :=
                  syntaxFormulaRelationSelectedFormula tokenTable width
                    tokenCount current next binderArity witness)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left :=
                    syntaxFormulaLogicalSelectedFormula tokenTable width
                      tokenCount current next witness)
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
                        hbinary)))))))) <=
      syntaxFormulaOuterBinaryFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let branchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left :=
        syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
          next binderArity witness)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left :=
          syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
            next witness)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
                current next binderArity witness ⋎
              syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
                current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
            (compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount binderArity hbinary))))
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
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr (by omega)
    omega
  have hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaBinaryTagBranchFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchCertificate]
    exact
      syntaxFormulaBinaryTagBranchCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity numericBound bitBound
        witness htag hbinary hwidth htokenCount hcurrentValue hnextValue
        htokenTableSize hcurrentSize hnextSize htailBoundarySize
        hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
        hnumericSize
  unfold syntaxFormulaOuterBinaryFullyFixedPayloadPolynomial
  exact
    syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      (syntaxFormulaBinaryTagBranchFullyFixedPayloadPolynomial numericBound
        bitBound)
      witness hcount hatTag branchCertificate hbranch hwidth htokenCount
      hcurrentValue htailCount htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive

def syntaxFormulaOuterQuantifierFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
    (syntaxFormulaQuantifierTagBranchFullyFixedPayloadPolynomial tokenCount
      numericBound bitBound)

theorem
    syntaxFormulaOuterQuantifierCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
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
            FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds.syntaxFormulaEmptyFormula
              tokenTable width tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left :=
                  syntaxFormulaRelationSelectedFormula tokenTable width
                    tokenCount current next binderArity witness)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left :=
                    syntaxFormulaLogicalSelectedFormula tokenTable width
                      tokenCount current next witness)
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                    (left :=
                      syntaxFormulaBinarySelectedFormula tokenTable width
                        tokenCount current next binderArity witness)
                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                      (right :=
                        syntaxFormulaInvalidTagSelectedFormula tokenTable width
                          tokenCount current next witness)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
                        (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
                          tokenTable width tokenCount current next
                          witness.tailBoundary witness.tailCount binderArity
                          hquantifier))))))))) <=
      syntaxFormulaOuterQuantifierFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let branchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left :=
        syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
          next binderArity witness)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left :=
          syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
            next witness)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left :=
            syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
              current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right :=
              syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
                current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
              (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount binderArity hquantifier)))))
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
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr (by omega)
    omega
  have hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaQuantifierTagBranchFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    dsimp only [branchCertificate]
    exact
      syntaxFormulaQuantifierTagBranchCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity numericBound bitBound
        witness htag hquantifier hwidth htokenCount hcurrentValue hnextValue
        htokenTableSize hcurrentSize hnextSize htailBoundarySize
        hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
        hnumericSize
  unfold syntaxFormulaOuterQuantifierFullyFixedPayloadPolynomial
  exact
    syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      (syntaxFormulaQuantifierTagBranchFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      witness hcount hatTag branchCertificate hbranch hwidth htokenCount
      hcurrentValue htailCount htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive

def syntaxFormulaOuterInvalidTagFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
    (syntaxFormulaInvalidTagBranchFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaOuterInvalidTagCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag0 : witness.tag ≠ 0)
    (htag1 : witness.tag ≠ 1)
    (htag2 : witness.tag ≠ 2)
    (htag3 : witness.tag ≠ 3)
    (htag4 : witness.tag ≠ 4)
    (htag5 : witness.tag ≠ 5)
    (htag6 : witness.tag ≠ 6)
    (htag7 : witness.tag ≠ 7)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
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
            FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds.syntaxFormulaEmptyFormula
              tokenTable width tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left :=
                  syntaxFormulaRelationSelectedFormula tokenTable width
                    tokenCount current next binderArity witness)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left :=
                    syntaxFormulaLogicalSelectedFormula tokenTable width
                      tokenCount current next witness)
                  (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                    (left :=
                      syntaxFormulaBinarySelectedFormula tokenTable width
                        tokenCount current next binderArity witness)
                    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                      (left :=
                        syntaxFormulaQuantifierSelectedFormula tokenTable width
                          tokenCount current next binderArity witness)
                      (syntaxFormulaInvalidSelectedCertificateOfData tokenTable
                        width tokenCount current next witness hfailure htag0
                        htag1 htag2 htag3 htag4 htag5 htag6 htag7)))))))) <=
      syntaxFormulaOuterInvalidTagFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let branchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left :=
        syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
          next binderArity witness)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left :=
          syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
            next witness)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left :=
            syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
              current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left :=
              syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
                current next binderArity witness)
            (syntaxFormulaInvalidSelectedCertificateOfData tokenTable width
              tokenCount current next witness hfailure htag0 htag1 htag2 htag3
              htag4 htag5 htag6 htag7))))
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
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr (by omega)
    omega
  have hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaInvalidTagBranchFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [branchCertificate]
    exact
      syntaxFormulaInvalidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity numericBound bitBound
        witness hfailure htag0 htag1 htag2 htag3 htag4 htag5 htag6 htag7
        hwidth htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize htagSize hnumericSize
  unfold syntaxFormulaOuterInvalidTagFullyFixedPayloadPolynomial
  exact
    syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      (syntaxFormulaInvalidTagBranchFullyFixedPayloadPolynomial numericBound
        bitBound)
      witness hcount hatTag branchCertificate hbranch hwidth htokenCount
      hcurrentValue htailCount htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive

def syntaxFormulaOuterRelationValidFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
    (syntaxFormulaRelationValidTagBranchFullyFixedPayloadPolynomial tokenCount
      numericBound bitBound)

theorem
    syntaxFormulaOuterRelationValidCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hvalid : ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.relationArity)
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
            FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds.syntaxFormulaEmptyFormula
              tokenTable width tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right :=
                  syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                      current next witness ⋎
                    syntaxFormulaBinarySelectedFormula tokenTable width
                        tokenCount current next binderArity witness ⋎
                      syntaxFormulaQuantifierSelectedFormula tokenTable width
                          tokenCount current next binderArity witness ⋎
                        syntaxFormulaInvalidTagSelectedFormula tokenTable width
                          tokenCount current next witness)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
                  (syntaxFormulaRelationValidBodyCertificate tokenTable width
                    tokenCount current next binderArity witness hthree hatArity
                    hatCode hvalid hfunction)))))) <=
      syntaxFormulaOuterRelationValidFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let branchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right :=
        syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
            next witness ⋎
          syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
              next binderArity witness ⋎
            syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
                current next binderArity witness ⋎
              syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
                current next witness)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
        (syntaxFormulaRelationValidBodyCertificate tokenTable width tokenCount
          current next binderArity witness hthree hatArity hatCode hvalid
          hfunction))
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have htailCount : witness.tailCount <= numericBound := by
    have htasks := hfunction.2.2
    unfold CompactAdditiveSyntaxTaskListConsRows at htasks
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hnextValue (7 : Fin 8)
    omega
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr (by omega)
    omega
  have hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaRelationValidTagBranchFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    dsimp only [branchCertificate]
    exact
      syntaxFormulaRelationValidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness numericBound
        bitBound htag hthree hatArity hatCode hvalid hfunction hwidth htokenCount
        hcurrentValue hnextValue htokenTableSize hcurrentSize hnextSize
        htailBoundarySize hbinderAritySize hrelationAritySize hrelationCodeSize
        htagSize hnumericSize
  unfold syntaxFormulaOuterRelationValidFullyFixedPayloadPolynomial
  exact
    syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      (syntaxFormulaRelationValidTagBranchFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      witness hcount hatTag branchCertificate hbranch hwidth htokenCount
      hcurrentValue htailCount htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive

def syntaxFormulaOuterRelationInvalidFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
    (syntaxFormulaRelationInvalidTagBranchFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem
    syntaxFormulaOuterRelationInvalidCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hinvalid : ¬ ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
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
            FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds.syntaxFormulaEmptyFormula
              tokenTable width tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right :=
                  syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                      current next witness ⋎
                    syntaxFormulaBinarySelectedFormula tokenTable width
                        tokenCount current next binderArity witness ⋎
                      syntaxFormulaQuantifierSelectedFormula tokenTable width
                          tokenCount current next binderArity witness ⋎
                        syntaxFormulaInvalidTagSelectedFormula tokenTable width
                          tokenCount current next witness)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
                  (syntaxFormulaRelationInvalidBodyCertificate tokenTable width
                    tokenCount current next binderArity witness hthree hatArity
                    hatCode hinvalid hfailure)))))) <=
      syntaxFormulaOuterRelationInvalidFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let branchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right :=
        syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
            next witness ⋎
          syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
              next binderArity witness ⋎
            syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
                current next binderArity witness ⋎
              syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
                current next witness)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
        (syntaxFormulaRelationInvalidBodyCertificate tokenTable width tokenCount
          current next binderArity witness hthree hatArity hatCode hinvalid
          hfailure))
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
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr (by omega)
    omega
  have hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaRelationInvalidTagBranchFullyFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [branchCertificate]
    exact
      syntaxFormulaRelationInvalidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness numericBound
        bitBound htag hthree hatArity hatCode hinvalid hfailure hwidth htokenCount
        hcurrentValue hnextValue htokenTableSize hcurrentSize hnextSize
        htailBoundarySize hbinderAritySize hrelationAritySize hrelationCodeSize
        htagSize hnumericSize
  unfold syntaxFormulaOuterRelationInvalidFullyFixedPayloadPolynomial
  exact
    syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      (syntaxFormulaRelationInvalidTagBranchFullyFixedPayloadPolynomial
        numericBound bitBound)
      witness hcount hatTag branchCertificate hbranch hwidth htokenCount
      hcurrentValue htailCount htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive

end FoundationCompactNumericListedDirectParserSyntaxFormulaOuterConcreteBranchesFullyFixedBounds
