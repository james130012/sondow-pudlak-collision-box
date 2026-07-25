import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationSelectedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fully fixed relation path in the syntax-formula tag branch

The selected relation certificate is inserted into the left branch of the
genuine five-way tag formula.  The unselected tail contributes syntax only,
through the graph-independent full tag-tree code and closedness theorems.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationTagBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongCertificates
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationShortFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationSelectedFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactArithmeticSymbolCode

def syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
    (selectedResource bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound +
      selectedResource + 1
  FoundationCompactPAHybridDisjunctionGeneralContextBounds.hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource

private theorem binaryFormulaCode_or_right_le_relationTag
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem relationSelectedCertificate_tagBranchPayloadBound_le_fullyFixed
    {valuation : Nat -> Nat}
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (bitBound selectedResource : Nat)
    (selected :
      CheckedHybridValuationBoundedFormulaCertificate valuation
        (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
          current next binderArity witness))
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= selectedResource)
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
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          selected) <=
      syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
        selectedResource bitBound := by
  let leftFormula :=
    syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
      next binderArity witness
  let rightFormula :=
    syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
        next witness ⋎
      syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
          next binderArity witness ⋎
        syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
            current next binderArity witness ⋎
          syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
            current next witness
  let syntaxResource :=
    syntaxFormulaTagBranchFullyFixedCodePolynomial bitBound +
      selectedResource + 1
  have hfullClosed :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  rw [syntaxFormulaTagBranchExplicitFormula_component_alignment] at hfullClosed
  change (leftFormula ⋎ rightFormula).freeVariables = ∅ at hfullClosed
  rw [LO.FirstOrder.Semiformula.freeVariables_or] at hfullClosed
  have hclosed := Finset.union_eq_empty.mp hfullClosed
  have hleftCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      selected
  have hleftCode :
      (binaryFormulaCode leftFormula).length <= syntaxResource := by
    exact (hleftCodeRaw.trans hselected).trans (by
      dsimp only [syntaxResource]
      omega)
  have hfullCodeFixed :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  have hfullCode :
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length <=
        syntaxResource := by
    change
      (binaryFormulaCode
        (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
          width tokenCount current next binderArity witness)).length <=
        syntaxResource
    exact hfullCodeFixed.trans (by
      dsimp only [syntaxResource]
      omega)
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= syntaxResource :=
    (binaryFormulaCode_or_right_le_relationTag leftFormula rightFormula).trans
      hfullCode
  unfold syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
  simpa only [leftFormula, rightFormula, syntaxResource] using
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral selected
      selectedResource syntaxResource hselected
      (by
        dsimp only [syntaxResource]
        omega)
      hclosed.1 hclosed.2 hleftCode hrightCode hfullCode

def syntaxFormulaRelationShortTagBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
    (syntaxFormulaRelationShortSelectedFullyFixedPayloadPolynomial numericBound
      bitBound)
    bitBound

theorem
    syntaxFormulaRelationShortTagBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hshort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
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
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
            (syntaxFormulaRelationShortBodyCertificate tokenTable width
              tokenCount current next binderArity witness hshort hfailure))) <=
      syntaxFormulaRelationShortTagBranchFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let selected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
      (syntaxFormulaRelationShortBodyCertificate tokenTable width tokenCount
        current next binderArity witness hshort hfailure)
  have hselected :
      hybridFormulaStructuralPayloadBound selected <=
        syntaxFormulaRelationShortSelectedFullyFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [selected]
    exact
      syntaxFormulaRelationShortSelectedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness
        numericBound bitBound htag hshort hfailure hwidth htokenCount htailCount
        hcurrentValue hnextValue htokenTableSize hwidthSize htokenCountSize
        hcurrentSize hnextSize htailBoundarySize hbinderAritySize
        hrelationAritySize hrelationCodeSize htagSize hnumericSize hbitPositive
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  unfold syntaxFormulaRelationShortTagBranchFullyFixedPayloadPolynomial
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          selected) <=
      syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
        (syntaxFormulaRelationShortSelectedFullyFixedPayloadPolynomial
          numericBound bitBound)
        bitBound
  exact
    relationSelectedCertificate_tagBranchPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      (syntaxFormulaRelationShortSelectedFullyFixedPayloadPolynomial numericBound
        bitBound)
      selected hselected htokenTableSize hwidthSize htokenCountSize hcurrentSize
      hnextSize htailBoundarySize htailCountSize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hbitPositive

def syntaxFormulaRelationValidTagBranchFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
    (syntaxFormulaRelationValidSelectedFullyFixedPayloadPolynomial tokenCount
      numericBound bitBound)
    bitBound

theorem
    syntaxFormulaRelationValidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hvalid : ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity)
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
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
            (syntaxFormulaRelationValidBodyCertificate tokenTable width
              tokenCount current next binderArity witness hthree hatArity
              hatCode hvalid hfunction))) <=
      syntaxFormulaRelationValidTagBranchFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let selected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
      (syntaxFormulaRelationValidBodyCertificate tokenTable width tokenCount
        current next binderArity witness hthree hatArity hatCode hvalid
        hfunction)
  have hselected :
      hybridFormulaStructuralPayloadBound selected <=
        syntaxFormulaRelationValidSelectedFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    dsimp only [selected]
    exact
      syntaxFormulaRelationValidSelectedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness
        numericBound bitBound htag hthree hatArity hatCode hvalid hfunction
        hwidth htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize htagSize hnumericSize
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
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hbitPositive : 1 <= bitBound := by
    have hcountPositive : 0 < current.tokensCount := by omega
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr hcountPositive
    omega
  unfold syntaxFormulaRelationValidTagBranchFullyFixedPayloadPolynomial
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          selected) <=
      syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
        (syntaxFormulaRelationValidSelectedFullyFixedPayloadPolynomial
          tokenCount numericBound bitBound)
        bitBound
  exact
    relationSelectedCertificate_tagBranchPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      (syntaxFormulaRelationValidSelectedFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      selected hselected htokenTableSize hwidthSize htokenCountSize hcurrentSize
      hnextSize htailBoundarySize htailCountSize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hbitPositive

def syntaxFormulaRelationInvalidTagBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
    (syntaxFormulaRelationInvalidSelectedFullyFixedPayloadPolynomial
      numericBound bitBound)
    bitBound

theorem
    syntaxFormulaRelationInvalidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
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
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
            (syntaxFormulaRelationInvalidBodyCertificate tokenTable width
              tokenCount current next binderArity witness hthree hatArity
              hatCode hinvalid hfailure))) <=
      syntaxFormulaRelationInvalidTagBranchFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let selected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
      (syntaxFormulaRelationInvalidBodyCertificate tokenTable width tokenCount
        current next binderArity witness hthree hatArity hatCode hinvalid
        hfailure)
  have hselected :
      hybridFormulaStructuralPayloadBound selected <=
        syntaxFormulaRelationInvalidSelectedFullyFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [selected]
    exact
      syntaxFormulaRelationInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness
        numericBound bitBound htag hthree hatArity hatCode hinvalid hfailure
        hwidth htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize htagSize hnumericSize
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
    have hcountPositive : 0 < current.tokensCount := by omega
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr hcountPositive
    omega
  unfold syntaxFormulaRelationInvalidTagBranchFullyFixedPayloadPolynomial
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          selected) <=
      syntaxFormulaRelationTagBranchFullyFixedPayloadPolynomial
        (syntaxFormulaRelationInvalidSelectedFullyFixedPayloadPolynomial
          numericBound bitBound)
        bitBound
  exact
    relationSelectedCertificate_tagBranchPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      (syntaxFormulaRelationInvalidSelectedFullyFixedPayloadPolynomial
        numericBound bitBound)
      selected hselected htokenTableSize hwidthSize htokenCountSize hcurrentSize
      hnextSize htailBoundarySize htailCountSize hbinderAritySize
      hrelationAritySize hrelationCodeSize htagSize hbitPositive

#print axioms relationSelectedCertificate_tagBranchPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaRelationShortTagBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaRelationValidTagBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaRelationInvalidTagBranchCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationTagBranchFullyFixedBounds
