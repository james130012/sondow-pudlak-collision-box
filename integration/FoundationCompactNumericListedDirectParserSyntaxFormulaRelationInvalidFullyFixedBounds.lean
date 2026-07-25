import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationInvalidCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongEnvelopeFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodyTreeFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
import integration.FoundationCompactListedProofHonestWeight

/-! Fully fixed structural payload bound for the invalid relation path. -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationInvalidFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactListedProofHonestWeight
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongCertificates
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodyTreeFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactArithmeticSymbolCode
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows

theorem
    syntaxFormulaRelationInvalidBodyCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
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
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxFormulaRelationInvalidBodyCertificate tokenTable width tokenCount
          current next binderArity witness hthree hatArity hatCode hinvalid
          hfailure) <=
      relationInvalidBodyFullyFixedPayloadPolynomial numericBound bitBound := by
  let longGuard := relationBodyLongGuardFormula current
  let atArity :=
    relationBodyAtArityFormula tokenTable width tokenCount current witness
  let atCode :=
    relationBodyAtCodeFormula tokenTable width tokenCount current witness
  let invalid := relationBodyInvalidFormula witness
  let failure :=
    relationBodyFailureFormula tokenTable width tokenCount current next witness
  let validPair :=
    relationBodyValidPairFormula tokenTable width tokenCount current next
      binderArity witness
  let invalidPair :=
    relationBodyInvalidPairFormula tokenTable width tokenCount current next
      witness
  let choice :=
    relationBodyChoiceFormula tokenTable width tokenCount current next
      binderArity witness
  let codeTail :=
    relationBodyCodeTailFormula tokenTable width tokenCount current next
      binderArity witness
  let arityTail :=
    relationBodyArityTailFormula tokenTable width tokenCount current next
      binderArity witness
  let longBranch :=
    relationBodyLongBranchFormula tokenTable width tokenCount current next
      binderArity witness
  let shortBranch :=
    relationBodyShortBranchFormula tokenTable width tokenCount current next
      witness
  let longGuardCertificate :=
    nativeShortLeCertificate 3 current.tokensCount hthree
  let atArityCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.relationArity (fixedNumeralTerm 1) (by simp) hatArity
  let atCodeCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.relationCode (fixedNumeralTerm 2) (by simp) hatCode
  let invalidCertificate :=
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
      witness.relationArity witness.relationCode hinvalid
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let invalidPairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      invalidCertificate failureCertificate
  let choiceCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := validPair) invalidPairCertificate
  let codeTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      atCodeCertificate choiceCertificate
  let arityTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      atArityCertificate codeTailCertificate
  let longBranchCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      longGuardCertificate arityTailCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hcurrentTokensCount :
      current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hnextTasksCount : next.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (7 : Fin 8)
  have htailCount : witness.tailCount <= numericBound := by
    have htasks := hfailure.2.2
    unfold CompactAdditiveSyntaxTaskListSameRows at htasks
    omega
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  let syntaxResource := syntaxFormulaRelationBodyCodePolynomial bitBound
  have hsyntax :=
    relationBodyTreeFixedFacts tokenTable width tokenCount current next
      binderArity witness bitBound htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize htailCountSize
      hbinderAritySize hrelationAritySize hrelationCodeSize
  have hsyntaxPositive : 1 <= syntaxResource := by
    exact
      (one_le_binaryFormulaCode_length
        (relationBodyTreeFormula tokenTable width tokenCount current next
          binderArity witness)).trans hsyntax.bodyCode
  have hlongGuardResource :
      hybridFormulaStructuralPayloadBound longGuardCertificate <=
        parserFormulaTermLeFixedPayloadPolynomial bitBound := by
    dsimp only [longGuardCertificate]
    exact nativeShortLeCertificate_structuralPayloadBound_le_fixed 3
      current.tokensCount bitBound hthree (by omega)
      hcurrentTokensCountSize
  have hatArityResource :
      hybridFormulaStructuralPayloadBound atArityCertificate <=
        compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 1
          numericBound bitBound := by
    dsimp only [atArityCertificate]
    exact
      compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount 1 witness.relationArity numericBound bitBound
        hatArity hwidth htokenCount hcurrentTokensCount htokenTableSize
        hwidthSize htokenCountSize hcurrentTokensBoundarySize
        hcurrentTokensCountSize hrelationAritySize (by omega)
  have hatCodeResource :
      hybridFormulaStructuralPayloadBound atCodeCertificate <=
        compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
          numericBound bitBound := by
    dsimp only [atCodeCertificate]
    exact
      compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount 2 witness.relationCode numericBound bitBound
        hatCode hwidth htokenCount hcurrentTokensCount htokenTableSize
        hwidthSize htokenCountSize hcurrentTokensBoundarySize
        hcurrentTokensCountSize hrelationCodeSize (by omega)
  have hinvalidResource :
      hybridFormulaStructuralPayloadBound invalidCertificate <=
        arithmeticRelCodeInvalidFullyFixedPayloadPolynomial bitBound := by
    dsimp only [invalidCertificate]
    exact
      compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        witness.relationArity witness.relationCode bitBound hinvalid
        hrelationAritySize hrelationCodeSize
  have hbitPositive : 1 <= bitBound := by
    have hcountPositive : 0 < current.tokensCount := by omega
    have hsizePositive : 0 < Nat.size current.tokensCount :=
      Nat.size_pos.mpr hcountPositive
    omega
  have hfailureResource :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        syntaxTermFailureFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [failureCertificate]
    exact
      compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount numericBound bitBound hfailure hwidth htokenCount
        htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
        htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
        hbitPositive
  have hinvalidPairResource :
      hybridFormulaStructuralPayloadBound invalidPairCertificate <=
        relationInvalidPairFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [invalidPairCertificate]
    unfold relationInvalidPairFullyFixedPayloadPolynomial
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      invalidCertificate failureCertificate _ _ syntaxResource
      hinvalidResource hfailureResource hsyntaxPositive hsyntax.invalidClosed
      hsyntax.failureClosed hsyntax.invalidCode hsyntax.failureCode
      hsyntax.invalidPairCode
  have hchoiceResource :
      hybridFormulaStructuralPayloadBound choiceCertificate <=
        relationInvalidChoiceFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [choiceCertificate]
    unfold relationInvalidChoiceFullyFixedPayloadPolynomial
    exact checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      invalidPairCertificate _ syntaxResource hinvalidPairResource
      hsyntaxPositive
      hsyntax.validPairClosed hsyntax.invalidPairClosed hsyntax.validPairCode
      hsyntax.invalidPairCode hsyntax.choiceCode
  have hcodeTailResource :
      hybridFormulaStructuralPayloadBound codeTailCertificate <=
        relationInvalidCodeTailFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [codeTailCertificate]
    unfold relationInvalidCodeTailFullyFixedPayloadPolynomial
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      atCodeCertificate choiceCertificate _ _ syntaxResource hatCodeResource
      hchoiceResource hsyntaxPositive hsyntax.atCodeClosed
      hsyntax.choiceClosed hsyntax.atCodeCode hsyntax.choiceCode
      hsyntax.codeTailCode
  have harityTailResource :
      hybridFormulaStructuralPayloadBound arityTailCertificate <=
        relationInvalidArityTailFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [arityTailCertificate]
    unfold relationInvalidArityTailFullyFixedPayloadPolynomial
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      atArityCertificate codeTailCertificate _ _ syntaxResource
      hatArityResource hcodeTailResource hsyntaxPositive
      hsyntax.atArityClosed hsyntax.codeTailClosed hsyntax.atArityCode
      hsyntax.codeTailCode hsyntax.arityTailCode
  have hlongBranchResource :
      hybridFormulaStructuralPayloadBound longBranchCertificate <=
        relationInvalidLongBranchFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [longBranchCertificate]
    unfold relationInvalidLongBranchFullyFixedPayloadPolynomial
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      longGuardCertificate arityTailCertificate _ _ syntaxResource
      hlongGuardResource harityTailResource hsyntaxPositive
      hsyntax.longGuardClosed hsyntax.arityTailClosed hsyntax.longGuardCode
      hsyntax.arityTailCode hsyntax.longBranchCode
  have hbodyResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := shortBranch) longBranchCertificate
      (relationInvalidLongBranchFullyFixedPayloadPolynomial numericBound
        bitBound)
      syntaxResource hlongBranchResource hsyntaxPositive
      hsyntax.shortBranchClosed hsyntax.longBranchClosed
      hsyntax.shortBranchCode hsyntax.longBranchCode hsyntax.bodyCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := shortBranch) longBranchCertificate) <= _
  unfold relationInvalidBodyFullyFixedPayloadPolynomial
  simpa only [syntaxResource] using hbodyResource

#print axioms
  syntaxFormulaRelationInvalidBodyCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationInvalidFullyFixedBounds
