import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationValidFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationInvalidFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationShortFullyFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! Fully fixed selected relation branches for tags `{0, 1}`. -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationSelectedFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongCertificates
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationShortFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationValidFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationInvalidFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactArithmeticSymbolCode

def syntaxFormulaRelationSelectedCodePolynomial
    (bodyResource bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound + bodyResource + 9

def syntaxFormulaRelationSelectedFullyFixedPayloadPolynomial
    (bodyResource bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationSelectedCodePolynomial bodyResource bitBound)
    (parserFormulaEqEitherFixedPayloadPolynomial bitBound) bodyResource

private theorem relationSelectedCertificate_structuralPayloadBound_le_fixed
    {valuation : Nat -> Nat}
    (tag body : ValuationFormula)
    (tagCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation tag)
    (bodyCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation body)
    (bodyResource bitBound : Nat)
    (htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <=
        parserFormulaEqEitherFixedPayloadPolynomial bitBound)
    (hbodyResource :
      hybridFormulaStructuralPayloadBound bodyCertificate <= bodyResource)
    (htagClosed : tag.freeVariables = ∅)
    (hbodyClosed : body.freeVariables = ∅)
    (htagCode :
      (binaryFormulaCode tag).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          tagCertificate bodyCertificate) <=
      syntaxFormulaRelationSelectedFullyFixedPayloadPolynomial bodyResource
        bitBound := by
  let syntaxResource :=
    syntaxFormulaRelationSelectedCodePolynomial bodyResource bitBound
  have hbodyCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      bodyCertificate
  have hbodyCode :
      (binaryFormulaCode body).length <= bodyResource :=
    hbodyCodeRaw.trans hbodyResource
  have hfullRaw := binaryFormulaCode_and_length_le tag body
  have htagCodeTotal :
      (binaryFormulaCode tag).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold syntaxFormulaRelationSelectedCodePolynomial
    omega
  have hbodyCodeTotal :
      (binaryFormulaCode body).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold syntaxFormulaRelationSelectedCodePolynomial
    omega
  have hfullCode :
      (binaryFormulaCode (tag ⋏ body)).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold syntaxFormulaRelationSelectedCodePolynomial
    omega
  unfold syntaxFormulaRelationSelectedFullyFixedPayloadPolynomial
  exact checkedHybridConjunctionPayloadBound_le_closedGeneral tagCertificate
    bodyCertificate _ _ syntaxResource htagResource hbodyResource
    (by
      dsimp only [syntaxResource]
      unfold syntaxFormulaRelationSelectedCodePolynomial
      omega)
    htagClosed hbodyClosed htagCodeTotal hbodyCodeTotal hfullCode

def syntaxFormulaRelationShortSelectedFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaRelationSelectedFullyFixedPayloadPolynomial
    (syntaxFormulaRelationShortBodyFullyFixedPayloadPolynomial numericBound
      bitBound)
    bitBound

theorem
    syntaxFormulaRelationShortSelectedCertificate_structuralPayloadBound_le_fullyFixed
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
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
          (syntaxFormulaRelationShortBodyCertificate tokenTable width
            tokenCount current next binderArity witness hshort hfailure)) <=
      syntaxFormulaRelationShortSelectedFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 0 ⋎ nativeEqFormula witness.tag 1
  let bodyFormula :=
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
      width tokenCount current next binderArity witness
  let tagCertificate :=
    nativeEqEitherCertificateFromData witness.tag 0 1 htag
  let bodyCertificate :=
    syntaxFormulaRelationShortBodyCertificate tokenTable width tokenCount
      current next binderArity witness hshort hfailure
  have htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <=
        parserFormulaEqEitherFixedPayloadPolynomial bitBound := by
    dsimp only [tagCertificate]
    exact nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
      witness.tag 0 1 bitBound htag htagSize (by omega) (by omega)
  have hbodyResource :
      hybridFormulaStructuralPayloadBound bodyCertificate <=
        syntaxFormulaRelationShortBodyFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [bodyCertificate]
    exact
      syntaxFormulaRelationShortBodyCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness
        numericBound bitBound hshort hfailure hwidth htokenCount htailCount
        hcurrentValue hnextValue htokenTableSize hwidthSize htokenCountSize
        hcurrentSize hnextSize htailBoundarySize hbinderAritySize
        hrelationAritySize hrelationCodeSize hnumericSize hbitPositive
  have htagClosed : tagFormula.freeVariables = ∅ := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_freeVariables_eq_empty_fixed witness.tag 0 1
  have hbodyClosed : bodyFormula.freeVariables = ∅ := by
    dsimp only [bodyFormula]
    exact
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount current next binderArity witness
  have htagCode :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 0 1 bitBound
      htagSize (by omega) (by omega)
  unfold syntaxFormulaRelationShortSelectedFullyFixedPayloadPolynomial
  simpa only [tagFormula, bodyFormula, tagCertificate, bodyCertificate] using
    relationSelectedCertificate_structuralPayloadBound_le_fixed tagFormula
      bodyFormula tagCertificate bodyCertificate
      (syntaxFormulaRelationShortBodyFullyFixedPayloadPolynomial numericBound
        bitBound)
      bitBound htagResource hbodyResource htagClosed hbodyClosed htagCode

def syntaxFormulaRelationValidSelectedFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  syntaxFormulaRelationSelectedFullyFixedPayloadPolynomial
    (relationValidBodyFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)
    bitBound

theorem
    syntaxFormulaRelationValidSelectedCertificate_structuralPayloadBound_le_fullyFixed
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
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
          (syntaxFormulaRelationValidBodyCertificate tokenTable width
            tokenCount current next binderArity witness hthree hatArity
            hatCode hvalid hfunction)) <=
      syntaxFormulaRelationValidSelectedFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 0 ⋎ nativeEqFormula witness.tag 1
  let bodyFormula :=
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
      width tokenCount current next binderArity witness
  let tagCertificate :=
    nativeEqEitherCertificateFromData witness.tag 0 1 htag
  let bodyCertificate :=
    syntaxFormulaRelationValidBodyCertificate tokenTable width tokenCount
      current next binderArity witness hthree hatArity hatCode hvalid hfunction
  have htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <=
        parserFormulaEqEitherFixedPayloadPolynomial bitBound := by
    dsimp only [tagCertificate]
    exact nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
      witness.tag 0 1 bitBound htag htagSize (by omega) (by omega)
  have hbodyResource :
      hybridFormulaStructuralPayloadBound bodyCertificate <=
        relationValidBodyFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound := by
    dsimp only [bodyCertificate]
    exact
      syntaxFormulaRelationValidBodyCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness
        numericBound bitBound hthree hatArity hatCode hvalid hfunction hwidth
        htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize hnumericSize
  have htagClosed : tagFormula.freeVariables = ∅ := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_freeVariables_eq_empty_fixed witness.tag 0 1
  have hbodyClosed : bodyFormula.freeVariables = ∅ := by
    dsimp only [bodyFormula]
    exact
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount current next binderArity witness
  have htagCode :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 0 1 bitBound
      htagSize (by omega) (by omega)
  unfold syntaxFormulaRelationValidSelectedFullyFixedPayloadPolynomial
  simpa only [tagFormula, bodyFormula, tagCertificate, bodyCertificate] using
    relationSelectedCertificate_structuralPayloadBound_le_fixed tagFormula
      bodyFormula tagCertificate bodyCertificate
      (relationValidBodyFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)
      bitBound htagResource hbodyResource htagClosed hbodyClosed htagCode

def syntaxFormulaRelationInvalidSelectedFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxFormulaRelationSelectedFullyFixedPayloadPolynomial
    (relationInvalidBodyFullyFixedPayloadPolynomial numericBound bitBound)
    bitBound

theorem
    syntaxFormulaRelationInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed
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
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
          (syntaxFormulaRelationInvalidBodyCertificate tokenTable width
            tokenCount current next binderArity witness hthree hatArity
            hatCode hinvalid hfailure)) <=
      syntaxFormulaRelationInvalidSelectedFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 0 ⋎ nativeEqFormula witness.tag 1
  let bodyFormula :=
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
      width tokenCount current next binderArity witness
  let tagCertificate :=
    nativeEqEitherCertificateFromData witness.tag 0 1 htag
  let bodyCertificate :=
    syntaxFormulaRelationInvalidBodyCertificate tokenTable width tokenCount
      current next binderArity witness hthree hatArity hatCode hinvalid
      hfailure
  have htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <=
        parserFormulaEqEitherFixedPayloadPolynomial bitBound := by
    dsimp only [tagCertificate]
    exact nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
      witness.tag 0 1 bitBound htag htagSize (by omega) (by omega)
  have hbodyResource :
      hybridFormulaStructuralPayloadBound bodyCertificate <=
        relationInvalidBodyFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [bodyCertificate]
    exact
      syntaxFormulaRelationInvalidBodyCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity witness
        numericBound bitBound hthree hatArity hatCode hinvalid hfailure hwidth
        htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize hnumericSize
  have htagClosed : tagFormula.freeVariables = ∅ := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_freeVariables_eq_empty_fixed witness.tag 0 1
  have hbodyClosed : bodyFormula.freeVariables = ∅ := by
    dsimp only [bodyFormula]
    exact
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount current next binderArity witness
  have htagCode :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 0 1 bitBound
      htagSize (by omega) (by omega)
  unfold syntaxFormulaRelationInvalidSelectedFullyFixedPayloadPolynomial
  simpa only [tagFormula, bodyFormula, tagCertificate, bodyCertificate] using
    relationSelectedCertificate_structuralPayloadBound_le_fixed tagFormula
      bodyFormula tagCertificate bodyCertificate
      (relationInvalidBodyFullyFixedPayloadPolynomial numericBound bitBound)
      bitBound htagResource hbodyResource htagClosed hbodyClosed htagCode

#print axioms
  syntaxFormulaRelationShortSelectedCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaRelationValidSelectedCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxFormulaRelationInvalidSelectedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationSelectedFullyFixedBounds
