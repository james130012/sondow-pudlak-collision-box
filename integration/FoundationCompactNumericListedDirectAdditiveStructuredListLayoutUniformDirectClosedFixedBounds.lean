import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds

/-!
# Closed fixed payload bound for the uniform direct structured-list layout

The concrete body-start witness is retained by the compiler but removed from
its public payload bound.  Every child proof and every assembly operation is
charged to one common numeric/bit-width coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev layoutClosedFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

def structuredListLayoutGuardTermCodePolynomial (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  2 * numeralCode + (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def structuredListLayoutGuardFormulaCodePolynomial (bitBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (structuredListLayoutGuardTermCodePolynomial bitBound)

def structuredListLayoutGuardFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (structuredListLayoutGuardTermCodePolynomial bitBound)

theorem boundaryRowGuardStructuralPayloadResource_le_fixed
    (bodyStart tokenCount bitBound : Nat)
    (hbodyStartSize : Nat.size bodyStart <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound) :
    boundaryRowGuardStructuralPayloadResource layoutClosedFixedZeroValuation
        bodyStart tokenCount <=
      structuredListLayoutGuardFixedPayloadPolynomial bitBound := by
  let firstTerm := shortBinaryNumeralTerm bodyStart
  let countTerm := shortBinaryNumeralTerm tokenCount
  let oneTerm : ValuationTerm := ‘1’
  let secondTerm : ValuationTerm := ‘!!countTerm + !!oneTerm’
  let args : Fin 2 -> ValuationTerm := ![firstTerm, secondTerm]
  let termCode := structuredListLayoutGuardTermCodePolynomial bitBound
  have hfirstCode : (binaryTermCode firstTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope bodyStart bitBound
      hbodyStartSize
    exact hraw.trans (by
      unfold termCode structuredListLayoutGuardTermCodePolynomial
      dsimp only
      omega)
  have hcountCode := binaryNumeralTerm_code_length_le_envelope tokenCount
    bitBound htokenCountSize
  have hsecondRaw := arithmeticAddTerm_code_length_le countTerm oneTerm
  have hsecondCode : (binaryTermCode secondTerm).length <= termCode := by
    unfold termCode structuredListLayoutGuardTermCodePolynomial
    dsimp only [secondTerm, countTerm, oneTerm] at *
    omega
  have hfirstClosed : firstTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty bodyStart
  have hsecondClosed : secondTerm.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiterm.func Language.Add.add
        ![countTerm, oneTerm]).freeVariables = ∅
    ext candidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    simp [countTerm, oneTerm, shortBinaryNumeralTerm_freeVariables_eq_empty,
      LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_one,
      LO.FirstOrder.Semiterm.Operator.One.term_eq]
  have hfirstVariables : (args 0).freeVariables ⊆ {0} := by
    change firstTerm.freeVariables ⊆ {0}
    rw [hfirstClosed]
    simp
  have hsecondVariables : (args 1).freeVariables ⊆ {0} := by
    change secondTerm.freeVariables ⊆ {0}
    rw [hsecondClosed]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    layoutClosedFixedZeroValuation Language.ORing.Rel.lt args hfirstVariables
    hsecondVariables
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
    layoutClosedFixedZeroValuation Language.ORing.Rel.lt args 0 termCode
    hfirstVariables hsecondVariables (by rfl) hfirstCode hsecondCode
  simpa only [boundaryRowGuardStructuralPayloadResource,
    structuredListLayoutGuardFixedPayloadPolynomial, args, firstTerm,
    secondTerm, countTerm, oneTerm, termCode] using hpublic.trans hfixed

#print axioms boundaryRowGuardStructuralPayloadResource_le_fixed

theorem structuredListLayoutGuardFormula_code_length_le_fixed
    (bodyStart tokenCount bitBound : Nat)
    (hbodyStartSize : Nat.size bodyStart <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm bodyStart) <
        !!(shortBinaryNumeralTerm tokenCount) + 1” : ValuationFormula)).length <=
      structuredListLayoutGuardFormulaCodePolynomial bitBound := by
  let firstTerm := shortBinaryNumeralTerm bodyStart
  let countTerm := shortBinaryNumeralTerm tokenCount
  let oneTerm : ValuationTerm := ‘1’
  let secondTerm : ValuationTerm := ‘!!countTerm + !!oneTerm’
  let termCode := structuredListLayoutGuardTermCodePolynomial bitBound
  have hfirstCode : (binaryTermCode firstTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope bodyStart bitBound
      hbodyStartSize
    exact hraw.trans (by
      unfold termCode structuredListLayoutGuardTermCodePolynomial
      dsimp only
      omega)
  have hcountCode := binaryNumeralTerm_code_length_le_envelope tokenCount
    bitBound htokenCountSize
  have hsecondRaw := arithmeticAddTerm_code_length_le countTerm oneTerm
  have hsecondCode : (binaryTermCode secondTerm).length <= termCode := by
    unfold termCode structuredListLayoutGuardTermCodePolynomial
    dsimp only [secondTerm, countTerm, oneTerm] at *
    omega
  change (binaryFormulaCode
    (binaryRelationFormula Language.LT.lt firstTerm secondTerm)).length <= _
  exact (binaryRelationFormula_code_le_orderAtomic Language.LT.lt firstTerm
    secondTerm termCode hfirstCode hsecondCode).trans_eq (by rfl)

#print axioms structuredListLayoutGuardFormula_code_length_le_fixed

def structuredListLayoutBoundarySourceFormula :
    LO.FirstOrder.ArithmeticSemisentence 5 :=
  compactAdditiveBoundaryTableDef.val

def structuredListLayoutBoundaryFormulaCodePolynomial (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        structuredListLayoutBoundarySourceFormula)).length

def structuredListLayoutBoundaryClosedTerms
    (tokenCount count bodyStart finish boundaryTable : Nat) :
    Fin 5 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm count,
    shortBinaryNumeralTerm bodyStart, shortBinaryNumeralTerm finish,
    shortBinaryNumeralTerm boundaryTable]

private theorem compactAdditiveBoundaryTableClosedFormula_eq_rewriting
    (tokenCount count bodyStart finish boundaryTable : Nat) :
    compactAdditiveBoundaryTableClosedFormula tokenCount count bodyStart finish
        boundaryTable =
      (Rew.subst (structuredListLayoutBoundaryClosedTerms tokenCount count
          bodyStart finish boundaryTable)) ▹
        (Rewriting.emb (ξ := Nat)
          structuredListLayoutBoundarySourceFormula) := by
  rfl

theorem compactAdditiveBoundaryTableRewriting_code_length_le_fixed
    (tokenCount count bodyStart finish boundaryTable bitBound : Nat)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbodyStartSize : Nat.size bodyStart <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (htableSize : Nat.size boundaryTable <= bitBound) :
    (binaryFormulaCode
      ((Rew.subst (structuredListLayoutBoundaryClosedTerms tokenCount count
          bodyStart finish boundaryTable)) ▹
        (Rewriting.emb (ξ := Nat)
          structuredListLayoutBoundarySourceFormula))).length <=
      uniformRewritingFormulaCodeEnvelope
        (binaryNumeralTermCodeEnvelope bitBound)
        (binaryFormulaCode
          (Rewriting.emb (ξ := Nat)
            structuredListLayoutBoundarySourceFormula)).length := by
  apply binaryFormulaCode_rewriting_length_le_uniform
  constructor
  · intro coordinate
    rw [Rew.subst_bvar]
    fin_cases coordinate
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
        htokenCountSize
    · exact binaryNumeralTerm_code_length_le_envelope count bitBound hcountSize
    · exact binaryNumeralTerm_code_length_le_envelope bodyStart bitBound
        hbodyStartSize
    · exact binaryNumeralTerm_code_length_le_envelope finish bitBound
        hfinishSize
    · exact binaryNumeralTerm_code_length_le_envelope boundaryTable bitBound
        htableSize
  · intro coordinate
    simp

def structuredListLayoutSourceFormula :
    LO.FirstOrder.ArithmeticSemisentence 7 :=
  compactAdditiveStructuredListLayoutDef.val

def structuredListLayoutExistentialFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        structuredListLayoutSourceFormula)).length

def structuredListLayoutClosedTerms
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm start,
    shortBinaryNumeralTerm count, shortBinaryNumeralTerm finish,
    shortBinaryNumeralTerm boundaryTable]

private theorem compactAdditiveStructuredListLayoutClosedFormula_eq_rewriting
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    compactAdditiveStructuredListLayoutClosedFormula tokenTable width tokenCount
        start count finish boundaryTable =
      (Rew.subst (structuredListLayoutClosedTerms tokenTable width tokenCount
          start count finish boundaryTable)) ▹
        (Rewriting.emb (ξ := Nat) structuredListLayoutSourceFormula) := by
  rfl

theorem compactAdditiveStructuredListLayoutRewriting_code_length_le_fixed
    (tokenTable width tokenCount start count finish boundaryTable bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound) :
    (binaryFormulaCode
      ((Rew.subst (structuredListLayoutClosedTerms tokenTable width tokenCount
          start count finish boundaryTable)) ▹
        (Rewriting.emb (ξ := Nat)
          structuredListLayoutSourceFormula))).length <=
      uniformRewritingFormulaCodeEnvelope
        (binaryNumeralTermCodeEnvelope bitBound)
        (binaryFormulaCode
          (Rewriting.emb (ξ := Nat)
            structuredListLayoutSourceFormula)).length := by
  apply binaryFormulaCode_rewriting_length_le_uniform
  constructor
  · intro coordinate
    rw [Rew.subst_bvar]
    fin_cases coordinate
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
        htokenTableSize
    · exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
        htokenCountSize
    · exact binaryNumeralTerm_code_length_le_envelope start bitBound hstartSize
    · exact binaryNumeralTerm_code_length_le_envelope count bitBound hcountSize
    · exact binaryNumeralTerm_code_length_le_envelope finish bitBound
        hfinishSize
    · exact binaryNumeralTerm_code_length_le_envelope boundaryTable bitBound
        hboundaryTableSize
  · intro coordinate
    simp

def compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
    (bitBound : Nat) : Nat :=
  structuredListLayoutGuardFormulaCodePolynomial bitBound +
    structuredListHeaderAssemblySyntaxPolynomial bitBound +
    structuredListLayoutBoundaryFormulaCodePolynomial bitBound +
    structuredListLayoutExistentialFormulaCodePolynomial bitBound +
    binaryNumeralTermCodeEnvelope bitBound +
    2 * (binaryNatCode 4).length + 1

def compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
      bitBound
  structuredListLayoutGuardFixedPayloadPolynomial bitBound +
    compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound
      bitBound +
    compactAdditiveBoundaryTableUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    7 * generalContextAssemblyEnvelope syntaxResource

private theorem transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource rightResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hconjunctionCode : (binaryFormulaCode (left ⋏ right)).length <=
      syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource rightResource <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        rightResource := by
  have hclosed : (left ⋏ right).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hleftClosed,
      hrightClosed]
    simp
  have hcontext : formulaCodeSum
      (valuationContext (left ⋏ right).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
    valuation left right leftResource rightResource syntaxResource hpositive
    hcontext hleftCode hrightCode hconjunctionCode
  change hybridConjunctionStructuralPayloadEnvelope valuation left right
      leftResource rightResource <= _
  exact hraw

theorem
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
    (tokenTable width tokenCount start count finish boundaryTable bodyStart
      numericBound bitBound : Nat)
    (hbodyStart : bodyStart <= tokenCount)
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart)
    (hboundaryFinish : finish <= tokenCount)
    (hboundaryStartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 bodyStart)
    (hboundaryFinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount count finish)
    (rows : (index : Fin count) ->
      CompactAdditiveBoundaryTableRowData tokenCount boundaryTable index)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hboundaryTableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount start count finish boundaryTable bodyStart
      numericBound bitBound hbodyStart hheader hboundaryFinish
      hboundaryStartEntry hboundaryFinishEntry rows htokenCount hcount
      hboundaryTableSize hnumericSize).payloadLength <=
      compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound := by
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let witnessTerm := shortBinaryNumeralTerm bodyStart
  let guardFormula : ValuationFormula :=
    “!!witnessTerm < !!(shortBinaryNumeralTerm tokenCount) + 1”
  let headerFormula := compactAdditiveListHeaderClosedFormula tokenTable width
    tokenCount start count bodyStart
  let boundaryFormula := compactAdditiveBoundaryTableClosedFormula tokenCount
    count bodyStart finish boundaryTable
  let innerFormula := headerFormula ⋏ boundaryFormula
  let postFormula := guardFormula ⋏ innerFormula
  let existentialFormula : ValuationFormula := ∃⁰ witnessBody
  let guardCertificate := boundedWitnessGuardCertificate
    layoutClosedFixedZeroValuation bodyStart tokenCount hbodyStart
  let headerCertificate := compactAdditiveListHeaderExplicitHybridCertificate
    tokenTable width tokenCount start count bodyStart hheader
  let boundaryRaw :=
    compileCompactAdditiveBoundaryTableUniformDirectClosedContext tokenCount
      count bodyStart finish boundaryTable numericBound bitBound hbodyStart
      hboundaryFinish hboundaryStartEntry hboundaryFinishEntry rows htokenCount
      hcount hboundaryTableSize hnumericSize
  have hboundaryContext : (∅ : Finset ValuationFormula) =
      valuationContext boundaryFormula.freeVariables
        layoutClosedFixedZeroValuation := by
    rw [show boundaryFormula.freeVariables = ∅ by
      simpa only [boundaryFormula] using
        compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
          tokenCount count bodyStart finish boundaryTable]
    simp [valuationContext]
  let boundaryProof := CertifiedPAContextProof.castContext hboundaryContext
    boundaryRaw
  let guardResource := structuredListLayoutGuardFixedPayloadPolynomial bitBound
  let headerResource :=
    compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound bitBound
  let boundaryResource :=
    compactAdditiveBoundaryTableUniformDirectFixedPayloadPolynomial numericBound
      bitBound
  let syntaxResource :=
    compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
      bitBound
  let innerGeneral := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    headerResource boundaryResource
  let postGeneral := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    guardResource innerGeneral
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hcountSize : Nat.size count <= bitBound :=
    (Nat.size_le_size hcount).trans hnumericSize
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthBound).trans hnumericSize
  have hstartBound : start <= numericBound :=
    (Nat.le_of_lt hheader.1.1).trans htokenCount
  have hstartSize : Nat.size start <= bitBound :=
    (Nat.size_le_size hstartBound).trans hnumericSize
  have hbodyStartBound : bodyStart <= numericBound :=
    hbodyStart.trans htokenCount
  have hbodyStartSize : Nat.size bodyStart <= bitBound :=
    (Nat.size_le_size hbodyStartBound).trans hnumericSize
  have hfinishBound : finish <= numericBound :=
    hboundaryFinish.trans htokenCount
  have hfinishSize : Nat.size finish <= bitBound :=
    (Nat.size_le_size hfinishBound).trans hnumericSize
  have hguard : guardCertificate.compile.payloadLength <= guardResource := by
    have hstructural :=
      boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
        layoutClosedFixedZeroValuation bodyStart tokenCount hbodyStart
    have hfixed := boundaryRowGuardStructuralPayloadResource_le_fixed bodyStart
      tokenCount bitBound hbodyStartSize htokenCountSize
    exact (compile_payloadLength_le_structuralPayloadBound
      guardCertificate).trans (hstructural.trans hfixed)
  have hheaderPayload :
      headerCertificate.compile.payloadLength <= headerResource := by
    exact (compile_payloadLength_le_structuralPayloadBound
      headerCertificate).trans
        (compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_fixed
          tokenTable width tokenCount start count bodyStart numericBound bitBound
          hwidthBound hstartBound htokenTableSize hwidthSize htokenCountSize
          hstartSize hcountSize hbodyStartSize hheader)
  have hboundaryRaw : boundaryRaw.payloadLength <= boundaryResource := by
    exact
      (compileCompactAdditiveBoundaryTableUniformDirectClosedContext_payloadLength_le
        tokenCount count bodyStart finish boundaryTable numericBound bitBound
        hbodyStart hboundaryFinish hboundaryStartEntry hboundaryFinishEntry rows
        htokenCount hcount hboundaryTableSize hnumericSize).trans
      (compactAdditiveBoundaryTableUniformDirectPayloadEnvelope_le_fixed
        tokenCount count bodyStart finish boundaryTable numericBound bitBound
        hbodyStart hboundaryFinish htokenCount hcount hboundaryTableSize
        hnumericSize)
  have hboundary : boundaryProof.payloadLength <= boundaryResource := by
    dsimp only [boundaryProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hboundaryRaw
  have hguardClosed : guardFormula.freeVariables = ∅ := by
    let rightTerm : ValuationTerm :=
      ‘!!(shortBinaryNumeralTerm tokenCount) + 1’
    have hright : rightTerm.freeVariables = ∅ := by
      change
        (LO.FirstOrder.Semiterm.func Language.Add.add
          ![shortBinaryNumeralTerm tokenCount, (‘1’ : ValuationTerm)]).freeVariables =
            ∅
      ext candidate
      rw [LO.FirstOrder.Semiterm.freeVariables_func]
      simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
        LO.FirstOrder.Semiterm.Operator.operator,
        LO.FirstOrder.Semiterm.Operator.numeral_one,
        LO.FirstOrder.Semiterm.Operator.One.term_eq]
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![witnessTerm, rightTerm]).freeVariables = ∅
    ext candidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    simp [witnessTerm, rightTerm, hright,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
  have hheaderClosed : headerFormula.freeVariables = ∅ := by
    simpa only [headerFormula] using
      compactAdditiveListHeaderClosedFormula_freeVariables_eq_empty tokenTable
        width tokenCount start count bodyStart
  have hboundaryClosed : boundaryFormula.freeVariables = ∅ := by
    simpa only [boundaryFormula] using
      compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
        tokenCount count bodyStart finish boundaryTable
  have hinnerClosed : innerFormula.freeVariables = ∅ := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hheaderClosed,
      hboundaryClosed]
    simp
  have hpostClosed : postFormula.freeVariables = ∅ := by
    dsimp only [postFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hguardClosed,
      hinnerClosed]
    simp
  have hguardCodeTight : (binaryFormulaCode guardFormula).length <=
      structuredListLayoutGuardFormulaCodePolynomial bitBound := by
    simpa only [guardFormula, witnessTerm] using
      structuredListLayoutGuardFormula_code_length_le_fixed bodyStart tokenCount
        bitBound hbodyStartSize htokenCountSize
  have hheaderCodeTight : (binaryFormulaCode headerFormula).length <=
      structuredListHeaderAssemblySyntaxPolynomial bitBound := by
    simpa only [headerFormula] using
      compactAdditiveListHeaderClosedFormula_code_length_le_fixed tokenTable width
        tokenCount start count bodyStart bitBound htokenTableSize hwidthSize
        htokenCountSize hstartSize hcountSize hbodyStartSize
  have hboundaryCodeTight : (binaryFormulaCode boundaryFormula).length <=
      structuredListLayoutBoundaryFormulaCodePolynomial bitBound := by
    dsimp only [boundaryFormula]
    rw [compactAdditiveBoundaryTableClosedFormula_eq_rewriting]
    exact compactAdditiveBoundaryTableRewriting_code_length_le_fixed tokenCount
      count bodyStart finish boundaryTable bitBound htokenCountSize hcountSize
      hbodyStartSize hfinishSize hboundaryTableSize
  have hexistentialCodeTight :
      (binaryFormulaCode existentialFormula).length <=
        structuredListLayoutExistentialFormulaCodePolynomial bitBound := by
    have hclosed :
        (binaryFormulaCode
          (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
            tokenCount start count finish boundaryTable)).length <=
          structuredListLayoutExistentialFormulaCodePolynomial bitBound := by
      rw [compactAdditiveStructuredListLayoutClosedFormula_eq_rewriting]
      exact compactAdditiveStructuredListLayoutRewriting_code_length_le_fixed
        tokenTable width tokenCount start count finish boundaryTable bitBound
        htokenTableSize hwidthSize htokenCountSize hstartSize hcountSize
        hfinishSize hboundaryTableSize
    rw [compactAdditiveStructuredListLayoutClosedFormula_alignment] at hclosed
    simpa only [existentialFormula, witnessBody] using hclosed
  have hwitnessCodeTight : (binaryTermCode witnessTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope bodyStart bitBound
      hbodyStartSize
  have hinnerCodeTight : (binaryFormulaCode innerFormula).length <=
      structuredListHeaderAssemblySyntaxPolynomial bitBound +
        structuredListLayoutBoundaryFormulaCodePolynomial bitBound +
          (binaryNatCode 4).length := by
    dsimp only [innerFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hpostCodeTight : (binaryFormulaCode postFormula).length <=
      structuredListLayoutGuardFormulaCodePolynomial bitBound +
        structuredListHeaderAssemblySyntaxPolynomial bitBound +
        structuredListLayoutBoundaryFormulaCodePolynomial bitBound +
        2 * (binaryNatCode 4).length := by
    dsimp only [postFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
    exact Nat.le_add_left 1 _
  have hguardCode : (binaryFormulaCode guardFormula).length <= syntaxResource :=
    hguardCodeTight.trans (by
      dsimp only [syntaxResource]
      unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
      omega)
  have hheaderCode : (binaryFormulaCode headerFormula).length <= syntaxResource :=
    hheaderCodeTight.trans (by
      dsimp only [syntaxResource]
      unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
      omega)
  have hboundaryCode : (binaryFormulaCode boundaryFormula).length <=
      syntaxResource := hboundaryCodeTight.trans (by
    dsimp only [syntaxResource]
    unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
    omega)
  have hinnerCode : (binaryFormulaCode innerFormula).length <= syntaxResource :=
    hinnerCodeTight.trans (by
      dsimp only [syntaxResource]
      unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
      omega)
  have hpostCode : (binaryFormulaCode postFormula).length <= syntaxResource :=
    hpostCodeTight.trans (by
      dsimp only [syntaxResource]
      unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
      omega)
  have hexistentialCode : (binaryFormulaCode existentialFormula).length <=
      syntaxResource := hexistentialCodeTight.trans (by
    dsimp only [syntaxResource]
    unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
    omega)
  have hbodyCode : (binaryFormulaCode witnessBody).length <= syntaxResource := by
    have hbodyLe : (binaryFormulaCode witnessBody).length <=
        (binaryFormulaCode existentialFormula).length := by
      dsimp only [existentialFormula]
      simp only [binaryFormulaCode, List.length_append]
      omega
    exact hbodyLe.trans hexistentialCode
  have hwitnessCode : (binaryTermCode witnessTerm).length <= syntaxResource :=
    hwitnessCodeTight.trans (by
      dsimp only [syntaxResource]
      unfold compactAdditiveStructuredListLayoutUniformDirectAssemblySyntaxPolynomial
      omega)
  have hinnerEnvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      layoutClosedFixedZeroValuation headerFormula boundaryFormula
      headerResource boundaryResource syntaxResource hpositive hheaderClosed
      hboundaryClosed hheaderCode hboundaryCode hinnerCode
  let inner := compileDirectConjunction headerCertificate.compile boundaryProof
  have hinnerRaw : inner.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope layoutClosedFixedZeroValuation
        headerFormula boundaryFormula headerResource boundaryResource :=
    compileDirectConjunction_payloadLength_le headerCertificate.compile
      boundaryProof headerResource boundaryResource hheaderPayload hboundary
  have hinner : inner.payloadLength <= innerGeneral := by
    exact hinnerRaw.trans hinnerEnvelope
  have hpostEnvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      layoutClosedFixedZeroValuation guardFormula innerFormula guardResource
      innerGeneral syntaxResource hpositive hguardClosed hinnerClosed hguardCode
      hinnerCode hpostCode
  let post := compileDirectConjunction guardCertificate.compile inner
  have hpostRaw : post.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope layoutClosedFixedZeroValuation
        guardFormula innerFormula guardResource innerGeneral :=
    compileDirectConjunction_payloadLength_le guardCertificate.compile inner
      guardResource innerGeneral hguard hinner
  have hpost : post.payloadLength <= postGeneral :=
    hpostRaw.trans hpostEnvelope
  have hpostContext : valuationContext postFormula.freeVariables
      layoutClosedFixedZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [hpostClosed]
    simp [valuationContext]
  let postAtEmpty := CertifiedPAContextProof.castContext hpostContext post
  have hpostAtEmpty : postAtEmpty.payloadLength <= postGeneral := by
    dsimp only [postAtEmpty]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hpost
  let installed := CertifiedPAContextProof.cast
    (compactAdditiveStructuredListLayoutWitnessBody_subst tokenTable width
      tokenCount start count finish boundaryTable bodyStart).symm postAtEmpty
  have hinstalled : installed.payloadLength <= postGeneral := by
    dsimp only [installed]
    rw [CertifiedPAContextProof.cast_payloadLength]
    exact hpostAtEmpty
  have hexistsCost := existsIntroFullAssemblyCost_le_general
    (∅ : Finset ValuationFormula) witnessBody witnessTerm syntaxResource
    hpositive (by simp [formulaCodeSum]) hbodyCode hwitnessCode (by
      rw [compactAdditiveStructuredListLayoutWitnessBody_subst]
      simpa only [postFormula, innerFormula, guardFormula, headerFormula,
        boundaryFormula, witnessTerm] using hpostCode) (by
      simpa only [existentialFormula] using hexistentialCode)
  let direct := CertifiedPAContextProof.existsIntro witnessTerm installed
  have hdirectRaw := CertifiedPAContextProof.existsIntro_payloadLength_le
    witnessTerm installed
  have hdirect : direct.payloadLength <= postGeneral +
      generalContextAssemblyEnvelope syntaxResource := by
    dsimp only [direct]
    exact hdirectRaw.trans
      ((Nat.add_le_add hinstalled hexistsCost))
  unfold compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  have hfinal := hdirect
  dsimp only [postGeneral, innerGeneral, guardResource, headerResource,
    boundaryResource, syntaxResource] at hfinal
  unfold hybridConjunctionGeneralPayloadEnvelope at hfinal
  exact hfinal.trans (by
    unfold compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
    dsimp only
    omega)

#print axioms
  compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed

end FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
