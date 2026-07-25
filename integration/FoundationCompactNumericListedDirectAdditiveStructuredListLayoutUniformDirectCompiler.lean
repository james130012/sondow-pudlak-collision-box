import integration.FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-!
# Uniform direct compiler for the additive structured-list layout

The body-start guard and list header retain their checked hybrid leaf
compilers.  The boundary-table leaf is replaced by the uniform direct closed
compiler.  The resulting three-leaf conjunction is installed with the actual
body-start witness by the certified PA existential-introduction constructor.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveBoundaryTableDirectCompiler
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev structuredZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private theorem structuredArithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem structuredArithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem compactAdditiveListHeaderClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start count bodyStart : Nat) :
    (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
      tokenTable width tokenCount start count bodyStart).freeVariables = ∅ := by
  unfold FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty start
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty bodyStart

theorem compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
      tokenCount start count finish boundaryTable).freeVariables = ∅ := by
  unfold compactAdditiveStructuredListLayoutClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty start
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty finish
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable

def compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope
    (tokenTable width tokenCount start count finish boundaryTable bodyStart
      numericBound bitBound : Nat) : Nat :=
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let witnessTerm := shortBinaryNumeralTerm bodyStart
  let guardFormula : ValuationFormula :=
    “!!witnessTerm < !!(shortBinaryNumeralTerm tokenCount) + 1”
  let headerFormula :=
    compactAdditiveListHeaderClosedFormula tokenTable width tokenCount start
      count bodyStart
  let boundaryFormula := compactAdditiveBoundaryTableClosedFormula tokenCount
    count bodyStart finish boundaryTable
  let guardResource := boundaryRowGuardStructuralPayloadResource
    structuredZeroValuation bodyStart tokenCount
  let headerResource := compactAdditiveListHeaderStructuralPayloadPolynomial
    tokenTable width tokenCount start count bodyStart
  let boundaryResource :=
    compactAdditiveBoundaryTableUniformDirectPayloadEnvelope tokenCount count
      bodyStart finish boundaryTable numericBound bitBound
  let innerResource := transparentHybridConjunctionPayloadEnvelope
    structuredZeroValuation headerFormula boundaryFormula headerResource
    boundaryResource
  let postResource := transparentHybridConjunctionPayloadEnvelope
    structuredZeroValuation guardFormula (headerFormula ⋏ boundaryFormula)
    guardResource innerResource
  postResource + CertifiedPAContextProof.existsIntroFullAssemblyCost ∅
    witnessBody witnessTerm

noncomputable def
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
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
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof ∅
      (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
        tokenCount start count finish boundaryTable) := by
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let witnessTerm := shortBinaryNumeralTerm bodyStart
  let guardFormula : ValuationFormula :=
    “!!witnessTerm < !!(shortBinaryNumeralTerm tokenCount) + 1”
  let headerFormula :=
    FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
      tokenTable width tokenCount start count bodyStart
  let boundaryFormula := compactAdditiveBoundaryTableClosedFormula tokenCount
    count bodyStart finish boundaryTable
  let guardCertificate := boundedWitnessGuardCertificate
    structuredZeroValuation bodyStart tokenCount hbodyStart
  let headerCertificate := compactAdditiveListHeaderExplicitHybridCertificate
    tokenTable width tokenCount start count bodyStart hheader
  let boundaryRaw :=
    compileCompactAdditiveBoundaryTableUniformDirectClosedContext tokenCount
      count bodyStart finish boundaryTable numericBound bitBound hbodyStart
      hboundaryFinish hboundaryStartEntry hboundaryFinishEntry rows htokenCount
      hcount htableSize hnumericSize
  have hboundaryContext : (∅ : Finset ValuationFormula) =
      valuationContext boundaryFormula.freeVariables structuredZeroValuation := by
    rw [show boundaryFormula.freeVariables = ∅ by
      simpa only [boundaryFormula] using
        compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
          tokenCount count bodyStart finish boundaryTable]
    simp [valuationContext]
  let boundaryProof := CertifiedPAContextProof.castContext hboundaryContext
    boundaryRaw
  let inner := compileDirectConjunction headerCertificate.compile boundaryProof
  let post := compileDirectConjunction guardCertificate.compile inner
  have hpostFree :
      (guardFormula ⋏ (headerFormula ⋏ boundaryFormula)).freeVariables = ∅ := by
    have hguard : guardFormula.freeVariables = ∅ := by
      dsimp only [guardFormula, witnessTerm]
      simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
      rw [structuredArithmeticAddTerm_freeVariables,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        structuredArithmeticOneTerm_freeVariables_eq_empty]
      simp
    have hheader : headerFormula.freeVariables = ∅ := by
      simpa only [headerFormula] using
        compactAdditiveListHeaderClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount start count bodyStart
    have hboundary : boundaryFormula.freeVariables = ∅ := by
      simpa only [boundaryFormula] using
        compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
          tokenCount count bodyStart finish boundaryTable
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hguard, hheader,
      hboundary, Finset.empty_union]
  have hpostContext :
      valuationContext
          (guardFormula ⋏ (headerFormula ⋏ boundaryFormula)).freeVariables
          structuredZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [hpostFree]
    simp [valuationContext]
  let postAtEmpty := CertifiedPAContextProof.castContext hpostContext post
  let installed := CertifiedPAContextProof.cast
    (compactAdditiveStructuredListLayoutWitnessBody_subst tokenTable width
      tokenCount start count finish boundaryTable bodyStart).symm postAtEmpty
  let direct := CertifiedPAContextProof.existsIntro witnessTerm installed
  exact CertifiedPAContextProof.cast
    (compactAdditiveStructuredListLayoutClosedFormula_alignment tokenTable
      width tokenCount start count finish boundaryTable).symm direct

theorem
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le
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
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount start count finish boundaryTable bodyStart
      numericBound bitBound hbodyStart hheader hboundaryFinish
      hboundaryStartEntry hboundaryFinishEntry rows htokenCount hcount
      htableSize hnumericSize).payloadLength <=
      compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope
        tokenTable width tokenCount start count finish boundaryTable bodyStart
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
  let guardCertificate := boundedWitnessGuardCertificate
    structuredZeroValuation bodyStart tokenCount hbodyStart
  let headerCertificate := compactAdditiveListHeaderExplicitHybridCertificate
    tokenTable width tokenCount start count bodyStart hheader
  let boundaryRaw :=
    compileCompactAdditiveBoundaryTableUniformDirectClosedContext tokenCount
      count bodyStart finish boundaryTable numericBound bitBound hbodyStart
      hboundaryFinish hboundaryStartEntry hboundaryFinishEntry rows htokenCount
      hcount htableSize hnumericSize
  have hboundaryContext : (∅ : Finset ValuationFormula) =
      valuationContext boundaryFormula.freeVariables structuredZeroValuation := by
    rw [show boundaryFormula.freeVariables = ∅ by
      simpa only [boundaryFormula] using
        compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
          tokenCount count bodyStart finish boundaryTable]
    simp [valuationContext]
  let boundaryProof := CertifiedPAContextProof.castContext hboundaryContext
    boundaryRaw
  let guardResource := boundaryRowGuardStructuralPayloadResource
    structuredZeroValuation bodyStart tokenCount
  let headerResource := compactAdditiveListHeaderStructuralPayloadPolynomial
    tokenTable width tokenCount start count bodyStart
  let boundaryResource :=
    compactAdditiveBoundaryTableUniformDirectPayloadEnvelope tokenCount count
      bodyStart finish boundaryTable numericBound bitBound
  have hguard : guardCertificate.compile.payloadLength <= guardResource :=
    (compile_payloadLength_le_structuralPayloadBound guardCertificate).trans
      (boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
        structuredZeroValuation bodyStart tokenCount hbodyStart)
  have hheader : headerCertificate.compile.payloadLength <= headerResource :=
    (compile_payloadLength_le_structuralPayloadBound headerCertificate).trans
      (compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenTable width tokenCount start count bodyStart hheader)
  have hboundaryRaw : boundaryRaw.payloadLength <= boundaryResource :=
    compileCompactAdditiveBoundaryTableUniformDirectClosedContext_payloadLength_le
      tokenCount count bodyStart finish boundaryTable numericBound bitBound
      hbodyStart hboundaryFinish hboundaryStartEntry hboundaryFinishEntry rows
      htokenCount hcount htableSize hnumericSize
  have hboundary : boundaryProof.payloadLength <= boundaryResource := by
    dsimp only [boundaryProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hboundaryRaw
  let inner := compileDirectConjunction headerCertificate.compile boundaryProof
  let innerResource := transparentHybridConjunctionPayloadEnvelope
    structuredZeroValuation headerFormula boundaryFormula headerResource
    boundaryResource
  have hinner : inner.payloadLength <= innerResource :=
    compileDirectConjunction_payloadLength_le headerCertificate.compile
      boundaryProof headerResource boundaryResource hheader hboundary
  let post := compileDirectConjunction guardCertificate.compile inner
  let postResource := transparentHybridConjunctionPayloadEnvelope
    structuredZeroValuation guardFormula (headerFormula ⋏ boundaryFormula)
    guardResource innerResource
  have hpost : post.payloadLength <= postResource :=
    compileDirectConjunction_payloadLength_le guardCertificate.compile inner
      guardResource innerResource hguard hinner
  have hguardFree : guardFormula.freeVariables = ∅ := by
    dsimp only [guardFormula, witnessTerm]
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
    rw [structuredArithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      structuredArithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hheaderFree : headerFormula.freeVariables = ∅ := by
    simpa only [headerFormula] using
      compactAdditiveListHeaderClosedFormula_freeVariables_eq_empty tokenTable
        width tokenCount start count bodyStart
  have hboundaryFree : boundaryFormula.freeVariables = ∅ := by
    simpa only [boundaryFormula] using
      compactAdditiveBoundaryTableClosedFormula_freeVariables_eq_empty
        tokenCount count bodyStart finish boundaryTable
  have hpostFree :
      (guardFormula ⋏ (headerFormula ⋏ boundaryFormula)).freeVariables = ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hguardFree,
      hheaderFree, hboundaryFree, Finset.empty_union]
  have hpostContext :
      valuationContext
          (guardFormula ⋏ (headerFormula ⋏ boundaryFormula)).freeVariables
          structuredZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [hpostFree]
    simp [valuationContext]
  let postAtEmpty := CertifiedPAContextProof.castContext hpostContext post
  have hpostAtEmpty : postAtEmpty.payloadLength <= postResource := by
    dsimp only [postAtEmpty]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hpost
  let installed := CertifiedPAContextProof.cast
    (compactAdditiveStructuredListLayoutWitnessBody_subst tokenTable width
      tokenCount start count finish boundaryTable bodyStart).symm postAtEmpty
  have hinstalled : installed.payloadLength <= postResource := by
    dsimp only [installed]
    rw [CertifiedPAContextProof.cast_payloadLength]
    exact hpostAtEmpty
  let direct := CertifiedPAContextProof.existsIntro witnessTerm installed
  have hdirectRaw := CertifiedPAContextProof.existsIntro_payloadLength_le
    witnessTerm installed
  have hdirect : direct.payloadLength <= postResource +
      CertifiedPAContextProof.existsIntroFullAssemblyCost ∅ witnessBody
        witnessTerm := by
    dsimp only [direct]
    exact hdirectRaw.trans (Nat.add_le_add_right hinstalled _)
  unfold compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  simpa only [
    compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope,
    witnessBody, witnessTerm, guardFormula, headerFormula, boundaryFormula,
    guardCertificate, headerCertificate, boundaryRaw, boundaryProof,
    guardResource, headerResource, boundaryResource, inner, innerResource,
    post, postResource, hpostContext, postAtEmpty, installed, direct] using
      hdirect

#print axioms compactAdditiveListHeaderClosedFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
#print axioms
  compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
#print axioms
  compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
