import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsPublicFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialParserTaskAtRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds

/-!
# Public exact certificate for the formula-transform initial parser source
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceCertificate

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialParserTaskAtRowsFullyFixedBounds

private def sourceZeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate sourceZeroValuation formula

private theorem arithmeticRewritingApp_congr_initialParserSource
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

def compactFormulaTransformInitialParserSourcePublicExplicitFormula
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      inputBoundary inputCount coordinates.parserTokensBoundary
        coordinates.parserTokensCount ⋏
    (“!!(shortBinaryNumeralTerm coordinates.parserTasksCount) = 1” ⋏
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
          tokenTable width tokenCount coordinates.parserTasksBoundary
          coordinates.parserTasksCount (‘0’ : ValuationTerm)
          (‘1’ : ValuationTerm) (shortBinaryNumeralTerm binderArity)
          (‘0’ : ValuationTerm) ⋏
        compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount coordinates.parserTasksFinish coordinates.parserFinish))

theorem compactFormulaTransformInitialParserSourcePublicFormula_alignment
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates =
      compactFormulaTransformInitialParserSourcePublicExplicitFormula
        tokenTable width tokenCount inputBoundary inputCount binderArity
        coordinates := by
  unfold compactFormulaTransformInitialParserSourcePublicFormula
  unfold compactFormulaTransformInitialParserSourcePublicExplicitFormula
  unfold compactUnifiedParserInitialStateRowsDef
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr_initialParserSource
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

def compactFormulaTransformInitialParserSourceClosedTerms
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    Fin 16 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm coordinates.start,
    shortBinaryNumeralTerm coordinates.parserFinish,
    shortBinaryNumeralTerm coordinates.parserTokensFinish,
    shortBinaryNumeralTerm coordinates.parserTasksFinish,
    shortBinaryNumeralTerm coordinates.parserTokensBoundary,
    shortBinaryNumeralTerm coordinates.parserTokensCount,
    shortBinaryNumeralTerm coordinates.parserTasksBoundary,
    shortBinaryNumeralTerm coordinates.parserTasksCount,
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    (‘1’ : ValuationTerm),
    shortBinaryNumeralTerm binderArity,
    (‘0’ : ValuationTerm)]

def compactFormulaTransformInitialParserSourceTermCodeEnvelope
    (bitBound : Nat) : Nat :=
  max (binaryNumeralTermCodeEnvelope bitBound)
    (max (binaryTermCode (‘0’ : ValuationTerm)).length
      (binaryTermCode (‘1’ : ValuationTerm)).length)

def compactFormulaTransformInitialParserSourceFormulaCodeEnvelope
    (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (compactFormulaTransformInitialParserSourceTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserInitialStateRowsDef.val)).length

def compactFormulaTransformInitialParserSourceSyntaxResource
    (bitBound : Nat) : Nat :=
  compactFormulaTransformInitialParserSourceFormulaCodeEnvelope bitBound + 1

theorem compactFormulaTransformInitialParserSourcePublicFormula_code_length_le
    (tokenTable width tokenCount inputBoundary inputCount binderArity
      bitBound : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hparserFinishSize : Nat.size coordinates.parserFinish <= bitBound)
    (hparserTokensFinishSize :
      Nat.size coordinates.parserTokensFinish <= bitBound)
    (hparserTasksFinishSize :
      Nat.size coordinates.parserTasksFinish <= bitBound)
    (hparserTokensBoundarySize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTokensCountSize :
      Nat.size coordinates.parserTokensCount <= bitBound)
    (hparserTasksBoundarySize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (hparserTasksCountSize :
      Nat.size coordinates.parserTasksCount <= bitBound)
    (hinputBoundarySize : Nat.size inputBoundary <= bitBound)
    (hinputCountSize : Nat.size inputCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates)).length <=
      compactFormulaTransformInitialParserSourceSyntaxResource bitBound := by
  let terms := compactFormulaTransformInitialParserSourceClosedTerms tokenTable
    width tokenCount inputBoundary inputCount binderArity coordinates
  let source : ArithmeticSemiformula Nat 16 :=
    Rewriting.emb (ξ := Nat) compactUnifiedParserInitialStateRowsDef.val
  have hshort (value : Nat) (hsize : Nat.size value <= bitBound) :
      (binaryTermCode (shortBinaryNumeralTerm value)).length <=
        compactFormulaTransformInitialParserSourceTermCodeEnvelope
          bitBound :=
    (binaryNumeralTerm_code_length_le_envelope value bitBound hsize).trans
      (Nat.le_max_left _ _)
  have hzero : (binaryTermCode (‘0’ : ValuationTerm)).length <=
      compactFormulaTransformInitialParserSourceTermCodeEnvelope bitBound :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hone : (binaryTermCode (‘1’ : ValuationTerm)).length <=
      compactFormulaTransformInitialParserSourceTermCodeEnvelope bitBound :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        compactFormulaTransformInitialParserSourceTermCodeEnvelope
          bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact hshort tokenTable htokenTableSize
    · exact hshort width hwidthSize
    · exact hshort tokenCount htokenCountSize
    · exact hshort coordinates.start hstartSize
    · exact hshort coordinates.parserFinish hparserFinishSize
    · exact hshort coordinates.parserTokensFinish hparserTokensFinishSize
    · exact hshort coordinates.parserTasksFinish hparserTasksFinishSize
    · exact hshort coordinates.parserTokensBoundary hparserTokensBoundarySize
    · exact hshort coordinates.parserTokensCount hparserTokensCountSize
    · exact hshort coordinates.parserTasksBoundary hparserTasksBoundarySize
    · exact hshort coordinates.parserTasksCount hparserTasksCountSize
    · exact hshort inputBoundary hinputBoundarySize
    · exact hshort inputCount hinputCountSize
    · exact hone
    · exact hshort binderArity hbinderAritySize
    · exact hzero
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 (compactFormulaTransformInitialParserSourceTermCodeEnvelope bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  have hraw' := hraw.trans (Nat.le_succ _)
  unfold compactFormulaTransformInitialParserSourcePublicFormula
    compactFormulaTransformInitialParserSourceSyntaxResource
    compactFormulaTransformInitialParserSourceFormulaCodeEnvelope
  simpa only [sourceSubstitutionQpow, terms, source,
    compactFormulaTransformInitialParserSourceClosedTerms] using hraw'

theorem
    compactFormulaTransformInitialParserSourcePublicFormula_freeVariables_eq_empty
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    (compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
      tokenCount inputBoundary inputCount binderArity coordinates
      ).freeVariables = ∅ := by
  unfold compactFormulaTransformInitialParserSourcePublicFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
      Semiterm.Operator.operator]

noncomputable def
    compactFormulaTransformInitialParserSourcePublicCertificateOfGraph
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates.parser inputBoundary inputCount 1 binderArity 0) :
    HybridCertificate
      (compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity coordinates) := by
  rcases hgraph with ⟨hsame, htaskCount, htask, hrunning⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount inputBoundary inputCount
      coordinates.parserTokensBoundary coordinates.parserTokensCount hsame)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (parserInitialTaskCountOneCertificate coordinates.parserTasksCount
        htaskCount)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (formulaTransformInitialParserTaskCertificateOfGraph tokenTable width
          tokenCount coordinates.parserTasksBoundary
          coordinates.parserTasksCount binderArity htask)
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates.parserTasksFinish
          coordinates.parserFinish hrunning)))
  exact .cast
    (compactFormulaTransformInitialParserSourcePublicFormula_alignment
      tokenTable width tokenCount inputBoundary inputCount binderArity
      coordinates).symm parts

end FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceCertificate
