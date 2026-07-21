import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicFiniteUniversalBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicFiniteUniversalBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for a quantified syntax-formula transition

The running status, one-token drop, and quantified-task insertion are charged
under the original right-nested conjunction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

private abbrev quantifierZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate.zeroValuation

private abbrev quantifierNativeNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate.nativeNumeralTerm
    value

private theorem quantifierNativeNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (quantifierNativeNumeralTerm value).freeVariables = ∅ := by
  unfold quantifierNativeNumeralTerm
  unfold
    FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate.nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem quantifierNativeNumeralTerm_value
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (quantifierNativeNumeralTerm value) = value :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate.termValue_nativeNumeralTerm
    valuation value

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
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

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem binderSuccessorTerm_freeVariables_eq_empty
    (binderArity : Nat) :
    (binderSuccessorTerm binderArity).freeVariables = ∅ := by
  unfold binderSuccessorTerm
  rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

noncomputable def
    compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokenDropFormula :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1
  let taskConsFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount (quantifierNativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (quantifierNativeNumeralTerm 0)
  let dropConsResource := transparentHybridConjunctionPayloadEnvelope
    quantifierZeroValuation tokenDropFormula taskConsFormula
    (compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 hgraph.2.1)
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 1 (binderArity + 1) 0
      (quantifierNativeNumeralTerm 1) (binderSuccessorTerm binderArity)
      (quantifierNativeNumeralTerm 0) hgraph.2.2)
  transparentHybridConjunctionPayloadEnvelope quantifierZeroValuation
    runningFormula (tokenDropFormula ⋏ taskConsFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    dropConsResource

def compactUnifiedParserSyntaxFormulaQuantifierPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokenDropFormula :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1
  let taskConsFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount (quantifierNativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (quantifierNativeNumeralTerm 0)
  let dropConsResource := transparentHybridConjunctionPayloadEnvelope
    quantifierZeroValuation tokenDropFormula taskConsFormula
    (compactAdditiveNatListDropFixedNumeralRowsPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1)
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 1 (binderArity + 1) 0
      (quantifierNativeNumeralTerm 1) (binderSuccessorTerm binderArity)
      (quantifierNativeNumeralTerm 0))
  transparentHybridConjunctionPayloadEnvelope quantifierZeroValuation
    runningFormula (tokenDropFormula ⋏ taskConsFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    dropConsResource

theorem
    compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) :
    compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope tokenTable
        width tokenCount current next tailBoundary tailCount binderArity
        hgraph <=
      compactUnifiedParserSyntaxFormulaQuantifierPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next tailBoundary tailCount
        binderArity := by
  unfold compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope
    compactUnifiedParserSyntaxFormulaQuantifierPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      (compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount next.tokensBoundary next.tokensCount 1 hgraph.2.1)
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
        next.tasksCount 1 (binderArity + 1) 0
        (quantifierNativeNumeralTerm 1) (binderSuccessorTerm binderArity)
        (quantifierNativeNumeralTerm 0) hgraph.2.2))

theorem
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity hgraph) <=
      compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope tokenTable
        width tokenCount current next tailBoundary tailCount binderArity
        hgraph := by
  rcases hgraph with ⟨hrunning, htokens, htasks⟩
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  let tokenDropCertificate :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  let taskConsCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 1 (binderArity + 1) 0
      (quantifierNativeNumeralTerm 1) (binderSuccessorTerm binderArity)
      (quantifierNativeNumeralTerm 0)
      (quantifierNativeNumeralTerm_value · 1)
      (termValue_binderSuccessorTerm · binderArity)
      (quantifierNativeNumeralTerm_value · 0) htasks
  have hrunningResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  have htokensResource :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds.compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  have htasksResource :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 1 (binderArity + 1) 0
      (quantifierNativeNumeralTerm 1) (binderSuccessorTerm binderArity)
      (quantifierNativeNumeralTerm 0)
      (quantifierNativeNumeralTerm_freeVariables_eq_empty 1)
      (binderSuccessorTerm_freeVariables_eq_empty binderArity)
      (quantifierNativeNumeralTerm_freeVariables_eq_empty 0)
      (quantifierNativeNumeralTerm_value · 1)
      (termValue_binderSuccessorTerm · binderArity)
      (quantifierNativeNumeralTerm_value · 0) htasks
  let dropConsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokenDropCertificate taskConsCertificate
  have hdropCons := transparentHybridConjunctionPayloadBound_le
    tokenDropCertificate taskConsCertificate _ _ htokensResource
    htasksResource
  let partsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate dropConsCertificate
  have hparts := transparentHybridConjunctionPayloadBound_le runningCertificate
    dropConsCertificate _ _ hrunningResource hdropCons
  unfold
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound partsCertificate <= _
  exact hparts

theorem
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity hgraph) <=
      compactUnifiedParserSyntaxFormulaQuantifierPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next tailBoundary tailCount
        binderArity := by
  exact
    (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity hgraph).trans
    (compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity hgraph)

#print axioms
  compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierPublicBounds
