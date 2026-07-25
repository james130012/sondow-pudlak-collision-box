import integration.FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalFixedBounds
import integration.FoundationCompactPAContextualBranchesFixedAssembly
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fixed offset branches over arbitrary closed token-slice starts

The completed bit-universal leaves are assembled through finite exhaustion
without replacing composite starts by numerals.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBranchesFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridBranchesLeafResourceMonotonicity
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAContextualBranchesFixedAssembly
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBodyFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalFixedBounds

def tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial
    (numericBound termCode : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial numericBound
        termCode) +
    2 * tokenSliceClosedTermOffsetUniversalBodyCodePolynomial termCode

def tokenSliceClosedTermOffsetUniversalLocalPayloadFixedPolynomial
    (numericBound termCode : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial numericBound
      termCode)

def tokenSliceClosedTermOffsetBranchesFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (tokenSliceClosedTermOffsetUniversalLeafSumFixedPolynomial numericBound
        termCode bitBound +
      3 * tokenSliceClosedTermOffsetUniversalLocalPayloadFixedPolynomial
        numericBound termCode)

def tokenSliceClosedTermOffsetContextualBranchesFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  contextualBranchesFixedAssemblyEnvelope
    (tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial numericBound
      termCode)
    (tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial numericBound
      termCode)
    (tokenSliceClosedTermOffsetBranchesFullyFixedPayloadPolynomial numericBound
      termCode bitBound)

theorem
    tokenSliceAtValuationOffsetBranchesTransparentEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound) :
    tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm count <=
      tokenSliceClosedTermOffsetBranchesFullyFixedPayloadPolynomial
        numericBound termCode bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    tokenSliceClosedTermOffsetUniversalLeafSumFixedPolynomial numericBound
      termCode bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope count outerVariables
      valuation body
      (tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
        tableTerm widthTerm sourceStartTerm targetStartTerm count) count
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope count outerVariables
      valuation body leafBound count
  let Gamma :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma count count body
      leafBound
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body, boundTerm, tableTerm,
      widthTerm]
    exact
      tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty_closed
        tokenTable width count sourceStartTerm targetStartTerm hsourceClosed
        htargetClosed
  have hleaf :
      tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation tableTerm
          widthTerm sourceStartTerm targetStartTerm count <= leafBound := by
    dsimp only [tableTerm, widthTerm, leafBound]
    exact
      tokenSliceAtValuationOffsetBranchPayloadResourceSum_le_closedFixed
        valuation tokenTable width count numericBound termCode bitBound
        sourceStartTerm targetStartTerm hsourceClosed htargetClosed htableCode
        hwidthCode hsourceCode htargetCode hwidth hsource htarget hcount
        htableSize hwidthSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf count
      outerVariables valuation body hleaf count
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [houter]
    simp [valuationContext]
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        count outerVariables valuation body leafBound
        (by rw [houter]; simp [valuationContext]) (caseCount := count) le_rfl
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceClosedTermOffsetUniversalBodyCodePolynomial termCode := by
    dsimp only [body, tableTerm, widthTerm]
    exact tokenSliceAtValuationOffsetBody_code_length_le_closedFixed
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      sourceStartTerm targetStartTerm termCode htableCode hwidthCode
      hsourceCode htargetCode
  have hsyntax :
      explicitHybridUniversalSyntaxResource count body <=
        tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial numericBound
          termCode := by
    unfold explicitHybridUniversalSyntaxResource
      tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial
    exact Nat.add_le_add hcount hbody
  have hformula :
      explicitHybridUniversalFormulaEnvelope count body <=
        tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial numericBound
          termCode := by
    have hclosed :=
      boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
    unfold explicitHybridUniversalFormulaEnvelope
      tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial
    exact Nat.add_le_add hclosed (Nat.mul_le_mul_left 2 hbody)
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma count body <=
        tokenSliceClosedTermOffsetUniversalLocalPayloadFixedPolynomial
          numericBound termCode := by
    unfold tokenSliceClosedTermOffsetUniversalLocalPayloadFixedPolynomial
      contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
    rw [hGamma]
    simp only [contextualHybridUniversalFormulaCodeSum, Finset.sum_empty,
      Nat.add_zero]
    exact smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        tokenSliceClosedTermOffsetBranchesFullyFixedPayloadPolynomial
          numericBound termCode bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      tokenSliceClosedTermOffsetBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
          tableTerm widthTerm sourceStartTerm targetStartTerm count =
        exactCore := by
    unfold tokenSliceAtValuationOffsetBranchesTransparentEnvelope
    simp only [termValue_shortBinaryNumeralTerm]
    rfl
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

theorem
    tokenSliceAtValuationOffsetContextualBranchesResource_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm
      sourceStartTerm targetStartTerm
    contextualBranchesUnderBoundPayloadEnvelope ∅ count
        (Rewriting.free body)
        (tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
          tableTerm widthTerm sourceStartTerm targetStartTerm count) <=
      tokenSliceClosedTermOffsetContextualBranchesFixedPayloadPolynomial
        numericBound termCode bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm
    sourceStartTerm targetStartTerm
  let targetFormula := Rewriting.free body
  let caseResource :=
    tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
      tableTerm widthTerm sourceStartTerm targetStartTerm count
  let syntaxCode :=
    tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial numericBound
      termCode
  let formulaCode :=
    tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial numericBound
      termCode
  let caseBound :=
    tokenSliceClosedTermOffsetBranchesFullyFixedPayloadPolynomial numericBound
      termCode bitBound
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceClosedTermOffsetUniversalBodyCodePolynomial termCode := by
    dsimp only [body, tableTerm, widthTerm]
    exact tokenSliceAtValuationOffsetBody_code_length_le_closedFixed
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      sourceStartTerm targetStartTerm termCode htableCode hwidthCode
      hsourceCode htargetCode
  have htargetFormula :
      (binaryFormulaCode targetFormula).length <= formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula, formulaCode]
    unfold tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial
    omega
  have hclosed :
      boundedUniversalClosedFormulaEnvelope syntaxCode <= formulaCode := by
    dsimp only [syntaxCode, formulaCode]
    unfold tokenSliceClosedTermOffsetUniversalFormulaFixedPolynomial
    omega
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound, tableTerm, widthTerm]
    exact
      tokenSliceAtValuationOffsetBranchesTransparentEnvelope_le_closedFixed
        valuation tokenTable width count numericBound termCode bitBound
        sourceStartTerm targetStartTerm hsourceClosed htargetClosed htableCode
        hwidthCode hsourceCode htargetCode hwidth hsource htarget hcount
        htableSize hwidthSize
  have hassembled :=
    contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly ∅ count
      syntaxCode formulaCode caseResource caseBound targetFormula
      (by
        dsimp only [syntaxCode]
        unfold tokenSliceClosedTermOffsetUniversalSyntaxFixedPolynomial
        omega)
      hclosed htargetFormula (by simp)
      (by
        intro formula hformula
        simp at hformula)
      hcase
  unfold tokenSliceClosedTermOffsetContextualBranchesFixedPayloadPolynomial
  simpa only [tableTerm, widthTerm, body, targetFormula, caseResource,
    syntaxCode, formulaCode, caseBound] using hassembled

#print axioms
  tokenSliceAtValuationOffsetBranchesTransparentEnvelope_le_closedFixed
#print axioms
  tokenSliceAtValuationOffsetContextualBranchesResource_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBranchesFixedBounds
