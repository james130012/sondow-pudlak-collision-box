import integration.FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFixedBounds
import integration.FoundationCompactPAContextualBranchesFixedAssembly

/-!
# Fully fixed offset branches for token slices

The finite offset family is bounded by the completed bit-universal leaf
polynomial, then charged for finite exhaustion and contextual assembly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridBranchesLeafResourceMonotonicity
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAContextualBranchesFixedAssembly
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFixedBounds

def tokenSliceOffsetUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (tokenSliceOffsetUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * tokenSliceOffsetUniversalBodyCodePolynomial numericBound bitBound

def tokenSliceOffsetUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (tokenSliceOffsetUniversalFormulaFixedPolynomial numericBound bitBound)

def tokenSliceOffsetBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (tokenSliceOffsetUniversalLeafSumFixedPolynomial numericBound bitBound +
      3 * tokenSliceOffsetUniversalLocalPayloadFixedPolynomial numericBound
        bitBound)

def tokenSliceOffsetContextualBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  contextualBranchesFixedAssemblyEnvelope
    (tokenSliceOffsetUniversalSyntaxFixedPolynomial numericBound bitBound)
    (tokenSliceOffsetUniversalFormulaFixedPolynomial numericBound bitBound)
    (tokenSliceOffsetBranchesFullyFixedPayloadPolynomial numericBound bitBound)

theorem tokenSliceAtValuationOffsetBranchesTransparentEnvelope_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart count numericBound bitBound :
      Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) count <=
      tokenSliceOffsetBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceTerm
    targetTerm
  let boundTerm := shortBinaryNumeralTerm count
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let leafBound :=
    tokenSliceOffsetUniversalLeafSumFixedPolynomial numericBound bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope count outerVariables
      valuation body
      (tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation
        tableTerm widthTerm sourceTerm targetTerm count) count
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
      widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty
      tokenTable width sourceStart targetStart count
  have hleaf :
      tokenSliceAtValuationOffsetBranchPayloadResourceSum valuation tableTerm
          widthTerm sourceTerm targetTerm count <= leafBound := by
    dsimp only [tableTerm, widthTerm, sourceTerm, targetTerm, leafBound]
    exact tokenSliceAtValuationOffsetBranchPayloadResourceSum_le_fullyFixed
      valuation tokenTable width sourceStart targetStart count numericBound
      bitBound hwidth hsourceStart htargetStart hcount htableSize hwidthSize
      hsourceStartSize htargetStartSize
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
        tokenSliceOffsetUniversalBodyCodePolynomial numericBound bitBound := by
    dsimp only [body, tableTerm, widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationOffsetBody_code_length_le_fixed tokenTable width
      sourceStart targetStart bitBound htableSize hwidthSize hsourceStartSize
      htargetStartSize
  have hsyntax :
      explicitHybridUniversalSyntaxResource count body <=
        tokenSliceOffsetUniversalSyntaxFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      tokenSliceOffsetUniversalSyntaxFixedPolynomial
    exact Nat.add_le_add hcount hbody
  have hformula :
      explicitHybridUniversalFormulaEnvelope count body <=
        tokenSliceOffsetUniversalFormulaFixedPolynomial numericBound
          bitBound := by
    have hclosed :=
      boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
    unfold explicitHybridUniversalFormulaEnvelope
      tokenSliceOffsetUniversalFormulaFixedPolynomial
    exact Nat.add_le_add hclosed (Nat.mul_le_mul_left 2 hbody)
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma count body <=
        tokenSliceOffsetUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    unfold tokenSliceOffsetUniversalLocalPayloadFixedPolynomial
      contextualHybridUniversalLocalPayloadEnvelope
      contextualHybridUniversalFormulaEnvelope
    rw [hGamma]
    simp only [contextualHybridUniversalFormulaCodeSum, Finset.sum_empty,
      Nat.add_zero]
    exact smallContextAssemblyEnvelope_mono_local hformula
  have hfixed :
      contextualCore <=
        tokenSliceOffsetBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      tokenSliceOffsetBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
          tableTerm widthTerm sourceTerm targetTerm count = exactCore := by
    unfold tokenSliceAtValuationOffsetBranchesTransparentEnvelope
    simp only [termValue_shortBinaryNumeralTerm]
    rfl
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

theorem tokenSliceAtValuationOffsetContextualBranchesResource_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart count numericBound bitBound :
      Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let sourceTerm := shortBinaryNumeralTerm sourceStart
    let targetTerm := shortBinaryNumeralTerm targetStart
    let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceTerm
      targetTerm
    contextualBranchesUnderBoundPayloadEnvelope ∅ count
        (Rewriting.free body)
        (tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
          tableTerm widthTerm sourceTerm targetTerm count) <=
      tokenSliceOffsetContextualBranchesFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let body := tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceTerm
    targetTerm
  let targetFormula := Rewriting.free body
  let caseResource :=
    tokenSliceAtValuationOffsetBranchesTransparentEnvelope valuation
      tableTerm widthTerm sourceTerm targetTerm count
  let syntaxCode :=
    tokenSliceOffsetUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    tokenSliceOffsetUniversalFormulaFixedPolynomial numericBound bitBound
  let caseBound :=
    tokenSliceOffsetBranchesFullyFixedPayloadPolynomial numericBound bitBound
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceOffsetUniversalBodyCodePolynomial numericBound bitBound := by
    dsimp only [body, tableTerm, widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationOffsetBody_code_length_le_fixed tokenTable width
      sourceStart targetStart bitBound htableSize hwidthSize hsourceStartSize
      htargetStartSize
  have htarget :
      (binaryFormulaCode targetFormula).length <= formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula, formulaCode]
    unfold tokenSliceOffsetUniversalFormulaFixedPolynomial
    omega
  have hclosed :
      boundedUniversalClosedFormulaEnvelope syntaxCode <= formulaCode := by
    dsimp only [syntaxCode, formulaCode]
    unfold tokenSliceOffsetUniversalFormulaFixedPolynomial
    omega
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound, tableTerm, widthTerm, sourceTerm,
      targetTerm]
    exact tokenSliceAtValuationOffsetBranchesTransparentEnvelope_le_fullyFixed
      valuation tokenTable width sourceStart targetStart count numericBound
      bitBound hwidth hsourceStart htargetStart hcount htableSize hwidthSize
      hsourceStartSize htargetStartSize
  have hassembled :=
    contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly ∅ count
      syntaxCode formulaCode caseResource caseBound targetFormula
      (by
        dsimp only [syntaxCode]
        unfold tokenSliceOffsetUniversalSyntaxFixedPolynomial
        omega)
      hclosed htarget (by simp)
      (by
        intro formula hformula
        simp at hformula)
      hcase
  unfold tokenSliceOffsetContextualBranchesFullyFixedPayloadPolynomial
  simpa only [tableTerm, widthTerm, sourceTerm, targetTerm, body,
    targetFormula, caseResource, syntaxCode, formulaCode, caseBound] using
      hassembled

#print axioms
  tokenSliceAtValuationOffsetBranchesTransparentEnvelope_le_fullyFixed
#print axioms
  tokenSliceAtValuationOffsetContextualBranchesResource_le_fullyFixed

end FoundationCompactNumericListedDirectTokenSliceOffsetBranchesFullyFixedBounds
