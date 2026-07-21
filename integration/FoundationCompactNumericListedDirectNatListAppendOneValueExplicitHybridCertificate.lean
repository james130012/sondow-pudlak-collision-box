import integration.FoundationCompactNumericListedDirectNatListAppendOneValue
import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for appending one natural-list value

The native source-count and target arithmetic terms are retained in the
certificate syntax.  The slice and final-row components use their valuation
term endpoints rather than evaluated replacement numerals.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate

open FoundationCompactNumericListedDirectNatListAppendOneValue
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_emptyFormulaSubstitution
    {targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm Empty sourceArity) :
    rewriting ▹ (formula ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      rewriting.comp (Rew.subst terms) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ (formula ⇜ terms) =
        (rewriting.comp (Rew.subst terms)) ▹ formula := by
      rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

def successorTerm (term : ValuationTerm) : ValuationTerm :=
  ‘!!term + 1’

def appendOneTargetFinishTerm
    (targetStartTerm targetCountTerm : ValuationTerm) : ValuationTerm :=
  ‘!!targetStartTerm + 1 + !!targetCountTerm’

/-- The original eleven-coordinate append-one predicate closed by numerals. -/
def compactAdditiveNatListAppendOneValueClosedFormula
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendOneValueDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceStart,
      shortBinaryNumeralTerm sourceFinish,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm targetFinish,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm value]

def compactAdditiveNatListAppendOneValueExplicitFormula
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat) :
    ValuationFormula :=
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let sourceStartTerm := shortBinaryNumeralTerm sourceStart
  let sourceFinishTerm := shortBinaryNumeralTerm sourceFinish
  let sourceCountTerm := shortBinaryNumeralTerm sourceCount
  let targetStartTerm := shortBinaryNumeralTerm targetStart
  let targetFinishTerm := shortBinaryNumeralTerm targetFinish
  let targetCountTerm := shortBinaryNumeralTerm targetCount
  “!!targetFinishTerm =
      !!(appendOneTargetFinishTerm targetStartTerm targetCountTerm)” ⋏
    (“!!targetCountTerm = !!(successorTerm sourceCountTerm)” ⋏
      (compactFixedWidthTokenSlicesEqAtValuationFormula
          tokenTableTerm widthTerm tokenCountTerm
          (successorTerm sourceStartTerm) sourceFinishTerm
          (successorTerm targetStartTerm)
          (appendOneTargetFinishTerm targetStartTerm sourceCountTerm) ⋏
        compactAdditiveNatListAtRowsAtValuationIndexFormula
          tokenTable width tokenCount targetBoundary targetCount value
          sourceCountTerm))

/-- Exact syntax alignment with the original quoted append-one predicate. -/
theorem compactAdditiveNatListAppendOneValueClosedFormula_alignment
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat) :
    compactAdditiveNatListAppendOneValueClosedFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value =
      compactAdditiveNatListAppendOneValueExplicitFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value := by
  unfold compactAdditiveNatListAppendOneValueClosedFormula
    compactAdditiveNatListAppendOneValueExplicitFormula
    compactAdditiveNatListAppendOneValueDef
    compactFixedWidthTokenSlicesEqAtValuationFormula
    successorTerm appendOneTargetFinishTerm
  simp only [
    compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution, Rew.subst_bvar]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Rew.subst_bvar]
  · congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Rew.subst_bvar]

theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

@[simp] theorem termValue_successorTerm
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    termValue valuation (successorTerm term) = termValue valuation term + 1 := by
  simp [successorTerm, termValue_arithmeticAdd, termValue_arithmeticOne]

@[simp] theorem termValue_appendOneTargetFinishTerm
    (valuation : Nat -> Nat) (targetStartTerm targetCountTerm : ValuationTerm) :
    termValue valuation
        (appendOneTargetFinishTerm targetStartTerm targetCountTerm) =
      termValue valuation targetStartTerm + 1 +
        termValue valuation targetCountTerm := by
  simp [appendOneTargetFinishTerm, termValue_arithmeticAdd,
    termValue_arithmeticOne]

noncomputable def equalityCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hequality : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm = !!rightTerm” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![leftTerm, rightTerm] hequality
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

/-- Fully explicit checked certificate constructed from the public append-one
graph.  No split graph assumptions or semantic truth selector are exposed. -/
noncomputable def
    compactAdditiveNatListAppendOneValueExplicitHybridCertificateDirectOfGraph
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value) :
    HybridCertificate
      (compactAdditiveNatListAppendOneValueExplicitFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value) := by
  have htargetFinish := hgraph.1
  have htargetCount := hgraph.2.1
  have hslices := hgraph.2.2.1
  have hrows := hgraph.2.2.2
  let sliceCount := Classical.choose hslices
  have hsliceSpec :
      sliceCount ≤ tokenCount ∧
      sourceFinish = sourceStart + 1 + sliceCount ∧
      targetStart + 1 + sourceCount = targetStart + 1 + sliceCount ∧
      sourceFinish ≤ tokenCount ∧
      targetStart + 1 + sourceCount ≤ tokenCount ∧
      ∀ offset < sliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [sliceCount, Nat.add_assoc] using Classical.choose_spec hslices
  have hsliceCountBound := hsliceSpec.1
  have hsourceEndpoint := hsliceSpec.2.1
  have htargetEndpoint := hsliceSpec.2.2.1
  have hsourceFinishBound := hsliceSpec.2.2.2.1
  have htargetFinishBound := hsliceSpec.2.2.2.2.1
  have hbits := hsliceSpec.2.2.2.2.2
  unfold compactAdditiveNatListAppendOneValueExplicitFormula
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm sourceCount))
      sliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceCountBound)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceEndpoint)
      (by simpa [termValue_shortBinaryNumeralTerm] using htargetEndpoint)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceFinishBound)
      (by simpa [termValue_shortBinaryNumeralTerm] using htargetFinishBound)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hbits offset hoffset bitIndex hbitIndex')
  let rowCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetBoundary targetCount sourceCount value
      (shortBinaryNumeralTerm sourceCount)
      (by simp [termValue_shortBinaryNumeralTerm]) hrows
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (equalityCertificate (shortBinaryNumeralTerm targetFinish)
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm targetCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using htargetFinish))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (equalityCertificate (shortBinaryNumeralTerm targetCount)
        (successorTerm (shortBinaryNumeralTerm sourceCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using htargetCount))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        sliceCertificate rowCertificate))

/-- The closed-form certificate is an explicit transport of the transparent
certificate above.  Keeping this transport visible makes structural-resource
audits reduce through the `.cast` constructor. -/
noncomputable def
    compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value) :
    HybridCertificate
      (compactAdditiveNatListAppendOneValueClosedFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value) :=
  .cast
    (compactAdditiveNatListAppendOneValueClosedFormula_alignment
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value).symm
    (compactAdditiveNatListAppendOneValueExplicitHybridCertificateDirectOfGraph
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value hgraph)

noncomputable def
    compileCompactAdditiveNatListAppendOneValueExplicitHybridContext
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value) :
    CertifiedPAContextProof
      (valuationContext
        (compactAdditiveNatListAppendOneValueClosedFormula
          tokenTable width tokenCount sourceStart sourceFinish sourceCount
          targetStart targetFinish targetBoundary targetCount value).freeVariables
        zeroValuation)
      (compactAdditiveNatListAppendOneValueClosedFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value) :=
  (compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
    tokenTable width tokenCount sourceStart sourceFinish sourceCount
    targetStart targetFinish targetBoundary targetCount value hgraph).compile

noncomputable def
    compactAdditiveNatListAppendOneValueExplicitStructuralResource
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value hgraph)

theorem
    compileCompactAdditiveNatListAppendOneValueExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value) :
    (compileCompactAdditiveNatListAppendOneValueExplicitHybridContext
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value hgraph).payloadLength ≤
      compactAdditiveNatListAppendOneValueExplicitStructuralResource
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value hgraph)

#print axioms compactAdditiveNatListAppendOneValueClosedFormula_alignment
#print axioms
  compactAdditiveNatListAppendOneValueExplicitHybridCertificateDirectOfGraph
#print axioms compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
#print axioms
  compileCompactAdditiveNatListAppendOneValueExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
