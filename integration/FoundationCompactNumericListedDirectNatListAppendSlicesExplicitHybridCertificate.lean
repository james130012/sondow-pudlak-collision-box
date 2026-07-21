import integration.FoundationCompactNumericListedDirectNatListAppendSlices
import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate

/-!
# Explicit hybrid certificate for natural-list append slices

The two source bodies are certified by the valuation-term token-slice
constructor.  This retains the original arithmetic starts, including the
shared target midpoint, instead of replacing them by evaluated numerals.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate

open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

def zeroValuation : Nat -> Nat := fun _ => 0

abbrev AppendSlicesHybridCertificate
    (formula : ValuationFormula) :=
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

def appendMidpointTerm
    (targetStartTerm leftCountTerm : ValuationTerm) : ValuationTerm :=
  ‘!!(successorTerm targetStartTerm) + !!leftCountTerm’

/-- The original twelve-coordinate append predicate closed by numerals. -/
def compactAdditiveNatListAppendSlicesClosedFormula
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendSlicesDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm leftStart,
      shortBinaryNumeralTerm leftFinish,
      shortBinaryNumeralTerm leftCount,
      shortBinaryNumeralTerm rightStart,
      shortBinaryNumeralTerm rightFinish,
      shortBinaryNumeralTerm rightCount,
      shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm targetFinish,
      shortBinaryNumeralTerm targetCount]

def compactAdditiveNatListAppendSlicesExplicitFormula
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) : ValuationFormula :=
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let leftStartTerm := shortBinaryNumeralTerm leftStart
  let leftFinishTerm := shortBinaryNumeralTerm leftFinish
  let leftCountTerm := shortBinaryNumeralTerm leftCount
  let rightStartTerm := shortBinaryNumeralTerm rightStart
  let rightFinishTerm := shortBinaryNumeralTerm rightFinish
  let rightCountTerm := shortBinaryNumeralTerm rightCount
  let targetStartTerm := shortBinaryNumeralTerm targetStart
  let targetFinishTerm := shortBinaryNumeralTerm targetFinish
  let targetCountTerm := shortBinaryNumeralTerm targetCount
  “!!targetCountTerm = !!leftCountTerm + !!rightCountTerm” ⋏
    (compactFixedWidthTokenSlicesEqAtValuationFormula tokenTableTerm widthTerm
        tokenCountTerm (successorTerm leftStartTerm) leftFinishTerm
        (successorTerm targetStartTerm)
        (appendMidpointTerm targetStartTerm leftCountTerm) ⋏
      compactFixedWidthTokenSlicesEqAtValuationFormula tokenTableTerm widthTerm
        tokenCountTerm (successorTerm rightStartTerm) rightFinishTerm
        (appendMidpointTerm targetStartTerm leftCountTerm) targetFinishTerm)

/-- Exact syntax alignment with the original quoted append predicate. -/
theorem compactAdditiveNatListAppendSlicesClosedFormula_alignment
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    compactAdditiveNatListAppendSlicesClosedFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        rightStart rightFinish rightCount targetStart targetFinish targetCount =
      compactAdditiveNatListAppendSlicesExplicitFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        rightStart rightFinish rightCount targetStart targetFinish
        targetCount := by
  unfold compactAdditiveNatListAppendSlicesClosedFormula
    compactAdditiveNatListAppendSlicesExplicitFormula
    compactAdditiveNatListAppendSlicesDef
    compactFixedWidthTokenSlicesEqAtValuationFormula
    successorTerm appendMidpointTerm
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution, Rew.subst_bvar]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [successorTerm, Rew.subst_bvar]
  · congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [successorTerm, Rew.subst_bvar]

private theorem arithmeticAddTerm_eq_func
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

@[simp] theorem termValue_appendMidpointTerm
    (valuation : Nat -> Nat) (targetStartTerm leftCountTerm : ValuationTerm) :
    termValue valuation
        (appendMidpointTerm targetStartTerm leftCountTerm) =
      termValue valuation targetStartTerm + 1 +
        termValue valuation leftCountTerm := by
  simp [appendMidpointTerm, termValue_arithmeticAdd]

noncomputable def appendCountCertificate
    (leftCount rightCount targetCount : Nat)
    (hcount : targetCount = leftCount + rightCount) :
    AppendSlicesHybridCertificate
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm leftCount) +
          !!(shortBinaryNumeralTerm rightCount)” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm leftCount) +
      !!(shortBinaryNumeralTerm rightCount)’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm targetCount, rightTerm] (by
        change termValue zeroValuation (shortBinaryNumeralTerm targetCount) =
          termValue zeroValuation rightTerm
        simpa [rightTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd] using hcount)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

/-- Fully explicit checked certificate constructed from the concrete append
graph.  Both bounded token-slice witnesses are consumed field by field. -/
noncomputable def
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateDirectOfGraph
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    AppendSlicesHybridCertificate
      (compactAdditiveNatListAppendSlicesExplicitFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount) := by
  have hcount := hgraph.1
  have hleft := hgraph.2.1
  have hright := hgraph.2.2
  let leftSliceCount := Classical.choose hleft
  have hleftSpec :
      leftSliceCount ≤ tokenCount ∧
      leftFinish = leftStart + 1 + leftSliceCount ∧
      targetStart + 1 + leftCount = targetStart + 1 + leftSliceCount ∧
      leftFinish ≤ tokenCount ∧
      targetStart + 1 + leftCount ≤ tokenCount ∧
      ∀ offset < leftSliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((leftStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [leftSliceCount, Nat.add_assoc] using Classical.choose_spec hleft
  have hleftCountBound := hleftSpec.1
  have hleftSourceEndpoint := hleftSpec.2.1
  have hleftTargetEndpoint := hleftSpec.2.2.1
  have hleftSourceFinishBound := hleftSpec.2.2.2.1
  have hleftTargetFinishBound := hleftSpec.2.2.2.2.1
  have hleftBits := hleftSpec.2.2.2.2.2
  let rightSliceCount := Classical.choose hright
  have hrightSpec :
      rightSliceCount ≤ tokenCount ∧
      rightFinish = rightStart + 1 + rightSliceCount ∧
      targetFinish = targetStart + 1 + leftCount + rightSliceCount ∧
      rightFinish ≤ tokenCount ∧
      targetFinish ≤ tokenCount ∧
      ∀ offset < rightSliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((rightStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + leftCount + offset) * width + bitIndex) := by
    simpa [rightSliceCount, Nat.add_assoc] using Classical.choose_spec hright
  have hrightCountBound := hrightSpec.1
  have hrightSourceEndpoint := hrightSpec.2.1
  have hrightTargetEndpoint := hrightSpec.2.2.1
  have hrightSourceFinishBound := hrightSpec.2.2.2.1
  have hrightTargetFinishBound := hrightSpec.2.2.2.2.1
  have hrightBits := hrightSpec.2.2.2.2.2
  unfold compactAdditiveNatListAppendSlicesExplicitFormula
  let leftCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))
      leftSliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hleftCountBound)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hleftSourceEndpoint)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hleftTargetEndpoint)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hleftSourceFinishBound)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hleftTargetFinishBound)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hleftBits offset hoffset bitIndex hbitIndex')
  let rightCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm rightStart))
      (shortBinaryNumeralTerm rightFinish)
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      rightSliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hrightCountBound)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hrightSourceEndpoint)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hrightTargetEndpoint)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hrightSourceFinishBound)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hrightTargetFinishBound)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hrightBits offset hoffset bitIndex hbitIndex')
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (appendCountCertificate leftCount rightCount targetCount hcount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightCertificate)

/-- Closed-form transport of the transparent append-slices certificate. -/
noncomputable def
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    AppendSlicesHybridCertificate
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount) :=
  .cast
    (compactAdditiveNatListAppendSlicesClosedFormula_alignment tokenTable width
      tokenCount leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount).symm
    (compactAdditiveNatListAppendSlicesExplicitHybridCertificateDirectOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount hgraph)

#print axioms compactAdditiveNatListAppendSlicesClosedFormula_alignment
#print axioms
  compactAdditiveNatListAppendSlicesExplicitHybridCertificateDirectOfGraph
#print axioms compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
