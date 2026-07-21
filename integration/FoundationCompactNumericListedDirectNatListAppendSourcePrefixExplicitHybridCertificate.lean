import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefix
import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for appending a source prefix

Both copied regions retain the arithmetic starts from the original
thirteen-coordinate formula.  Their bitwise slice witnesses are passed to
the valuation-term token-slice certificate without numeral normalization.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate

open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
  cases h
  rfl

def successorTerm (term : ValuationTerm) : ValuationTerm :=
  ‘!!term + 1’

def addTerm (left right : ValuationTerm) : ValuationTerm :=
  ‘!!left + !!right’

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

@[simp] private theorem termValue_successorTerm
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    termValue valuation (successorTerm term) =
      termValue valuation term + 1 := by
  simp [successorTerm, termValue_arithmeticAdd, termValue_arithmeticOne]

@[simp] private theorem termValue_addTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (addTerm left right) =
      termValue valuation left + termValue valuation right := by
  simp [addTerm, termValue_arithmeticAdd]

def compactAdditiveNatListAppendSourcePrefixClosedFormula
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendSourcePrefixDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm leftStart,
      shortBinaryNumeralTerm leftFinish,
      shortBinaryNumeralTerm leftCount,
      shortBinaryNumeralTerm sourceStart,
      shortBinaryNumeralTerm sourceFinish,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm prefixCount,
      shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm targetFinish,
      shortBinaryNumeralTerm targetCount]

def compactAdditiveNatListAppendSourcePrefixExplicitFormula
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) : ValuationFormula :=
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let leftStartTerm := shortBinaryNumeralTerm leftStart
  let leftFinishTerm := shortBinaryNumeralTerm leftFinish
  let leftCountTerm := shortBinaryNumeralTerm leftCount
  let sourceStartTerm := shortBinaryNumeralTerm sourceStart
  let sourceFinishTerm := shortBinaryNumeralTerm sourceFinish
  let sourceCountTerm := shortBinaryNumeralTerm sourceCount
  let prefixCountTerm := shortBinaryNumeralTerm prefixCount
  let targetStartTerm := shortBinaryNumeralTerm targetStart
  let targetFinishTerm := shortBinaryNumeralTerm targetFinish
  let targetCountTerm := shortBinaryNumeralTerm targetCount
  “!!prefixCountTerm ≤ !!sourceCountTerm” ⋏
    (“!!(addTerm (successorTerm sourceStartTerm) prefixCountTerm) ≤
        !!sourceFinishTerm” ⋏
      (“!!targetCountTerm = !!(addTerm leftCountTerm prefixCountTerm)” ⋏
        (compactFixedWidthTokenSlicesEqAtValuationFormula
            tokenTableTerm widthTerm tokenCountTerm
            (successorTerm leftStartTerm) leftFinishTerm
            (successorTerm targetStartTerm)
            (addTerm (successorTerm targetStartTerm) leftCountTerm) ⋏
          compactFixedWidthTokenSlicesEqAtValuationFormula
            tokenTableTerm widthTerm tokenCountTerm
            (successorTerm sourceStartTerm)
            (addTerm (successorTerm sourceStartTerm) prefixCountTerm)
            (addTerm (successorTerm targetStartTerm) leftCountTerm)
            targetFinishTerm)))

theorem compactAdditiveNatListAppendSourcePrefixClosedFormula_alignment
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) :
    compactAdditiveNatListAppendSourcePrefixClosedFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount
        targetStart targetFinish targetCount =
      compactAdditiveNatListAppendSourcePrefixExplicitFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount
        targetStart targetFinish targetCount := by
  unfold compactAdditiveNatListAppendSourcePrefixClosedFormula
  unfold compactAdditiveNatListAppendSourcePrefixExplicitFormula
  unfold compactAdditiveNatListAppendSourcePrefixDef
  unfold compactFixedWidthTokenSlicesEqAtValuationFormula
  unfold successorTerm addTerm
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def valuationLeCertificate
    (left right : ValuationTerm)
    (hle : termValue zeroValuation left ≤ termValue zeroValuation right) :
    HybridCertificate “!!left ≤ !!right” := by
  if heq : termValue zeroValuation left = termValue zeroValuation right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![left, right] heq
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![left, right]) equality
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      direct
  else
    have hlt : termValue zeroValuation left < termValue zeroValuation right :=
      Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![left, right] hlt
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![left, right]) strict
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      direct

noncomputable def valuationEqCertificate
    (left right : ValuationTerm)
    (heq : termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate “!!left = !!right” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![left, right] heq
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

noncomputable def
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) :
    HybridCertificate
      (compactAdditiveNatListAppendSourcePrefixClosedFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount
        targetStart targetFinish targetCount) := by
  rcases hgraph with
    ⟨hprefix, hsourceWithin, hcount, hleftSlice, hsourceSlice⟩
  let leftSliceCount := Classical.choose hleftSlice
  have hleftSpec :
      leftSliceCount ≤ tokenCount ∧
      leftFinish = leftStart + 1 + leftSliceCount ∧
      targetStart + 1 + leftCount = targetStart + 1 + leftSliceCount ∧
      leftFinish ≤ tokenCount ∧
      targetStart + 1 + leftCount ≤ tokenCount ∧
      ∀ offset < leftSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((leftStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [leftSliceCount, Nat.add_assoc] using
      Classical.choose_spec hleftSlice
  let sourceSliceCount := Classical.choose hsourceSlice
  have hsourceSpec :
      sourceSliceCount ≤ tokenCount ∧
      sourceStart + 1 + prefixCount =
        sourceStart + 1 + sourceSliceCount ∧
      targetFinish = targetStart + 1 + leftCount + sourceSliceCount ∧
      sourceStart + 1 + prefixCount ≤ tokenCount ∧
      targetFinish ≤ tokenCount ∧
      ∀ offset < sourceSliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + leftCount + offset) * width + bitIndex) := by
    simpa [sourceSliceCount, Nat.add_assoc] using
      Classical.choose_spec hsourceSlice
  let leftCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      leftSliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.2.1)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hleftSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex')
  let sourceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      sourceSliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.2.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.2.2.2.2.1)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hsourceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex')
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (valuationLeCertificate
      (shortBinaryNumeralTerm prefixCount)
      (shortBinaryNumeralTerm sourceCount) (by
        simpa [termValue_shortBinaryNumeralTerm] using hprefix))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (valuationLeCertificate
        (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
          (shortBinaryNumeralTerm prefixCount))
        (shortBinaryNumeralTerm sourceFinish) (by
          simpa [termValue_shortBinaryNumeralTerm] using hsourceWithin))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (valuationEqCertificate
          (shortBinaryNumeralTerm targetCount)
          (addTerm (shortBinaryNumeralTerm leftCount)
            (shortBinaryNumeralTerm prefixCount)) (by
              simpa [termValue_shortBinaryNumeralTerm] using hcount))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate sourceCertificate)))
  exact .cast
    (compactAdditiveNatListAppendSourcePrefixClosedFormula_alignment tokenTable
      width tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
      sourceCount prefixCount targetStart targetFinish targetCount).symm direct

noncomputable def
    compileCompactAdditiveNatListAppendSourcePrefixExplicitHybridContext
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactAdditiveNatListAppendSourcePrefixClosedFormula
          tokenTable width tokenCount leftStart leftFinish leftCount
          sourceStart sourceFinish sourceCount prefixCount
          targetStart targetFinish targetCount).freeVariables zeroValuation)
      (compactAdditiveNatListAppendSourcePrefixClosedFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount
        targetStart targetFinish targetCount) :=
  (compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
    tokenTable width tokenCount leftStart leftFinish leftCount
    sourceStart sourceFinish sourceCount prefixCount
    targetStart targetFinish targetCount hgraph).compile

noncomputable def
    compactAdditiveNatListAppendSourcePrefixExplicitStructuralResource
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount hgraph)

theorem
    compileCompactAdditiveNatListAppendSourcePrefixExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) :
    (compileCompactAdditiveNatListAppendSourcePrefixExplicitHybridContext
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount hgraph).payloadLength ≤
      compactAdditiveNatListAppendSourcePrefixExplicitStructuralResource
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount
        targetStart targetFinish targetCount hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount hgraph)

#print axioms compactAdditiveNatListAppendSourcePrefixClosedFormula_alignment
#print axioms
  compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
#print axioms
  compileCompactAdditiveNatListAppendSourcePrefixExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
