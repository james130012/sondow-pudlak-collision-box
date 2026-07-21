import integration.FoundationCompactNumericListedDirectNatListAppendTwoValues
import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for appending two values

The certificate retains the native `sourceCount + 1` lookup and the native
arithmetic numeral `2` from the original twelve-coordinate formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate

open FoundationCompactNumericListedDirectNatListAppendTwoValues
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

abbrev zeroValuation : Nat -> Nat := fun _ => 0

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

theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  unfold termValue
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simp

@[simp] theorem termValue_successorTerm
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    termValue valuation (successorTerm term) =
      termValue valuation term + 1 := by
  simp [successorTerm, termValue_arithmeticAdd, termValue_arithmeticOne]

@[simp] theorem termValue_addTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (addTerm left right) =
      termValue valuation left + termValue valuation right := by
  simp [addTerm, termValue_arithmeticAdd]

def compactAdditiveNatListAppendTwoValuesClosedFormula
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendTwoValuesDef.val) ⇜
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
      shortBinaryNumeralTerm first,
      shortBinaryNumeralTerm second]

private def compactAdditiveNatListAppendTwoValuesExplicitFormula
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat) : ValuationFormula :=
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
      !!(addTerm (successorTerm targetStartTerm) targetCountTerm)” ⋏
    (“!!targetCountTerm = !!(addTerm sourceCountTerm (‘2’ : ValuationTerm))” ⋏
      (compactFixedWidthTokenSlicesEqAtValuationFormula
          tokenTableTerm widthTerm tokenCountTerm
          (successorTerm sourceStartTerm) sourceFinishTerm
          (successorTerm targetStartTerm)
          (addTerm (successorTerm targetStartTerm) sourceCountTerm) ⋏
        (compactAdditiveNatListAtRowsAtValuationIndexFormula
            tokenTable width tokenCount targetBoundary targetCount first
            sourceCountTerm ⋏
          compactAdditiveNatListAtRowsAtValuationIndexFormula
            tokenTable width tokenCount targetBoundary targetCount second
            (successorTerm sourceCountTerm))))

theorem compactAdditiveNatListAppendTwoValuesClosedFormula_alignment
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat) :
    compactAdditiveNatListAppendTwoValuesClosedFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount first second =
      compactAdditiveNatListAppendTwoValuesExplicitFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount first second := by
  unfold compactAdditiveNatListAppendTwoValuesClosedFormula
  unfold compactAdditiveNatListAppendTwoValuesExplicitFormula
  unfold compactAdditiveNatListAppendTwoValuesDef
  unfold compactFixedWidthTokenSlicesEqAtValuationFormula
  simp only [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
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

noncomputable def valuationEqCertificate
    (left right : ValuationTerm)
    (heq : termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate “!!left = !!right” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![left, right] heq
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

noncomputable def
    compactAdditiveNatListAppendTwoValuesExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) :
    HybridCertificate
      (compactAdditiveNatListAppendTwoValuesClosedFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount first second) := by
  rcases hgraph with ⟨hfinish, hcount, hslice, hfirst, hsecond⟩
  let sliceCount := Classical.choose hslice
  have hsliceSpec :
      sliceCount ≤ tokenCount ∧
      sourceFinish = sourceStart + 1 + sliceCount ∧
      targetStart + 1 + sourceCount = targetStart + 1 + sliceCount ∧
      sourceFinish ≤ tokenCount ∧
      targetStart + 1 + sourceCount ≤ tokenCount ∧
      ∀ offset < sliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [sliceCount, Nat.add_assoc] using Classical.choose_spec hslice
  rw [compactAdditiveNatListAppendTwoValuesClosedFormula_alignment]
  unfold compactAdditiveNatListAppendTwoValuesExplicitFormula
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount))
      sliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.2.1)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hsliceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex')
  let firstCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetBoundary targetCount sourceCount first
      (shortBinaryNumeralTerm sourceCount)
      (by simp [termValue_shortBinaryNumeralTerm]) hfirst
  let secondCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetBoundary targetCount
      (sourceCount + 1) second
      (successorTerm (shortBinaryNumeralTerm sourceCount))
      (by simp [termValue_shortBinaryNumeralTerm]) hsecond
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (valuationEqCertificate
      (shortBinaryNumeralTerm targetFinish)
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using hfinish))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (valuationEqCertificate
        (shortBinaryNumeralTerm targetCount)
        (addTerm (shortBinaryNumeralTerm sourceCount)
          (‘2’ : ValuationTerm)) (by
            simpa [termValue_shortBinaryNumeralTerm,
              termValue_arithmeticTwo] using hcount))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        sliceCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          firstCertificate secondCertificate)))

/-! ## Exact value-term endpoint

Formula-transform branches append arithmetic expressions, not only closed
binary numerals.  This endpoint preserves the caller's two value terms while
linking them to the same semantic append graph through their evaluated values.
-/

def compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount : Nat)
    (firstTerm secondTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendTwoValuesDef.val) ⇜
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
      firstTerm,
      secondTerm]

def
    compactAdditiveNatListAppendTwoValuesExplicitFormulaAtValuationValues
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount : Nat)
    (firstTerm secondTerm : ValuationTerm) : ValuationFormula :=
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
      !!(addTerm (successorTerm targetStartTerm) targetCountTerm)” ⋏
    (“!!targetCountTerm = !!(addTerm sourceCountTerm (‘2’ : ValuationTerm))” ⋏
      (compactFixedWidthTokenSlicesEqAtValuationFormula
          tokenTableTerm widthTerm tokenCountTerm
          (successorTerm sourceStartTerm) sourceFinishTerm
          (successorTerm targetStartTerm)
          (addTerm (successorTerm targetStartTerm) sourceCountTerm) ⋏
        (compactAdditiveNatListAtRowsAtValuationIndexValueFormula
            tokenTable width tokenCount targetBoundary targetCount
            sourceCountTerm firstTerm ⋏
          compactAdditiveNatListAtRowsAtValuationIndexValueFormula
            tokenTable width tokenCount targetBoundary targetCount
            (successorTerm sourceCountTerm) secondTerm)))

theorem
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_alignment
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount : Nat)
    (firstTerm secondTerm : ValuationTerm) :
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount firstTerm
          secondTerm =
      compactAdditiveNatListAppendTwoValuesExplicitFormulaAtValuationValues
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount firstTerm
          secondTerm := by
  unfold compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
  unfold compactAdditiveNatListAppendTwoValuesExplicitFormulaAtValuationValues
  unfold compactAdditiveNatListAppendTwoValuesDef
  unfold compactFixedWidthTokenSlicesEqAtValuationFormula
  simp only [
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_eq_explicitSubstitution]
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

noncomputable def
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (hfirstValue : termValue zeroValuation firstTerm = first)
    (hsecondValue : termValue zeroValuation secondTerm = second)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) :
    HybridCertificate
      (compactAdditiveNatListAppendTwoValuesExplicitFormulaAtValuationValues
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount firstTerm
          secondTerm) := by
  rcases hgraph with ⟨hfinish, hcount, hslice, hfirst, hsecond⟩
  let sliceCount := Classical.choose hslice
  have hsliceSpec :
      sliceCount ≤ tokenCount ∧
      sourceFinish = sourceStart + 1 + sliceCount ∧
      targetStart + 1 + sourceCount = targetStart + 1 + sliceCount ∧
      sourceFinish ≤ tokenCount ∧
      targetStart + 1 + sourceCount ≤ tokenCount ∧
      ∀ offset < sliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [sliceCount, Nat.add_assoc] using Classical.choose_spec hslice
  unfold compactAdditiveNatListAppendTwoValuesExplicitFormulaAtValuationValues
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount))
      sliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.2.1)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hsliceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex')
  let firstCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      tokenTable width tokenCount targetBoundary targetCount
      sourceCount first (shortBinaryNumeralTerm sourceCount) firstTerm
      (by simp [termValue_shortBinaryNumeralTerm]) (by
        change termValue (fun _ => 0) firstTerm = first
        change termValue (fun _ => 0) firstTerm = first at hfirstValue
        exact hfirstValue) hfirst
  let secondCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      tokenTable width tokenCount targetBoundary targetCount
      (sourceCount + 1) second
      (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
      (by simp [termValue_shortBinaryNumeralTerm]) (by
        change termValue (fun _ => 0) secondTerm = second
        change termValue (fun _ => 0) secondTerm = second at hsecondValue
        exact hsecondValue) hsecond
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (valuationEqCertificate
      (shortBinaryNumeralTerm targetFinish)
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using hfinish))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (valuationEqCertificate
        (shortBinaryNumeralTerm targetCount)
        (addTerm (shortBinaryNumeralTerm sourceCount)
          (‘2’ : ValuationTerm)) (by
            simpa [termValue_shortBinaryNumeralTerm,
              termValue_arithmeticTwo] using hcount))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        sliceCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          firstCertificate secondCertificate)))

/-- Formula-level transport of the transparent two-value certificate. -/
noncomputable def
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (hfirstValue : termValue zeroValuation firstTerm = first)
    (hsecondValue : termValue zeroValuation secondTerm = second)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) :
    HybridCertificate
      (compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount firstTerm
          secondTerm) :=
  .cast
    (compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_alignment
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount firstTerm
      secondTerm).symm
    (compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount first second firstTerm
      secondTerm hfirstValue hsecondValue hgraph)

noncomputable def
    compileCompactAdditiveNatListAppendTwoValuesExplicitHybridContext
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) :
    CertifiedPAContextProof
      (valuationContext
        (compactAdditiveNatListAppendTwoValuesClosedFormula
          tokenTable width tokenCount sourceStart sourceFinish sourceCount
          targetStart targetFinish targetBoundary targetCount first second).freeVariables
            zeroValuation)
      (compactAdditiveNatListAppendTwoValuesClosedFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount first second) :=
  (compactAdditiveNatListAppendTwoValuesExplicitHybridCertificateOfGraph
    tokenTable width tokenCount sourceStart sourceFinish sourceCount
    targetStart targetFinish targetBoundary targetCount first second hgraph).compile

noncomputable def compactAdditiveNatListAppendTwoValuesExplicitStructuralResource
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendTwoValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount first second hgraph)

theorem
    compileCompactAdditiveNatListAppendTwoValuesExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second) :
    (compileCompactAdditiveNatListAppendTwoValuesExplicitHybridContext
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount first second
      hgraph).payloadLength ≤
      compactAdditiveNatListAppendTwoValuesExplicitStructuralResource
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount first second hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendTwoValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount first second hgraph)

#print axioms compactAdditiveNatListAppendTwoValuesClosedFormula_alignment
#print axioms compactAdditiveNatListAppendTwoValuesExplicitHybridCertificateOfGraph
#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_alignment
#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph
#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
#print axioms
  compileCompactAdditiveNatListAppendTwoValuesExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
