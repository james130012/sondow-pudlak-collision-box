import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for a mapped source prefix

The two copied slices and the mapped head row retain every native arithmetic
term from the original fifteen-coordinate formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate

open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
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

def twoTerm : ValuationTerm := ‘2’

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

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  unfold termValue
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simp

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

@[simp] private theorem termValue_twoTerm (valuation : Nat -> Nat) :
    termValue valuation twoTerm = 2 := by
  simp [twoTerm, termValue_arithmeticTwo]

def compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactAdditiveNatListAppendMappedSourcePrefixDef.val) ⇜
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
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm mappedHead]

def compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat) : ValuationFormula :=
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
  “!!(‘1’ : ValuationTerm) ≤ !!prefixCountTerm” ⋏
    (“!!prefixCountTerm ≤ !!sourceCountTerm” ⋏
      (“!!(addTerm (successorTerm sourceStartTerm) prefixCountTerm) ≤
          !!sourceFinishTerm” ⋏
        (“!!targetFinishTerm =
            !!(addTerm (successorTerm targetStartTerm) targetCountTerm)” ⋏
          (“!!targetCountTerm = !!(addTerm leftCountTerm prefixCountTerm)” ⋏
            (compactFixedWidthTokenSlicesEqAtValuationFormula
                tokenTableTerm widthTerm tokenCountTerm
                (successorTerm leftStartTerm) leftFinishTerm
                (successorTerm targetStartTerm)
                (addTerm (successorTerm targetStartTerm) leftCountTerm) ⋏
              (compactAdditiveNatListAtRowsAtValuationIndexFormula
                  tokenTable width tokenCount targetBoundary targetCount
                  mappedHead leftCountTerm ⋏
                compactFixedWidthTokenSlicesEqAtValuationFormula
                  tokenTableTerm widthTerm tokenCountTerm
                  (addTerm sourceStartTerm twoTerm)
                  (addTerm (successorTerm sourceStartTerm) prefixCountTerm)
                  (addTerm (addTerm targetStartTerm twoTerm) leftCountTerm)
                  targetFinishTerm))))))

theorem compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_alignment
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat) :
    compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount targetStart
        targetFinish targetBoundary targetCount mappedHead =
      compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount targetStart
        targetFinish targetBoundary targetCount mappedHead := by
  unfold compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
  unfold compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula
  unfold compactAdditiveNatListAppendMappedSourcePrefixDef
  unfold compactFixedWidthTokenSlicesEqAtValuationFormula
  simp only [
    compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  unfold successorTerm addTerm twoTerm
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
    compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) :
    HybridCertificate
      (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount targetStart
        targetFinish targetBoundary targetCount mappedHead) := by
  rcases hgraph with
    ⟨hpositive, hprefix, hsourceWithin, htargetFinish, hcount,
      hleftSlice, hhead, htailSlice⟩
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
  let tailSliceCount := Classical.choose htailSlice
  have htailSpec :
      tailSliceCount ≤ tokenCount ∧
      sourceStart + 1 + prefixCount = sourceStart + 2 + tailSliceCount ∧
      targetFinish = targetStart + 2 + leftCount + tailSliceCount ∧
      sourceStart + 1 + prefixCount ≤ tokenCount ∧
      targetFinish ≤ tokenCount ∧
      ∀ offset < tailSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((sourceStart + 2 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 2 + leftCount + offset) * width + bitIndex) := by
    simpa [tailSliceCount, Nat.add_assoc] using
      Classical.choose_spec htailSlice
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
  let headCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetBoundary targetCount leftCount
      mappedHead (shortBinaryNumeralTerm leftCount)
      (by simp [termValue_shortBinaryNumeralTerm]) hhead
  let tailCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm
        (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      tailSliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using htailSpec.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using htailSpec.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using htailSpec.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using htailSpec.2.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using htailSpec.2.2.2.2.1)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          htailSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex')
  let positiveCertificate := valuationLeCertificate (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm prefixCount) (by
      simpa [termValue_arithmeticOne,
        termValue_shortBinaryNumeralTerm] using hpositive)
  let prefixCertificate := valuationLeCertificate
    (shortBinaryNumeralTerm prefixCount)
    (shortBinaryNumeralTerm sourceCount) (by
      simpa [termValue_shortBinaryNumeralTerm] using hprefix)
  let sourceWithinCertificate := valuationLeCertificate
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish) (by
      simpa [termValue_shortBinaryNumeralTerm] using hsourceWithin)
  let targetFinishCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount)) (by
        simpa [termValue_shortBinaryNumeralTerm] using htargetFinish)
  let countCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount)) (by
        simpa [termValue_shortBinaryNumeralTerm] using hcount)
  let headTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    headCertificate tailCertificate
  let leftTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate headTail
  let countTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate leftTail
  let targetTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    targetFinishCertificate countTail
  let sourceTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sourceWithinCertificate targetTail
  let prefixTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    prefixCertificate sourceTail
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    positiveCertificate prefixTail
  exact .cast
    (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_alignment
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish
      targetBoundary targetCount mappedHead).symm direct

noncomputable def
    compileCompactAdditiveNatListAppendMappedSourcePrefixExplicitHybridContext
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) :
    CertifiedPAContextProof
      (valuationContext
        (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
          tokenTable width tokenCount leftStart leftFinish leftCount
          sourceStart sourceFinish sourceCount prefixCount targetStart
          targetFinish targetBoundary targetCount mappedHead).freeVariables
            zeroValuation)
      (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount targetStart
        targetFinish targetBoundary targetCount mappedHead) :=
  (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
    tokenTable width tokenCount leftStart leftFinish leftCount
    sourceStart sourceFinish sourceCount prefixCount targetStart
    targetFinish targetBoundary targetCount mappedHead hgraph).compile

noncomputable def
    compactAdditiveNatListAppendMappedSourcePrefixExplicitStructuralResource
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead hgraph)

theorem
    compileCompactAdditiveNatListAppendMappedSourcePrefixExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) :
    (compileCompactAdditiveNatListAppendMappedSourcePrefixExplicitHybridContext
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead hgraph).payloadLength ≤
      compactAdditiveNatListAppendMappedSourcePrefixExplicitStructuralResource
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount targetStart
        targetFinish targetBoundary targetCount mappedHead hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead hgraph)

#print axioms
  compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_alignment
#print axioms
  compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
#print axioms
  compileCompactAdditiveNatListAppendMappedSourcePrefixExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
