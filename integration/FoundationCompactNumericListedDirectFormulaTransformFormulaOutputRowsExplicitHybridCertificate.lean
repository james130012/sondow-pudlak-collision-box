import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for formula-transform formula output rows

The closed formula retains the original twenty-nine-coordinate substitution.
The explicit formula keeps its native arithmetic leaves and right-associated
output-mode branches while delegating each row-table graph to its endpoint.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactParserDirectTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
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
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

def nativeAddTerm (left right : ValuationTerm) : ValuationTerm :=
  ‘!!left + !!right’

def nativeEqFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left = !!right”

def nativeNeFormula
    (left right : ValuationTerm) : ValuationFormula :=
  ∼(nativeEqFormula left right)

def nativeLeFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left ≤ !!right”

def rawModeFormula (modeTerm : ValuationTerm) : ValuationFormula :=
  nativeEqFormula modeTerm (‘0’ : ValuationTerm) ⋎
    (nativeEqFormula modeTerm (‘1’ : ValuationTerm) ⋎
      (nativeEqFormula modeTerm (‘2’ : ValuationTerm) ⋎
        nativeEqFormula modeTerm (‘5’ : ValuationTerm)))

def otherModeWithTailFormula
    (modeTerm : ValuationTerm) (tail : ValuationFormula) : ValuationFormula :=
  nativeNeFormula modeTerm (‘0’ : ValuationTerm) ⋏
    (nativeNeFormula modeTerm (‘1’ : ValuationTerm) ⋏
      (nativeNeFormula modeTerm (‘2’ : ValuationTerm) ⋏
        (nativeNeFormula modeTerm (‘4’ : ValuationTerm) ⋏
          (nativeNeFormula modeTerm (‘5’ : ValuationTerm) ⋏ tail))))

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

theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

theorem termValue_arithmeticFour (valuation : Nat -> Nat) :
    termValue valuation (‘4’ : ValuationTerm) = 4 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

theorem termValue_arithmeticFive (valuation : Nat -> Nat) :
    termValue valuation (‘5’ : ValuationTerm) = 5 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

noncomputable def nativeEqCertificate
    (left right : ValuationTerm)
    (heq : termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate (nativeEqFormula left right) := by
  unfold nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![left, right] heq
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

noncomputable def nativeNeCertificate
    (left right : ValuationTerm)
    (hne : ¬termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate (nativeNeFormula left right) := by
  unfold nativeNeFormula nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq ![left, right] hne
  exact .cast
    (congrArg (fun formula : ValuationFormula => ∼formula)
      (Semiformula.Operator.eq_def _ _).symm) direct

noncomputable def nativeLeCertificateCore
    (left right : ValuationTerm)
    (hle : termValue zeroValuation left ≤ termValue zeroValuation right) :
    HybridCertificate “!!left ≤ !!right” := by
  if heq : termValue zeroValuation left = termValue zeroValuation right then
    have hequality :
        FoundationCompactPAValuationAtomicCompiler.formulaValue zeroValuation
          (LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right]) := by
      change termValue zeroValuation left = termValue zeroValuation right
      exact heq
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![left, right] hequality
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![left, right]) equality
    exact .cast (Semiformula.Operator.le_def _ _).symm
      direct
  else
    have hlt : termValue zeroValuation left < termValue zeroValuation right :=
      Nat.lt_of_le_of_ne hle heq
    have hstrict :
        FoundationCompactPAValuationAtomicCompiler.formulaValue zeroValuation
          (LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
            ![left, right]) := by
      change termValue zeroValuation left < termValue zeroValuation right
      exact hlt
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![left, right] hstrict
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![left, right]) strict
    exact .cast (Semiformula.Operator.le_def _ _).symm
      direct

noncomputable def nativeLeCertificate
    (left right : ValuationTerm)
    (hle : termValue zeroValuation left ≤ termValue zeroValuation right) :
    HybridCertificate (nativeLeFormula left right) :=
  nativeLeCertificateCore left right hle

def compactFormulaTransformFormulaOutputRowsClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformFormulaOutputRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm current.start,
      shortBinaryNumeralTerm current.finish,
      shortBinaryNumeralTerm current.parserFinish,
      shortBinaryNumeralTerm current.parserTokensFinish,
      shortBinaryNumeralTerm current.parserTasksFinish,
      shortBinaryNumeralTerm current.parserTokensBoundary,
      shortBinaryNumeralTerm current.parserTokensCount,
      shortBinaryNumeralTerm current.parserTasksBoundary,
      shortBinaryNumeralTerm current.parserTasksCount,
      shortBinaryNumeralTerm current.outputBoundary,
      shortBinaryNumeralTerm current.outputCount,
      shortBinaryNumeralTerm next.start,
      shortBinaryNumeralTerm next.finish,
      shortBinaryNumeralTerm next.parserFinish,
      shortBinaryNumeralTerm next.parserTokensFinish,
      shortBinaryNumeralTerm next.parserTasksFinish,
      shortBinaryNumeralTerm next.parserTokensBoundary,
      shortBinaryNumeralTerm next.parserTokensCount,
      shortBinaryNumeralTerm next.parserTasksBoundary,
      shortBinaryNumeralTerm next.parserTasksCount,
      shortBinaryNumeralTerm next.outputBoundary,
      shortBinaryNumeralTerm next.outputCount,
      shortBinaryNumeralTerm mode,
      shortBinaryNumeralTerm tag,
      shortBinaryNumeralTerm consumedCount,
      shortBinaryNumeralTerm mappedHead]

def compactFormulaTransformFormulaOutputRowsExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : ValuationFormula :=
  let currentTokensCountTerm := shortBinaryNumeralTerm current.parserTokensCount
  let nextTokensCountTerm := shortBinaryNumeralTerm next.parserTokensCount
  let modeTerm := shortBinaryNumeralTerm mode
  let consumedCountTerm := shortBinaryNumeralTerm consumedCount
  nativeEqFormula currentTokensCountTerm
      (nativeAddTerm consumedCountTerm nextTokensCountTerm) ⋏
    ((nativeEqFormula consumedCountTerm (‘0’ : ValuationTerm) ⋏
        compactAdditiveNatListSameRowsClosedFormula
          tokenTable width tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount) ⋎
      (nativeLeFormula (‘1’ : ValuationTerm) consumedCountTerm ⋏
        ((rawModeFormula modeTerm ⋏
            compactAdditiveNatListAppendSourcePrefixClosedFormula
              tokenTable width tokenCount
              current.parserFinish current.finish current.outputCount
              current.start current.parserTokensFinish current.parserTokensCount
              consumedCount next.parserFinish next.finish next.outputCount) ⋎
          ((nativeEqFormula modeTerm (‘4’ : ValuationTerm) ⋏
              compactAdditiveNatListSameRowsClosedFormula
                tokenTable width tokenCount current.outputBoundary current.outputCount
                  next.outputBoundary next.outputCount) ⋎
            otherModeWithTailFormula modeTerm
              (compactNegationFormulaTagClosedFormula tag mappedHead ⋏
                compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
                  tokenTable width tokenCount
                  current.parserFinish current.finish current.outputCount
                  current.start current.parserTokensFinish
                    current.parserTokensCount consumedCount
                  next.parserFinish next.finish next.outputBoundary
                    next.outputCount mappedHead)))))

theorem compactFormulaTransformFormulaOutputRowsClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) :
    compactFormulaTransformFormulaOutputRowsClosedFormula
        tokenTable width tokenCount current next mode tag consumedCount mappedHead =
      compactFormulaTransformFormulaOutputRowsExplicitFormula
        tokenTable width tokenCount current next mode tag consumedCount mappedHead := by
  unfold compactFormulaTransformFormulaOutputRowsClosedFormula
  unfold compactFormulaTransformFormulaOutputRowsExplicitFormula
  unfold compactFormulaTransformFormulaOutputRowsDef
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactAdditiveNatListAppendSourcePrefixClosedFormula
  unfold compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
  unfold compactNegationFormulaTagClosedFormula
  unfold rawModeFormula otherModeWithTailFormula
  unfold nativeEqFormula nativeNeFormula nativeLeFormula nativeAddTerm
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    first
    | rfl
    | (congr 1
       apply arithmeticRewritingApp_congr
       apply Rew.ext
       · intro coordinate
         fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
       · intro coordinate
         exact Empty.elim coordinate)

noncomputable def consumedCountEqualityCertificate
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount))) :=
  nativeEqCertificate
    (shortBinaryNumeralTerm current.parserTokensCount)
    (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm next.parserTokensCount)) (by
      simpa [nativeAddTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd] using hcount)

noncomputable def consumedCountZeroCertificate
    (consumedCount : Nat) (hzero : consumedCount = 0) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
        (‘0’ : ValuationTerm)) :=
  nativeEqCertificate (shortBinaryNumeralTerm consumedCount)
    (‘0’ : ValuationTerm) (by
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticZero] using hzero)

noncomputable def consumedCountPositiveCertificate
    (consumedCount : Nat) (hpositive : 1 ≤ consumedCount) :
    HybridCertificate
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount)) :=
  nativeLeCertificate (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm consumedCount) (by
      simpa [termValue_arithmeticOne,
        termValue_shortBinaryNumeralTerm] using hpositive)

noncomputable def modeNativeEqualityCertificate
    (mode : Nat) (literal : ValuationTerm) (expected : Nat)
    (hliteral : termValue zeroValuation literal = expected)
    (heq : mode = expected) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm mode)
        literal) :=
  nativeEqCertificate (shortBinaryNumeralTerm mode) literal (by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using heq)

noncomputable def modeNativeInequalityCertificate
    (mode : Nat) (literal : ValuationTerm) (expected : Nat)
    (hliteral : termValue zeroValuation literal = expected)
    (hne : mode ≠ expected) :
    HybridCertificate
      (nativeNeFormula (shortBinaryNumeralTerm mode)
        literal) :=
  nativeNeCertificate (shortBinaryNumeralTerm mode) literal (by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using hne)

private theorem rawModeCertificate_nonempty
    (mode : Nat) (hmode : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 5) :
    Nonempty (HybridCertificate
      (rawModeFormula (shortBinaryNumeralTerm mode))) := by
  rcases hmode with hmode | hmode | hmode | hmode
  · exact ⟨.disjunctionLeft
      (modeNativeEqualityCertificate mode (‘0’ : ValuationTerm) 0
        (termValue_arithmeticZero zeroValuation) hmode)⟩
  · exact ⟨.disjunctionRight (.disjunctionLeft
      (modeNativeEqualityCertificate mode (‘1’ : ValuationTerm) 1
        (termValue_arithmeticOne zeroValuation) hmode))⟩
  · exact ⟨.disjunctionRight (.disjunctionRight (.disjunctionLeft
      (modeNativeEqualityCertificate mode (‘2’ : ValuationTerm) 2
        (termValue_arithmeticTwo zeroValuation) hmode)))⟩
  · exact ⟨.disjunctionRight (.disjunctionRight (.disjunctionRight
      (modeNativeEqualityCertificate mode (‘5’ : ValuationTerm) 5
        (termValue_arithmeticFive zeroValuation) hmode)))⟩

private noncomputable def rawModeCertificate
    (mode : Nat) (hmode : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 5) :
    HybridCertificate (rawModeFormula (shortBinaryNumeralTerm mode)) :=
  Classical.choice (rawModeCertificate_nonempty mode hmode)

noncomputable def otherModeWithTailCertificate
    (mode : Nat)
    (hzero : mode ≠ 0) (hone : mode ≠ 1) (htwo : mode ≠ 2)
    (hfour : mode ≠ 4) (hfive : mode ≠ 5)
    (tail : ValuationFormula) (tailCertificate : HybridCertificate tail) :
    HybridCertificate
      (otherModeWithTailFormula (shortBinaryNumeralTerm mode) tail) :=
  .conjunction
    (modeNativeInequalityCertificate mode (‘0’ : ValuationTerm) 0
      (termValue_arithmeticZero zeroValuation) hzero)
    (.conjunction
      (modeNativeInequalityCertificate mode (‘1’ : ValuationTerm) 1
        (termValue_arithmeticOne zeroValuation) hone)
      (.conjunction
        (modeNativeInequalityCertificate mode (‘2’ : ValuationTerm) 2
          (termValue_arithmeticTwo zeroValuation) htwo)
        (.conjunction
          (modeNativeInequalityCertificate mode (‘4’ : ValuationTerm) 4
            (termValue_arithmeticFour zeroValuation) hfour)
          (.conjunction
            (modeNativeInequalityCertificate mode (‘5’ : ValuationTerm) 5
              (termValue_arithmeticFive zeroValuation) hfive)
            tailCertificate))))

inductive CompactFormulaTransformFormulaOutputRowsCheckedBranchData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) : Type
  | zero
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : consumedCount = 0)
      (hsame : CompactFormulaTransformOutputSameRows
        tokenTable width tokenCount current next)
  | rawZero
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 0)
      (hsource : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | rawOne
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 1)
      (hsource : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | rawTwo
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 2)
      (hsource : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | rawFive
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 5)
      (hsource : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | sameFour
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 4)
      (hsame : CompactFormulaTransformOutputSameRows
        tokenTable width tokenCount current next)
  | mapped
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmodeZero : mode ≠ 0)
      (hmodeOne : mode ≠ 1)
      (hmodeTwo : mode ≠ 2)
      (hmodeFour : mode ≠ 4)
      (hmodeFive : mode ≠ 5)
      (htag : CompactNegationFormulaTagGraph tag mappedHead)
      (hrows : CompactFormulaTransformOutputMappedPrefixRows
        tokenTable width tokenCount current next consumedCount mappedHead)

theorem
    compactFormulaTransformFormulaOutputRowsCheckedBranchData_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount mappedHead) :
    Nonempty (CompactFormulaTransformFormulaOutputRowsCheckedBranchData
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) := by
  rcases hgraph with ⟨hcount, hzero | hpositive⟩
  · rcases hzero with ⟨hconsumed, hsame⟩
    exact ⟨.zero hcount hconsumed hsame⟩
  · rcases hpositive with ⟨hconsumed, hbranches⟩
    rcases hbranches with hraw | hsame | hmapped
    · rcases hraw with ⟨hmode, hsource⟩
      rcases hmode with hmode | hmode | hmode | hmode
      · exact ⟨.rawZero hcount hconsumed hmode hsource⟩
      · exact ⟨.rawOne hcount hconsumed hmode hsource⟩
      · exact ⟨.rawTwo hcount hconsumed hmode hsource⟩
      · exact ⟨.rawFive hcount hconsumed hmode hsource⟩
    · rcases hsame with ⟨hmode, hrows⟩
      exact ⟨.sameFour hcount hconsumed hmode hrows⟩
    · rcases hmapped with
        ⟨hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive, htag, hrows⟩
      exact ⟨.mapped hcount hconsumed hmodeZero hmodeOne hmodeTwo
        hmodeFour hmodeFive htag hrows⟩

noncomputable def
    compactFormulaTransformFormulaOutputRowsCheckedBranchDataOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) :
    CompactFormulaTransformFormulaOutputRowsCheckedBranchData
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead :=
  Classical.choice
    (compactFormulaTransformFormulaOutputRowsCheckedBranchData_nonempty
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      hgraph)

noncomputable def
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (data : CompactFormulaTransformFormulaOutputRowsCheckedBranchData
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead) :
    HybridCertificate
      (compactFormulaTransformFormulaOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode tag consumedCount mappedHead) := by
  cases data with
  | zero hcount hconsumed hsame =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let zeroCertificate :=
        consumedCountZeroCertificate consumedCount hconsumed
      let sameCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount hsame
      exact .conjunction countCertificate
        (.disjunctionLeft (.conjunction zeroCertificate sameCertificate))
  | rawZero hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : HybridCertificate
          (rawModeFormula (shortBinaryNumeralTerm mode)) := .disjunctionLeft
        (modeNativeEqualityCertificate mode (‘0’ : ValuationTerm) 0
          (termValue_arithmeticZero zeroValuation) hmode)
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionLeft (.conjunction modeCertificate sourceCertificate))))
  | rawOne hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : HybridCertificate
          (rawModeFormula (shortBinaryNumeralTerm mode)) :=
        .disjunctionRight (.disjunctionLeft
        (modeNativeEqualityCertificate mode (‘1’ : ValuationTerm) 1
          (termValue_arithmeticOne zeroValuation) hmode))
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionLeft (.conjunction modeCertificate sourceCertificate))))
  | rawTwo hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : HybridCertificate
          (rawModeFormula (shortBinaryNumeralTerm mode)) :=
        .disjunctionRight (.disjunctionRight (.disjunctionLeft
          (modeNativeEqualityCertificate mode (‘2’ : ValuationTerm) 2
            (termValue_arithmeticTwo zeroValuation) hmode)))
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionLeft (.conjunction modeCertificate sourceCertificate))))
  | rawFive hcount hconsumed hmode hsource =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate : HybridCertificate
          (rawModeFormula (shortBinaryNumeralTerm mode)) :=
        .disjunctionRight (.disjunctionRight (.disjunctionRight
          (modeNativeEqualityCertificate mode (‘5’ : ValuationTerm) 5
            (termValue_arithmeticFive zeroValuation) hmode)))
      let sourceCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hsource
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionLeft (.conjunction modeCertificate sourceCertificate))))
  | sameFour hcount hconsumed hmode hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate :=
        modeNativeEqualityCertificate mode (‘4’ : ValuationTerm) 4
          (termValue_arithmeticFour zeroValuation) hmode
      let sameCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionLeft
            (.conjunction modeCertificate sameCertificate)))))
  | mapped hcount hconsumed hmodeZero hmodeOne hmodeTwo hmodeFour hmodeFive
      htag hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let tagCertificate :=
        compactNegationFormulaTagExplicitHybridCertificateOfGraph
          tag mappedHead htag
      let rowsCertificate :=
        compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount
          current.parserFinish current.finish current.outputCount
          current.start current.parserTokensFinish current.parserTokensCount
          consumedCount next.parserFinish next.finish next.outputBoundary
          next.outputCount mappedHead hrows
      let mappedCertificate := otherModeWithTailCertificate mode hmodeZero
        hmodeOne hmodeTwo hmodeFour hmodeFive
        (compactNegationFormulaTagClosedFormula tag mappedHead ⋏
          compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            current.start current.parserTokensFinish current.parserTokensCount
            consumedCount next.parserFinish next.finish next.outputBoundary
            next.outputCount mappedHead)
        (.conjunction tagCertificate rowsCertificate)
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight
            mappedCertificate))))

noncomputable def
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount mappedHead) :
    HybridCertificate
      (compactFormulaTransformFormulaOutputRowsClosedFormula
        tokenTable width tokenCount current next mode tag consumedCount mappedHead) :=
  .cast
    (compactFormulaTransformFormulaOutputRowsClosedFormula_alignment
      tokenTable width tokenCount current next mode tag consumedCount mappedHead).symm
    (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      (compactFormulaTransformFormulaOutputRowsCheckedBranchDataOfGraph
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead hgraph))

noncomputable def
    compileCompactFormulaTransformFormulaOutputRowsExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount mappedHead) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformFormulaOutputRowsClosedFormula
          tokenTable width tokenCount current next mode tag consumedCount mappedHead).freeVariables
        zeroValuation)
      (compactFormulaTransformFormulaOutputRowsClosedFormula
        tokenTable width tokenCount current next mode tag consumedCount mappedHead) :=
  (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current next mode tag consumedCount mappedHead hgraph).compile

noncomputable def
    compactFormulaTransformFormulaOutputRowsExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount mappedHead) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode tag consumedCount mappedHead hgraph)

theorem
    compileCompactFormulaTransformFormulaOutputRowsExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hgraph : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount mappedHead) :
    (compileCompactFormulaTransformFormulaOutputRowsExplicitHybridContext
      tokenTable width tokenCount current next mode tag consumedCount mappedHead hgraph).payloadLength ≤
      compactFormulaTransformFormulaOutputRowsExplicitStructuralResource
        tokenTable width tokenCount current next mode tag consumedCount mappedHead hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode tag consumedCount mappedHead hgraph)

#print axioms compactFormulaTransformFormulaOutputRowsClosedFormula_alignment
#print axioms
  compactFormulaTransformFormulaOutputRowsCheckedBranchData_nonempty
#print axioms
  compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
#print axioms compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformFormulaOutputRowsExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
