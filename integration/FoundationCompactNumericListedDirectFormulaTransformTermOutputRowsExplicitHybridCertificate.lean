import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for formula-transform term output rows

The formula below retains the original thirty-three-coordinate substitution,
including native arithmetic expressions, implication guards, and the bounded
residual witness used by the fix-iterator branch.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactParserDirectTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

abbrev zeroValuation : Nat -> Nat := fun _ => 0

abbrev HybridCertificate (formula : ValuationFormula) :=
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

private theorem arithmeticRew_comp_assoc
    {variables₁ variables₂ variables₃ variables₄ : Type*}
    {arity₁ arity₂ arity₃ arity₄ : Nat}
    (outer : Rew ℒₒᵣ variables₃ arity₃ variables₄ arity₄)
    (middle : Rew ℒₒᵣ variables₂ arity₂ variables₃ arity₃)
    (inner : Rew ℒₒᵣ variables₁ arity₁ variables₂ arity₂) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  apply Rew.ext
  · intro coordinate
    simp [Rew.comp_app]
  · intro coordinate
    simp [Rew.comp_app]

private theorem rewriting_emptyFormulaSubstitution
    {targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity -> ArithmeticSemiterm Empty sourceArity) :
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

def nativeAddTerm (left right : ValuationTerm) : ValuationTerm :=
  ‘!!left + !!right’

def nativeEqFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left = !!right”

def nativeNeFormula
    (left right : ValuationTerm) : ValuationFormula :=
  ∼(nativeEqFormula left right)

def nativeLtFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left < !!right”

def nativeLeFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left ≤ !!right”

def nativeImpFormula
    (left right : ValuationFormula) : ValuationFormula :=
  left 🡒 right

def tripleFailureFormula
    (consumedTerm tagTerm argumentTerm binderArityTerm : ValuationTerm) :
    ValuationFormula :=
  nativeImpFormula
    (nativeEqFormula consumedTerm (‘2’ : ValuationTerm))
    (nativeImpFormula
      (nativeEqFormula tagTerm (‘0’ : ValuationTerm))
      (nativeNeFormula (nativeAddTerm argumentTerm (‘1’ : ValuationTerm))
        binderArityTerm))

def doubleFailureFormula
    (consumedTerm tagTerm : ValuationTerm) : ValuationFormula :=
  nativeImpFormula
    (nativeEqFormula consumedTerm (‘2’ : ValuationTerm))
    (nativeNeFormula tagTerm (‘1’ : ValuationTerm))

def otherModesWithTailFormula
    (modeTerm : ValuationTerm) (tail : ValuationFormula) : ValuationFormula :=
  nativeNeFormula modeTerm (‘0’ : ValuationTerm) ⋏
    (nativeNeFormula modeTerm (‘1’ : ValuationTerm) ⋏
      (nativeNeFormula modeTerm (‘2’ : ValuationTerm) ⋏
        (nativeNeFormula modeTerm (‘4’ : ValuationTerm) ⋏
          (nativeNeFormula modeTerm (‘5’ : ValuationTerm) ⋏ tail))))

def compactFormulaTransformTermResidualWitnessBody
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount : Nat) : ArithmeticSemiformula Nat 1 :=
  let argumentTerm := shortBinaryNumeralTerm argument
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  “#0 < !!(Rew.bShift argumentTerm) + 1” ⋏
    (“!!(Rew.bShift argumentTerm) =
        !!(Rew.bShift witnessCountTerm) + #0” ⋏
      ((Rewriting.emb (ξ := Nat)
          compactAdditiveNatListAppendTwoValuesDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
          Rew.bShift (shortBinaryNumeralTerm width),
          Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (shortBinaryNumeralTerm current.parserFinish),
          Rew.bShift (shortBinaryNumeralTerm current.finish),
          Rew.bShift (shortBinaryNumeralTerm current.outputCount),
          Rew.bShift (shortBinaryNumeralTerm next.parserFinish),
          Rew.bShift (shortBinaryNumeralTerm next.finish),
          Rew.bShift (shortBinaryNumeralTerm next.outputBoundary),
          Rew.bShift (shortBinaryNumeralTerm next.outputCount),
          Rew.bShift (‘1’ : ValuationTerm),
          (#0 : ArithmeticSemiterm Nat 1)]))

def compactFormulaTransformTermResidualExistsFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount : Nat) : ValuationFormula :=
  ∃⁰ compactFormulaTransformTermResidualWitnessBody tokenTable width
    tokenCount current next argument witnessCount

def compactFormulaTransformTermOutputRowsOuterTerms
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : Fin 33 -> ValuationTerm :=
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
    shortBinaryNumeralTerm binderArity,
    shortBinaryNumeralTerm tag,
    shortBinaryNumeralTerm argument,
    shortBinaryNumeralTerm consumedCount,
    shortBinaryNumeralTerm witnessStart,
    shortBinaryNumeralTerm witnessFinish,
    shortBinaryNumeralTerm witnessCount]

private def compactFormulaTransformTermOutputRowsDepthOneTerms
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    Fin 34 -> ArithmeticSemiterm Nat 1 :=
  ![(#0 : ArithmeticSemiterm Nat 1),
    Rew.bShift (shortBinaryNumeralTerm tokenTable),
    Rew.bShift (shortBinaryNumeralTerm width),
    Rew.bShift (shortBinaryNumeralTerm tokenCount),
    Rew.bShift (shortBinaryNumeralTerm current.start),
    Rew.bShift (shortBinaryNumeralTerm current.finish),
    Rew.bShift (shortBinaryNumeralTerm current.parserFinish),
    Rew.bShift (shortBinaryNumeralTerm current.parserTokensFinish),
    Rew.bShift (shortBinaryNumeralTerm current.parserTasksFinish),
    Rew.bShift (shortBinaryNumeralTerm current.parserTokensBoundary),
    Rew.bShift (shortBinaryNumeralTerm current.parserTokensCount),
    Rew.bShift (shortBinaryNumeralTerm current.parserTasksBoundary),
    Rew.bShift (shortBinaryNumeralTerm current.parserTasksCount),
    Rew.bShift (shortBinaryNumeralTerm current.outputBoundary),
    Rew.bShift (shortBinaryNumeralTerm current.outputCount),
    Rew.bShift (shortBinaryNumeralTerm next.start),
    Rew.bShift (shortBinaryNumeralTerm next.finish),
    Rew.bShift (shortBinaryNumeralTerm next.parserFinish),
    Rew.bShift (shortBinaryNumeralTerm next.parserTokensFinish),
    Rew.bShift (shortBinaryNumeralTerm next.parserTasksFinish),
    Rew.bShift (shortBinaryNumeralTerm next.parserTokensBoundary),
    Rew.bShift (shortBinaryNumeralTerm next.parserTokensCount),
    Rew.bShift (shortBinaryNumeralTerm next.parserTasksBoundary),
    Rew.bShift (shortBinaryNumeralTerm next.parserTasksCount),
    Rew.bShift (shortBinaryNumeralTerm next.outputBoundary),
    Rew.bShift (shortBinaryNumeralTerm next.outputCount),
    Rew.bShift (shortBinaryNumeralTerm mode),
    Rew.bShift (shortBinaryNumeralTerm binderArity),
    Rew.bShift (shortBinaryNumeralTerm tag),
    Rew.bShift (shortBinaryNumeralTerm argument),
    Rew.bShift (shortBinaryNumeralTerm consumedCount),
    Rew.bShift (shortBinaryNumeralTerm witnessStart),
    Rew.bShift (shortBinaryNumeralTerm witnessFinish),
    Rew.bShift (shortBinaryNumeralTerm witnessCount)]

private theorem compactFormulaTransformTermOutputRowsOuterQ_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    (Rew.subst (compactFormulaTransformTermOutputRowsOuterTerms tokenTable width
      tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount)).q =
      Rew.subst (compactFormulaTransformTermOutputRowsDepthOneTerms tokenTable
        width tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [compactFormulaTransformTermOutputRowsOuterTerms,
        compactFormulaTransformTermOutputRowsDepthOneTerms, Rew.q]
  · rfl

private def compactFormulaTransformTermResidualSourcePayload :
    ArithmeticSemiformula Empty 34 :=
  (“#29 = #33 + #0” : ArithmeticSemiformula Empty 34) ⋏
    (compactAdditiveNatListAppendTwoValuesDef.val ⇜
      ![(#1 : ArithmeticSemiterm Empty 34), #2, #3, #6, #5, #14,
        #17, #16, #24, #25, (‘1’ : ArithmeticSemiterm Empty 34), #0])

private def compactFormulaTransformTermResidualTargetPayload
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount : Nat) : ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift (shortBinaryNumeralTerm argument)) =
      !!(Rew.bShift (shortBinaryNumeralTerm witnessCount)) + #0” ⋏
    ((Rewriting.emb (ξ := Nat)
        compactAdditiveNatListAppendTwoValuesDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
        Rew.bShift (shortBinaryNumeralTerm width),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (shortBinaryNumeralTerm current.parserFinish),
        Rew.bShift (shortBinaryNumeralTerm current.finish),
        Rew.bShift (shortBinaryNumeralTerm current.outputCount),
        Rew.bShift (shortBinaryNumeralTerm next.parserFinish),
        Rew.bShift (shortBinaryNumeralTerm next.finish),
        Rew.bShift (shortBinaryNumeralTerm next.outputBoundary),
        Rew.bShift (shortBinaryNumeralTerm next.outputCount),
        Rew.bShift (‘1’ : ValuationTerm),
        (#0 : ArithmeticSemiterm Nat 1)])

private theorem compactFormulaTransformTermResidualAppendRewriting_outer_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    ((Rew.subst (compactFormulaTransformTermOutputRowsOuterTerms tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount)).q.comp
      ((Rew.emb : Rew ℒₒᵣ Empty 34 Nat 34).comp
        (Rew.subst
          ![(#1 : ArithmeticSemiterm Empty 34), #2, #3, #6, #5, #14,
            #17, #16, #24, #25,
            (‘1’ : ArithmeticSemiterm Empty 34), #0]))) =
      (Rew.subst
        ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
          Rew.bShift (shortBinaryNumeralTerm width),
          Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (shortBinaryNumeralTerm current.parserFinish),
          Rew.bShift (shortBinaryNumeralTerm current.finish),
          Rew.bShift (shortBinaryNumeralTerm current.outputCount),
          Rew.bShift (shortBinaryNumeralTerm next.parserFinish),
          Rew.bShift (shortBinaryNumeralTerm next.finish),
          Rew.bShift (shortBinaryNumeralTerm next.outputBoundary),
          Rew.bShift (shortBinaryNumeralTerm next.outputCount),
          Rew.bShift (‘1’ : ValuationTerm),
          (#0 : ArithmeticSemiterm Nat 1)]).comp
        (Rew.emb : Rew ℒₒᵣ Empty 12 Nat 12) := by
  rw [compactFormulaTransformTermOutputRowsOuterQ_eq]
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [compactFormulaTransformTermOutputRowsDepthOneTerms,
        Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

private theorem compactFormulaTransformTermResidualPayload_outer_rewrite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    ((Rew.subst (compactFormulaTransformTermOutputRowsOuterTerms tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount)).q.comp
      (Rew.emb : Rew ℒₒᵣ Empty 34 Nat 34)) ▹
        compactFormulaTransformTermResidualSourcePayload =
      compactFormulaTransformTermResidualTargetPayload tokenTable width
        tokenCount current next argument witnessCount := by
  rw [compactFormulaTransformTermOutputRowsOuterQ_eq]
  have hcomposition :
      (Rew.subst (compactFormulaTransformTermOutputRowsDepthOneTerms tokenTable
        width tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount)).comp
          (Rew.emb : Rew ℒₒᵣ Empty 34 Nat 34) =
        Rew.embSubsts
          (compactFormulaTransformTermOutputRowsDepthOneTerms tokenTable width
            tokenCount current next mode binderArity tag argument consumedCount
            witnessStart witnessFinish witnessCount) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  rw [hcomposition]
  unfold compactFormulaTransformTermResidualSourcePayload
  unfold compactFormulaTransformTermResidualTargetPayload
  simp [← TransitiveRewriting.comp_app,
    compactFormulaTransformTermOutputRowsDepthOneTerms]
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

def compactFormulaTransformTermOutputRowsClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformTermOutputRowsDef.val) ⇜
    compactFormulaTransformTermOutputRowsOuterTerms tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
        witnessFinish witnessCount

def compactFormulaTransformTermOutputRowsExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : ValuationFormula :=
  let modeTerm := shortBinaryNumeralTerm mode
  let binderArityTerm := shortBinaryNumeralTerm binderArity
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  let tripleFailure := tripleFailureFormula consumedTerm tagTerm argumentTerm
    binderArityTerm
  let doubleFailure := doubleFailureFormula consumedTerm tagTerm
  let rawPrefix :=
    compactAdditiveNatListAppendSourcePrefixClosedFormula
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      current.start current.parserTokensFinish current.parserTokensCount
      consumedCount next.parserFinish next.finish next.outputCount
  let sameRows :=
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount
  let guardZeroTag :=
    nativeEqFormula consumedTerm (‘2’ : ValuationTerm) ⋏
      (nativeEqFormula tagTerm (‘0’ : ValuationTerm) ⋏
        nativeEqFormula
          (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm)
  let guardOneTag :=
    nativeEqFormula consumedTerm (‘2’ : ValuationTerm) ⋏
      nativeEqFormula tagTerm (‘1’ : ValuationTerm)
  let appendTwoOneZero :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
  let appendTwoShifted :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘1’ : ValuationTerm)
      (nativeAddTerm argumentTerm (‘1’ : ValuationTerm))
  let witnessRows := compactAdditiveNatListAppendSlicesClosedFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount witnessStart witnessFinish witnessCount
    next.parserFinish next.finish next.outputCount
  let oneValueRows := compactAdditiveNatListAppendOneValueClosedFormula
    tokenTable width tokenCount current.parserFinish current.finish
    current.outputCount next.parserFinish next.finish next.outputBoundary
    next.outputCount argument
  let capturedGuard :=
    nativeEqFormula consumedTerm (‘2’ : ValuationTerm) ⋏
      (nativeEqFormula tagTerm (‘1’ : ValuationTerm) ⋏
        nativeLtFormula argumentTerm witnessCountTerm)
  let capturedRows :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘0’ : ValuationTerm)
      (nativeAddTerm binderArityTerm argumentTerm)
  let residualGuard :=
    nativeEqFormula consumedTerm (‘2’ : ValuationTerm) ⋏
      (nativeEqFormula tagTerm (‘1’ : ValuationTerm) ⋏
        nativeLeFormula witnessCountTerm argumentTerm)
  let residualRows := compactFormulaTransformTermResidualExistsFormula
    tokenTable width tokenCount current next argument witnessCount
  let modeZeroBranch :=
    nativeEqFormula modeTerm (‘0’ : ValuationTerm) ⋏
      ((guardZeroTag ⋏ appendTwoOneZero) ⋎
        ((tripleFailure ⋏ (guardOneTag ⋏ appendTwoShifted)) ⋎
          (tripleFailure ⋏ (doubleFailure ⋏ rawPrefix))))
  let modeOneBranch :=
    nativeEqFormula modeTerm (‘1’ : ValuationTerm) ⋏
      ((guardOneTag ⋏ appendTwoShifted) ⋎
        (doubleFailure ⋏ rawPrefix))
  let modeTwoBranch :=
    nativeEqFormula modeTerm (‘2’ : ValuationTerm) ⋏
      ((guardZeroTag ⋏ witnessRows) ⋎
        (tripleFailure ⋏ rawPrefix))
  let modeFourBranch :=
    nativeEqFormula modeTerm (‘4’ : ValuationTerm) ⋏
      ((guardOneTag ⋏ oneValueRows) ⋎
        (doubleFailure ⋏ sameRows))
  let modeFiveBranch :=
    nativeEqFormula modeTerm (‘5’ : ValuationTerm) ⋏
      ((capturedGuard ⋏ capturedRows) ⋎
        ((residualGuard ⋏ residualRows) ⋎
          (doubleFailure ⋏ rawPrefix)))
  let otherBranch := otherModesWithTailFormula modeTerm rawPrefix
  nativeEqFormula (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm consumedTerm
        (shortBinaryNumeralTerm next.parserTokensCount)) ⋏
    ((nativeEqFormula consumedTerm (‘0’ : ValuationTerm) ⋏ sameRows) ⋎
      (nativeLeFormula (‘1’ : ValuationTerm) consumedTerm ⋏
        (modeZeroBranch ⋎
          (modeOneBranch ⋎
            (modeTwoBranch ⋎
              (modeFourBranch ⋎ (modeFiveBranch ⋎ otherBranch)))))))

theorem compactFormulaTransformTermResidualWitnessBody_substitution_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount residual : Nat) :
    (compactFormulaTransformTermResidualWitnessBody tokenTable width tokenCount
      current next argument witnessCount)/[shortBinaryNumeralTerm residual] =
      (“!!(shortBinaryNumeralTerm residual) <
          !!(shortBinaryNumeralTerm argument) + 1” ⋏
        (nativeEqFormula (shortBinaryNumeralTerm argument)
            (nativeAddTerm (shortBinaryNumeralTerm witnessCount)
              (shortBinaryNumeralTerm residual)) ⋏
          compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            next.parserFinish next.finish next.outputBoundary next.outputCount
            (‘1’ : ValuationTerm) (shortBinaryNumeralTerm residual))) := by
  unfold compactFormulaTransformTermResidualWitnessBody
  unfold compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
  unfold nativeEqFormula nativeAddTerm
  simp [← TransitiveRewriting.comp_app, Rew.subst_bvar]
  all_goals
    first
    | rfl
    | (congr 1
       apply arithmeticRewritingApp_congr
       apply Rew.ext
       · intro coordinate
         fin_cases coordinate <;>
           simp [Rew.comp_app, Rew.subst_bvar]
       · intro coordinate
         exact Empty.elim coordinate)

theorem compactFormulaTransformTermOutputRowsClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    compactFormulaTransformTermOutputRowsClosedFormula tokenTable width tokenCount
        current next mode binderArity tag argument consumedCount witnessStart
          witnessFinish witnessCount =
      compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount := by
  unfold compactFormulaTransformTermOutputRowsClosedFormula
  unfold compactFormulaTransformTermOutputRowsExplicitFormula
  unfold compactFormulaTransformTermResidualExistsFormula
  unfold compactFormulaTransformTermResidualWitnessBody
  unfold compactFormulaTransformTermOutputRowsDef
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactAdditiveNatListAppendSourcePrefixClosedFormula
  unfold compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
  unfold compactAdditiveNatListAppendOneValueClosedFormula
  unfold compactAdditiveNatListAppendSlicesClosedFormula
  unfold tripleFailureFormula doubleFailureFormula otherModesWithTailFormula
  unfold nativeImpFormula nativeEqFormula nativeNeFormula nativeLtFormula
    nativeLeFormula nativeAddTerm
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    DeMorgan.imply, ← TransitiveRewriting.comp_app,
    compactFormulaTransformTermOutputRowsOuterTerms]
  repeat' apply And.intro
  all_goals
    first
    | rfl
    | (have hq := compactFormulaTransformTermOutputRowsOuterQ_eq
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
       have happend :=
        compactFormulaTransformTermResidualAppendRewriting_outer_eq
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
       unfold compactFormulaTransformTermOutputRowsOuterTerms at hq happend
       rw [happend, hq]
       simp [compactFormulaTransformTermOutputRowsDepthOneTerms,
         Rew.subst_bvar, LO.FirstOrder.bexs])
    | (congr 1
       apply arithmeticRewritingApp_congr
       apply Rew.ext
       · intro coordinate
         fin_cases coordinate <;>
           simp [Rew.comp_app, Rew.subst_bvar]
       · intro coordinate
         exact Empty.elim coordinate)

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

theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

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
    (hne : termValue zeroValuation left ≠ termValue zeroValuation right) :
    HybridCertificate (nativeNeFormula left right) := by
  unfold nativeNeFormula nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq ![left, right] hne
  exact .cast
    (congrArg (fun formula : ValuationFormula => ∼formula)
      (Semiformula.Operator.eq_def _ _).symm) direct

noncomputable def nativeLtCertificate
    (left right : ValuationTerm)
    (hlt : termValue zeroValuation left < termValue zeroValuation right) :
    HybridCertificate (nativeLtFormula left right) := by
  unfold nativeLtFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt ![left, right] hlt
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

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

noncomputable def shortNumeralLiteralEqCertificate
    (value expected : Nat) (literal : ValuationTerm)
    (hliteral : termValue zeroValuation literal = expected)
    (heq : value = expected) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm value) literal) :=
  nativeEqCertificate (shortBinaryNumeralTerm value) literal (by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using heq)

noncomputable def shortNumeralLiteralNeCertificate
    (value expected : Nat) (literal : ValuationTerm)
    (hliteral : termValue zeroValuation literal = expected)
    (hne : value ≠ expected) :
    HybridCertificate
      (nativeNeFormula (shortBinaryNumeralTerm value) literal) :=
  nativeNeCertificate (shortBinaryNumeralTerm value) literal (by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using hne)

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
  shortNumeralLiteralEqCertificate consumedCount 0 (‘0’ : ValuationTerm)
    (termValue_arithmeticZero zeroValuation) hzero

noncomputable def consumedCountPositiveCertificate
    (consumedCount : Nat) (hpositive : 1 ≤ consumedCount) :
    HybridCertificate
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount)) :=
  nativeLeCertificate (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm consumedCount) (by
      simpa [termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]
        using hpositive)

noncomputable def zeroTagGuardCertificate
    (consumedCount tag argument binderArity : Nat)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
          (‘2’ : ValuationTerm) ⋏
        (nativeEqFormula (shortBinaryNumeralTerm tag)
            (‘0’ : ValuationTerm) ⋏
          nativeEqFormula
            (nativeAddTerm (shortBinaryNumeralTerm argument)
              (‘1’ : ValuationTerm))
            (shortBinaryNumeralTerm binderArity))) :=
  .conjunction
    (shortNumeralLiteralEqCertificate consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo zeroValuation) hguard.1)
    (.conjunction
      (shortNumeralLiteralEqCertificate tag 0 (‘0’ : ValuationTerm)
        (termValue_arithmeticZero zeroValuation) hguard.2.1)
      (nativeEqCertificate
        (nativeAddTerm (shortBinaryNumeralTerm argument)
          (‘1’ : ValuationTerm))
        (shortBinaryNumeralTerm binderArity) (by
          simpa [nativeAddTerm, termValue_arithmeticAdd,
            termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]
            using hguard.2.2)))

noncomputable def oneTagGuardCertificate
    (consumedCount tag : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
          (‘2’ : ValuationTerm) ⋏
        nativeEqFormula (shortBinaryNumeralTerm tag)
          (‘1’ : ValuationTerm)) :=
  .conjunction
    (shortNumeralLiteralEqCertificate consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo zeroValuation) hguard.1)
    (shortNumeralLiteralEqCertificate tag 1 (‘1’ : ValuationTerm)
      (termValue_arithmeticOne zeroValuation) hguard.2)

noncomputable def capturedGuardCertificate
    (consumedCount tag argument witnessCount : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
          (‘2’ : ValuationTerm) ⋏
        (nativeEqFormula (shortBinaryNumeralTerm tag)
            (‘1’ : ValuationTerm) ⋏
          nativeLtFormula (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm witnessCount))) :=
  .conjunction
    (shortNumeralLiteralEqCertificate consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo zeroValuation) hguard.1)
    (.conjunction
      (shortNumeralLiteralEqCertificate tag 1 (‘1’ : ValuationTerm)
        (termValue_arithmeticOne zeroValuation) hguard.2.1)
      (nativeLtCertificate (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm witnessCount) (by
          simpa [termValue_shortBinaryNumeralTerm] using hguard.2.2)))

noncomputable def residualGuardCertificate
    (consumedCount tag argument witnessCount : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ witnessCount ≤ argument) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
          (‘2’ : ValuationTerm) ⋏
        (nativeEqFormula (shortBinaryNumeralTerm tag)
            (‘1’ : ValuationTerm) ⋏
          nativeLeFormula (shortBinaryNumeralTerm witnessCount)
            (shortBinaryNumeralTerm argument))) :=
  .conjunction
    (shortNumeralLiteralEqCertificate consumedCount 2 (‘2’ : ValuationTerm)
      (termValue_arithmeticTwo zeroValuation) hguard.1)
    (.conjunction
      (shortNumeralLiteralEqCertificate tag 1 (‘1’ : ValuationTerm)
        (termValue_arithmeticOne zeroValuation) hguard.2.1)
      (nativeLeCertificate (shortBinaryNumeralTerm witnessCount)
        (shortBinaryNumeralTerm argument) (by
          simpa [termValue_shortBinaryNumeralTerm] using hguard.2.2)))

def tripleFailureDisjunctionFormula
    (consumedTerm tagTerm argumentTerm binderArityTerm : ValuationTerm) :
    ValuationFormula :=
  nativeNeFormula consumedTerm (‘2’ : ValuationTerm) ⋎
    (nativeNeFormula tagTerm (‘0’ : ValuationTerm) ⋎
      nativeNeFormula (nativeAddTerm argumentTerm (‘1’ : ValuationTerm))
        binderArityTerm)

theorem tripleFailureFormula_eq_disjunction
    (consumedTerm tagTerm argumentTerm binderArityTerm : ValuationTerm) :
    tripleFailureFormula consumedTerm tagTerm argumentTerm binderArityTerm =
      tripleFailureDisjunctionFormula consumedTerm tagTerm argumentTerm
        binderArityTerm := by
  simp [tripleFailureFormula, tripleFailureDisjunctionFormula,
    nativeImpFormula, nativeNeFormula, DeMorgan.imply]

inductive TripleFailureCheckedData
    (consumedCount tag argument binderArity : Nat) : Type
  | consumed (hconsumed : consumedCount ≠ 2)
  | tag (hconsumed : consumedCount = 2) (htag : tag ≠ 0)
  | argument
      (hconsumed : consumedCount = 2)
      (htag : tag = 0)
      (hargument : argument + 1 ≠ binderArity)

def tripleFailureCheckedDataOfFailure
    (consumedCount tag argument binderArity : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 0 ∧
      argument + 1 = binderArity)) :
    TripleFailureCheckedData consumedCount tag argument binderArity := by
  by_cases hconsumed : consumedCount = 2
  · by_cases htag : tag = 0
    · exact .argument hconsumed htag (by
        intro hargument
        exact hfailure ⟨hconsumed, htag, hargument⟩)
    · exact .tag hconsumed htag
  · exact .consumed hconsumed

noncomputable def tripleFailureCertificateFromData
    (consumedCount tag argument binderArity : Nat)
    (data : TripleFailureCheckedData consumedCount tag argument binderArity) :
    HybridCertificate
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity)) := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let binderArityTerm := shortBinaryNumeralTerm binderArity
  cases data with
  | consumed hconsumed =>
      let core : HybridCertificate
          (tripleFailureDisjunctionFormula consumedTerm tagTerm argumentTerm
            binderArityTerm) :=
        .disjunctionLeft
          (shortNumeralLiteralNeCertificate consumedCount 2
            (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation)
            hconsumed)
      exact .cast
        (tripleFailureFormula_eq_disjunction consumedTerm tagTerm argumentTerm
          binderArityTerm).symm core
  | tag _ htag =>
      let core : HybridCertificate
          (tripleFailureDisjunctionFormula consumedTerm tagTerm argumentTerm
            binderArityTerm) :=
        .disjunctionRight (.disjunctionLeft
          (shortNumeralLiteralNeCertificate tag 0 (‘0’ : ValuationTerm)
            (termValue_arithmeticZero zeroValuation) htag))
      exact .cast
        (tripleFailureFormula_eq_disjunction consumedTerm tagTerm argumentTerm
          binderArityTerm).symm core
  | argument _ _ hargument =>
      let core : HybridCertificate
          (tripleFailureDisjunctionFormula consumedTerm tagTerm argumentTerm
            binderArityTerm) :=
        .disjunctionRight (.disjunctionRight
          (nativeNeCertificate
            (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) binderArityTerm
            (by
              simpa [consumedTerm, tagTerm, argumentTerm, binderArityTerm,
                nativeAddTerm, termValue_arithmeticAdd,
                termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]
                using hargument)))
      exact .cast
        (tripleFailureFormula_eq_disjunction consumedTerm tagTerm argumentTerm
          binderArityTerm).symm core

noncomputable def tripleFailureCertificate
    (consumedCount tag argument binderArity : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 0 ∧
      argument + 1 = binderArity)) :
    HybridCertificate
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity)) :=
  tripleFailureCertificateFromData consumedCount tag argument binderArity
    (tripleFailureCheckedDataOfFailure consumedCount tag argument binderArity
      hfailure)

def doubleFailureDisjunctionFormula
    (consumedTerm tagTerm : ValuationTerm) : ValuationFormula :=
  nativeNeFormula consumedTerm (‘2’ : ValuationTerm) ⋎
    nativeNeFormula tagTerm (‘1’ : ValuationTerm)

theorem doubleFailureFormula_eq_disjunction
    (consumedTerm tagTerm : ValuationTerm) :
    doubleFailureFormula consumedTerm tagTerm =
      doubleFailureDisjunctionFormula consumedTerm tagTerm := by
  simp [doubleFailureFormula, doubleFailureDisjunctionFormula,
    nativeImpFormula, nativeNeFormula, DeMorgan.imply]

inductive DoubleFailureCheckedData (consumedCount tag : Nat) : Type
  | consumed (hconsumed : consumedCount ≠ 2)
  | tag (hconsumed : consumedCount = 2) (htag : tag ≠ 1)

def doubleFailureCheckedDataOfFailure
    (consumedCount tag : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 1)) :
    DoubleFailureCheckedData consumedCount tag := by
  by_cases hconsumed : consumedCount = 2
  · exact .tag hconsumed (by
      intro htag
      exact hfailure ⟨hconsumed, htag⟩)
  · exact .consumed hconsumed

noncomputable def doubleFailureCertificateFromData
    (consumedCount tag : Nat)
    (data : DoubleFailureCheckedData consumedCount tag) :
    HybridCertificate
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag)) := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  cases data with
  | consumed hconsumed =>
      let core : HybridCertificate
          (doubleFailureDisjunctionFormula consumedTerm tagTerm) :=
        .disjunctionLeft
          (shortNumeralLiteralNeCertificate consumedCount 2
            (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation)
            hconsumed)
      exact .cast
        (doubleFailureFormula_eq_disjunction consumedTerm tagTerm).symm core
  | tag _ htag =>
      let core : HybridCertificate
          (doubleFailureDisjunctionFormula consumedTerm tagTerm) :=
        .disjunctionRight
          (shortNumeralLiteralNeCertificate tag 1 (‘1’ : ValuationTerm)
            (termValue_arithmeticOne zeroValuation) htag)
      exact .cast
        (doubleFailureFormula_eq_disjunction consumedTerm tagTerm).symm core

noncomputable def doubleFailureCertificate
    (consumedCount tag : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 1)) :
    HybridCertificate
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag)) :=
  doubleFailureCertificateFromData consumedCount tag
    (doubleFailureCheckedDataOfFailure consumedCount tag hfailure)

noncomputable def otherModesWithTailCertificate
    (mode : Nat)
    (hzero : mode ≠ 0) (hone : mode ≠ 1) (htwo : mode ≠ 2)
    (hfour : mode ≠ 4) (hfive : mode ≠ 5)
    (tail : ValuationFormula) (tailCertificate : HybridCertificate tail) :
    HybridCertificate
      (otherModesWithTailFormula (shortBinaryNumeralTerm mode) tail) :=
  .conjunction
    (shortNumeralLiteralNeCertificate mode 0 (‘0’ : ValuationTerm)
      (termValue_arithmeticZero zeroValuation) hzero)
    (.conjunction
      (shortNumeralLiteralNeCertificate mode 1 (‘1’ : ValuationTerm)
        (termValue_arithmeticOne zeroValuation) hone)
      (.conjunction
        (shortNumeralLiteralNeCertificate mode 2 (‘2’ : ValuationTerm)
          (termValue_arithmeticTwo zeroValuation) htwo)
        (.conjunction
          (shortNumeralLiteralNeCertificate mode 4 (‘4’ : ValuationTerm)
            (termValue_arithmeticFour zeroValuation) hfour)
          (.conjunction
            (shortNumeralLiteralNeCertificate mode 5 (‘5’ : ValuationTerm)
              (termValue_arithmeticFive zeroValuation) hfive)
            tailCertificate))))

noncomputable def compactFormulaTransformTermResidualExistsCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (argument witnessCount residual : Nat)
    (hresidual : residual ≤ argument)
    (hequality : argument = witnessCount + residual)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 residual) :
    HybridCertificate
      (compactFormulaTransformTermResidualExistsFormula tokenTable width
        tokenCount current next argument witnessCount) := by
  let residualTerm := shortBinaryNumeralTerm residual
  let argumentTerm := shortBinaryNumeralTerm argument
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  let boundCertificate := nativeLtCertificate residualTerm
    (nativeAddTerm argumentTerm (‘1’ : ValuationTerm)) (by
      simpa [residualTerm, argumentTerm, nativeAddTerm,
        termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
        termValue_arithmeticOne] using (Nat.lt_succ_iff.mpr hresidual))
  let equalityCertificate := nativeEqCertificate argumentTerm
    (nativeAddTerm witnessCountTerm residualTerm) (by
      simpa [argumentTerm, witnessCountTerm, residualTerm, nativeAddTerm,
        termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd]
        using hequality)
  let rowsCertificate :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 residual (‘1’ : ValuationTerm) residualTerm
      (termValue_arithmeticOne zeroValuation)
      (by simp [residualTerm, termValue_shortBinaryNumeralTerm]) hrows
  let canonicalCertificate : HybridCertificate
      (“!!residualTerm < !!argumentTerm + 1” ⋏
        (nativeEqFormula argumentTerm
            (nativeAddTerm witnessCountTerm residualTerm) ⋏
          compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            next.parserFinish next.finish next.outputBoundary next.outputCount
            (‘1’ : ValuationTerm) residualTerm)) :=
    .conjunction boundCertificate
      (.conjunction equalityCertificate rowsCertificate)
  let bodyCertificate : HybridCertificate
      ((compactFormulaTransformTermResidualWitnessBody tokenTable width tokenCount
        current next argument witnessCount)/[residualTerm]) :=
    .cast
      (compactFormulaTransformTermResidualWitnessBody_substitution_alignment
        tokenTable width tokenCount current next argument witnessCount residual).symm
      canonicalCertificate
  unfold compactFormulaTransformTermResidualExistsFormula
  exact .existsWitness
    (compactFormulaTransformTermResidualWitnessBody tokenTable width tokenCount
      current next argument witnessCount) residual bodyCertificate

inductive CompactFormulaTransformTermOutputRowsCheckedBranchData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : Type
  | zero
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : consumedCount = 0)
      (hsame : CompactFormulaTransformOutputSameRows
        tokenTable width tokenCount current next)
  | modeZeroLower
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 0)
      (hguard : consumedCount = 2 ∧ tag = 0 ∧
        argument + 1 = binderArity)
      (hrows : CompactFormulaTransformOutputTwoValuesRows
        tokenTable width tokenCount current next 1 0)
  | modeZeroShifted
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 0)
      (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
      (hguard : consumedCount = 2 ∧ tag = 1)
      (hrows : CompactFormulaTransformOutputTwoValuesRows
        tokenTable width tokenCount current next 1 (argument + 1))
  | modeZeroRaw
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 0)
      (lowerFailure : TripleFailureCheckedData
        consumedCount tag argument binderArity)
      (shiftFailure : DoubleFailureCheckedData consumedCount tag)
      (hrows : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | modeOneShifted
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 1)
      (hguard : consumedCount = 2 ∧ tag = 1)
      (hrows : CompactFormulaTransformOutputTwoValuesRows
        tokenTable width tokenCount current next 1 (argument + 1))
  | modeOneRaw
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 1)
      (failure : DoubleFailureCheckedData consumedCount tag)
      (hrows : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | modeTwoLower
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 2)
      (hguard : consumedCount = 2 ∧ tag = 0 ∧
        argument + 1 = binderArity)
      (hrows : CompactFormulaTransformOutputWitnessRows tokenTable width
        tokenCount current next witnessStart witnessFinish witnessCount)
  | modeTwoRaw
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 2)
      (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
      (hrows : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | modeFourOne
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 4)
      (hguard : consumedCount = 2 ∧ tag = 1)
      (hrows : CompactFormulaTransformOutputOneValueRows
        tokenTable width tokenCount current next argument)
  | modeFourSame
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 4)
      (failure : DoubleFailureCheckedData consumedCount tag)
      (hrows : CompactFormulaTransformOutputSameRows
        tokenTable width tokenCount current next)
  | modeFiveCaptured
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 5)
      (hguard : consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount)
      (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
        tokenCount current next 0 (binderArity + argument))
  | modeFiveResidual
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 5)
      (hguard : consumedCount = 2 ∧ tag = 1 ∧ witnessCount ≤ argument)
      (residual : Nat)
      (hresidual : residual ≤ argument)
      (hequality : argument = witnessCount + residual)
      (hrows : CompactFormulaTransformOutputTwoValuesRows
        tokenTable width tokenCount current next 1 residual)
  | modeFiveRaw
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hmode : mode = 5)
      (failure : DoubleFailureCheckedData consumedCount tag)
      (hrows : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)
  | other
      (hcount : current.parserTokensCount =
        consumedCount + next.parserTokensCount)
      (hconsumed : 1 ≤ consumedCount)
      (hzero : mode ≠ 0)
      (hone : mode ≠ 1)
      (htwo : mode ≠ 2)
      (hfour : mode ≠ 4)
      (hfive : mode ≠ 5)
      (hrows : CompactFormulaTransformOutputRawPrefixRows
        tokenTable width tokenCount current next consumedCount)

theorem compactFormulaTransformTermOutputRowsCheckedBranchData_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    Nonempty (CompactFormulaTransformTermOutputRowsCheckedBranchData tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount) := by
  rcases hgraph with ⟨hcount, hzero | hpositive⟩
  · rcases hzero with ⟨hconsumed, hsame⟩
    exact ⟨.zero hcount hconsumed hsame⟩
  · rcases hpositive with ⟨hconsumed, hbranches⟩
    rcases hbranches with hmodeZero | hmodeOne | hmodeTwo | hmodeFour |
        hmodeFive | hother
    · rcases hmodeZero with ⟨hmode, hlower | hshifted | hraw⟩
      · rcases hlower with ⟨hguard, hrows⟩
        exact ⟨.modeZeroLower hcount hconsumed hmode hguard hrows⟩
      · rcases hshifted with ⟨hfailure, hguard, hrows⟩
        exact ⟨.modeZeroShifted hcount hconsumed hmode
          (tripleFailureCheckedDataOfFailure consumedCount tag argument
            binderArity hfailure) hguard hrows⟩
      · rcases hraw with ⟨hlowerFailure, hshiftFailure, hrows⟩
        exact ⟨.modeZeroRaw hcount hconsumed hmode
          (tripleFailureCheckedDataOfFailure consumedCount tag argument
            binderArity hlowerFailure)
          (doubleFailureCheckedDataOfFailure consumedCount tag hshiftFailure)
          hrows⟩
    · rcases hmodeOne with ⟨hmode, hshifted | hraw⟩
      · rcases hshifted with ⟨hguard, hrows⟩
        exact ⟨.modeOneShifted hcount hconsumed hmode hguard hrows⟩
      · rcases hraw with ⟨hfailure, hrows⟩
        exact ⟨.modeOneRaw hcount hconsumed hmode
          (doubleFailureCheckedDataOfFailure consumedCount tag hfailure)
          hrows⟩
    · rcases hmodeTwo with ⟨hmode, hlower | hraw⟩
      · rcases hlower with ⟨hguard, hrows⟩
        exact ⟨.modeTwoLower hcount hconsumed hmode hguard hrows⟩
      · rcases hraw with ⟨hfailure, hrows⟩
        exact ⟨.modeTwoRaw hcount hconsumed hmode
          (tripleFailureCheckedDataOfFailure consumedCount tag argument
            binderArity hfailure) hrows⟩
    · rcases hmodeFour with ⟨hmode, hone | hsame⟩
      · rcases hone with ⟨hguard, hrows⟩
        exact ⟨.modeFourOne hcount hconsumed hmode hguard hrows⟩
      · rcases hsame with ⟨hfailure, hrows⟩
        exact ⟨.modeFourSame hcount hconsumed hmode
          (doubleFailureCheckedDataOfFailure consumedCount tag hfailure)
          hrows⟩
    · rcases hmodeFive with ⟨hmode, hcaptured | hresidual | hraw⟩
      · rcases hcaptured with ⟨hguard, hrows⟩
        exact ⟨.modeFiveCaptured hcount hconsumed hmode hguard hrows⟩
      · rcases hresidual with
          ⟨hguard, residual, hresidual, hequality, hrows⟩
        exact ⟨.modeFiveResidual hcount hconsumed hmode hguard residual
          hresidual hequality hrows⟩
      · rcases hraw with ⟨hfailure, hrows⟩
        exact ⟨.modeFiveRaw hcount hconsumed hmode
          (doubleFailureCheckedDataOfFailure consumedCount tag hfailure)
          hrows⟩
    · rcases hother with ⟨hzero, hone, htwo, hfour, hfive, hrows⟩
      exact ⟨.other hcount hconsumed hzero hone htwo hfour hfive hrows⟩

noncomputable def compactFormulaTransformTermOutputRowsCheckedBranchDataOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    CompactFormulaTransformTermOutputRowsCheckedBranchData tokenTable width
      tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount :=
  Classical.choice
    (compactFormulaTransformTermOutputRowsCheckedBranchData_nonempty tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount hgraph)

private theorem compactFormulaTransformTermOutputRowsCertificate_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    Nonempty (HybridCertificate
      (compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount)) := by
  rcases hgraph with ⟨hcount, hzero | hpositive⟩
  · rcases hzero with ⟨hconsumed, hsame⟩
    let countCertificate :=
      consumedCountEqualityCertificate current next consumedCount hcount
    let zeroCertificate := consumedCountZeroCertificate consumedCount hconsumed
    let sameCertificate :=
      compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.outputBoundary current.outputCount
        next.outputBoundary next.outputCount hsame
    exact ⟨.conjunction countCertificate
      (.disjunctionLeft (.conjunction zeroCertificate sameCertificate))⟩
  · rcases hpositive with ⟨hconsumed, hbranches⟩
    let countCertificate :=
      consumedCountEqualityCertificate current next consumedCount hcount
    let positiveCertificate :=
      consumedCountPositiveCertificate consumedCount hconsumed
    rcases hbranches with hmodeZero | hmodeOne | hmodeTwo | hmodeFour |
        hmodeFive | hother
    · rcases hmodeZero with ⟨hmode, hlower | hshifted | hraw⟩
      · rcases hlower with ⟨hguard, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 0
          (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
        let guardCertificate := zeroTagGuardCertificate consumedCount tag
          argument binderArity hguard
        let rowsCertificate :=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish next.outputBoundary
            next.outputCount 1 0 (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
            (termValue_arithmeticOne zeroValuation)
            (termValue_arithmeticZero zeroValuation) hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionLeft (.conjunction modeCertificate
              (.disjunctionLeft
                (.conjunction guardCertificate rowsCertificate))))))⟩
      · rcases hshifted with ⟨hfailure, hguard, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 0
          (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
        let failureCertificate := tripleFailureCertificate consumedCount tag
          argument binderArity hfailure
        let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
        let rowsCertificate :=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish next.outputBoundary
            next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm argument)
              (‘1’ : ValuationTerm))
            (termValue_arithmeticOne zeroValuation)
            (by
              simp [nativeAddTerm, termValue_arithmeticAdd,
                termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionLeft (.conjunction modeCertificate
              (.disjunctionRight (.disjunctionLeft
                (.conjunction failureCertificate
                  (.conjunction guardCertificate rowsCertificate))))))))⟩
      · rcases hraw with ⟨hlowerFailure, hshiftFailure, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 0
          (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
        let lowerFailureCertificate := tripleFailureCertificate consumedCount tag
          argument binderArity hlowerFailure
        let shiftFailureCertificate :=
          doubleFailureCertificate consumedCount tag hshiftFailure
        let rowsCertificate :=
          compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            current.start current.parserTokensFinish current.parserTokensCount
            consumedCount next.parserFinish next.finish next.outputCount hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionLeft (.conjunction modeCertificate
              (.disjunctionRight (.disjunctionRight
                (.conjunction lowerFailureCertificate
                  (.conjunction shiftFailureCertificate rowsCertificate))))))))⟩
    · rcases hmodeOne with ⟨hmode, hshifted | hraw⟩
      · rcases hshifted with ⟨hguard, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 1
          (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) hmode
        let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
        let rowsCertificate :=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish next.outputBoundary
            next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm argument)
              (‘1’ : ValuationTerm))
            (termValue_arithmeticOne zeroValuation)
            (by
              simp [nativeAddTerm, termValue_arithmeticAdd,
                termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionLeft
              (.conjunction modeCertificate
                (.disjunctionLeft
                  (.conjunction guardCertificate rowsCertificate)))))))⟩
      · rcases hraw with ⟨hfailure, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 1
          (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) hmode
        let failureCertificate :=
          doubleFailureCertificate consumedCount tag hfailure
        let rowsCertificate :=
          compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            current.start current.parserTokensFinish current.parserTokensCount
            consumedCount next.parserFinish next.finish next.outputCount hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionLeft
              (.conjunction modeCertificate
                (.disjunctionRight
                  (.conjunction failureCertificate rowsCertificate)))))))⟩
    · rcases hmodeTwo with ⟨hmode, hlower | hraw⟩
      · rcases hlower with ⟨hguard, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 2
          (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation) hmode
        let guardCertificate := zeroTagGuardCertificate consumedCount tag
          argument binderArity hguard
        let rowsCertificate :=
          compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            witnessStart witnessFinish witnessCount next.parserFinish next.finish
            next.outputCount hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionRight (.disjunctionLeft
              (.conjunction modeCertificate
                (.disjunctionLeft
                  (.conjunction guardCertificate rowsCertificate))))))))⟩
      · rcases hraw with ⟨hfailure, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 2
          (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation) hmode
        let failureCertificate := tripleFailureCertificate consumedCount tag
          argument binderArity hfailure
        let rowsCertificate :=
          compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            current.start current.parserTokensFinish current.parserTokensCount
            consumedCount next.parserFinish next.finish next.outputCount hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionRight (.disjunctionLeft
              (.conjunction modeCertificate
                (.disjunctionRight
                  (.conjunction failureCertificate rowsCertificate))))))))⟩
    · rcases hmodeFour with ⟨hmode, hone | hsame⟩
      · rcases hone with ⟨hguard, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 4
          (‘4’ : ValuationTerm) (termValue_arithmeticFour zeroValuation) hmode
        let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
        let rowsCertificate :=
          compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish next.outputBoundary
            next.outputCount argument hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionRight (.disjunctionRight
              (.disjunctionLeft (.conjunction modeCertificate
                (.disjunctionLeft
                  (.conjunction guardCertificate rowsCertificate)))))))))⟩
      · rcases hsame with ⟨hfailure, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 4
          (‘4’ : ValuationTerm) (termValue_arithmeticFour zeroValuation) hmode
        let failureCertificate :=
          doubleFailureCertificate consumedCount tag hfailure
        let rowsCertificate :=
          compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionRight (.disjunctionRight
              (.disjunctionLeft (.conjunction modeCertificate
                (.disjunctionRight
                  (.conjunction failureCertificate rowsCertificate)))))))))⟩
    · rcases hmodeFive with ⟨hmode, hcaptured | hresidual | hraw⟩
      · rcases hcaptured with ⟨hguard, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 5
          (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
        let guardCertificate := capturedGuardCertificate consumedCount tag
          argument witnessCount hguard
        let rowsCertificate :=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish next.outputBoundary
            next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm binderArity)
              (shortBinaryNumeralTerm argument))
            (termValue_arithmeticZero zeroValuation)
            (by
              simp [nativeAddTerm, termValue_arithmeticAdd,
                termValue_shortBinaryNumeralTerm]) hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionRight (.disjunctionRight
              (.disjunctionRight (.disjunctionLeft
                (.conjunction modeCertificate
                  (.disjunctionLeft
                    (.conjunction guardCertificate rowsCertificate))))))))))⟩
      · rcases hresidual with
          ⟨hguard, residual, hresidual, hequality, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 5
          (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
        let guardCertificate := residualGuardCertificate consumedCount tag
          argument witnessCount hguard
        let residualCertificate :=
          compactFormulaTransformTermResidualExistsCertificate tokenTable width
            tokenCount current next argument witnessCount residual hresidual
            hequality hrows
        exact ⟨.conjunction countCertificate
          (.disjunctionRight (.conjunction positiveCertificate
            (.disjunctionRight (.disjunctionRight (.disjunctionRight
              (.disjunctionRight (.disjunctionLeft
                (.conjunction modeCertificate
                  (.disjunctionRight (.disjunctionLeft
                    (.conjunction guardCertificate
                      residualCertificate)))))))))))⟩
      · rcases hraw with ⟨hfailure, hrows⟩
        let modeCertificate := shortNumeralLiteralEqCertificate mode 5
          (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
        let failureCertificate :=
          doubleFailureCertificate consumedCount tag hfailure
        let rowsCertificate :=
          compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
            tokenTable width tokenCount
            current.parserFinish current.finish current.outputCount
            current.start current.parserTokensFinish current.parserTokensCount
            consumedCount next.parserFinish next.finish next.outputCount hrows
        exact ⟨
          .conjunction countCertificate
            (.disjunctionRight
              (.conjunction positiveCertificate
                (.disjunctionRight
                  (.disjunctionRight
                    (.disjunctionRight
                      (.disjunctionRight
                        (.disjunctionLeft
                          (.conjunction modeCertificate
                            (.disjunctionRight
                              (.disjunctionRight
                                (.conjunction failureCertificate
                                  rowsCertificate)))))))))))⟩
    · rcases hother with
        ⟨hzero, hone, htwo, hfour, hfive, hrows⟩
      let rowsCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount
          current.parserFinish current.finish current.outputCount
          current.start current.parserTokensFinish current.parserTokensCount
          consumedCount next.parserFinish next.finish next.outputCount hrows
      let otherCertificate := otherModesWithTailCertificate mode hzero hone htwo
        hfour hfive
        (compactAdditiveNatListAppendSourcePrefixClosedFormula
          tokenTable width tokenCount
          current.parserFinish current.finish current.outputCount
          current.start current.parserTokensFinish current.parserTokensCount
          consumedCount next.parserFinish next.finish next.outputCount)
        rowsCertificate
      exact ⟨.conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionRight
            (.disjunctionRight (.disjunctionRight otherCertificate)))))))⟩

noncomputable def
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (data : CompactFormulaTransformTermOutputRowsCheckedBranchData tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount) :
    HybridCertificate
      (compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount) := by
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
  | modeZeroLower hcount hconsumed hmode hguard hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 0
        (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
      let guardCertificate := zeroTagGuardCertificate consumedCount tag
        argument binderArity hguard
      let rowsCertificate :=
        compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 0 (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
          (termValue_arithmeticOne zeroValuation)
          (termValue_arithmeticZero zeroValuation) hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionLeft (.conjunction modeCertificate
            (.disjunctionLeft
              (.conjunction guardCertificate rowsCertificate))))))
  | modeZeroShifted hcount hconsumed hmode failure hguard hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 0
        (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
      let failureCertificate := tripleFailureCertificateFromData consumedCount
        tag argument binderArity failure
      let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
      let rowsCertificate :=
        compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm argument)
            (‘1’ : ValuationTerm))
          (termValue_arithmeticOne zeroValuation)
          (by
            simp [nativeAddTerm, termValue_arithmeticAdd,
              termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionLeft (.conjunction modeCertificate
            (.disjunctionRight (.disjunctionLeft
              (.conjunction failureCertificate
                (.conjunction guardCertificate rowsCertificate))))))))
  | modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 0
        (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hmode
      let lowerFailureCertificate := tripleFailureCertificateFromData
        consumedCount tag argument binderArity lowerFailure
      let shiftFailureCertificate :=
        doubleFailureCertificateFromData consumedCount tag shiftFailure
      let rowsCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionLeft (.conjunction modeCertificate
            (.disjunctionRight (.disjunctionRight
              (.conjunction lowerFailureCertificate
                (.conjunction shiftFailureCertificate rowsCertificate))))))))
  | modeOneShifted hcount hconsumed hmode hguard hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 1
        (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) hmode
      let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
      let rowsCertificate :=
        compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm argument)
            (‘1’ : ValuationTerm))
          (termValue_arithmeticOne zeroValuation)
          (by
            simp [nativeAddTerm, termValue_arithmeticAdd,
              termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionLeft
            (.conjunction modeCertificate
              (.disjunctionLeft
                (.conjunction guardCertificate rowsCertificate)))))))
  | modeOneRaw hcount hconsumed hmode failure hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 1
        (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) hmode
      let failureCertificate :=
        doubleFailureCertificateFromData consumedCount tag failure
      let rowsCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionLeft
            (.conjunction modeCertificate
              (.disjunctionRight
                (.conjunction failureCertificate rowsCertificate)))))))
  | modeTwoLower hcount hconsumed hmode hguard hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 2
        (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation) hmode
      let guardCertificate := zeroTagGuardCertificate consumedCount tag
        argument binderArity hguard
      let rowsCertificate :=
        compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount witnessStart witnessFinish witnessCount
          next.parserFinish next.finish next.outputCount hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionLeft
            (.conjunction modeCertificate
              (.disjunctionLeft
                (.conjunction guardCertificate rowsCertificate))))))))
  | modeTwoRaw hcount hconsumed hmode failure hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 2
        (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation) hmode
      let failureCertificate := tripleFailureCertificateFromData consumedCount
        tag argument binderArity failure
      let rowsCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionLeft
            (.conjunction modeCertificate
              (.disjunctionRight
                (.conjunction failureCertificate rowsCertificate))))))))
  | modeFourOne hcount hconsumed hmode hguard hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 4
        (‘4’ : ValuationTerm) (termValue_arithmeticFour zeroValuation) hmode
      let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
      let rowsCertificate :=
        compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount argument hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionRight
            (.disjunctionLeft (.conjunction modeCertificate
              (.disjunctionLeft
                (.conjunction guardCertificate rowsCertificate)))))))))
  | modeFourSame hcount hconsumed hmode failure hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 4
        (‘4’ : ValuationTerm) (termValue_arithmeticFour zeroValuation) hmode
      let failureCertificate :=
        doubleFailureCertificateFromData consumedCount tag failure
      let rowsCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionRight
            (.disjunctionLeft (.conjunction modeCertificate
              (.disjunctionRight
                (.conjunction failureCertificate rowsCertificate)))))))))
  | modeFiveCaptured hcount hconsumed hmode hguard hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 5
        (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
      let guardCertificate := capturedGuardCertificate consumedCount tag
        argument witnessCount hguard
      let rowsCertificate :=
        compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm argument))
          (termValue_arithmeticZero zeroValuation)
          (by
            simp [nativeAddTerm, termValue_arithmeticAdd,
              termValue_shortBinaryNumeralTerm]) hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionRight
            (.disjunctionRight (.disjunctionLeft
              (.conjunction modeCertificate
                (.disjunctionLeft
                  (.conjunction guardCertificate rowsCertificate))))))))))
  | modeFiveResidual hcount hconsumed hmode hguard residual hresidual hequality
      hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 5
        (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
      let guardCertificate := residualGuardCertificate consumedCount tag
        argument witnessCount hguard
      let residualCertificate :=
        compactFormulaTransformTermResidualExistsCertificate tokenTable width
          tokenCount current next argument witnessCount residual hresidual
          hequality hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionRight
            (.disjunctionRight (.disjunctionLeft
              (.conjunction modeCertificate
                (.disjunctionRight (.disjunctionLeft
                  (.conjunction guardCertificate
                    residualCertificate)))))))))))
  | modeFiveRaw hcount hconsumed hmode failure hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let modeCertificate := shortNumeralLiteralEqCertificate mode 5
        (‘5’ : ValuationTerm) (termValue_arithmeticFive zeroValuation) hmode
      let failureCertificate :=
        doubleFailureCertificateFromData consumedCount tag failure
      let rowsCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionRight
            (.disjunctionRight (.disjunctionLeft
              (.conjunction modeCertificate
                (.disjunctionRight (.disjunctionRight
                  (.conjunction failureCertificate rowsCertificate)))))))))))
  | other hcount hconsumed hzero hone htwo hfour hfive hrows =>
      let countCertificate :=
        consumedCountEqualityCertificate current next consumedCount hcount
      let positiveCertificate :=
        consumedCountPositiveCertificate consumedCount hconsumed
      let rowsCertificate :=
        compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows
      let otherCertificate := otherModesWithTailCertificate mode hzero hone htwo
        hfour hfive
        (compactAdditiveNatListAppendSourcePrefixClosedFormula tokenTable width
          tokenCount current.parserFinish current.finish current.outputCount
          current.start current.parserTokensFinish current.parserTokensCount
          consumedCount next.parserFinish next.finish next.outputCount)
        rowsCertificate
      exact .conjunction countCertificate
        (.disjunctionRight (.conjunction positiveCertificate
          (.disjunctionRight (.disjunctionRight (.disjunctionRight
            (.disjunctionRight (.disjunctionRight otherCertificate)))))))

noncomputable def
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    HybridCertificate
      (compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount) :=
  .cast
    (compactFormulaTransformTermOutputRowsClosedFormula_alignment tokenTable width
      tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount).symm
    (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount
      (compactFormulaTransformTermOutputRowsCheckedBranchDataOfGraph tokenTable
        width tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount hgraph))

noncomputable def
    compileCompactFormulaTransformTermOutputRowsExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount).freeVariables zeroValuation)
      (compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount) :=
  (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount current next mode binderArity tag argument
    consumedCount witnessStart witnessFinish witnessCount hgraph).compile

noncomputable def
    compactFormulaTransformTermOutputRowsExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount hgraph)

theorem
    compileCompactFormulaTransformTermOutputRowsExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    (compileCompactFormulaTransformTermOutputRowsExplicitHybridContext
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount hgraph).payloadLength ≤
      compactFormulaTransformTermOutputRowsExplicitStructuralResource
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount hgraph)

#print axioms compactFormulaTransformTermResidualWitnessBody_substitution_alignment
#print axioms compactFormulaTransformTermOutputRowsClosedFormula_alignment
#print axioms compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformTermOutputRowsExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
