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

private def zeroValuation : Nat -> Nat := fun _ => 0

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

private def nativeAddTerm (left right : ValuationTerm) : ValuationTerm :=
  ‘!!left + !!right’

private def nativeEqFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left = !!right”

private def nativeNeFormula
    (left right : ValuationTerm) : ValuationFormula :=
  ∼(nativeEqFormula left right)

private def nativeLtFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left < !!right”

private def nativeLeFormula
    (left right : ValuationTerm) : ValuationFormula :=
  “!!left ≤ !!right”

private def nativeImpFormula
    (left right : ValuationFormula) : ValuationFormula :=
  left 🡒 right

private def tripleFailureFormula
    (consumedTerm tagTerm argumentTerm binderArityTerm : ValuationTerm) :
    ValuationFormula :=
  nativeImpFormula
    (nativeEqFormula consumedTerm (‘2’ : ValuationTerm))
    (nativeImpFormula
      (nativeEqFormula tagTerm (‘0’ : ValuationTerm))
      (nativeNeFormula (nativeAddTerm argumentTerm (‘1’ : ValuationTerm))
        binderArityTerm))

private def doubleFailureFormula
    (consumedTerm tagTerm : ValuationTerm) : ValuationFormula :=
  nativeImpFormula
    (nativeEqFormula consumedTerm (‘2’ : ValuationTerm))
    (nativeNeFormula tagTerm (‘1’ : ValuationTerm))

private def otherModesWithTailFormula
    (modeTerm : ValuationTerm) (tail : ValuationFormula) : ValuationFormula :=
  nativeNeFormula modeTerm (‘0’ : ValuationTerm) ⋏
    (nativeNeFormula modeTerm (‘1’ : ValuationTerm) ⋏
      (nativeNeFormula modeTerm (‘2’ : ValuationTerm) ⋏
        (nativeNeFormula modeTerm (‘4’ : ValuationTerm) ⋏
          (nativeNeFormula modeTerm (‘5’ : ValuationTerm) ⋏ tail))))

private def compactFormulaTransformTermResidualWitnessBody
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

private def compactFormulaTransformTermResidualExistsFormula
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

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_arithmeticFour (valuation : Nat -> Nat) :
    termValue valuation (‘4’ : ValuationTerm) = 4 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem termValue_arithmeticFive (valuation : Nat -> Nat) :
    termValue valuation (‘5’ : ValuationTerm) = 5 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private noncomputable def nativeEqCertificate
    (left right : ValuationTerm)
    (heq : termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate (nativeEqFormula left right) := by
  unfold nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![left, right] heq
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def nativeNeCertificate
    (left right : ValuationTerm)
    (hne : termValue zeroValuation left ≠ termValue zeroValuation right) :
    HybridCertificate (nativeNeFormula left right) := by
  unfold nativeNeFormula nativeEqFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq ![left, right] hne
  exact .cast
    (congrArg (fun formula : ValuationFormula => ∼formula)
      (Semiformula.Operator.eq_def _ _).symm) direct

private noncomputable def nativeLtCertificate
    (left right : ValuationTerm)
    (hlt : termValue zeroValuation left < termValue zeroValuation right) :
    HybridCertificate (nativeLtFormula left right) := by
  unfold nativeLtFormula
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt ![left, right] hlt
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def nativeLeCertificate
    (left right : ValuationTerm)
    (hle : termValue zeroValuation left ≤ termValue zeroValuation right) :
    HybridCertificate (nativeLeFormula left right) := by
  unfold nativeLeFormula
  if heq : termValue zeroValuation left = termValue zeroValuation right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![left, right] heq
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation left < termValue zeroValuation right :=
      Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![left, right] hlt
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

private noncomputable def shortNumeralLiteralEqCertificate
    (value expected : Nat) (literal : ValuationTerm)
    (hliteral : termValue zeroValuation literal = expected)
    (heq : value = expected) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm value) literal) :=
  nativeEqCertificate (shortBinaryNumeralTerm value) literal (by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using heq)

private noncomputable def shortNumeralLiteralNeCertificate
    (value expected : Nat) (literal : ValuationTerm)
    (hliteral : termValue zeroValuation literal = expected)
    (hne : value ≠ expected) :
    HybridCertificate
      (nativeNeFormula (shortBinaryNumeralTerm value) literal) :=
  nativeNeCertificate (shortBinaryNumeralTerm value) literal (by
    simpa [termValue_shortBinaryNumeralTerm, hliteral] using hne)

private noncomputable def consumedCountEqualityCertificate
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

private noncomputable def consumedCountZeroCertificate
    (consumedCount : Nat) (hzero : consumedCount = 0) :
    HybridCertificate
      (nativeEqFormula (shortBinaryNumeralTerm consumedCount)
        (‘0’ : ValuationTerm)) :=
  shortNumeralLiteralEqCertificate consumedCount 0 (‘0’ : ValuationTerm)
    (termValue_arithmeticZero zeroValuation) hzero

private noncomputable def consumedCountPositiveCertificate
    (consumedCount : Nat) (hpositive : 1 ≤ consumedCount) :
    HybridCertificate
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount)) :=
  nativeLeCertificate (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm consumedCount) (by
      simpa [termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]
        using hpositive)

private noncomputable def zeroTagGuardCertificate
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

private noncomputable def oneTagGuardCertificate
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

private noncomputable def capturedGuardCertificate
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

private noncomputable def residualGuardCertificate
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

private def tripleFailureDisjunctionFormula
    (consumedTerm tagTerm argumentTerm binderArityTerm : ValuationTerm) :
    ValuationFormula :=
  nativeNeFormula consumedTerm (‘2’ : ValuationTerm) ⋎
    (nativeNeFormula tagTerm (‘0’ : ValuationTerm) ⋎
      nativeNeFormula (nativeAddTerm argumentTerm (‘1’ : ValuationTerm))
        binderArityTerm)

private theorem tripleFailureFormula_eq_disjunction
    (consumedTerm tagTerm argumentTerm binderArityTerm : ValuationTerm) :
    tripleFailureFormula consumedTerm tagTerm argumentTerm binderArityTerm =
      tripleFailureDisjunctionFormula consumedTerm tagTerm argumentTerm
        binderArityTerm := by
  simp [tripleFailureFormula, tripleFailureDisjunctionFormula,
    nativeImpFormula, nativeNeFormula, DeMorgan.imply]

private theorem tripleFailureCertificate_nonempty
    (consumedCount tag argument binderArity : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 0 ∧
      argument + 1 = binderArity)) :
    Nonempty (HybridCertificate
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity))) := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let binderArityTerm := shortBinaryNumeralTerm binderArity
  by_cases hconsumed : consumedCount = 2
  · by_cases htag : tag = 0
    · have hargument : argument + 1 ≠ binderArity := by
        intro hargument
        exact hfailure ⟨hconsumed, htag, hargument⟩
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
      exact ⟨.cast
        (tripleFailureFormula_eq_disjunction consumedTerm tagTerm argumentTerm
          binderArityTerm).symm core⟩
    · let core : HybridCertificate
          (tripleFailureDisjunctionFormula consumedTerm tagTerm argumentTerm
            binderArityTerm) :=
        .disjunctionRight (.disjunctionLeft
          (shortNumeralLiteralNeCertificate tag 0 (‘0’ : ValuationTerm)
            (termValue_arithmeticZero zeroValuation) htag))
      exact ⟨.cast
        (tripleFailureFormula_eq_disjunction consumedTerm tagTerm argumentTerm
          binderArityTerm).symm core⟩
  · let core : HybridCertificate
        (tripleFailureDisjunctionFormula consumedTerm tagTerm argumentTerm
          binderArityTerm) :=
      .disjunctionLeft
        (shortNumeralLiteralNeCertificate consumedCount 2
          (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation)
          hconsumed)
    exact ⟨.cast
      (tripleFailureFormula_eq_disjunction consumedTerm tagTerm argumentTerm
        binderArityTerm).symm core⟩

private noncomputable def tripleFailureCertificate
    (consumedCount tag argument binderArity : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 0 ∧
      argument + 1 = binderArity)) :
    HybridCertificate
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity)) :=
  Classical.choice (tripleFailureCertificate_nonempty consumedCount tag
    argument binderArity hfailure)

private def doubleFailureDisjunctionFormula
    (consumedTerm tagTerm : ValuationTerm) : ValuationFormula :=
  nativeNeFormula consumedTerm (‘2’ : ValuationTerm) ⋎
    nativeNeFormula tagTerm (‘1’ : ValuationTerm)

private theorem doubleFailureFormula_eq_disjunction
    (consumedTerm tagTerm : ValuationTerm) :
    doubleFailureFormula consumedTerm tagTerm =
      doubleFailureDisjunctionFormula consumedTerm tagTerm := by
  simp [doubleFailureFormula, doubleFailureDisjunctionFormula,
    nativeImpFormula, nativeNeFormula, DeMorgan.imply]

private theorem doubleFailureCertificate_nonempty
    (consumedCount tag : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 1)) :
    Nonempty (HybridCertificate
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag))) := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  by_cases hconsumed : consumedCount = 2
  · have htag : tag ≠ 1 := by
      intro htag
      exact hfailure ⟨hconsumed, htag⟩
    let core : HybridCertificate
        (doubleFailureDisjunctionFormula consumedTerm tagTerm) :=
      .disjunctionRight
        (shortNumeralLiteralNeCertificate tag 1 (‘1’ : ValuationTerm)
          (termValue_arithmeticOne zeroValuation) htag)
    exact ⟨.cast
      (doubleFailureFormula_eq_disjunction consumedTerm tagTerm).symm core⟩
  · let core : HybridCertificate
        (doubleFailureDisjunctionFormula consumedTerm tagTerm) :=
      .disjunctionLeft
        (shortNumeralLiteralNeCertificate consumedCount 2
          (‘2’ : ValuationTerm) (termValue_arithmeticTwo zeroValuation)
          hconsumed)
    exact ⟨.cast
      (doubleFailureFormula_eq_disjunction consumedTerm tagTerm).symm core⟩

private noncomputable def doubleFailureCertificate
    (consumedCount tag : Nat)
    (hfailure : ¬(consumedCount = 2 ∧ tag = 1)) :
    HybridCertificate
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag)) :=
  Classical.choice
    (doubleFailureCertificate_nonempty consumedCount tag hfailure)

private noncomputable def otherModesWithTailCertificate
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

private noncomputable def compactFormulaTransformTermResidualExistsCertificate
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
    (Classical.choice
      (compactFormulaTransformTermOutputRowsCertificate_nonempty tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
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
