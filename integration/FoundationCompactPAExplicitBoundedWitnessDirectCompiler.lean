import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPABoundedWitnessGuardCompiler
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Direct installation of explicit bounded witnesses

This compiler mirrors the checked bounded-existential formula exactly, but it
uses the short-binary guard compiler instead of routing each guard through the
generic valuation-atomic compiler.  The terminal proof may still come from an
existing hybrid certificate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompiler

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactCertifiedContextualModusPonens

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem boundedWitnessGuardFormula_eq_operator
    (value bound : Nat) :
    boundedWitnessGuardFormula value bound =
      Semiformula.Operator.LT.lt.operator
        ![shortBinaryNumeralTerm value,
          ‘!!(shortBinaryNumeralTerm bound) + 1’] := by
  unfold boundedWitnessGuardFormula
  exact (Semiformula.Operator.lt_def _ _).symm

/-- Install the lowest coordinate and its short-binary bound guard. -/
noncomputable def installExplicitBoundedWitnessDirectHead
    {valuation : Nat -> Nat} {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (hbound : values 0 ≤ bound)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    CertifiedPAContextProof
      (valuationContext
        ((explicitWitnessBodyAfterTail body values).bexsLTSucc
          (shortBinaryNumeralTerm bound)).freeVariables valuation)
      ((explicitWitnessBodyAfterTail body values).bexsLTSucc
        (shortBinaryNumeralTerm bound)) := by
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let guard := boundedWitnessGuardFormula (values 0) bound
  let installedFormula := witnessBody/[witnessTerm]
  have hbodySubstitution :
      installedFormula =
        body ⇜ fun index => shortBinaryNumeralTerm (values index) :=
    explicitWitnessBodyAfterTail_subst_head body values
  let sourceFormula :=
    body ⇜ fun index => shortBinaryNumeralTerm (values index)
  let installedAtSourceContext : CertifiedPAContextProof
      (valuationContext sourceFormula.freeVariables valuation)
      installedFormula :=
    CertifiedPAContextProof.cast hbodySubstitution.symm terminal
  have hinstalledContext :
      valuationContext sourceFormula.freeVariables valuation =
        valuationContext installedFormula.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation)
      hbodySubstitution.symm
  let installed : CertifiedPAContextProof
      (valuationContext installedFormula.freeVariables valuation)
      installedFormula :=
    CertifiedPAContextProof.castContext hinstalledContext
      installedAtSourceContext
  let guardRaw := proveBoundedWitnessGuard (values 0) bound hbound
  let guardContext : CertifiedPAContextProof
      (valuationContext guard.freeVariables valuation) guard := by
    exact CertifiedPAContextProof.weakenCertified
      (valuationContext guard.freeVariables valuation) guardRaw
  let matrix := guard ⋏ installedFormula
  have hguardVariables : guard.freeVariables ⊆ matrix.freeVariables := by
    simp [matrix]
  have hinstalledVariables :
      installedFormula.freeVariables ⊆ matrix.freeVariables := by
    simp [matrix]
  let guardAtMatrix := CertifiedPAContextProof.weakenContext guardContext
    (valuationContext_mono valuation hguardVariables)
  let installedAtMatrix := CertifiedPAContextProof.weakenContext installed
    (valuationContext_mono valuation hinstalledVariables)
  let guarded : CertifiedPAContextProof
      (valuationContext matrix.freeVariables valuation) matrix :=
    CertifiedPAContextProof.conjunction guardAtMatrix installedAtMatrix
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
      witnessBody
  let instantiated := boundedMatrix/[witnessTerm]
  have hinstantiated : instantiated = matrix := by
    simp [instantiated, boundedMatrix, matrix, guard, witnessTerm,
      installedFormula,
      boundedWitnessGuardFormula_eq_operator, arithmeticAddTerm_eq_func]
  let instantiatedAtMatrixContext : CertifiedPAContextProof
      (valuationContext matrix.freeVariables valuation)
      instantiated :=
    CertifiedPAContextProof.cast hinstantiated.symm guarded
  have hinstantiatedContext :
      valuationContext matrix.freeVariables valuation =
        valuationContext instantiated.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation)
      hinstantiated.symm
  let instantiatedProof : CertifiedPAContextProof
      (valuationContext instantiated.freeVariables valuation)
      instantiated :=
    CertifiedPAContextProof.castContext hinstantiatedContext
      instantiatedAtMatrixContext
  have hvariables : instantiated.freeVariables ⊆
      (∃⁰ boundedMatrix : ValuationFormula).freeVariables :=
    (shortBinarySubstitution_freeVariables_subset
      boundedMatrix (values 0)).trans (by simp)
  let bodyProof := CertifiedPAContextProof.weakenContext instantiatedProof
    (valuationContext_mono valuation hvariables)
  let direct := CertifiedPAContextProof.existsIntro witnessTerm bodyProof
  exact direct

/-- Structural cost of one direct bounded-witness installation.  Every term is
an existing certified constructor cost; the generated proof payload itself is
not an input. -/
def explicitBoundedWitnessDirectHeadPayloadEnvelope
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) : Nat :=
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let guard := boundedWitnessGuardFormula (values 0) bound
  let installedFormula := witnessBody/[witnessTerm]
  let matrix := guard ⋏ installedFormula
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
      witnessBody
  let instantiated := boundedMatrix/[witnessTerm]
  let existential := (∃⁰ boundedMatrix : ValuationFormula)
  let guardContext := valuationContext guard.freeVariables valuation
  let matrixContext := valuationContext matrix.freeVariables valuation
  let existentialContext :=
    valuationContext existential.freeVariables valuation
  boundedWitnessGuardPayloadPolynomial
      (boundedWitnessGuardBitWidth (values 0) bound) +
    weakeningFullAssemblyCost (insert guard guardContext) +
    weakeningFullAssemblyCost (insert guard matrixContext) +
    weakeningFullAssemblyCost (insert installedFormula matrixContext) +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      matrixContext guard installedFormula +
    weakeningFullAssemblyCost (insert instantiated existentialContext) +
    CertifiedPAContextProof.existsIntroFullAssemblyCost
      existentialContext boundedMatrix witnessTerm

theorem installExplicitBoundedWitnessDirectHead_payloadLength_le
    {valuation : Nat -> Nat} {k terminalResource : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (hbound : values 0 ≤ bound)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    (installExplicitBoundedWitnessDirectHead
      bound body values hbound terminal).payloadLength ≤
      terminalResource +
        explicitBoundedWitnessDirectHeadPayloadEnvelope
          valuation bound body values := by
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let guard := boundedWitnessGuardFormula (values 0) bound
  let installedFormula := witnessBody/[witnessTerm]
  have hbodySubstitution :
      installedFormula =
        body ⇜ fun index => shortBinaryNumeralTerm (values index) :=
    explicitWitnessBodyAfterTail_subst_head body values
  let sourceFormula :=
    body ⇜ fun index => shortBinaryNumeralTerm (values index)
  let installedAtSourceContext : CertifiedPAContextProof
      (valuationContext sourceFormula.freeVariables valuation)
      installedFormula :=
    CertifiedPAContextProof.cast hbodySubstitution.symm terminal
  have hinstalledContext :
      valuationContext sourceFormula.freeVariables valuation =
        valuationContext installedFormula.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation)
      hbodySubstitution.symm
  let installed : CertifiedPAContextProof
      (valuationContext installedFormula.freeVariables valuation)
      installedFormula :=
    CertifiedPAContextProof.castContext hinstalledContext
      installedAtSourceContext
  have hinstalledPayload : installed.payloadLength = terminal.payloadLength := by
    calc
      installed.payloadLength = installedAtSourceContext.payloadLength :=
        CertifiedPAContextProof.castContext_payloadLength
          hinstalledContext installedAtSourceContext
      _ = terminal.payloadLength :=
        CertifiedPAContextProof.cast_payloadLength
          hbodySubstitution.symm terminal
  let guardRaw := proveBoundedWitnessGuard (values 0) bound hbound
  let guardContext : CertifiedPAContextProof
      (valuationContext guard.freeVariables valuation) guard :=
    CertifiedPAContextProof.weakenCertified
      (valuationContext guard.freeVariables valuation) guardRaw
  have hguardRaw : guardRaw.payloadLength ≤
      boundedWitnessGuardPayloadPolynomial
        (boundedWitnessGuardBitWidth (values 0) bound) := by
    exact proveBoundedWitnessGuard_payloadLength_le_polynomial
      (values 0) bound hbound
  have hguardContext : guardContext.payloadLength ≤
      guardRaw.payloadLength +
        weakeningFullAssemblyCost
          (insert guard
            (valuationContext guard.freeVariables valuation)) := by
    exact CertifiedPAContextProof.weakenCertified_payloadLength_le
      (valuationContext guard.freeVariables valuation) guardRaw
  let matrix := guard ⋏ installedFormula
  have hguardVariables : guard.freeVariables ⊆ matrix.freeVariables := by
    simp [matrix]
  have hinstalledVariables :
      installedFormula.freeVariables ⊆ matrix.freeVariables := by
    simp [matrix]
  let guardAtMatrix := CertifiedPAContextProof.weakenContext guardContext
    (valuationContext_mono valuation hguardVariables)
  let installedAtMatrix := CertifiedPAContextProof.weakenContext installed
    (valuationContext_mono valuation hinstalledVariables)
  have hguardAtMatrix : guardAtMatrix.payloadLength ≤
      guardContext.payloadLength +
        weakeningFullAssemblyCost
          (insert guard
            (valuationContext matrix.freeVariables valuation)) := by
    exact CertifiedPAContextProof.weakenContext_payloadLength_le
      guardContext (valuationContext_mono valuation hguardVariables)
  have hinstalledAtMatrix : installedAtMatrix.payloadLength ≤
      installed.payloadLength +
        weakeningFullAssemblyCost
          (insert installedFormula
            (valuationContext matrix.freeVariables valuation)) := by
    exact CertifiedPAContextProof.weakenContext_payloadLength_le
      installed (valuationContext_mono valuation hinstalledVariables)
  let guarded : CertifiedPAContextProof
      (valuationContext matrix.freeVariables valuation) matrix :=
    CertifiedPAContextProof.conjunction guardAtMatrix installedAtMatrix
  have hguarded : guarded.payloadLength ≤
      guardAtMatrix.payloadLength + installedAtMatrix.payloadLength +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (valuationContext matrix.freeVariables valuation)
          guard installedFormula := by
    exact CertifiedPAContextProof.conjunction_payloadLength_le
      guardAtMatrix installedAtMatrix
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
      witnessBody
  let instantiated := boundedMatrix/[witnessTerm]
  have hinstantiated : instantiated = matrix := by
    simp [instantiated, boundedMatrix, matrix, guard, witnessTerm,
      installedFormula,
      boundedWitnessGuardFormula_eq_operator, arithmeticAddTerm_eq_func]
  let instantiatedAtMatrixContext : CertifiedPAContextProof
      (valuationContext matrix.freeVariables valuation)
      instantiated :=
    CertifiedPAContextProof.cast hinstantiated.symm guarded
  have hinstantiatedContext :
      valuationContext matrix.freeVariables valuation =
        valuationContext instantiated.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation)
      hinstantiated.symm
  let instantiatedProof : CertifiedPAContextProof
      (valuationContext instantiated.freeVariables valuation)
      instantiated :=
    CertifiedPAContextProof.castContext hinstantiatedContext
      instantiatedAtMatrixContext
  have hinstantiatedPayload :
      instantiatedProof.payloadLength = guarded.payloadLength := by
    calc
      instantiatedProof.payloadLength =
          instantiatedAtMatrixContext.payloadLength :=
        CertifiedPAContextProof.castContext_payloadLength
          hinstantiatedContext instantiatedAtMatrixContext
      _ = guarded.payloadLength :=
        CertifiedPAContextProof.cast_payloadLength
          hinstantiated.symm guarded
  let existential := (∃⁰ boundedMatrix : ValuationFormula)
  have hvariables : instantiated.freeVariables ⊆ existential.freeVariables :=
    (shortBinarySubstitution_freeVariables_subset
      boundedMatrix (values 0)).trans (by
        dsimp only [existential]
        simp)
  let bodyProof := CertifiedPAContextProof.weakenContext instantiatedProof
    (valuationContext_mono valuation hvariables)
  have hbodyProof : bodyProof.payloadLength ≤
      instantiatedProof.payloadLength +
        weakeningFullAssemblyCost
          (insert instantiated
            (valuationContext existential.freeVariables valuation)) := by
    exact CertifiedPAContextProof.weakenContext_payloadLength_le
      instantiatedProof (valuationContext_mono valuation hvariables)
  let direct := CertifiedPAContextProof.existsIntro witnessTerm bodyProof
  have hdirect : direct.payloadLength ≤
      bodyProof.payloadLength +
        CertifiedPAContextProof.existsIntroFullAssemblyCost
          (valuationContext existential.freeVariables valuation)
          boundedMatrix witnessTerm := by
    exact CertifiedPAContextProof.existsIntro_payloadLength_le
      witnessTerm bodyProof
  change direct.payloadLength ≤ _
  unfold explicitBoundedWitnessDirectHeadPayloadEnvelope
  dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix, boundedMatrix, instantiated, existential] at hguardContext hguardAtMatrix hinstalledAtMatrix hguarded hbodyProof hdirect ⊢
  omega

/-- One recursion step: install the lowest witness, then transport the result
to the tail-substituted bounded formula used by the remaining coordinates. -/
noncomputable def advanceExplicitBoundedWitnessDirectTerminal
    {valuation : Nat -> Nat} {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (hbound : values 0 ≤ bound)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    CertifiedPAContextProof
      (valuationContext
        ((body.bexsLTSucc
            (closedShift k (shortBinaryNumeralTerm bound))) ⇜
          (fun index : Fin k =>
            shortBinaryNumeralTerm (values index.succ))).freeVariables
        valuation)
      ((body.bexsLTSucc
          (closedShift k (shortBinaryNumeralTerm bound))) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))) := by
  let innerFormula :=
    (explicitWitnessBodyAfterTail body values).bexsLTSucc
      (shortBinaryNumeralTerm bound)
  let inner : CertifiedPAContextProof
      (valuationContext innerFormula.freeVariables valuation)
      innerFormula :=
    installExplicitBoundedWitnessDirectHead bound body values hbound terminal
  let recursiveFormula :=
    (body.bexsLTSucc
      (closedShift k (shortBinaryNumeralTerm bound))) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))
  have htail : recursiveFormula = innerFormula :=
    shortBinarySubstitution_bexsLTSucc_tail
      (shortBinaryNumeralTerm bound) body values
  let recursiveAtInnerContext : CertifiedPAContextProof
      (valuationContext innerFormula.freeVariables valuation)
      recursiveFormula :=
    CertifiedPAContextProof.cast htail.symm inner
  have hrecursiveContext :
      valuationContext innerFormula.freeVariables valuation =
        valuationContext recursiveFormula.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation) htail.symm
  exact CertifiedPAContextProof.castContext hrecursiveContext
    recursiveAtInnerContext

theorem advanceExplicitBoundedWitnessDirectTerminal_payloadLength_le
    {valuation : Nat -> Nat} {k terminalResource : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (hbound : values 0 ≤ bound)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    (advanceExplicitBoundedWitnessDirectTerminal
      bound body values hbound terminal).payloadLength ≤
      terminalResource +
        explicitBoundedWitnessDirectHeadPayloadEnvelope
          valuation bound body values := by
  let innerFormula :=
    (explicitWitnessBodyAfterTail body values).bexsLTSucc
      (shortBinaryNumeralTerm bound)
  let inner : CertifiedPAContextProof
      (valuationContext innerFormula.freeVariables valuation)
      innerFormula :=
    installExplicitBoundedWitnessDirectHead bound body values hbound terminal
  let recursiveFormula :=
    (body.bexsLTSucc
      (closedShift k (shortBinaryNumeralTerm bound))) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))
  have htail : recursiveFormula = innerFormula :=
    shortBinarySubstitution_bexsLTSucc_tail
      (shortBinaryNumeralTerm bound) body values
  let recursiveAtInnerContext : CertifiedPAContextProof
      (valuationContext innerFormula.freeVariables valuation)
      recursiveFormula :=
    CertifiedPAContextProof.cast htail.symm inner
  have hrecursiveContext :
      valuationContext innerFormula.freeVariables valuation =
        valuationContext recursiveFormula.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation) htail.symm
  let recursiveTerminal :=
    CertifiedPAContextProof.castContext hrecursiveContext
      recursiveAtInnerContext
  have hpayload : recursiveTerminal.payloadLength = inner.payloadLength := by
    calc
      recursiveTerminal.payloadLength =
          recursiveAtInnerContext.payloadLength :=
        CertifiedPAContextProof.castContext_payloadLength
          hrecursiveContext recursiveAtInnerContext
      _ = inner.payloadLength :=
        CertifiedPAContextProof.cast_payloadLength htail.symm inner
  change recursiveTerminal.payloadLength ≤ _
  rw [hpayload]
  exact installExplicitBoundedWitnessDirectHead_payloadLength_le
    (terminalResource := terminalResource)
    bound body values hbound terminal hterminal

/-- Install a concrete witness vector around an already compiled terminal. -/
noncomputable def buildExplicitBoundedWitnessDirectContextProof :
    {valuation : Nat -> Nat} -> {k : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (∀ index, values index ≤ bound) ->
    CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)) ->
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) k body).freeVariables valuation)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) k body)
  | valuation, 0, bound, body, values, hbounds, terminal => by
      simpa [explicitBoundedWitnessFormula] using terminal
  | valuation, k + 1, bound, body, values, hbounds, terminal => by
      let tailValues : Fin k -> Nat := fun index => values index.succ
      let recursiveTerminal : CertifiedPAContextProof
          (valuationContext
            ((body.bexsLTSucc
                (closedShift k (shortBinaryNumeralTerm bound))) ⇜
              (fun index : Fin k =>
                shortBinaryNumeralTerm (tailValues index))).freeVariables
            valuation)
          ((body.bexsLTSucc
              (closedShift k (shortBinaryNumeralTerm bound))) ⇜
            (fun index : Fin k =>
              shortBinaryNumeralTerm (tailValues index))) :=
        advanceExplicitBoundedWitnessDirectTerminal
          bound body values (hbounds 0) terminal
      simpa only [explicitBoundedWitnessFormula] using
        buildExplicitBoundedWitnessDirectContextProof bound
          (body.bexsLTSucc
            (closedShift k (shortBinaryNumeralTerm bound)))
          tailValues (fun index => hbounds index.succ) recursiveTerminal

/-- Public wrapper accepting the existing proof-producing hybrid terminal. -/
noncomputable def buildExplicitBoundedWitnessDirectFromHybrid
    {valuation : Nat -> Nat} {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat k)
    (values : Fin k -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) k body).freeVariables valuation)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) k body) :=
  buildExplicitBoundedWitnessDirectContextProof bound body values hbounds
    terminal.compile

#print axioms installExplicitBoundedWitnessDirectHead
#print axioms installExplicitBoundedWitnessDirectHead_payloadLength_le
#print axioms advanceExplicitBoundedWitnessDirectTerminal
#print axioms advanceExplicitBoundedWitnessDirectTerminal_payloadLength_le
#print axioms buildExplicitBoundedWitnessDirectContextProof
#print axioms buildExplicitBoundedWitnessDirectFromHybrid

end FoundationCompactPAExplicitBoundedWitnessDirectCompiler
