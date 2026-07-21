import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

/-!
# Transparent structural bounds for explicit bounded hybrid witnesses

This file follows the existing bounded-witness certificate recursion exactly.
The terminal proof contributes only a caller-proved numeric resource; every
subsequent guard, conjunction, and existential cost is computed from public
syntax and witness data.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

/-- Structural resource for one bounded-witness installation layer. -/
def explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (terminalResource : Nat) : Nat :=
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let guard : ValuationFormula :=
    “!!(shortBinaryNumeralTerm (values 0)) <
      !!(shortBinaryNumeralTerm bound) + 1”
  let installed := witnessBody/[witnessTerm]
  let guardedResource := hybridConjunctionStructuralPayloadEnvelope valuation
    guard installed
    (compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm (values 0), rightTerm])
    terminalResource
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1), Rew.bShift rightTerm] ⋏
      witnessBody
  hybridExistsWitnessStructuralPayloadEnvelope valuation boundedMatrix
    (values 0) guardedResource

/-- Recursive proof-independent envelope for the complete witness vector. -/
def explicitBoundedWitnessHybridStructuralPayloadEnvelope
    (valuation : Nat -> Nat) :
    {k : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (terminalResource : Nat) -> Nat
  | 0, _, _, _, terminalResource => terminalResource
  | k + 1, bound, body, values, terminalResource =>
      let tailValues : Fin k -> Nat := fun index => values index.succ
      explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation bound
        (body.bexsLTSucc
          (closedShift k (shortBinaryNumeralTerm bound)))
        tailValues
        (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
          valuation bound body values terminalResource)

theorem explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_mono
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    {small large : Nat} (hresource : small <= large) :
    explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
        body values small <=
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
        body values large := by
  unfold explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
    hybridConjunctionStructuralPayloadEnvelope
    hybridExistsWitnessStructuralPayloadEnvelope
  dsimp only
  omega

theorem explicitBoundedWitnessHybridStructuralPayloadEnvelope_mono
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat k)
    (values : Fin k -> Nat)
    {small large : Nat} (hresource : small <= large) :
    explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation bound body
        values small <=
      explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation bound body
        values large := by
  induction k generalizing small large with
  | zero => exact hresource
  | succ k inductionHypothesis =>
      simp only [explicitBoundedWitnessHybridStructuralPayloadEnvelope]
      exact inductionHypothesis
        (body := body.bexsLTSucc
          (closedShift k (shortBinaryNumeralTerm bound)))
        (values := fun index => values index.succ)
        (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_mono
          valuation bound body values hresource)

theorem boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat) (value bound : Nat)
    (hvalue : value <= bound) :
    hybridFormulaStructuralPayloadBound
        (boundedWitnessGuardCertificate valuation value bound hvalue) <=
      compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm value,
          (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)] := by
  simp only [boundedWitnessGuardCertificate,
    hybridFormulaStructuralPayloadBound]
  exact le_rfl

theorem advanceExplicitBoundedWitnessHybridTerminal_structuralPayloadBound_le_transparent
    {valuation : Nat -> Nat} {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat)
    (hbound : values 0 <= bound)
    (terminal : HybridCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (terminalResource : Nat)
    (hterminal : hybridFormulaStructuralPayloadBound terminal <=
      terminalResource) :
    hybridFormulaStructuralPayloadBound
        (advanceExplicitBoundedWitnessHybridTerminal
          bound body values hbound terminal) <=
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
        valuation bound body values terminalResource := by
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let guard : ValuationFormula :=
    “!!(shortBinaryNumeralTerm (values 0)) <
      !!(shortBinaryNumeralTerm bound) + 1”
  let guardCertificate :=
    boundedWitnessGuardCertificate valuation (values 0) bound hbound
  have hbodySubstitution :
      witnessBody/[witnessTerm] =
        body ⇜ fun index => shortBinaryNumeralTerm (values index) :=
    explicitWitnessBodyAfterTail_subst_head body values
  let installed : HybridCertificate valuation
      (witnessBody/[witnessTerm]) :=
    .cast hbodySubstitution.symm terminal
  let guarded :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      guardCertificate installed
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1), Rew.bShift rightTerm] ⋏
      witnessBody
  let innerBody : HybridCertificate valuation
      (boundedMatrix/[witnessTerm]) :=
    .cast (by simp [boundedMatrix, rightTerm, witnessTerm]) guarded
  let direct : HybridCertificate valuation (∃⁰ boundedMatrix) :=
    .existsWitness boundedMatrix (values 0) innerBody
  let inner : HybridCertificate valuation
      (witnessBody.bexsLTSucc (shortBinaryNumeralTerm bound)) :=
    .cast (by rfl) direct
  let recursiveTerminal : HybridCertificate valuation
      ((body.bexsLTSucc
          (closedShift k (shortBinaryNumeralTerm bound))) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))) :=
    .cast
      (shortBinarySubstitution_bexsLTSucc_tail
        (shortBinaryNumeralTerm bound) body values).symm inner
  have hguard : hybridFormulaStructuralPayloadBound guardCertificate <=
      compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm (values 0), rightTerm] := by
    exact boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
      valuation (values 0) bound hbound
  have hinstalled : hybridFormulaStructuralPayloadBound installed <=
      terminalResource := by
    simpa only [installed, hybridFormulaStructuralPayloadBound] using
      hterminal
  have hguarded : hybridFormulaStructuralPayloadBound guarded <=
      hybridConjunctionStructuralPayloadEnvelope valuation guard
        (witnessBody/[witnessTerm])
        (compilePositiveRelationPayloadResource valuation
          Language.ORing.Rel.lt
          ![shortBinaryNumeralTerm (values 0), rightTerm])
        terminalResource := by
    exact hybridConjunctionStructuralPayloadBound_le_envelope
      guardCertificate installed _ _ hguard hinstalled
  have hbody : hybridFormulaStructuralPayloadBound innerBody <=
      hybridConjunctionStructuralPayloadEnvelope valuation guard
        (witnessBody/[witnessTerm])
        (compilePositiveRelationPayloadResource valuation
          Language.ORing.Rel.lt
          ![shortBinaryNumeralTerm (values 0), rightTerm])
        terminalResource := by
    simpa only [innerBody, hybridFormulaStructuralPayloadBound] using hguarded
  have hdirect : hybridFormulaStructuralPayloadBound direct <=
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
        valuation bound body values terminalResource := by
    have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
      boundedMatrix (values 0) innerBody _ hbody
    simpa only [explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope,
      witnessBody, witnessTerm, rightTerm, guard, boundedMatrix] using hexists
  have hinner : hybridFormulaStructuralPayloadBound inner <=
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
        valuation bound body values terminalResource := by
    change hybridFormulaStructuralPayloadBound direct <= _
    exact hdirect
  have hrecursive : hybridFormulaStructuralPayloadBound recursiveTerminal <=
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
        valuation bound body values terminalResource := by
    change hybridFormulaStructuralPayloadBound inner <= _
    exact hinner
  simpa only [advanceExplicitBoundedWitnessHybridTerminal, witnessBody,
    witnessTerm, rightTerm, guard, guardCertificate, hbodySubstitution,
    installed, guarded, boundedMatrix, innerBody, direct, inner,
    recursiveTerminal] using hrecursive

theorem buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
    {valuation : Nat -> Nat} {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat k)
    (values : Fin k -> Nat)
    (hbounds : forall index, values index <= bound)
    (terminal : HybridCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (terminalResource : Nat)
    (hterminal : hybridFormulaStructuralPayloadBound terminal <=
      terminalResource) :
    hybridFormulaStructuralPayloadBound
        (buildExplicitBoundedWitnessHybridCertificate
          bound body values hbounds terminal) <=
      explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation
        bound body values terminalResource := by
  induction k generalizing terminalResource with
  | zero =>
      simpa only [buildExplicitBoundedWitnessHybridCertificate,
        explicitBoundedWitnessHybridStructuralPayloadEnvelope,
        hybridFormulaStructuralPayloadBound] using hterminal
  | succ k inductionHypothesis =>
      let tailValues : Fin k -> Nat := fun index => values index.succ
      let recursiveTerminal : HybridCertificate valuation
          ((body.bexsLTSucc
              (closedShift k (shortBinaryNumeralTerm bound))) ⇜
            (fun index : Fin k =>
              shortBinaryNumeralTerm (tailValues index))) :=
        advanceExplicitBoundedWitnessHybridTerminal
          bound body values (hbounds 0) terminal
      have hrecursive :=
        advanceExplicitBoundedWitnessHybridTerminal_structuralPayloadBound_le_transparent
          bound body values (hbounds 0) terminal terminalResource hterminal
      have htail := inductionHypothesis
        (body := body.bexsLTSucc
          (closedShift k (shortBinaryNumeralTerm bound)))
        (values := tailValues)
        (hbounds := fun index => hbounds index.succ)
        (terminal := recursiveTerminal)
        (terminalResource :=
          explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
            valuation bound body values terminalResource)
        hrecursive
      change hybridFormulaStructuralPayloadBound
          (buildExplicitBoundedWitnessHybridCertificate bound
            (body.bexsLTSucc
              (closedShift k (shortBinaryNumeralTerm bound)))
            tailValues (fun index => hbounds index.succ)
            recursiveTerminal) <=
        explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation bound
          (body.bexsLTSucc
            (closedShift k (shortBinaryNumeralTerm bound)))
          tailValues
          (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
            valuation bound body values terminalResource)
      exact htail

#print axioms
  boundedWitnessGuardCertificate_structuralPayloadBound_le_transparent
#print axioms
  buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
#print axioms
  explicitBoundedWitnessHybridStructuralPayloadEnvelope_mono

end FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
