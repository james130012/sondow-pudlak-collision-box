import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds

/-!
# Public recursive bounds for direct bounded witnesses

The exact compiler adds one audited head payload at each witness coordinate.
This file bounds that real recursion by public scalar coordinates.  In
particular, neither concrete witness values nor generated proof payloads occur
in the public envelope.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

def closedShiftShortBinaryNumeralPublicCodeEnvelope :
    (arity bound : Nat) -> Nat
  | 0, bound => boundedWitnessNumeralTermCodeEnvelope bound
  | arity + 1, bound =>
      closedShiftShortBinaryNumeralPublicCodeEnvelope arity bound +
        2 * boundedWitnessNumeralTermCodeEnvelope bound

theorem termSymbolCount_closedShift
    (term : ValuationTerm) :
    forall arity,
      termSymbolCount (closedShift arity term) = termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [closedShift, termSymbolCount_bShift,
        termSymbolCount_closedShift term arity]

theorem closedShift_shortBinaryNumeralTerm_code_length_le_public
    (arity bound : Nat) :
    (binaryTermCode
      (closedShift arity (shortBinaryNumeralTerm bound))).length <=
        closedShiftShortBinaryNumeralPublicCodeEnvelope arity bound := by
  let numeralCodeBound := boundedWitnessNumeralTermCodeEnvelope bound
  have hnumeral :
      (binaryTermCode (shortBinaryNumeralTerm bound)).length <=
        numeralCodeBound :=
    shortBinaryNumeralTerm_code_length_le_bound bound bound le_rfl
  have hsymbols :
      termSymbolCount (shortBinaryNumeralTerm bound) <= numeralCodeBound :=
    (termSymbolCount_le_binaryTermCode_length
      (shortBinaryNumeralTerm bound)).trans hnumeral
  induction arity with
  | zero =>
      simpa [closedShift, closedShiftShortBinaryNumeralPublicCodeEnvelope,
        numeralCodeBound] using hnumeral
  | succ arity ih =>
      have hshift := binaryTermCode_bShift_length_le_add_symbols
        (closedShift arity (shortBinaryNumeralTerm bound))
      have hshiftSymbols :
          termSymbolCount
              (closedShift arity (shortBinaryNumeralTerm bound)) <=
            numeralCodeBound := by
        rw [termSymbolCount_closedShift]
        exact hsymbols
      change
        (binaryTermCode
          (Rew.bShift
            (closedShift arity
              (shortBinaryNumeralTerm bound)))).length <= _
      simp only [closedShiftShortBinaryNumeralPublicCodeEnvelope]
      dsimp only [numeralCodeBound] at ih hshiftSymbols
      omega

def explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope
    (arity bound : Nat) : Nat :=
  closedShiftShortBinaryNumeralPublicCodeEnvelope arity bound +
    (binaryTermCode (‘1’ : ArithmeticSemiterm Nat arity)).length +
    binaryFunctionTermCodeOverhead Language.Add.add

theorem explicitBoundedWitnessRecursiveSuccessorTerm_code_length_le_public
    (arity bound : Nat) :
    (binaryTermCode
      (‘!!(closedShift arity (shortBinaryNumeralTerm bound)) + 1’ :
        ArithmeticSemiterm Nat arity)).length <=
      explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope
        arity bound := by
  have hclosed :=
    closedShift_shortBinaryNumeralTerm_code_length_le_public arity bound
  have hadd := arithmeticAddTerm_code_length_le
    (closedShift arity (shortBinaryNumeralTerm bound))
    (‘1’ : ArithmeticSemiterm Nat arity)
  unfold explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope
  omega

def explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope
    (arity bound : Nat) : Nat :=
  3 * explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope
    arity bound

theorem explicitBoundedWitnessRecursiveShiftedSuccessor_code_length_le_public
    (arity bound : Nat) :
    (binaryTermCode
      (Rew.bShift
        (‘!!(closedShift arity (shortBinaryNumeralTerm bound)) + 1’ :
          ArithmeticSemiterm Nat arity))).length <=
      explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope
        arity bound := by
  let source : ArithmeticSemiterm Nat arity :=
    ‘!!(closedShift arity (shortBinaryNumeralTerm bound)) + 1’
  have hshift := binaryTermCode_bShift_length_le_add_symbols source
  have hsymbols := termSymbolCount_le_binaryTermCode_length source
  have hsource :=
    explicitBoundedWitnessRecursiveSuccessorTerm_code_length_le_public
      arity bound
  unfold explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope
  dsimp only [source] at hshift hsymbols hsource
  omega

def explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope
    (arity bound : Nat) : Nat :=
  (binaryTermCode (#0 : ArithmeticSemiterm Nat (arity + 1))).length +
    explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope
      arity bound +
    lessThanFormulaCodeOverhead

theorem explicitBoundedWitnessRecursiveGuard_code_length_le_public
    (arity bound : Nat) :
    (binaryFormulaCode
      (Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat (arity + 1)),
          Rew.bShift
            (‘!!(closedShift arity (shortBinaryNumeralTerm bound)) + 1’ :
              ArithmeticSemiterm Nat arity)])).length <=
      explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity bound := by
  have hright :=
    explicitBoundedWitnessRecursiveShiftedSuccessor_code_length_le_public
      arity bound
  have hguard := lessThanSemiformula_code_length_le
    (#0 : ArithmeticSemiterm Nat (arity + 1))
    (Rew.bShift
      (‘!!(closedShift arity (shortBinaryNumeralTerm bound)) + 1’ :
        ArithmeticSemiterm Nat arity))
  unfold explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope
  omega

def explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
    (arity bound bodyCodeBound : Nat) : Nat :=
  (binaryNatCode 7).length +
    explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity bound +
    bodyCodeBound + (binaryNatCode 4).length

theorem explicitBoundedWitnessRecursiveBody_code_length_le_public
    {arity : Nat}
    (bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (body.bexsLTSucc
        (closedShift arity (shortBinaryNumeralTerm bound)))).length <=
      explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
        arity bound bodyCodeBound := by
  let guard : ArithmeticSemiformula Nat (arity + 1) :=
    Semiformula.Operator.LT.lt.operator
      ![(#0 : ArithmeticSemiterm Nat (arity + 1)),
        Rew.bShift
          (‘!!(closedShift arity (shortBinaryNumeralTerm bound)) + 1’ :
            ArithmeticSemiterm Nat arity)]
  have hguard : (binaryFormulaCode guard).length <=
      explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity bound :=
    explicitBoundedWitnessRecursiveGuard_code_length_le_public arity bound
  have hand := andSemiformula_code_length_le guard body
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT
  change (binaryNatCode 7 ++ binaryFormulaCode (guard ⋏ body)).length <= _
  rw [List.length_append]
  unfold explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
  omega

/-- Public resource recursion matching the exact direct compiler.  Its inputs
are only the fixed arity, a context-code bound, the witness bound, a formula
code bound, and an independently established terminal resource. -/
def explicitBoundedWitnessDirectPublicPayloadEnvelope :
    (arity : Nat) ->
    (contextCodeBound bound bodyCodeBound terminalResource : Nat) -> Nat
  | 0, _, _, _, terminalResource => terminalResource
  | arity + 1, contextCodeBound, bound, bodyCodeBound, terminalResource =>
      explicitBoundedWitnessDirectPublicPayloadEnvelope arity
        contextCodeBound bound
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
          arity bound bodyCodeBound)
        (terminalResource +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
            contextCodeBound bound bodyCodeBound)

#print axioms termSymbolCount_closedShift
#print axioms closedShift_shortBinaryNumeralTerm_code_length_le_public
#print axioms explicitBoundedWitnessRecursiveBody_code_length_le_public
#print axioms explicitBoundedWitnessDirectPublicPayloadEnvelope

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
