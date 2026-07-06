/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth9Month10InternalPudlakWitnessSurface

/-!
# Month 11-12 PA/Hilbert checker surface

This module isolates the PA/Hilbert proof-object and checker layer needed by
the Month 9-10 internal Pudlak theorem-5 finite-search surface.

The file is intentionally an interface layer.  It does not formalize every PA
Hilbert scheme here; instead it names the proof object, formula, recognizer,
rule, and checker boundaries, then records the exactness obligations that must
be closed before the Month 9-10 no-small-code core becomes unconditional.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth11PAHilbertCheckerSurface

universe q

open SondowProjectMonth9Month10InternalPudlakWitnessSurface

/-- Formula boundary for the PA/Hilbert checker.  The code is the project-wide
formula code used by the proof-length layer. -/
structure PAHilbertFormula : Type where
  code : _root_.FormulaCode

namespace PAHilbertFormula

def ofFormulaCode (code : _root_.FormulaCode) : PAHilbertFormula where
  code := code

theorem ofFormulaCode_code (code : _root_.FormulaCode) :
    (ofFormulaCode code).code = code :=
  rfl

theorem eq_of_code_eq
    {left right : PAHilbertFormula}
    (hcode : left.code = right.code) :
    left = right := by
  cases left with
  | mk leftCode =>
    cases right with
    | mk rightCode =>
      cases hcode
      rfl

end PAHilbertFormula

/-- Proof-object boundary for the PA/Hilbert checker.  The `code` field is the
number searched by the finite enumeration layer; `steps` is the decoded
Hilbert derivation trace; `conclusion` is the claimed final formula. -/
structure PAHilbertProofObject : Type where
  code : Nat
  steps : List Nat
  conclusion : PAHilbertFormula

/-- Recognizer boundary for the PA/Hilbert schemes used by the checker. -/
structure PAHilbertAxiomRecognizer : Type where
  recognizesLogical : PAHilbertFormula → Bool
  recognizesEquality : PAHilbertFormula → Bool
  recognizesInduction : PAHilbertFormula → Bool
  recognizesPAArithmetic : PAHilbertFormula → Bool
  recognizesAny : PAHilbertFormula → Bool

/-- Inference-rule names for the PA/Hilbert checker surface. -/
inductive PAHilbertInferenceRule : Type where
  | modusPonens
  | universalGeneralization
  | substitution

/-- One decoded Hilbert proof step.  Premises are referenced by earlier line
numbers in the decoded trace. -/
structure PAHilbertProofStep : Type where
  formula : PAHilbertFormula
  premises : List Nat
  rule : Option PAHilbertInferenceRule

/-- Decoded proof trace paired with the original proof object. -/
structure PAHilbertCheckedProofTrace : Type where
  proof : PAHilbertProofObject
  decodedSteps : List PAHilbertProofStep
  traceLengthMatches : decodedSteps.length = proof.steps.length
  conclusionAppears :
    ∃ step : PAHilbertProofStep,
      step ∈ decodedSteps ∧ step.formula = proof.conclusion

/-- Executable trace-checker boundary for decoded Hilbert derivation traces. -/
structure PAHilbertTraceChecker : Type where
  checkTrace : PAHilbertCheckedProofTrace → Bool
  checkStep : PAHilbertCheckedProofTrace → PAHilbertProofStep → Bool

/-- Decoder boundary from searched numeric codes to PA/Hilbert proof objects. -/
structure PAHilbertProofObjectDecoder : Type where
  decode : Nat → Option PAHilbertProofObject
  decodedCode_eq :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        decode code = some proof → proof.code = code

/-- Checker boundary.  `accepts proof formula` is the executable check that a
proof object derives the given formula; `rejectsCode code formula` is the
finite-search-side check for a decoded proof code. -/
structure PAHilbertChecker : Type where
  recognizer : PAHilbertAxiomRecognizer
  decoder : PAHilbertProofObjectDecoder
  accepts : PAHilbertProofObject → PAHilbertFormula → Bool
  rejectsCode : Nat → PAHilbertFormula → Bool
  ruleAllowed : PAHilbertInferenceRule → Bool

/-- Exactness skeleton for the proof-object decoder and code rejection layer. -/
structure PAHilbertCheckerDecoderExactness
    (checker : PAHilbertChecker) : Type where
  decodeProofCode_complete :
    ∀ proof : PAHilbertProofObject,
      checker.decoder.decode proof.code = some proof
  rejectsUndecodable :
    ∀ code : Nat,
      ∀ formula : PAHilbertFormula,
        checker.decoder.decode code = none →
          checker.rejectsCode code formula = true
  rejectsDecodedToNotAccepted :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        ∀ formula : PAHilbertFormula,
          checker.decoder.decode code = some proof →
            proof.conclusion = formula →
              checker.rejectsCode code formula = true →
                checker.accepts proof formula = false

namespace PAHilbertCheckerDecoderExactness

/-- A necessary consequence of the current global decoder exactness interface:
proof objects with the same numeric code must be equal.  This exposes the
precise obstruction to constructing the full checker interface for unrestricted
`PAHilbertProofObject`s. -/
theorem proofObject_extensional_by_code
    {checker : PAHilbertChecker}
    (exactness : PAHilbertCheckerDecoderExactness checker)
    {left right : PAHilbertProofObject}
    (hcode : left.code = right.code) :
    left = right := by
  have hleft :
      checker.decoder.decode left.code = some left :=
    exactness.decodeProofCode_complete left
  have hright :
      checker.decoder.decode left.code = some right := by
    simpa [hcode] using exactness.decodeProofCode_complete right
  rw [hleft] at hright
  cases hright
  rfl

end PAHilbertCheckerDecoderExactness

/-- Semantic derivability target exposed by the checker.  The PA derivability
predicate itself is a boundary in this surface file. -/
structure PAHilbertDerivabilitySemantics : Type where
  Derivable : PAHilbertFormula → Prop

/-- Code-level derivability predicate induced by the PA/Hilbert formula-code
calibration. -/
def PAHilbertFormulaCodeDerivable
    (semantics : PAHilbertDerivabilitySemantics)
    (formulaCode : _root_.FormulaCode) : Prop :=
  ∃ formula : PAHilbertFormula,
    formula.code = formulaCode ∧ semantics.Derivable formula

/-- Scheme-level semantic predicates for the PA/Hilbert axiom-recognizer layer.
These predicates are the named targets for exactness of the executable
recognizers. -/
structure PAHilbertAxiomSchemeSemantics
    (semantics : PAHilbertDerivabilitySemantics) : Type where
  IsLogicalAxiom : PAHilbertFormula → Prop
  IsEqualityAxiom : PAHilbertFormula → Prop
  IsInductionSchema : PAHilbertFormula → Prop
  IsPAArithmeticAxiom : PAHilbertFormula → Prop
  logicalAxiomDerivable :
    ∀ formula : PAHilbertFormula,
      IsLogicalAxiom formula → semantics.Derivable formula
  equalityAxiomDerivable :
    ∀ formula : PAHilbertFormula,
      IsEqualityAxiom formula → semantics.Derivable formula
  inductionSchemaDerivable :
    ∀ formula : PAHilbertFormula,
      IsInductionSchema formula → semantics.Derivable formula
  paArithmeticAxiomDerivable :
    ∀ formula : PAHilbertFormula,
      IsPAArithmeticAxiom formula → semantics.Derivable formula

/-- Semantic soundness target for the Hilbert inference-rule layer. -/
structure PAHilbertInferenceRuleSemantics
    (semantics : PAHilbertDerivabilitySemantics) : Type where
  RuleApplication :
    PAHilbertInferenceRule → List PAHilbertFormula → PAHilbertFormula → Prop
  ruleApplicationSound :
    ∀ rule : PAHilbertInferenceRule,
      ∀ premises : List PAHilbertFormula,
        ∀ conclusion : PAHilbertFormula,
          RuleApplication rule premises conclusion →
            (∀ premise : PAHilbertFormula,
              premise ∈ premises → semantics.Derivable premise) →
                semantics.Derivable conclusion

/-- Exactness skeleton for the executable inference-rule recognizer. -/
structure PAHilbertInferenceRuleExactness
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (ruleSemantics : PAHilbertInferenceRuleSemantics semantics) : Type where
  allowedSound :
    ∀ rule : PAHilbertInferenceRule,
      checker.ruleAllowed rule = true →
        ∃ premises : List PAHilbertFormula,
          ∃ conclusion : PAHilbertFormula,
            ruleSemantics.RuleApplication rule premises conclusion
  allowedComplete :
    ∀ rule : PAHilbertInferenceRule,
      ∀ premises : List PAHilbertFormula,
        ∀ conclusion : PAHilbertFormula,
          ruleSemantics.RuleApplication rule premises conclusion →
            checker.ruleAllowed rule = true

/-- Exactness skeleton for the executable trace checker. -/
structure PAHilbertTraceCheckerExactness
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (traceChecker : PAHilbertTraceChecker) : Type where
  checkTraceToCheckedSteps :
    ∀ trace : PAHilbertCheckedProofTrace,
      traceChecker.checkTrace trace = true →
        ∀ step : PAHilbertProofStep,
          step ∈ trace.decodedSteps →
            traceChecker.checkStep trace step = true
  checkStepSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      ∀ step : PAHilbertProofStep,
        step ∈ trace.decodedSteps →
          traceChecker.checkStep trace step = true →
            semantics.Derivable step.formula
  checkTraceConclusionSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      traceChecker.checkTrace trace = true →
        semantics.Derivable trace.proof.conclusion

/-- Per-step soundness boundary for checked PA/Hilbert traces.  This is where
the executable trace checker will later connect recognized scheme steps and
allowed inference-rule steps to PA derivability. -/
structure PAHilbertTraceStepSoundness
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (ruleSemantics : PAHilbertInferenceRuleSemantics semantics) : Type where
  premiseFormulas :
    PAHilbertCheckedProofTrace → PAHilbertProofStep → List PAHilbertFormula
  logicalStepSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      ∀ step : PAHilbertProofStep,
        step ∈ trace.decodedSteps →
          checker.recognizer.recognizesLogical step.formula = true →
            semantics.Derivable step.formula
  equalityStepSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      ∀ step : PAHilbertProofStep,
        step ∈ trace.decodedSteps →
          checker.recognizer.recognizesEquality step.formula = true →
            semantics.Derivable step.formula
  inductionStepSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      ∀ step : PAHilbertProofStep,
        step ∈ trace.decodedSteps →
          checker.recognizer.recognizesInduction step.formula = true →
            semantics.Derivable step.formula
  paArithmeticStepSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      ∀ step : PAHilbertProofStep,
        step ∈ trace.decodedSteps →
          checker.recognizer.recognizesPAArithmetic step.formula = true →
            semantics.Derivable step.formula
  inferenceStepSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      ∀ step : PAHilbertProofStep,
        ∀ rule : PAHilbertInferenceRule,
          step ∈ trace.decodedSteps →
            step.rule = some rule →
              checker.ruleAllowed rule = true →
                ruleSemantics.RuleApplication
                  rule (premiseFormulas trace step) step.formula →
                  (∀ premise : PAHilbertFormula,
                    premise ∈ premiseFormulas trace step →
                      semantics.Derivable premise) →
                    semantics.Derivable step.formula

/-- A finite list of proof codes together with the small-code bound it covers. -/
structure PAHilbertFiniteCodeList : Type where
  codes : List Nat
  bound : Nat
  coversSmallCodes : ∀ code : Nat, code < bound → code ∈ codes

/-- No accepted proof object with code below the bound derives the formula. -/
def PAHilbertNoSmallProofCode
    (checker : PAHilbertChecker) (formula : PAHilbertFormula)
    (bound : Nat) : Prop :=
  ∀ proof : PAHilbertProofObject,
    proof.code < bound →
      proof.conclusion = formula →
        checker.accepts proof formula = false

/-- Code-level version of no-small-proof, calibrated through
`PAHilbertFormula.code`. -/
def PAHilbertNoSmallProofCodeForFormulaCode
    (checker : PAHilbertChecker) (formulaCode : _root_.FormulaCode)
    (bound : Nat) : Prop :=
  ∀ proof : PAHilbertProofObject,
    proof.code < bound →
      proof.conclusion.code = formulaCode →
        checker.accepts proof proof.conclusion = false

/-- A numeric proof code decodes to an accepted PA/Hilbert proof object whose
conclusion has the given formula code. -/
def PAHilbertAcceptedProofCodeForFormulaCode
    (checker : PAHilbertChecker) (formulaCode : _root_.FormulaCode)
    (code : Nat) : Prop :=
  ∃ proof : PAHilbertProofObject,
    checker.decoder.decode code = some proof ∧
      proof.conclusion.code = formulaCode ∧
        checker.accepts proof proof.conclusion = true

/-- No numeric proof code below the bound decodes to an accepted PA/Hilbert
proof object for the given formula code. -/
def PAHilbertNoSmallAcceptedProofCodeForFormulaCode
    (checker : PAHilbertChecker) (formulaCode : _root_.FormulaCode)
    (bound : Nat) : Prop :=
  ∀ code : Nat,
    code < bound →
      ¬ PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code

namespace PAHilbertNoSmallProofCode

theorem toFormulaCode
    {checker : PAHilbertChecker} {formula : PAHilbertFormula}
    {bound : Nat}
    (hno : PAHilbertNoSmallProofCode checker formula bound) :
    PAHilbertNoSmallProofCodeForFormulaCode checker formula.code bound := by
  intro proof hsmall hcode
  have hconclusion : proof.conclusion = formula :=
    PAHilbertFormula.eq_of_code_eq hcode
  simpa [hconclusion] using hno proof hsmall hconclusion

end PAHilbertNoSmallProofCode

namespace PAHilbertNoSmallProofCodeForFormulaCode

theorem toNoSmallAcceptedProofCode
    {checker : PAHilbertChecker} {formulaCode : _root_.FormulaCode}
    {bound : Nat}
    (hno : PAHilbertNoSmallProofCodeForFormulaCode
      checker formulaCode bound) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode
      checker formulaCode bound := by
  intro code hsmall hacceptedCode
  rcases hacceptedCode with
    ⟨proof, hdecode, hconclusionCode, haccepts⟩
  have hproofCode : proof.code = code :=
    checker.decoder.decodedCode_eq code proof hdecode
  have hproofSmall : proof.code < bound := by
    simpa [hproofCode] using hsmall
  have hnotAccepted :
      checker.accepts proof proof.conclusion = false :=
    hno proof hproofSmall hconclusionCode
  rw [hnotAccepted] at haccepts
  contradiction

end PAHilbertNoSmallProofCodeForFormulaCode

/-- Exactness skeleton for the recognizer families.  These fields are the
Month 11-12 obligations that replace a monolithic, fully expanded PA encoding
inside this file. -/
structure PAHilbertAxiomRecognizerExactness
    (recognizer : PAHilbertAxiomRecognizer)
    (semantics : PAHilbertDerivabilitySemantics) : Type where
  schemeSemantics : PAHilbertAxiomSchemeSemantics semantics
  logicalExact :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesLogical formula = true ↔
        schemeSemantics.IsLogicalAxiom formula
  equalityExact :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesEquality formula = true ↔
        schemeSemantics.IsEqualityAxiom formula
  inductionExact :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesInduction formula = true ↔
        schemeSemantics.IsInductionSchema formula
  paArithmeticExact :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesPAArithmetic formula = true ↔
        schemeSemantics.IsPAArithmeticAxiom formula
  recognizesAnyExact :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesAny formula = true ↔
        schemeSemantics.IsLogicalAxiom formula ∨
          schemeSemantics.IsEqualityAxiom formula ∨
            schemeSemantics.IsInductionSchema formula ∨
              schemeSemantics.IsPAArithmeticAxiom formula
  logicalSound :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesLogical formula = true →
        semantics.Derivable formula
  equalitySound :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesEquality formula = true →
        semantics.Derivable formula
  inductionSound :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesInduction formula = true →
        semantics.Derivable formula
  paArithmeticSound :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesPAArithmetic formula = true →
        semantics.Derivable formula
  recognizesAnySound :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesAny formula = true →
        semantics.Derivable formula
  logicalCovered :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesLogical formula = true →
        recognizer.recognizesAny formula = true
  equalityCovered :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesEquality formula = true →
        recognizer.recognizesAny formula = true
  inductionCovered :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesInduction formula = true →
        recognizer.recognizesAny formula = true
  paArithmeticCovered :
    ∀ formula : PAHilbertFormula,
      recognizer.recognizesPAArithmetic formula = true →
        recognizer.recognizesAny formula = true

namespace PAHilbertAxiomRecognizerExactness

theorem recognizes_logical_iff
    {recognizer : PAHilbertAxiomRecognizer}
    {semantics : PAHilbertDerivabilitySemantics}
    (exactness : PAHilbertAxiomRecognizerExactness recognizer semantics)
    (formula : PAHilbertFormula) :
    recognizer.recognizesLogical formula = true ↔
      exactness.schemeSemantics.IsLogicalAxiom formula :=
  exactness.logicalExact formula

theorem recognizes_equality_iff
    {recognizer : PAHilbertAxiomRecognizer}
    {semantics : PAHilbertDerivabilitySemantics}
    (exactness : PAHilbertAxiomRecognizerExactness recognizer semantics)
    (formula : PAHilbertFormula) :
    recognizer.recognizesEquality formula = true ↔
      exactness.schemeSemantics.IsEqualityAxiom formula :=
  exactness.equalityExact formula

theorem recognizes_induction_iff
    {recognizer : PAHilbertAxiomRecognizer}
    {semantics : PAHilbertDerivabilitySemantics}
    (exactness : PAHilbertAxiomRecognizerExactness recognizer semantics)
    (formula : PAHilbertFormula) :
    recognizer.recognizesInduction formula = true ↔
      exactness.schemeSemantics.IsInductionSchema formula :=
  exactness.inductionExact formula

theorem recognizes_pa_arithmetic_iff
    {recognizer : PAHilbertAxiomRecognizer}
    {semantics : PAHilbertDerivabilitySemantics}
    (exactness : PAHilbertAxiomRecognizerExactness recognizer semantics)
    (formula : PAHilbertFormula) :
    recognizer.recognizesPAArithmetic formula = true ↔
      exactness.schemeSemantics.IsPAArithmeticAxiom formula :=
  exactness.paArithmeticExact formula

theorem recognizes_any_iff
    {recognizer : PAHilbertAxiomRecognizer}
    {semantics : PAHilbertDerivabilitySemantics}
    (exactness : PAHilbertAxiomRecognizerExactness recognizer semantics)
    (formula : PAHilbertFormula) :
    recognizer.recognizesAny formula = true ↔
      exactness.schemeSemantics.IsLogicalAxiom formula ∨
        exactness.schemeSemantics.IsEqualityAxiom formula ∨
          exactness.schemeSemantics.IsInductionSchema formula ∨
            exactness.schemeSemantics.IsPAArithmeticAxiom formula :=
  exactness.recognizesAnyExact formula

theorem recognizes_any_to_derivable
    {recognizer : PAHilbertAxiomRecognizer}
    {semantics : PAHilbertDerivabilitySemantics}
    (exactness : PAHilbertAxiomRecognizerExactness recognizer semantics)
    (formula : PAHilbertFormula)
    (hrecognized : recognizer.recognizesAny formula = true) :
    semantics.Derivable formula :=
  exactness.recognizesAnySound formula hrecognized

end PAHilbertAxiomRecognizerExactness

/-! ## Concrete tagged PA/Hilbert syntax and executable scheme recognizer -/

/-- Concrete PA term syntax used by the implementation-producing checker
layer.  This is intentionally small but executable, so later batches can refine
the coding without changing the surface interfaces. -/
inductive ConcretePATerm : Type where
  | var : Nat → ConcretePATerm
  | zero : ConcretePATerm
  | succ : ConcretePATerm → ConcretePATerm
  | add : ConcretePATerm → ConcretePATerm → ConcretePATerm
  | mul : ConcretePATerm → ConcretePATerm → ConcretePATerm
deriving Repr, DecidableEq

namespace ConcretePATerm

/-- Executable raw term code for the concrete syntax layer. -/
def rawCode : ConcretePATerm → Nat
  | var n => 5 * n + 1
  | zero => 0
  | succ term => 5 * term.rawCode + 2
  | add left right => 5 * (left.rawCode + 2 * right.rawCode) + 3
  | mul left right => 5 * (left.rawCode + 2 * right.rawCode) + 4

end ConcretePATerm

/-- Tags for the PA/Hilbert scheme families recognized by the executable
checker component. -/
inductive ConcretePAAxiomKind : Type where
  | logical : ConcretePAAxiomKind
  | equality : ConcretePAAxiomKind
  | induction : ConcretePAAxiomKind
  | paArithmetic : ConcretePAAxiomKind
deriving Repr, DecidableEq

namespace ConcretePAAxiomKind

/-- Executable tag embedded in the formula-code index. -/
def tag : ConcretePAAxiomKind → Nat
  | logical => 0
  | equality => 1
  | induction => 2
  | paArithmetic => 3

end ConcretePAAxiomKind

/-- Concrete PA/Hilbert formula syntax.  General connectives are present, while
`scheme` records the four recognized scheme families checked in this batch. -/
inductive ConcretePAFormula : Type where
  | equal : ConcretePATerm → ConcretePATerm → ConcretePAFormula
  | imp : ConcretePAFormula → ConcretePAFormula → ConcretePAFormula
  | neg : ConcretePAFormula → ConcretePAFormula
  | forallE : Nat → ConcretePAFormula → ConcretePAFormula
  | scheme : ConcretePAAxiomKind → Nat → ConcretePAFormula
deriving Repr, DecidableEq

namespace ConcretePAFormula

/-- Executable raw formula code.  Scheme formulas carry the family tag in the
low residue of the index; other formulas use residue `4`. -/
def rawCode : ConcretePAFormula → Nat
  | equal left right =>
      5 * (left.rawCode + 2 * right.rawCode) + 4
  | imp antecedent consequent =>
      5 * (antecedent.rawCode + 2 * consequent.rawCode + 1) + 4
  | neg formula =>
      5 * (formula.rawCode + 2) + 4
  | forallE var body =>
      5 * (var + 2 * body.rawCode + 3) + 4
  | scheme kind payload =>
      5 * payload + kind.tag

/-- Projection from concrete formulas to the project-wide formula-code object.
This keeps Month 11-12 connected to the same `FormulaCode` object used by the
Month 9-10 proof-length layer. -/
def formulaCode (formula : ConcretePAFormula) : _root_.FormulaCode where
  family := _root_.FormulaFamily.sondowIdentity
  index := formula.rawCode

def toPAHilbertFormula (formula : ConcretePAFormula) : PAHilbertFormula :=
  PAHilbertFormula.ofFormulaCode formula.formulaCode

theorem toPAHilbertFormula_code
    (formula : ConcretePAFormula) :
    formula.toPAHilbertFormula.code = formula.formulaCode :=
  rfl

end ConcretePAFormula

/-- Extract the executable Month 11-12 tag from formula codes generated for the
concrete checker layer.  Codes outside the selected formula-code family are not
accepted by this concrete recognizer component. -/
def ConcretePAHilbertFormulaTag
    (formula : PAHilbertFormula) : Option Nat :=
  match formula.code.family with
  | _root_.FormulaFamily.sondowIdentity => some (formula.code.index % 5)
  | _ => none

def ConcretePAHilbertIsTaggedAxiom
    (tag : Nat) (formula : PAHilbertFormula) : Prop :=
  ConcretePAHilbertFormulaTag formula = some tag

def ConcretePAHilbertRecognizesTag
    (tag : Nat) (formula : PAHilbertFormula) : Bool :=
  match ConcretePAHilbertFormulaTag formula with
  | some found => found == tag
  | none => false

def ConcretePAHilbertRecognizesAny
    (formula : PAHilbertFormula) : Bool :=
  ConcretePAHilbertRecognizesTag 0 formula ||
    (ConcretePAHilbertRecognizesTag 1 formula ||
      (ConcretePAHilbertRecognizesTag 2 formula ||
        ConcretePAHilbertRecognizesTag 3 formula))

def ConcretePAHilbertDerivable
    (formula : PAHilbertFormula) : Prop :=
  ConcretePAHilbertIsTaggedAxiom 0 formula ∨
    ConcretePAHilbertIsTaggedAxiom 1 formula ∨
      ConcretePAHilbertIsTaggedAxiom 2 formula ∨
        ConcretePAHilbertIsTaggedAxiom 3 formula

theorem ConcretePAHilbertRecognizesTag_iff
    (tag : Nat) (formula : PAHilbertFormula) :
    ConcretePAHilbertRecognizesTag tag formula = true ↔
      ConcretePAHilbertIsTaggedAxiom tag formula := by
  unfold ConcretePAHilbertRecognizesTag ConcretePAHilbertIsTaggedAxiom
  cases htag : ConcretePAHilbertFormulaTag formula with
  | none =>
      simp
  | some found =>
      constructor
      · intro hbeq
        have hfound : found = tag := by
          simpa using hbeq
        simp [hfound]
      · intro hsome
        have hfound : found = tag := by
          simpa [htag] using hsome
        simp [hfound]

theorem ConcretePAHilbertRecognizesAny_iff
    (formula : PAHilbertFormula) :
    ConcretePAHilbertRecognizesAny formula = true ↔
      ConcretePAHilbertDerivable formula := by
  simp [ConcretePAHilbertRecognizesAny, ConcretePAHilbertDerivable,
    ConcretePAHilbertRecognizesTag_iff]

/-- Executable scheme recognizer produced by the concrete tagged syntax layer. -/
def concretePAHilbertAxiomRecognizer : PAHilbertAxiomRecognizer where
  recognizesLogical := ConcretePAHilbertRecognizesTag 0
  recognizesEquality := ConcretePAHilbertRecognizesTag 1
  recognizesInduction := ConcretePAHilbertRecognizesTag 2
  recognizesPAArithmetic := ConcretePAHilbertRecognizesTag 3
  recognizesAny := ConcretePAHilbertRecognizesAny

def concretePAHilbertDerivabilitySemantics :
    PAHilbertDerivabilitySemantics where
  Derivable := ConcretePAHilbertDerivable

def concretePAHilbertAxiomSchemeSemantics :
    PAHilbertAxiomSchemeSemantics
      concretePAHilbertDerivabilitySemantics where
  IsLogicalAxiom := ConcretePAHilbertIsTaggedAxiom 0
  IsEqualityAxiom := ConcretePAHilbertIsTaggedAxiom 1
  IsInductionSchema := ConcretePAHilbertIsTaggedAxiom 2
  IsPAArithmeticAxiom := ConcretePAHilbertIsTaggedAxiom 3
  logicalAxiomDerivable := by
    intro formula htag
    exact Or.inl htag
  equalityAxiomDerivable := by
    intro formula htag
    exact Or.inr (Or.inl htag)
  inductionSchemaDerivable := by
    intro formula htag
    exact Or.inr (Or.inr (Or.inl htag))
  paArithmeticAxiomDerivable := by
    intro formula htag
    exact Or.inr (Or.inr (Or.inr htag))

/-- Concrete executable recognizer exactness for the tagged PA/Hilbert syntax
fragment.  This is an implementation-producing component, not merely an
assumed exactness field. -/
def concretePAHilbertAxiomRecognizerExactness :
    PAHilbertAxiomRecognizerExactness
      concretePAHilbertAxiomRecognizer
      concretePAHilbertDerivabilitySemantics where
  schemeSemantics := concretePAHilbertAxiomSchemeSemantics
  logicalExact := by
    intro formula
    simpa [concretePAHilbertAxiomRecognizer,
      concretePAHilbertAxiomSchemeSemantics] using
      (ConcretePAHilbertRecognizesTag_iff 0 formula)
  equalityExact := by
    intro formula
    simpa [concretePAHilbertAxiomRecognizer,
      concretePAHilbertAxiomSchemeSemantics] using
      (ConcretePAHilbertRecognizesTag_iff 1 formula)
  inductionExact := by
    intro formula
    simpa [concretePAHilbertAxiomRecognizer,
      concretePAHilbertAxiomSchemeSemantics] using
      (ConcretePAHilbertRecognizesTag_iff 2 formula)
  paArithmeticExact := by
    intro formula
    simpa [concretePAHilbertAxiomRecognizer,
      concretePAHilbertAxiomSchemeSemantics] using
      (ConcretePAHilbertRecognizesTag_iff 3 formula)
  recognizesAnyExact := by
    intro formula
    simpa [concretePAHilbertAxiomRecognizer,
      concretePAHilbertAxiomSchemeSemantics,
      ConcretePAHilbertDerivable] using
      (ConcretePAHilbertRecognizesAny_iff formula)
  logicalSound := by
    intro formula hrecognized
    exact Or.inl
      ((ConcretePAHilbertRecognizesTag_iff 0 formula).mp hrecognized)
  equalitySound := by
    intro formula hrecognized
    exact Or.inr (Or.inl
      ((ConcretePAHilbertRecognizesTag_iff 1 formula).mp hrecognized))
  inductionSound := by
    intro formula hrecognized
    exact Or.inr (Or.inr (Or.inl
      ((ConcretePAHilbertRecognizesTag_iff 2 formula).mp hrecognized)))
  paArithmeticSound := by
    intro formula hrecognized
    exact Or.inr (Or.inr (Or.inr
      ((ConcretePAHilbertRecognizesTag_iff 3 formula).mp hrecognized)))
  recognizesAnySound := by
    intro formula hrecognized
    exact (ConcretePAHilbertRecognizesAny_iff formula).mp hrecognized
  logicalCovered := by
    intro formula hrecognized
    exact (ConcretePAHilbertRecognizesAny_iff formula).mpr
      (Or.inl
        ((ConcretePAHilbertRecognizesTag_iff 0 formula).mp hrecognized))
  equalityCovered := by
    intro formula hrecognized
    exact (ConcretePAHilbertRecognizesAny_iff formula).mpr
      (Or.inr (Or.inl
        ((ConcretePAHilbertRecognizesTag_iff 1 formula).mp hrecognized)))
  inductionCovered := by
    intro formula hrecognized
    exact (ConcretePAHilbertRecognizesAny_iff formula).mpr
      (Or.inr (Or.inr (Or.inl
        ((ConcretePAHilbertRecognizesTag_iff 2 formula).mp hrecognized))))
  paArithmeticCovered := by
    intro formula hrecognized
    exact (ConcretePAHilbertRecognizesAny_iff formula).mpr
      (Or.inr (Or.inr (Or.inr
        ((ConcretePAHilbertRecognizesTag_iff 3 formula).mp hrecognized))))

theorem concretePAHilbertAxiomRecognizerExactness_nonempty :
    Nonempty
      (PAHilbertAxiomRecognizerExactness
        concretePAHilbertAxiomRecognizer
        concretePAHilbertDerivabilitySemantics) :=
  ⟨concretePAHilbertAxiomRecognizerExactness⟩

/-! ## Concrete executable inference-rule seed -/

def concretePAHilbertCanonicalPremiseFormula :
    PAHilbertFormula :=
  (ConcretePAFormula.scheme ConcretePAAxiomKind.logical 0)
    |>.toPAHilbertFormula

def concretePAHilbertCanonicalConclusionFormula :
    PAHilbertFormula :=
  (ConcretePAFormula.scheme ConcretePAAxiomKind.equality 0)
    |>.toPAHilbertFormula

def concretePAHilbertCanonicalImplicationFormula :
    PAHilbertFormula :=
  (ConcretePAFormula.imp
      (ConcretePAFormula.scheme ConcretePAAxiomKind.logical 0)
      (ConcretePAFormula.scheme ConcretePAAxiomKind.equality 0))
    |>.toPAHilbertFormula

theorem concretePAHilbertCanonicalConclusion_derivable :
    concretePAHilbertDerivabilitySemantics.Derivable
      concretePAHilbertCanonicalConclusionFormula := by
  unfold concretePAHilbertCanonicalConclusionFormula
  exact Or.inr (Or.inl rfl)

/-- Executable rule recognizer for the current concrete checker seed.  This
batch implements the first nontrivial rule component by allowing one canonical
modus-ponens shape and rejecting the other rule names until their concrete
syntax is implemented. -/
def concretePAHilbertRuleAllowed : PAHilbertInferenceRule → Bool
  | PAHilbertInferenceRule.modusPonens => true
  | PAHilbertInferenceRule.universalGeneralization => false
  | PAHilbertInferenceRule.substitution => false

def concretePAHilbertRuleApplication :
    PAHilbertInferenceRule →
      List PAHilbertFormula → PAHilbertFormula → Prop
  | PAHilbertInferenceRule.modusPonens, premises, conclusion =>
      premises =
          [concretePAHilbertCanonicalPremiseFormula,
            concretePAHilbertCanonicalImplicationFormula] ∧
        conclusion = concretePAHilbertCanonicalConclusionFormula
  | PAHilbertInferenceRule.universalGeneralization, _, _ => False
  | PAHilbertInferenceRule.substitution, _, _ => False

def concretePAHilbertInferenceRuleSemantics :
    PAHilbertInferenceRuleSemantics
      concretePAHilbertDerivabilitySemantics where
  RuleApplication := concretePAHilbertRuleApplication
  ruleApplicationSound := by
    intro rule premises conclusion happlication _hpremises
    cases rule with
    | modusPonens =>
        rcases happlication with ⟨_hpremisesShape, hconclusion⟩
        rw [hconclusion]
        exact concretePAHilbertCanonicalConclusion_derivable
    | universalGeneralization =>
        cases happlication
    | substitution =>
        cases happlication

/-- Project a numeric concrete proof code to the shared formula-code layer. -/
def concretePAHilbertFormulaCodeOfIndex
    (index : Nat) : _root_.FormulaCode where
  family := _root_.FormulaFamily.sondowIdentity
  index := index

def concretePAHilbertCanonicalFormula
    (code : Nat) : PAHilbertFormula :=
  PAHilbertFormula.ofFormulaCode
    (concretePAHilbertFormulaCodeOfIndex code)

def concretePAHilbertCanonicalProofStep
    (code : Nat) : PAHilbertProofStep where
  formula := concretePAHilbertCanonicalFormula code
  premises := []
  rule := none

def concretePAHilbertCanonicalProofObject
    (code : Nat) : PAHilbertProofObject where
  code := code
  steps := [code]
  conclusion := concretePAHilbertCanonicalFormula code

def concretePAHilbertCanonicalTrace
    (code : Nat) : PAHilbertCheckedProofTrace where
  proof := concretePAHilbertCanonicalProofObject code
  decodedSteps := [concretePAHilbertCanonicalProofStep code]
  traceLengthMatches := rfl
  conclusionAppears := by
    exact
      ⟨concretePAHilbertCanonicalProofStep code,
        by simp,
        rfl⟩

/-- Executable proof-object decoder for the concrete seed checker.  It decodes
every numeric code to the canonical one-line proof object carrying that code. -/
def concretePAHilbertProofObjectDecoder :
    PAHilbertProofObjectDecoder where
  decode := fun code => some (concretePAHilbertCanonicalProofObject code)
  decodedCode_eq := by
    intro code proof hdecode
    cases hdecode
    rfl

theorem concretePAHilbertProofObjectDecoder_complete
    (code : Nat) :
    concretePAHilbertProofObjectDecoder.decode code =
      some (concretePAHilbertCanonicalProofObject code) :=
  rfl

theorem concretePAHilbertProofObjectDecoder_decodedCode_eq
    (code : Nat) (proof : PAHilbertProofObject)
    (hdecode :
      concretePAHilbertProofObjectDecoder.decode code = some proof) :
    proof.code = code :=
  concretePAHilbertProofObjectDecoder.decodedCode_eq code proof hdecode

/-- Canonical proof objects are the ones produced by the executable concrete
decoder from their own numeric code. -/
def ConcretePAHilbertCanonicalProofObject
    (proof : PAHilbertProofObject) : Prop :=
  proof = concretePAHilbertCanonicalProofObject proof.code

theorem concretePAHilbertProofObjectDecoder_complete_for_canonical
    (proof : PAHilbertProofObject)
    (hcanonical : ConcretePAHilbertCanonicalProofObject proof) :
    concretePAHilbertProofObjectDecoder.decode proof.code = some proof := by
  rw [hcanonical]
  rfl

structure ConcretePAHilbertCanonicalDecoderExactness : Type where
  completeCanonical :
    ∀ proof : PAHilbertProofObject,
      ConcretePAHilbertCanonicalProofObject proof →
        concretePAHilbertProofObjectDecoder.decode proof.code = some proof
  decodedCode_eq :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        concretePAHilbertProofObjectDecoder.decode code = some proof →
          proof.code = code

def concretePAHilbertCanonicalDecoderExactness :
    ConcretePAHilbertCanonicalDecoderExactness where
  completeCanonical :=
    concretePAHilbertProofObjectDecoder_complete_for_canonical
  decodedCode_eq :=
    concretePAHilbertProofObjectDecoder_decodedCode_eq

theorem concretePAHilbertCanonicalDecoderExactness_nonempty :
    Nonempty ConcretePAHilbertCanonicalDecoderExactness :=
  ⟨concretePAHilbertCanonicalDecoderExactness⟩

def concretePAHilbertDecoderObstructionLeft :
    PAHilbertProofObject where
  code := 0
  steps := []
  conclusion := concretePAHilbertCanonicalFormula 0

def concretePAHilbertDecoderObstructionRight :
    PAHilbertProofObject where
  code := 0
  steps := [0]
  conclusion := concretePAHilbertCanonicalFormula 0

theorem concretePAHilbertDecoderObstruction_same_code :
    concretePAHilbertDecoderObstructionLeft.code =
      concretePAHilbertDecoderObstructionRight.code :=
  rfl

theorem concretePAHilbertDecoderObstruction_ne :
    concretePAHilbertDecoderObstructionLeft ≠
      concretePAHilbertDecoderObstructionRight := by
  intro h
  have hsteps :=
    congrArg PAHilbertProofObject.steps h
  simp [concretePAHilbertDecoderObstructionLeft,
    concretePAHilbertDecoderObstructionRight] at hsteps

/-- Precise obstruction: the unrestricted proof-object type cannot satisfy the
current full decoder exactness interface, because two different proof objects
can carry the same numeric code.  A full constructive core therefore needs a
code-indexed/canonical proof-object invariant or a weakened decoder interface. -/
theorem no_full_decoder_exactness_for_unrestricted_proof_objects
    (checker : PAHilbertChecker) :
    PAHilbertCheckerDecoderExactness checker → False := by
  intro exactness
  exact concretePAHilbertDecoderObstruction_ne
    (exactness.proofObject_extensional_by_code
      concretePAHilbertDecoderObstruction_same_code)

/-- Minimal executable checker seed used to attach concrete recognizer and
rule-checker components before the decoder and trace layers are implemented. -/
def concretePAHilbertSeedChecker : PAHilbertChecker where
  recognizer := concretePAHilbertAxiomRecognizer
  decoder := concretePAHilbertProofObjectDecoder
  accepts := fun _ formula =>
    concretePAHilbertAxiomRecognizer.recognizesAny formula
  rejectsCode := fun _ _ => true
  ruleAllowed := concretePAHilbertRuleAllowed

theorem concretePAHilbertSeedChecker_accepts_to_derivable
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts :
      concretePAHilbertSeedChecker.accepts proof formula = true) :
    concretePAHilbertDerivabilitySemantics.Derivable formula :=
  (ConcretePAHilbertRecognizesAny_iff formula).mp
    (by
      simpa [concretePAHilbertSeedChecker,
        concretePAHilbertAxiomRecognizer] using haccepts)

theorem concretePAHilbertSeedChecker_rejectsCode_eq_true
    (code : Nat) (formula : PAHilbertFormula) :
    concretePAHilbertSeedChecker.rejectsCode code formula = true :=
  rfl

/-- Executable check for one decoded concrete trace step. -/
def concretePAHilbertTraceCheckStep
    (step : PAHilbertProofStep) : Bool :=
  concretePAHilbertAxiomRecognizer.recognizesAny step.formula

/-- Executable fold over decoded trace steps. -/
def concretePAHilbertTraceCheckSteps :
    List PAHilbertProofStep → Bool
  | [] => true
  | step :: steps =>
      concretePAHilbertTraceCheckStep step &&
        concretePAHilbertTraceCheckSteps steps

theorem concretePAHilbertTraceCheckSteps_mem
    {steps : List PAHilbertProofStep}
    (hsteps : concretePAHilbertTraceCheckSteps steps = true)
    {step : PAHilbertProofStep}
    (hmem : step ∈ steps) :
    concretePAHilbertTraceCheckStep step = true := by
  induction steps with
  | nil =>
      cases hmem
  | cons head tail ih =>
      simp [concretePAHilbertTraceCheckSteps] at hsteps
      rcases hsteps with ⟨hhead, htail⟩
      simp at hmem
      rcases hmem with hEq | hmemTail
      · simpa [hEq] using hhead
      ·
          exact ih htail hmemTail

/-- Executable trace checker for the concrete seed.  A trace is accepted only
when every decoded step and the claimed conclusion are accepted by the concrete
scheme recognizer. -/
def concretePAHilbertTraceChecker : PAHilbertTraceChecker where
  checkTrace := fun trace =>
    concretePAHilbertTraceCheckSteps trace.decodedSteps &&
      concretePAHilbertAxiomRecognizer.recognizesAny
        trace.proof.conclusion
  checkStep := fun _trace step =>
    concretePAHilbertTraceCheckStep step

def concretePAHilbertTraceCheckerExactness :
    PAHilbertTraceCheckerExactness
      concretePAHilbertSeedChecker
      concretePAHilbertDerivabilitySemantics
      concretePAHilbertTraceChecker where
  checkTraceToCheckedSteps := by
    intro trace htrace step hstep
    have htraceBool :
        (concretePAHilbertTraceCheckSteps trace.decodedSteps &&
          concretePAHilbertAxiomRecognizer.recognizesAny
            trace.proof.conclusion) = true := by
      simpa [concretePAHilbertTraceChecker] using htrace
    have htraceParts :
        concretePAHilbertTraceCheckSteps trace.decodedSteps = true ∧
          concretePAHilbertAxiomRecognizer.recognizesAny
            trace.proof.conclusion = true := by
      simpa using htraceBool
    have hsteps :
        concretePAHilbertTraceCheckSteps trace.decodedSteps = true :=
      htraceParts.1
    simpa [concretePAHilbertTraceChecker] using
      concretePAHilbertTraceCheckSteps_mem hsteps hstep
  checkStepSound := by
    intro trace step _hstep hchecked
    exact
      (ConcretePAHilbertRecognizesAny_iff step.formula).mp
        (by
          simpa [concretePAHilbertTraceChecker,
            concretePAHilbertTraceCheckStep,
            concretePAHilbertAxiomRecognizer] using hchecked)
  checkTraceConclusionSound := by
    intro trace htrace
    have htraceBool :
        (concretePAHilbertTraceCheckSteps trace.decodedSteps &&
          concretePAHilbertAxiomRecognizer.recognizesAny
            trace.proof.conclusion) = true := by
      simpa [concretePAHilbertTraceChecker] using htrace
    have htraceParts :
        concretePAHilbertTraceCheckSteps trace.decodedSteps = true ∧
          concretePAHilbertAxiomRecognizer.recognizesAny
            trace.proof.conclusion = true := by
      simpa using htraceBool
    have hconclusion :
        ConcretePAHilbertRecognizesAny
          trace.proof.conclusion = true := by
      simpa [concretePAHilbertAxiomRecognizer] using htraceParts.2
    exact
      (ConcretePAHilbertRecognizesAny_iff trace.proof.conclusion).mp
        hconclusion

theorem concretePAHilbertTraceCheckerExactness_nonempty :
    Nonempty
      (PAHilbertTraceCheckerExactness
        concretePAHilbertSeedChecker
        concretePAHilbertDerivabilitySemantics
        concretePAHilbertTraceChecker) :=
  ⟨concretePAHilbertTraceCheckerExactness⟩

/-- Executable premise extractor for concrete trace-step soundness.  Numeric
premise references are resolved to the current canonical premise formula in
this seed layer; later batches can replace this with an indexed trace lookup. -/
def concretePAHilbertPremiseFormulas
    (_trace : PAHilbertCheckedProofTrace)
    (step : PAHilbertProofStep) :
    List PAHilbertFormula :=
  step.premises.map (fun _ => concretePAHilbertCanonicalPremiseFormula)

/-- Concrete per-step soundness object for the current executable checker seed.
It ties recognized scheme steps and the implemented rule-semantics seed to PA
derivability. -/
def concretePAHilbertTraceStepSoundness :
    PAHilbertTraceStepSoundness
      concretePAHilbertSeedChecker
      concretePAHilbertDerivabilitySemantics
      concretePAHilbertInferenceRuleSemantics where
  premiseFormulas := concretePAHilbertPremiseFormulas
  logicalStepSound := by
    intro _trace step _hmem hrecognized
    exact
      concretePAHilbertAxiomRecognizerExactness.logicalSound
        step.formula
        (by
          simpa [concretePAHilbertSeedChecker] using hrecognized)
  equalityStepSound := by
    intro _trace step _hmem hrecognized
    exact
      concretePAHilbertAxiomRecognizerExactness.equalitySound
        step.formula
        (by
          simpa [concretePAHilbertSeedChecker] using hrecognized)
  inductionStepSound := by
    intro _trace step _hmem hrecognized
    exact
      concretePAHilbertAxiomRecognizerExactness.inductionSound
        step.formula
        (by
          simpa [concretePAHilbertSeedChecker] using hrecognized)
  paArithmeticStepSound := by
    intro _trace step _hmem hrecognized
    exact
      concretePAHilbertAxiomRecognizerExactness.paArithmeticSound
        step.formula
        (by
          simpa [concretePAHilbertSeedChecker] using hrecognized)
  inferenceStepSound := by
    intro trace step rule _hmem _hrule _hallowed happlication hpremises
    exact
      concretePAHilbertInferenceRuleSemantics.ruleApplicationSound
        rule
        (concretePAHilbertPremiseFormulas trace step)
        step.formula
        happlication
        hpremises

theorem concretePAHilbertTraceStepSoundness_nonempty :
    Nonempty
      (PAHilbertTraceStepSoundness
        concretePAHilbertSeedChecker
        concretePAHilbertDerivabilitySemantics
        concretePAHilbertInferenceRuleSemantics) :=
  ⟨concretePAHilbertTraceStepSoundness⟩

/-- Concrete exactness for the executable rule recognizer seed.  This is not a
full PA/Hilbert rule calculus yet; it is the first implemented rule component
and records exactly the canonical modus-ponens shape accepted in this batch. -/
def concretePAHilbertInferenceRuleExactness :
    PAHilbertInferenceRuleExactness
      concretePAHilbertSeedChecker
      concretePAHilbertDerivabilitySemantics
      concretePAHilbertInferenceRuleSemantics where
  allowedSound := by
    intro rule hallowed
    cases rule with
    | modusPonens =>
        exact
          ⟨[concretePAHilbertCanonicalPremiseFormula,
              concretePAHilbertCanonicalImplicationFormula],
            concretePAHilbertCanonicalConclusionFormula,
            ⟨rfl, rfl⟩⟩
    | universalGeneralization =>
        simp [concretePAHilbertSeedChecker,
          concretePAHilbertRuleAllowed] at hallowed
    | substitution =>
        simp [concretePAHilbertSeedChecker,
          concretePAHilbertRuleAllowed] at hallowed
  allowedComplete := by
    intro rule premises conclusion happlication
    cases rule with
    | modusPonens =>
        simp [concretePAHilbertSeedChecker,
          concretePAHilbertRuleAllowed]
    | universalGeneralization =>
        cases happlication
    | substitution =>
        cases happlication

theorem concretePAHilbertInferenceRuleExactness_nonempty :
    Nonempty
      (PAHilbertInferenceRuleExactness
        concretePAHilbertSeedChecker
        concretePAHilbertDerivabilitySemantics
        concretePAHilbertInferenceRuleSemantics) :=
  ⟨concretePAHilbertInferenceRuleExactness⟩

/-- Paper-proof-facing checker interface: accepted proof objects yield PA
derivability, and finite rejection of the covered list excludes all small proof
codes below the list bound. -/
structure PAHilbertCheckerInterface
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics) : Type where
  decoderExactness : PAHilbertCheckerDecoderExactness checker
  inferenceRuleSemantics : PAHilbertInferenceRuleSemantics semantics
  inferenceRuleExactness :
    PAHilbertInferenceRuleExactness
      checker semantics inferenceRuleSemantics
  traceChecker : PAHilbertTraceChecker
  traceCheckerExactness :
    PAHilbertTraceCheckerExactness checker semantics traceChecker
  traceStepSoundness :
    PAHilbertTraceStepSoundness checker semantics inferenceRuleSemantics
  traceOf : PAHilbertProofObject → Option PAHilbertCheckedProofTrace
  acceptsConclusion :
    ∀ proof : PAHilbertProofObject,
      ∀ formula : PAHilbertFormula,
        checker.accepts proof formula = true →
          proof.conclusion = formula
  acceptsToCheckedTrace :
    ∀ proof : PAHilbertProofObject,
      ∀ formula : PAHilbertFormula,
        checker.accepts proof formula = true →
          ∃ trace : PAHilbertCheckedProofTrace,
            traceOf proof = some trace ∧
              trace.proof = proof ∧
                traceChecker.checkTrace trace = true
  checkedTraceSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      traceChecker.checkTrace trace = true →
        semantics.Derivable trace.proof.conclusion
  checkedTraceEveryStepSound :
    ∀ trace : PAHilbertCheckedProofTrace,
      traceChecker.checkTrace trace = true →
        ∀ step : PAHilbertProofStep,
          step ∈ trace.decodedSteps →
            semantics.Derivable step.formula
  acceptsToDerivable :
    ∀ proof : PAHilbertProofObject,
      ∀ formula : PAHilbertFormula,
        checker.accepts proof formula = true →
          semantics.Derivable formula
  decodedRejectsToNotAccepted :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        ∀ formula : PAHilbertFormula,
          checker.decoder.decode code = some proof →
            proof.conclusion = formula →
              checker.rejectsCode code formula = true →
                checker.accepts proof formula = false
  rejectsFiniteListToNoSmallProofCode :
    ∀ formula : PAHilbertFormula,
      ∀ finiteList : PAHilbertFiniteCodeList,
        (∀ code : Nat, code ∈ finiteList.codes →
          checker.rejectsCode code formula = true) →
            PAHilbertNoSmallProofCode checker formula finiteList.bound

namespace PAHilbertCheckerInterface

theorem decode_proof_code_complete
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (proof : PAHilbertProofObject) :
    checker.decoder.decode proof.code = some proof :=
  interface.decoderExactness.decodeProofCode_complete proof

theorem rejects_undecodable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (code : Nat) (formula : PAHilbertFormula)
    (hdecode : checker.decoder.decode code = none) :
    checker.rejectsCode code formula = true :=
  interface.decoderExactness.rejectsUndecodable code formula hdecode

theorem accepts_to_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    semantics.Derivable formula :=
  interface.acceptsToDerivable proof formula haccepts

theorem accepts_to_conclusion_eq
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    proof.conclusion = formula :=
  interface.acceptsConclusion proof formula haccepts

theorem accepts_to_formulaCode_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    PAHilbertFormulaCodeDerivable semantics formula.code :=
  ⟨formula, rfl, interface.acceptsToDerivable proof formula haccepts⟩

theorem rejects_finite_list_to_no_small_proof_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true) :
    PAHilbertNoSmallProofCode checker formula finiteList.bound :=
  interface.rejectsFiniteListToNoSmallProofCode formula finiteList hrejects

theorem decoded_rejects_to_not_accepted
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (code : Nat) (proof : PAHilbertProofObject)
    (formula : PAHilbertFormula)
    (hdecode : checker.decoder.decode code = some proof)
    (hconclusion : proof.conclusion = formula)
    (hrejects : checker.rejectsCode code formula = true) :
    checker.accepts proof formula = false :=
  interface.decodedRejectsToNotAccepted
    code proof formula hdecode hconclusion hrejects

theorem accepted_decoded_code_to_formulaCode_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code) :
    PAHilbertFormulaCodeDerivable semantics formulaCode := by
  rcases haccepted with
    ⟨proof, _hdecode, hconclusionCode, haccepts⟩
  exact
    ⟨proof.conclusion, hconclusionCode,
      interface.acceptsToDerivable proof proof.conclusion haccepts⟩

theorem accepts_to_checked_trace
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    ∃ trace : PAHilbertCheckedProofTrace,
      interface.traceOf proof = some trace ∧
        trace.proof = proof ∧
          interface.traceChecker.checkTrace trace = true :=
  interface.acceptsToCheckedTrace proof formula haccepts

theorem checked_trace_to_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (trace : PAHilbertCheckedProofTrace)
    (htrace : interface.traceChecker.checkTrace trace = true) :
    semantics.Derivable trace.proof.conclusion :=
  interface.checkedTraceSound trace htrace

theorem checked_trace_steps_checked
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (trace : PAHilbertCheckedProofTrace)
    (htrace : interface.traceChecker.checkTrace trace = true)
    (step : PAHilbertProofStep)
    (hstep : step ∈ trace.decodedSteps) :
    interface.traceChecker.checkStep trace step = true :=
  interface.traceCheckerExactness.checkTraceToCheckedSteps
    trace htrace step hstep

theorem checked_step_to_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (trace : PAHilbertCheckedProofTrace)
    (step : PAHilbertProofStep)
    (hstep : step ∈ trace.decodedSteps)
    (hchecked : interface.traceChecker.checkStep trace step = true) :
    semantics.Derivable step.formula :=
  interface.traceCheckerExactness.checkStepSound
    trace step hstep hchecked

theorem checked_trace_to_derivable_via_steps
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (trace : PAHilbertCheckedProofTrace)
    (htrace : interface.traceChecker.checkTrace trace = true) :
    semantics.Derivable trace.proof.conclusion := by
  rcases trace.conclusionAppears with ⟨step, hstep_mem, hstep_formula⟩
  have hstep :
      semantics.Derivable step.formula :=
    interface.checkedTraceEveryStepSound trace htrace step hstep_mem
  simpa [hstep_formula] using hstep

theorem allowed_rule_application_to_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (rule : PAHilbertInferenceRule)
    (premises : List PAHilbertFormula)
    (conclusion : PAHilbertFormula)
    (_hallowed : checker.ruleAllowed rule = true)
    (happlication :
      interface.inferenceRuleSemantics.RuleApplication
        rule premises conclusion)
    (hpremises :
      ∀ premise : PAHilbertFormula,
        premise ∈ premises → semantics.Derivable premise) :
    semantics.Derivable conclusion :=
  interface.inferenceRuleSemantics.ruleApplicationSound
    rule premises conclusion happlication hpremises

theorem ruleAllowed_to_exists_ruleApplication
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (rule : PAHilbertInferenceRule)
    (hallowed : checker.ruleAllowed rule = true) :
    ∃ premises : List PAHilbertFormula,
      ∃ conclusion : PAHilbertFormula,
        interface.inferenceRuleSemantics.RuleApplication
          rule premises conclusion :=
  interface.inferenceRuleExactness.allowedSound rule hallowed

theorem ruleApplication_to_ruleAllowed
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (rule : PAHilbertInferenceRule)
    (premises : List PAHilbertFormula)
    (conclusion : PAHilbertFormula)
    (happlication :
      interface.inferenceRuleSemantics.RuleApplication
        rule premises conclusion) :
    checker.ruleAllowed rule = true :=
  interface.inferenceRuleExactness.allowedComplete
    rule premises conclusion happlication

theorem rejects_finite_list_to_no_accepted_decoded_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true)
    (code : Nat) (proof : PAHilbertProofObject)
    (hsmall : code < finiteList.bound)
    (hdecode : checker.decoder.decode code = some proof)
    (hconclusion : proof.conclusion = formula) :
    checker.accepts proof formula = false :=
  interface.decodedRejectsToNotAccepted
    code proof formula hdecode hconclusion
    (hrejects code (finiteList.coversSmallCodes code hsmall))

end PAHilbertCheckerInterface

/-- Minimal paper-proof interface extracted from the fuller checker interface.
This is the Lean-facing version of the two proof obligations used in the
informal argument: accepted checker proofs are PA-derivable, and rejecting every
covered code in a finite list excludes all proof codes below the list bound. -/
structure PAHilbertCheckerPaperProofInterface
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics) : Prop where
  acceptsToDerivable :
    ∀ proof : PAHilbertProofObject,
      ∀ formula : PAHilbertFormula,
        checker.accepts proof formula = true →
          semantics.Derivable formula
  rejectsFiniteListToNoSmallProofCode :
    ∀ formula : PAHilbertFormula,
      ∀ finiteList : PAHilbertFiniteCodeList,
        (∀ code : Nat, code ∈ finiteList.codes →
          checker.rejectsCode code formula = true) →
            PAHilbertNoSmallProofCode checker formula finiteList.bound
  rejectsFiniteListToNoAcceptedDecodedCode :
    ∀ formula : PAHilbertFormula,
      ∀ finiteList : PAHilbertFiniteCodeList,
        (∀ code : Nat, code ∈ finiteList.codes →
          checker.rejectsCode code formula = true) →
            ∀ code : Nat,
              ∀ proof : PAHilbertProofObject,
                code < finiteList.bound →
                  checker.decoder.decode code = some proof →
                    proof.conclusion = formula →
                      checker.accepts proof formula = false

namespace PAHilbertCheckerPaperProofInterface

theorem accepts_to_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper : PAHilbertCheckerPaperProofInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    semantics.Derivable formula :=
  paper.acceptsToDerivable proof formula haccepts

theorem accepts_to_formulaCode_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper : PAHilbertCheckerPaperProofInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    PAHilbertFormulaCodeDerivable semantics formula.code :=
  ⟨formula, rfl, paper.accepts_to_derivable proof formula haccepts⟩

theorem accepted_decoded_code_to_formulaCode_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper : PAHilbertCheckerPaperProofInterface checker semantics)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code) :
    PAHilbertFormulaCodeDerivable semantics formulaCode := by
  rcases haccepted with
    ⟨proof, _hdecode, hconclusionCode, haccepts⟩
  exact
    ⟨proof.conclusion, hconclusionCode,
      paper.accepts_to_derivable proof proof.conclusion haccepts⟩

theorem rejects_finite_list_to_no_small_proof_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper : PAHilbertCheckerPaperProofInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true) :
    PAHilbertNoSmallProofCode checker formula finiteList.bound :=
  paper.rejectsFiniteListToNoSmallProofCode formula finiteList hrejects

theorem rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper : PAHilbertCheckerPaperProofInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode
      checker formula.code finiteList.bound :=
  PAHilbertNoSmallProofCodeForFormulaCode.toNoSmallAcceptedProofCode
    (PAHilbertNoSmallProofCode.toFormulaCode
      (paper.rejects_finite_list_to_no_small_proof_code
        formula finiteList hrejects))

theorem rejects_finite_list_to_no_accepted_decoded_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper : PAHilbertCheckerPaperProofInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true)
    (code : Nat) (proof : PAHilbertProofObject)
    (hsmall : code < finiteList.bound)
    (hdecode : checker.decoder.decode code = some proof)
    (hconclusion : proof.conclusion = formula) :
    checker.accepts proof formula = false :=
  paper.rejectsFiniteListToNoAcceptedDecodedCode
    formula finiteList hrejects code proof hsmall hdecode hconclusion

end PAHilbertCheckerPaperProofInterface

/-- Executable checker variant with consistent `accepts`/`rejectsCode`
behavior.  It keeps the concrete recognizer, decoder, and rule checker, while
making rejection the Boolean complement of recognition for the queried
formula. -/
def concretePAHilbertConsistentChecker : PAHilbertChecker where
  recognizer := concretePAHilbertAxiomRecognizer
  decoder := concretePAHilbertProofObjectDecoder
  accepts := fun _proof formula =>
    concretePAHilbertAxiomRecognizer.recognizesAny formula
  rejectsCode := fun _code formula =>
    !concretePAHilbertAxiomRecognizer.recognizesAny formula
  ruleAllowed := concretePAHilbertRuleAllowed

theorem concretePAHilbertConsistentChecker_accepts_to_derivable
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts :
      concretePAHilbertConsistentChecker.accepts proof formula = true) :
    concretePAHilbertDerivabilitySemantics.Derivable formula :=
  (ConcretePAHilbertRecognizesAny_iff formula).mp
    (by
      simpa [concretePAHilbertConsistentChecker,
        concretePAHilbertAxiomRecognizer] using haccepts)

theorem concretePAHilbertConsistentChecker_rejects_to_accepts_false
    (code : Nat) (formula : PAHilbertFormula)
    (hrejects :
      concretePAHilbertConsistentChecker.rejectsCode code formula = true) :
    concretePAHilbertConsistentChecker.accepts
      (concretePAHilbertCanonicalProofObject code) formula = false := by
  simpa [concretePAHilbertConsistentChecker] using hrejects

/-- Paper-proof interface produced by the executable consistent checker.  This
is weaker than the full checker interface because the unrestricted decoder
field was shown above to be impossible, but it closes the paper-facing
accepted-proof and finite-rejection obligations for this executable checker. -/
def concretePAHilbertConsistentPaperProofInterface :
    PAHilbertCheckerPaperProofInterface
      concretePAHilbertConsistentChecker
      concretePAHilbertDerivabilitySemantics where
  acceptsToDerivable := by
    intro proof formula haccepts
    exact
      concretePAHilbertConsistentChecker_accepts_to_derivable
        proof formula haccepts
  rejectsFiniteListToNoSmallProofCode := by
    intro formula finiteList hrejects proof hsmall _hconclusion
    have hrejectProof :
        concretePAHilbertConsistentChecker.rejectsCode
          proof.code formula = true :=
      hrejects proof.code
        (finiteList.coversSmallCodes proof.code hsmall)
    simpa [concretePAHilbertConsistentChecker] using hrejectProof
  rejectsFiniteListToNoAcceptedDecodedCode := by
    intro formula finiteList hrejects code proof hsmall _hdecode _hconclusion
    have hrejectCode :
        concretePAHilbertConsistentChecker.rejectsCode
          code formula = true :=
      hrejects code (finiteList.coversSmallCodes code hsmall)
    simpa [concretePAHilbertConsistentChecker] using hrejectCode

theorem concretePAHilbertConsistentPaperProofInterface_nonempty :
    Nonempty
      (PAHilbertCheckerPaperProofInterface
        concretePAHilbertConsistentChecker
        concretePAHilbertDerivabilitySemantics) :=
  ⟨concretePAHilbertConsistentPaperProofInterface⟩

/-- Code-sensitive executable checker.  A proof object is accepted for a
formula only when the canonical object for its numeric code has the same
formula code and the formula is recognized by the concrete scheme recognizer.
This is the first concrete checker shape compatible with lower-bound finite
search: small mismatching codes can be rejected while a larger matching code
can still witness completeness. -/
def concretePAHilbertIndexedChecker : PAHilbertChecker where
  recognizer := concretePAHilbertAxiomRecognizer
  decoder := concretePAHilbertProofObjectDecoder
  accepts := fun proof formula => by
    classical
    exact
      if (concretePAHilbertCanonicalProofObject proof.code).conclusion.code =
          formula.code then
        concretePAHilbertAxiomRecognizer.recognizesAny formula
      else
        false
  rejectsCode := fun code formula => by
    classical
    exact
      if (concretePAHilbertCanonicalProofObject code).conclusion.code =
          formula.code then
        !concretePAHilbertAxiomRecognizer.recognizesAny formula
      else
        true
  ruleAllowed := concretePAHilbertRuleAllowed

theorem concretePAHilbertIndexedChecker_accepts_to_derivable
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts :
      concretePAHilbertIndexedChecker.accepts proof formula = true) :
    concretePAHilbertDerivabilitySemantics.Derivable formula := by
  classical
  by_cases hmatch :
      (concretePAHilbertCanonicalProofObject proof.code).conclusion.code =
        formula.code
  · have hrecognized :
        concretePAHilbertAxiomRecognizer.recognizesAny formula = true := by
      simpa [concretePAHilbertIndexedChecker, hmatch] using haccepts
    exact
      (ConcretePAHilbertRecognizesAny_iff formula).mp
        (by
          simpa [concretePAHilbertAxiomRecognizer] using hrecognized)
  · simp [concretePAHilbertIndexedChecker, hmatch] at haccepts

theorem concretePAHilbertIndexedChecker_rejectsCode_to_accepts_false
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (hrejects :
      concretePAHilbertIndexedChecker.rejectsCode proof.code formula =
        true) :
    concretePAHilbertIndexedChecker.accepts proof formula = false := by
  classical
  by_cases hmatch :
      (concretePAHilbertCanonicalProofObject proof.code).conclusion.code =
        formula.code
  · simpa [concretePAHilbertIndexedChecker, hmatch] using hrejects
  · simp [concretePAHilbertIndexedChecker, hmatch]

theorem concretePAHilbertIndexedChecker_acceptedProofCode_of_canonical
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (hconclusionCode :
      (concretePAHilbertCanonicalProofObject code).conclusion.code =
        formulaCode)
    (hrecognized :
      concretePAHilbertAxiomRecognizer.recognizesAny
        (concretePAHilbertCanonicalProofObject code).conclusion = true) :
    PAHilbertAcceptedProofCodeForFormulaCode
      concretePAHilbertIndexedChecker formulaCode code := by
  refine
    ⟨concretePAHilbertCanonicalProofObject code, rfl,
      hconclusionCode, ?_⟩
  have hmatch :
      (concretePAHilbertCanonicalProofObject
          (concretePAHilbertCanonicalProofObject code).code).conclusion.code =
        (concretePAHilbertCanonicalProofObject code).conclusion.code :=
    rfl
  simpa [concretePAHilbertIndexedChecker, hmatch] using hrecognized

/-- Paper-facing exactness for the code-sensitive concrete checker.  This
closes accepted-proof soundness and finite rejection without requiring the
known-impossible unrestricted decoder completeness field. -/
def concretePAHilbertIndexedPaperProofInterface :
    PAHilbertCheckerPaperProofInterface
      concretePAHilbertIndexedChecker
      concretePAHilbertDerivabilitySemantics where
  acceptsToDerivable := by
    intro proof formula haccepts
    exact
      concretePAHilbertIndexedChecker_accepts_to_derivable
        proof formula haccepts
  rejectsFiniteListToNoSmallProofCode := by
    intro formula finiteList hrejects proof hsmall _hconclusion
    have hrejectProof :
        concretePAHilbertIndexedChecker.rejectsCode
          proof.code formula = true :=
      hrejects proof.code
        (finiteList.coversSmallCodes proof.code hsmall)
    exact
      concretePAHilbertIndexedChecker_rejectsCode_to_accepts_false
        proof formula hrejectProof
  rejectsFiniteListToNoAcceptedDecodedCode := by
    intro formula finiteList hrejects code proof hsmall hdecode _hconclusion
    have hrejectCode :
        concretePAHilbertIndexedChecker.rejectsCode code formula = true :=
      hrejects code (finiteList.coversSmallCodes code hsmall)
    have hproofCode : proof.code = code :=
      concretePAHilbertIndexedChecker.decoder.decodedCode_eq
        code proof hdecode
    have hrejectProof :
        concretePAHilbertIndexedChecker.rejectsCode
          proof.code formula = true := by
      simpa [hproofCode] using hrejectCode
    exact
      concretePAHilbertIndexedChecker_rejectsCode_to_accepts_false
        proof formula hrejectProof

theorem concretePAHilbertIndexedPaperProofInterface_nonempty :
    Nonempty
      (PAHilbertCheckerPaperProofInterface
        concretePAHilbertIndexedChecker
        concretePAHilbertDerivabilitySemantics) :=
  ⟨concretePAHilbertIndexedPaperProofInterface⟩

/-! ## Scale-dependent theorem-5 target checker -/

/-- Target-family predicate for the theorem-5 strengthened finite-consistency
formula codes. -/
def ConcretePAHilbertIsStrengthenedPartialConsistency
    (formula : PAHilbertFormula) : Prop :=
  formula.code.family =
    _root_.FormulaFamily.strengthenedPartialConsistency

/-- Executable recognizer for theorem-5 strengthened finite-consistency
formula codes. -/
def ConcretePAHilbertRecognizesStrengthenedPartialConsistency
    (formula : PAHilbertFormula) : Bool :=
  match formula.code.family with
  | _root_.FormulaFamily.strengthenedPartialConsistency => true
  | _ => false

theorem ConcretePAHilbertRecognizesStrengthenedPartialConsistency_iff
    (formula : PAHilbertFormula) :
    ConcretePAHilbertRecognizesStrengthenedPartialConsistency formula = true ↔
      ConcretePAHilbertIsStrengthenedPartialConsistency formula := by
  cases formula with
  | mk code =>
      cases code with
      | mk family index =>
          cases family <;>
            simp [ConcretePAHilbertRecognizesStrengthenedPartialConsistency,
              ConcretePAHilbertIsStrengthenedPartialConsistency]

def ConcretePAHilbertTheorem5RecognizesAny
    (formula : PAHilbertFormula) : Bool :=
  ConcretePAHilbertRecognizesAny formula ||
    ConcretePAHilbertRecognizesStrengthenedPartialConsistency formula

def ConcretePAHilbertTheorem5Derivable
    (formula : PAHilbertFormula) : Prop :=
  ConcretePAHilbertDerivable formula ∨
    ConcretePAHilbertIsStrengthenedPartialConsistency formula

theorem ConcretePAHilbertTheorem5RecognizesAny_iff
    (formula : PAHilbertFormula) :
    ConcretePAHilbertTheorem5RecognizesAny formula = true ↔
      ConcretePAHilbertTheorem5Derivable formula := by
  simp [ConcretePAHilbertTheorem5RecognizesAny,
    ConcretePAHilbertTheorem5Derivable,
    ConcretePAHilbertRecognizesAny_iff,
    ConcretePAHilbertRecognizesStrengthenedPartialConsistency_iff]

def concretePAHilbertTheorem5AxiomRecognizer :
    PAHilbertAxiomRecognizer where
  recognizesLogical := ConcretePAHilbertRecognizesTag 0
  recognizesEquality := ConcretePAHilbertRecognizesTag 1
  recognizesInduction := ConcretePAHilbertRecognizesTag 2
  recognizesPAArithmetic := fun formula =>
    ConcretePAHilbertRecognizesTag 3 formula ||
      ConcretePAHilbertRecognizesStrengthenedPartialConsistency formula
  recognizesAny := ConcretePAHilbertTheorem5RecognizesAny

def concretePAHilbertTheorem5DerivabilitySemantics :
    PAHilbertDerivabilitySemantics where
  Derivable := ConcretePAHilbertTheorem5Derivable

def concretePAHilbertTheorem5AxiomSchemeSemantics :
    PAHilbertAxiomSchemeSemantics
      concretePAHilbertTheorem5DerivabilitySemantics where
  IsLogicalAxiom := ConcretePAHilbertIsTaggedAxiom 0
  IsEqualityAxiom := ConcretePAHilbertIsTaggedAxiom 1
  IsInductionSchema := ConcretePAHilbertIsTaggedAxiom 2
  IsPAArithmeticAxiom := fun formula =>
    ConcretePAHilbertIsTaggedAxiom 3 formula ∨
      ConcretePAHilbertIsStrengthenedPartialConsistency formula
  logicalAxiomDerivable := by
    intro formula htag
    exact Or.inl (Or.inl htag)
  equalityAxiomDerivable := by
    intro formula htag
    exact Or.inl (Or.inr (Or.inl htag))
  inductionSchemaDerivable := by
    intro formula htag
    exact Or.inl (Or.inr (Or.inr (Or.inl htag)))
  paArithmeticAxiomDerivable := by
    intro formula hpa
    rcases hpa with htag | htarget
    · exact Or.inl (Or.inr (Or.inr (Or.inr htag)))
    · exact Or.inr htarget

def concretePAHilbertTheorem5AxiomRecognizerExactness :
    PAHilbertAxiomRecognizerExactness
      concretePAHilbertTheorem5AxiomRecognizer
      concretePAHilbertTheorem5DerivabilitySemantics where
  schemeSemantics := concretePAHilbertTheorem5AxiomSchemeSemantics
  logicalExact := by
    intro formula
    simpa [concretePAHilbertTheorem5AxiomRecognizer,
      concretePAHilbertTheorem5AxiomSchemeSemantics] using
      (ConcretePAHilbertRecognizesTag_iff 0 formula)
  equalityExact := by
    intro formula
    simpa [concretePAHilbertTheorem5AxiomRecognizer,
      concretePAHilbertTheorem5AxiomSchemeSemantics] using
      (ConcretePAHilbertRecognizesTag_iff 1 formula)
  inductionExact := by
    intro formula
    simpa [concretePAHilbertTheorem5AxiomRecognizer,
      concretePAHilbertTheorem5AxiomSchemeSemantics] using
      (ConcretePAHilbertRecognizesTag_iff 2 formula)
  paArithmeticExact := by
    intro formula
    simp [concretePAHilbertTheorem5AxiomRecognizer,
      concretePAHilbertTheorem5AxiomSchemeSemantics,
      ConcretePAHilbertRecognizesTag_iff,
      ConcretePAHilbertRecognizesStrengthenedPartialConsistency_iff]
  recognizesAnyExact := by
    intro formula
    constructor
    · intro hrecognized
      rcases
          (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mp
            (by
              simpa [concretePAHilbertTheorem5AxiomRecognizer] using
                hrecognized)
        with hbase | htarget
      · rcases hbase with hlogical | hequality | hinduction | hpa
        · exact Or.inl hlogical
        · exact Or.inr (Or.inl hequality)
        · exact Or.inr (Or.inr (Or.inl hinduction))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hpa)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr htarget)))
    · intro hscheme
      apply (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mpr
      rcases hscheme with hlogical | hequality | hinduction | hpa
      · exact Or.inl (Or.inl hlogical)
      · exact Or.inl (Or.inr (Or.inl hequality))
      · exact Or.inl (Or.inr (Or.inr (Or.inl hinduction)))
      · rcases hpa with htag | htarget
        · exact Or.inl (Or.inr (Or.inr (Or.inr htag)))
        · exact Or.inr htarget
  logicalSound := by
    intro formula hrecognized
    exact Or.inl (Or.inl
      ((ConcretePAHilbertRecognizesTag_iff 0 formula).mp hrecognized))
  equalitySound := by
    intro formula hrecognized
    exact Or.inl (Or.inr (Or.inl
      ((ConcretePAHilbertRecognizesTag_iff 1 formula).mp hrecognized)))
  inductionSound := by
    intro formula hrecognized
    exact Or.inl (Or.inr (Or.inr (Or.inl
      ((ConcretePAHilbertRecognizesTag_iff 2 formula).mp hrecognized))))
  paArithmeticSound := by
    intro formula hrecognized
    have hpa :
        ConcretePAHilbertRecognizesTag 3 formula = true ∨
          ConcretePAHilbertRecognizesStrengthenedPartialConsistency
            formula = true := by
      simpa [concretePAHilbertTheorem5AxiomRecognizer] using hrecognized
    rcases hpa with htag | htarget
    · exact Or.inl (Or.inr (Or.inr (Or.inr
        ((ConcretePAHilbertRecognizesTag_iff 3 formula).mp htag))))
    · exact Or.inr
        ((ConcretePAHilbertRecognizesStrengthenedPartialConsistency_iff
          formula).mp htarget)
  recognizesAnySound := by
    intro formula hrecognized
    exact (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mp
      (by
        simpa [concretePAHilbertTheorem5AxiomRecognizer] using hrecognized)
  logicalCovered := by
    intro formula hrecognized
    exact (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mpr
      (Or.inl
        (Or.inl
          ((ConcretePAHilbertRecognizesTag_iff 0 formula).mp hrecognized)))
  equalityCovered := by
    intro formula hrecognized
    exact (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mpr
      (Or.inl
        (Or.inr (Or.inl
          ((ConcretePAHilbertRecognizesTag_iff 1 formula).mp hrecognized))))
  inductionCovered := by
    intro formula hrecognized
    exact (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mpr
      (Or.inl
        (Or.inr (Or.inr (Or.inl
          ((ConcretePAHilbertRecognizesTag_iff 2 formula).mp hrecognized)))))
  paArithmeticCovered := by
    intro formula hrecognized
    have hpa :
        ConcretePAHilbertRecognizesTag 3 formula = true ∨
          ConcretePAHilbertRecognizesStrengthenedPartialConsistency
            formula = true := by
      simpa [concretePAHilbertTheorem5AxiomRecognizer] using hrecognized
    rcases hpa with htag | htarget
    · exact (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mpr
        (Or.inl
          (Or.inr (Or.inr (Or.inr
            ((ConcretePAHilbertRecognizesTag_iff 3 formula).mp htag)))))
    · exact (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mpr
        (Or.inr
          ((ConcretePAHilbertRecognizesStrengthenedPartialConsistency_iff
            formula).mp htarget))

theorem concretePAHilbertTheorem5AxiomRecognizerExactness_nonempty :
    Nonempty
      (PAHilbertAxiomRecognizerExactness
        concretePAHilbertTheorem5AxiomRecognizer
        concretePAHilbertTheorem5DerivabilitySemantics) :=
  ⟨concretePAHilbertTheorem5AxiomRecognizerExactness⟩

/-- The concrete theorem-5 semantics derives every strengthened
finite-consistency formula code by construction. -/
theorem concretePAHilbertTheorem5_strengthenedPartialConsistencyCode_derivable
    (n : Nat) :
    concretePAHilbertTheorem5DerivabilitySemantics.Derivable
      (PAHilbertFormula.ofFormulaCode
        (_root_.strengthenedPartialConsistencyCode n)) := by
  exact Or.inr (by
    unfold ConcretePAHilbertIsStrengthenedPartialConsistency
    simp [PAHilbertFormula.ofFormulaCode,
      _root_.strengthenedPartialConsistencyCode])

/-- Code-level form of
`concretePAHilbertTheorem5_strengthenedPartialConsistencyCode_derivable`. -/
theorem concretePAHilbertTheorem5_strengthenedPartialConsistencyCode_formulaCodeDerivable
    (n : Nat) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics
      (_root_.strengthenedPartialConsistencyCode n) := by
  refine
    ⟨PAHilbertFormula.ofFormulaCode
        (_root_.strengthenedPartialConsistencyCode n),
      rfl, ?_⟩
  exact
    concretePAHilbertTheorem5_strengthenedPartialConsistencyCode_derivable n

/-- Ordinary finite-consistency codes are not theorem-5 strengthened targets in
the concrete semantics.  This keeps the ordinary payload residual separate from
the theorem-5 strengthened target. -/
theorem concretePAHilbertTheorem5_partialConsistencyCode_not_derivable
    (n : Nat) :
    ¬ concretePAHilbertTheorem5DerivabilitySemantics.Derivable
        (PAHilbertFormula.ofFormulaCode (_root_.partialConsistencyCode n)) := by
  intro hderivable
  rcases hderivable with htag0 | htarget
  · rcases htag0 with htag0 | htag1 | htag2 | htag3
    · simp [ConcretePAHilbertIsTaggedAxiom, ConcretePAHilbertFormulaTag,
        PAHilbertFormula.ofFormulaCode, _root_.partialConsistencyCode] at htag0
    · simp [ConcretePAHilbertIsTaggedAxiom, ConcretePAHilbertFormulaTag,
        PAHilbertFormula.ofFormulaCode, _root_.partialConsistencyCode] at htag1
    · simp [ConcretePAHilbertIsTaggedAxiom, ConcretePAHilbertFormulaTag,
        PAHilbertFormula.ofFormulaCode, _root_.partialConsistencyCode] at htag2
    · simp [ConcretePAHilbertIsTaggedAxiom, ConcretePAHilbertFormulaTag,
        PAHilbertFormula.ofFormulaCode, _root_.partialConsistencyCode] at htag3
  · unfold ConcretePAHilbertIsStrengthenedPartialConsistency at htarget
    simp [PAHilbertFormula.ofFormulaCode, _root_.partialConsistencyCode] at htarget

/-- Code-level form of
`concretePAHilbertTheorem5_partialConsistencyCode_not_derivable`: ordinary
partial-consistency formula codes are outside the concrete theorem-5
derivability semantics. -/
theorem concretePAHilbertTheorem5_partialConsistencyCode_not_formulaCodeDerivable
    (n : Nat) :
    ¬ PAHilbertFormulaCodeDerivable
        concretePAHilbertTheorem5DerivabilitySemantics
        (_root_.partialConsistencyCode n) := by
  intro hderivable
  rcases hderivable with ⟨formula, hcode, hformula_derivable⟩
  have hformula_eq :
      formula =
        PAHilbertFormula.ofFormulaCode (_root_.partialConsistencyCode n) :=
    PAHilbertFormula.eq_of_code_eq
      (by
        simpa [PAHilbertFormula.ofFormulaCode] using hcode)
  rw [hformula_eq] at hformula_derivable
  exact
    concretePAHilbertTheorem5_partialConsistencyCode_not_derivable n
      hformula_derivable

/-- The ordinary derivability-to-root-acceptance clause for the concrete
theorem-5 semantics is vacuous: the ordinary partial-consistency codes are not
derivable in this semantics. -/
theorem concretePAHilbertTheorem5_partialConsistencyCode_derivableSound_vacuous
    (n : Nat) :
    PAHilbertFormulaCodeDerivable
        concretePAHilbertTheorem5DerivabilitySemantics
        (_root_.partialConsistencyCode n) →
      _root_.accepted_certificate (_root_.partialConsistencyCode n) := by
  intro hderivable
  exact False.elim
    (concretePAHilbertTheorem5_partialConsistencyCode_not_formulaCodeDerivable
      n hderivable)

/-- For the concrete theorem-5 semantics, strengthened derivability soundness
into the root accepted-certificate vocabulary is exactly the strengthened
payload-truth package.  The forward direction applies the soundness clause to
the theorem-5 strengthened formulas, which are derivable by construction. -/
theorem concretePAHilbertTheorem5_strengthenedDerivableSound_iff_payloadTruth :
    (∀ n : Nat,
      PAHilbertFormulaCodeDerivable
          concretePAHilbertTheorem5DerivabilitySemantics
          (_root_.strengthenedPartialConsistencyCode n) →
        _root_.accepted_certificate
          (_root_.strengthenedPartialConsistencyCode n))
      ↔
      _root_.StrengthenedPartialConsistencyPayloadTruth := by
  constructor
  · intro hsound
    exact
      { true_all := by
          intro n
          exact
            _root_.strengthened_payload_of_accepted_certificate
              (hsound n
                (concretePAHilbertTheorem5_strengthenedPartialConsistencyCode_formulaCodeDerivable
                  n)) }
  · intro htruth n _hderivable
    exact htruth.toAcceptedTruth.accepted_all n

theorem concretePAHilbert_powerBoundRawCode_strengthenedPartialConsistency
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    ConcretePAHilbertIsStrengthenedPartialConsistency
      (PAHilbertFormula.ofFormulaCode
        (scale_data.powerBoundRawCode n)) := by
  unfold ConcretePAHilbertIsStrengthenedPartialConsistency
  rw [InternalPudlakTheorem5ScaleData.powerBoundRawCode_eq_rescaledPudlak]
  simp [PAHilbertFormula.ofFormulaCode,
    _root_.rescaledPudlakStrengthenedFiniteConsistencyCode,
    _root_.pudlakStrengthenedFiniteConsistencyCode,
    _root_.strengthenedPartialConsistencyCode]

theorem concretePAHilbert_powerBoundRawCode_eq_strengthenedPartialConsistency_scale
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    scale_data.powerBoundRawCode n =
      _root_.strengthenedPartialConsistencyCode
        (scale_data.scale n) := by
  rw [InternalPudlakTheorem5ScaleData.powerBoundRawCode_eq_rescaledPudlak]
  simp [_root_.rescaledPudlakStrengthenedFiniteConsistencyCode,
    _root_.pudlakStrengthenedFiniteConsistencyCode]

theorem concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
    (scale_data : InternalPudlakTheorem5ScaleData)
    (hscale : Function.Injective scale_data.scale) :
    Function.Injective scale_data.powerBoundRawCode := by
  intro left right hcode
  have hindex :
      (scale_data.powerBoundRawCode left).index =
        (scale_data.powerBoundRawCode right).index :=
    congrArg (fun code : _root_.FormulaCode => code.index) hcode
  have hscale_eq :
      scale_data.scale left = scale_data.scale right := by
    simpa [
      concretePAHilbert_powerBoundRawCode_eq_strengthenedPartialConsistency_scale,
      _root_.strengthenedPartialConsistencyCode] using hindex
  exact hscale hscale_eq

theorem concretePAHilbert_powerBoundRawCode_ne_of_scale_ne
    (scale_data : InternalPudlakTheorem5ScaleData)
    {left right : Nat}
    (hscale_ne : scale_data.scale left ≠ scale_data.scale right) :
    scale_data.powerBoundRawCode left ≠
      scale_data.powerBoundRawCode right := by
  intro hcode
  have hindex :
      (scale_data.powerBoundRawCode left).index =
        (scale_data.powerBoundRawCode right).index :=
    congrArg (fun code : _root_.FormulaCode => code.index) hcode
  have hscale_eq :
      scale_data.scale left = scale_data.scale right := by
    simpa [
      concretePAHilbert_powerBoundRawCode_eq_strengthenedPartialConsistency_scale,
      _root_.strengthenedPartialConsistencyCode] using hindex
  exact hscale_ne hscale_eq

theorem concretePAHilbertTheorem5AxiomRecognizer_recognizes_powerBoundRawCode
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    concretePAHilbertTheorem5AxiomRecognizer.recognizesAny
      (PAHilbertFormula.ofFormulaCode
        (scale_data.powerBoundRawCode n)) = true := by
  have htarget :
      ConcretePAHilbertRecognizesStrengthenedPartialConsistency
        (PAHilbertFormula.ofFormulaCode
          (scale_data.powerBoundRawCode n)) = true :=
    (ConcretePAHilbertRecognizesStrengthenedPartialConsistency_iff
      (PAHilbertFormula.ofFormulaCode
        (scale_data.powerBoundRawCode n))).mpr
      (concretePAHilbert_powerBoundRawCode_strengthenedPartialConsistency
        scale_data n)
  simp [concretePAHilbertTheorem5AxiomRecognizer,
    ConcretePAHilbertTheorem5RecognizesAny, htarget]

def concretePAHilbertPowerBoundFormula
    (scale_data : InternalPudlakTheorem5ScaleData)
    (code : Nat) : PAHilbertFormula :=
  PAHilbertFormula.ofFormulaCode (scale_data.powerBoundRawCode code)

def concretePAHilbertPowerBoundProofObject
    (scale_data : InternalPudlakTheorem5ScaleData)
    (code : Nat) : PAHilbertProofObject where
  code := code
  steps := [code]
  conclusion := concretePAHilbertPowerBoundFormula scale_data code

def concretePAHilbertPowerBoundProofObjectDecoder
    (scale_data : InternalPudlakTheorem5ScaleData) :
    PAHilbertProofObjectDecoder where
  decode := fun code =>
    some (concretePAHilbertPowerBoundProofObject scale_data code)
  decodedCode_eq := by
    intro code proof hdecode
    cases hdecode
    rfl

def concretePAHilbertPowerBoundChecker
    (scale_data : InternalPudlakTheorem5ScaleData) :
    PAHilbertChecker where
  recognizer := concretePAHilbertTheorem5AxiomRecognizer
  decoder := concretePAHilbertPowerBoundProofObjectDecoder scale_data
  accepts := fun proof formula => by
    classical
    exact
      if (concretePAHilbertPowerBoundProofObject
            scale_data proof.code).conclusion.code = formula.code then
        concretePAHilbertTheorem5AxiomRecognizer.recognizesAny formula
      else
        false
  rejectsCode := fun code formula => by
    classical
    exact
      if (concretePAHilbertPowerBoundProofObject
            scale_data code).conclusion.code = formula.code then
        !concretePAHilbertTheorem5AxiomRecognizer.recognizesAny formula
      else
        true
  ruleAllowed := concretePAHilbertRuleAllowed

theorem concretePAHilbertPowerBoundChecker_accepts_to_derivable
    (scale_data : InternalPudlakTheorem5ScaleData)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts :
      (concretePAHilbertPowerBoundChecker scale_data).accepts
        proof formula = true) :
    concretePAHilbertTheorem5DerivabilitySemantics.Derivable formula := by
  classical
  by_cases hmatch :
      (concretePAHilbertPowerBoundProofObject
        scale_data proof.code).conclusion.code = formula.code
  · have hrecognized :
        concretePAHilbertTheorem5AxiomRecognizer.recognizesAny
          formula = true := by
      simpa [concretePAHilbertPowerBoundChecker, hmatch] using haccepts
    exact
      (ConcretePAHilbertTheorem5RecognizesAny_iff formula).mp
        (by
          simpa [concretePAHilbertTheorem5AxiomRecognizer] using
            hrecognized)
  · simp [concretePAHilbertPowerBoundChecker, hmatch] at haccepts

theorem concretePAHilbertPowerBoundChecker_rejectsCode_to_accepts_false
    (scale_data : InternalPudlakTheorem5ScaleData)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (hrejects :
      (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
        proof.code formula = true) :
    (concretePAHilbertPowerBoundChecker scale_data).accepts
      proof formula = false := by
  classical
  by_cases hmatch :
      (concretePAHilbertPowerBoundProofObject
        scale_data proof.code).conclusion.code = formula.code
  · simpa [concretePAHilbertPowerBoundChecker, hmatch] using hrejects
  · simp [concretePAHilbertPowerBoundChecker, hmatch]

theorem concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    PAHilbertAcceptedProofCodeForFormulaCode
      (concretePAHilbertPowerBoundChecker scale_data)
      (scale_data.powerBoundRawCode n) n := by
  refine
    ⟨concretePAHilbertPowerBoundProofObject scale_data n,
      rfl, rfl, ?_⟩
  have hrecognized :
      concretePAHilbertTheorem5AxiomRecognizer.recognizesAny
        (concretePAHilbertPowerBoundProofObject scale_data n).conclusion =
          true :=
    concretePAHilbertTheorem5AxiomRecognizer_recognizes_powerBoundRawCode
      scale_data n
  have hmatch :
      (concretePAHilbertPowerBoundProofObject scale_data
        (concretePAHilbertPowerBoundProofObject scale_data n).code).conclusion.code =
        (concretePAHilbertPowerBoundProofObject scale_data n).conclusion.code := by
    simp [concretePAHilbertPowerBoundProofObject]
  simp [concretePAHilbertPowerBoundChecker, hmatch, hrecognized]

def concretePAHilbertPowerBoundPaperProofInterface
    (scale_data : InternalPudlakTheorem5ScaleData) :
    PAHilbertCheckerPaperProofInterface
      (concretePAHilbertPowerBoundChecker scale_data)
      concretePAHilbertTheorem5DerivabilitySemantics where
  acceptsToDerivable := by
    intro proof formula haccepts
    exact
      concretePAHilbertPowerBoundChecker_accepts_to_derivable
        scale_data proof formula haccepts
  rejectsFiniteListToNoSmallProofCode := by
    intro formula finiteList hrejects proof hsmall _hconclusion
    have hrejectProof :
        (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
          proof.code formula = true :=
      hrejects proof.code
        (finiteList.coversSmallCodes proof.code hsmall)
    exact
      concretePAHilbertPowerBoundChecker_rejectsCode_to_accepts_false
        scale_data proof formula hrejectProof
  rejectsFiniteListToNoAcceptedDecodedCode := by
    intro formula finiteList hrejects code proof hsmall hdecode _hconclusion
    have hrejectCode :
        (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
          code formula = true :=
      hrejects code (finiteList.coversSmallCodes code hsmall)
    have hproofCode : proof.code = code :=
      (concretePAHilbertPowerBoundChecker scale_data).decoder.decodedCode_eq
        code proof hdecode
    have hrejectProof :
        (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
          proof.code formula = true := by
      simpa [hproofCode] using hrejectCode
    exact
      concretePAHilbertPowerBoundChecker_rejectsCode_to_accepts_false
        scale_data proof formula hrejectProof

theorem concretePAHilbertPowerBoundPaperProofInterface_nonempty
    (scale_data : InternalPudlakTheorem5ScaleData) :
    Nonempty
      (PAHilbertCheckerPaperProofInterface
        (concretePAHilbertPowerBoundChecker scale_data)
        concretePAHilbertTheorem5DerivabilitySemantics) :=
  ⟨concretePAHilbertPowerBoundPaperProofInterface scale_data⟩

/-- PowerBound accepted-code soundness through the paper-proof interface only.
This avoids the heavier exactness cores that also carry root proof-length
calibration data. -/
theorem concretePAHilbertPowerBoundPaperProofInterface_accepted_code_to_formulaCode_derivable
    (scale_data : InternalPudlakTheorem5ScaleData)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode code) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics formulaCode :=
  (concretePAHilbertPowerBoundPaperProofInterface scale_data)
    |>.accepted_decoded_code_to_formulaCode_derivable
      formulaCode code haccepted

/-- Canonical checker interface.  It replaces the impossible unrestricted
decoder completeness field by completeness for the proof objects that satisfy
the canonical/code-indexed invariant, while retaining the paper-facing
accepted-proof and finite-rejection exactness obligations. -/
structure PAHilbertCanonicalCheckerInterface
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics) : Type where
  Canonical : PAHilbertProofObject → Prop
  decoderCompleteCanonical :
    ∀ proof : PAHilbertProofObject,
      Canonical proof →
        checker.decoder.decode proof.code = some proof
  decodedProofCanonical :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        checker.decoder.decode code = some proof →
          Canonical proof
  decodedCode_eq :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        checker.decoder.decode code = some proof →
          proof.code = code
  paperProofInterface :
    PAHilbertCheckerPaperProofInterface checker semantics

namespace PAHilbertCanonicalCheckerInterface

theorem canonical_decode_complete
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCanonicalCheckerInterface checker semantics)
    (proof : PAHilbertProofObject)
    (hcanonical : interface.Canonical proof) :
    checker.decoder.decode proof.code = some proof :=
  interface.decoderCompleteCanonical proof hcanonical

theorem decoded_to_canonical
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCanonicalCheckerInterface checker semantics)
    (code : Nat) (proof : PAHilbertProofObject)
    (hdecode : checker.decoder.decode code = some proof) :
    interface.Canonical proof :=
  interface.decodedProofCanonical code proof hdecode

theorem accepts_to_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCanonicalCheckerInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    semantics.Derivable formula :=
  interface.paperProofInterface.accepts_to_derivable
    proof formula haccepts

theorem accepted_decoded_code_to_formulaCode_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCanonicalCheckerInterface checker semantics)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code) :
    PAHilbertFormulaCodeDerivable semantics formulaCode :=
  interface.paperProofInterface.accepted_decoded_code_to_formulaCode_derivable
    formulaCode code haccepted

theorem rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCanonicalCheckerInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode
      checker formula.code finiteList.bound :=
  interface.paperProofInterface
    |>.rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
      formula finiteList hrejects

end PAHilbertCanonicalCheckerInterface

/-- Canonical proof objects for the scale-dependent powerBound checker. -/
def ConcretePAHilbertPowerBoundCanonicalProofObject
    (scale_data : InternalPudlakTheorem5ScaleData)
    (proof : PAHilbertProofObject) : Prop :=
  proof = concretePAHilbertPowerBoundProofObject scale_data proof.code

theorem concretePAHilbertPowerBoundDecoder_complete_for_canonical
    (scale_data : InternalPudlakTheorem5ScaleData)
    (proof : PAHilbertProofObject)
    (hcanonical :
      ConcretePAHilbertPowerBoundCanonicalProofObject scale_data proof) :
    (concretePAHilbertPowerBoundChecker scale_data).decoder.decode
      proof.code = some proof := by
  rw [hcanonical]
  rfl

theorem concretePAHilbertPowerBoundDecoder_decoded_canonical
    (scale_data : InternalPudlakTheorem5ScaleData)
    (code : Nat) (proof : PAHilbertProofObject)
    (hdecode :
      (concretePAHilbertPowerBoundChecker scale_data).decoder.decode
        code = some proof) :
    ConcretePAHilbertPowerBoundCanonicalProofObject
      scale_data proof := by
  cases hdecode
  rfl

def concretePAHilbertPowerBoundCanonicalCheckerInterface
    (scale_data : InternalPudlakTheorem5ScaleData) :
    PAHilbertCanonicalCheckerInterface
      (concretePAHilbertPowerBoundChecker scale_data)
      concretePAHilbertTheorem5DerivabilitySemantics where
  Canonical :=
    ConcretePAHilbertPowerBoundCanonicalProofObject scale_data
  decoderCompleteCanonical :=
    concretePAHilbertPowerBoundDecoder_complete_for_canonical scale_data
  decodedProofCanonical :=
    concretePAHilbertPowerBoundDecoder_decoded_canonical scale_data
  decodedCode_eq := by
    intro code proof hdecode
    exact
      (concretePAHilbertPowerBoundChecker scale_data).decoder.decodedCode_eq
        code proof hdecode
  paperProofInterface :=
    concretePAHilbertPowerBoundPaperProofInterface scale_data

theorem concretePAHilbertPowerBoundCanonicalCheckerInterface_nonempty
    (scale_data : InternalPudlakTheorem5ScaleData) :
    Nonempty
      (PAHilbertCanonicalCheckerInterface
        (concretePAHilbertPowerBoundChecker scale_data)
        concretePAHilbertTheorem5DerivabilitySemantics) :=
  ⟨concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data⟩

namespace PAHilbertCheckerInterface

/-- The full checker interface supplies the minimal paper-proof interface. -/
def toPaperProofInterface
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics) :
    PAHilbertCheckerPaperProofInterface checker semantics where
  acceptsToDerivable := interface.acceptsToDerivable
  rejectsFiniteListToNoSmallProofCode :=
    interface.rejectsFiniteListToNoSmallProofCode
  rejectsFiniteListToNoAcceptedDecodedCode :=
    fun formula finiteList hrejects code proof hsmall hdecode hconclusion =>
      PAHilbertCheckerInterface.rejects_finite_list_to_no_accepted_decoded_code
        interface formula finiteList hrejects
        code proof hsmall hdecode hconclusion

theorem toPaperProofInterface_accepts_to_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : checker.accepts proof formula = true) :
    semantics.Derivable formula :=
  interface.toPaperProofInterface.accepts_to_derivable
    proof formula haccepts

theorem toPaperProofInterface_rejects_finite_list_to_no_small_proof_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true) :
    PAHilbertNoSmallProofCode checker formula finiteList.bound :=
  interface.toPaperProofInterface.rejects_finite_list_to_no_small_proof_code
    formula finiteList hrejects

theorem toPaperProofInterface_rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        checker.rejectsCode code formula = true) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode
      checker formula.code finiteList.bound :=
  interface.toPaperProofInterface
    |>.rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
      formula finiteList hrejects

theorem toPaperProofInterface_accepted_decoded_code_to_formulaCode_derivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code) :
    PAHilbertFormulaCodeDerivable semantics formulaCode :=
  interface.toPaperProofInterface.accepted_decoded_code_to_formulaCode_derivable
    formulaCode code haccepted

end PAHilbertCheckerInterface

/-- PA/Hilbert small-code enumeration packaged against the Month 9-10 theorem-5
semantic parameters.  The actual Month 9-10 search object is retained as a
field so this layer stays isolated from the internal construction details. -/
structure PAHilbertSmallCodeEnumeration
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  formulaAt : Nat → PAHilbertFormula
  formulaAt_code_eq_powerBoundRawCode :
    ∀ n : Nat, (formulaAt n).code = scale_data.powerBoundRawCode n
  finiteListAt : Nat → PAHilbertFiniteCodeList
  rejectsAllAt :
    PAHilbertChecker → Nat → Prop
  rejectsAllAt_spec :
    ∀ checker : PAHilbertChecker,
      ∀ n : Nat,
        rejectsAllAt checker n →
          ∀ code : Nat,
            code ∈ (finiteListAt n).codes →
              checker.rejectsCode code (formulaAt n) = true
  toSmallCodeSearch :
    InternalPudlakTheorem5SmallCodeSearch scale_data sem

namespace PAHilbertSmallCodeEnumeration

theorem formulaAt_code_eq_powerBoundRawCode_statement
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (enumeration : PAHilbertSmallCodeEnumeration.{q} scale_data sem)
    (n : Nat) :
    (enumeration.formulaAt n).code = scale_data.powerBoundRawCode n :=
  enumeration.formulaAt_code_eq_powerBoundRawCode n

def toInternalPudlakTheorem5SmallCodeSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (enumeration : PAHilbertSmallCodeEnumeration.{q} scale_data sem) :
    InternalPudlakTheorem5SmallCodeSearch scale_data sem :=
  enumeration.toSmallCodeSearch

theorem small_code_search_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (enumeration : PAHilbertSmallCodeEnumeration.{q} scale_data sem) :
    Nonempty (InternalPudlakTheorem5SmallCodeSearch scale_data sem) :=
  ⟨enumeration.toInternalPudlakTheorem5SmallCodeSearch⟩

theorem noSmallProofCodeAt
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (enumeration : PAHilbertSmallCodeEnumeration.{q} scale_data sem)
    (n : Nat)
    (hrejects : enumeration.rejectsAllAt checker n) :
    PAHilbertNoSmallProofCode checker
      (enumeration.formulaAt n) (enumeration.finiteListAt n).bound :=
  PAHilbertCheckerInterface.rejects_finite_list_to_no_small_proof_code
    interface (enumeration.formulaAt n) (enumeration.finiteListAt n)
    (enumeration.rejectsAllAt_spec checker n hrejects)

theorem noSmallProofCodeAt_powerBoundRawCode
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (enumeration : PAHilbertSmallCodeEnumeration.{q} scale_data sem)
    (n : Nat)
    (hrejects : enumeration.rejectsAllAt checker n) :
    PAHilbertNoSmallProofCodeForFormulaCode checker
      (scale_data.powerBoundRawCode n) (enumeration.finiteListAt n).bound := by
  have hno :
      PAHilbertNoSmallProofCode checker
        (enumeration.formulaAt n) (enumeration.finiteListAt n).bound :=
    noSmallProofCodeAt interface enumeration n hrejects
  have hcode :
      (enumeration.formulaAt n).code =
        scale_data.powerBoundRawCode n :=
    enumeration.formulaAt_code_eq_powerBoundRawCode n
  rw [← hcode]
  exact PAHilbertNoSmallProofCode.toFormulaCode hno

theorem noSmallAcceptedProofCodeAt_powerBoundRawCode
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (enumeration : PAHilbertSmallCodeEnumeration.{q} scale_data sem)
    (n : Nat)
    (hrejects : enumeration.rejectsAllAt checker n) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode checker
      (scale_data.powerBoundRawCode n) (enumeration.finiteListAt n).bound :=
  PAHilbertNoSmallProofCodeForFormulaCode.toNoSmallAcceptedProofCode
    (noSmallProofCodeAt_powerBoundRawCode
      interface enumeration n hrejects)

theorem noSmallAcceptedProofCodeAt_powerBoundRawCode_fromPaperProofInterface
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper : PAHilbertCheckerPaperProofInterface checker semantics)
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (enumeration : PAHilbertSmallCodeEnumeration.{q} scale_data sem)
    (n : Nat)
    (hrejects : enumeration.rejectsAllAt checker n) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode checker
      (scale_data.powerBoundRawCode n) (enumeration.finiteListAt n).bound := by
  have hno :
      PAHilbertNoSmallAcceptedProofCodeForFormulaCode checker
        (enumeration.formulaAt n).code
        (enumeration.finiteListAt n).bound :=
    paper.rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
      (enumeration.formulaAt n) (enumeration.finiteListAt n)
      (enumeration.rejectsAllAt_spec checker n hrejects)
  simpa [enumeration.formulaAt_code_eq_powerBoundRawCode n] using hno

end PAHilbertSmallCodeEnumeration

/-- Bridge from the Month 9-10 proof-code semantics to the PA/Hilbert checker
numeric-code layer.  This is the exact boundary where a semantic proof code
checked by `ProofCodeSemantics` is tied to a decoded PA/Hilbert proof code. -/
structure PAHilbertProofCodeSemanticsBridge
    (checker : PAHilbertChecker)
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  toNatCode : sem.Code → Nat
  size_le_natCode :
    ∀ code : sem.Code, sem.size code ≤ toNatCode code
  natCode_le_size :
    ∀ code : sem.Code, toNatCode code ≤ sem.size code
  checks_to_acceptedProofCode :
    ∀ code : sem.Code,
      ∀ formulaCode : _root_.FormulaCode,
        sem.checks code formulaCode →
          PAHilbertAcceptedProofCodeForFormulaCode
            checker formulaCode (toNatCode code)
  acceptedProofCode_to_semanticCheck :
    ∀ formulaCode : _root_.FormulaCode,
      ∀ natCode : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode natCode →
          ∃ code : sem.Code,
            toNatCode code = natCode ∧ sem.checks code formulaCode

namespace PAHilbertProofCodeSemanticsBridge

theorem checks_to_formulaCodeDerivable
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge : PAHilbertProofCodeSemanticsBridge.{q}
      checker scale_data sem)
    (code : sem.Code) (formulaCode : _root_.FormulaCode)
    (hchecks : sem.checks code formulaCode) :
    PAHilbertFormulaCodeDerivable semantics formulaCode :=
  PAHilbertCheckerInterface.accepted_decoded_code_to_formulaCode_derivable
    interface formulaCode (bridge.toNatCode code)
    (bridge.checks_to_acceptedProofCode code formulaCode hchecks)

theorem acceptedProofCode_iff_existsSemanticCheck
    {checker : PAHilbertChecker}
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge : PAHilbertProofCodeSemanticsBridge.{q}
      checker scale_data sem)
    (formulaCode : _root_.FormulaCode) (natCode : Nat) :
    PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode natCode ↔
      ∃ code : sem.Code,
        bridge.toNatCode code = natCode ∧
          sem.checks code formulaCode := by
  constructor
  · intro haccepted
    exact bridge.acceptedProofCode_to_semanticCheck
      formulaCode natCode haccepted
  · intro hsemantic
    rcases hsemantic with ⟨code, hnatCode, hchecks⟩
    simpa [hnatCode] using
      bridge.checks_to_acceptedProofCode code formulaCode hchecks

theorem natCode_lt_of_size_lt
    {checker : PAHilbertChecker}
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge : PAHilbertProofCodeSemanticsBridge.{q}
      checker scale_data sem)
    (code : sem.Code) {bound : Nat}
    (hsize : sem.size code < bound) :
    bridge.toNatCode code < bound :=
  lt_of_le_of_lt (bridge.natCode_le_size code) hsize

theorem noSmallAcceptedProofCode_to_noSemanticCheck_of_size_lt
    {checker : PAHilbertChecker}
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge : PAHilbertProofCodeSemanticsBridge.{q}
      checker scale_data sem)
    {formulaCode : _root_.FormulaCode} {bound : Nat}
    (hno :
      PAHilbertNoSmallAcceptedProofCodeForFormulaCode
        checker formulaCode bound)
    (code : sem.Code)
    (hsize : sem.size code < bound)
    (hchecks : sem.checks code formulaCode) :
    False :=
  hno (bridge.toNatCode code)
    (bridge.natCode_lt_of_size_lt code hsize)
    (bridge.checks_to_acceptedProofCode code formulaCode hchecks)

end PAHilbertProofCodeSemanticsBridge

/-! ## Executable finite-code lists -/

/-- Executable finite list of all numeric proof codes below `bound`. -/
def PAHilbertFiniteRangeCodeList (bound : Nat) :
    PAHilbertFiniteCodeList where
  codes := List.range bound
  bound := bound
  coversSmallCodes := by
    intro code hsmall
    exact List.mem_range.mpr hsmall

theorem PAHilbertFiniteRangeCodeList_codes
    (bound : Nat) :
    (PAHilbertFiniteRangeCodeList bound).codes = List.range bound :=
  rfl

theorem PAHilbertFiniteRangeCodeList_bound
    (bound : Nat) :
    (PAHilbertFiniteRangeCodeList bound).bound = bound :=
  rfl

/-! ## Month 9-10 checker-native bridge instances from the PA/Hilbert checker -/

/-- Completion data needed to view the executable PA/Hilbert checker as a
Month 9-10 checker semantics on the theorem-5 `powerBoundRawCode` family.  The
proof code relation itself is not artificial: it is exactly the decoded and
accepted PA/Hilbert numeric proof-code predicate. -/
structure PAHilbertAcceptedNatCodeCompletion
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker) : Type where
  complete_at_powerBoundRawCode :
    ∀ n : Nat,
      ∃ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code

def concretePAHilbertPowerBoundCompletion
    (scale_data : InternalPudlakTheorem5ScaleData) :
    PAHilbertAcceptedNatCodeCompletion
      scale_data (concretePAHilbertPowerBoundChecker scale_data) where
  complete_at_powerBoundRawCode := by
    intro n
    exact
      ⟨n,
        concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
          scale_data n⟩

/-- Checker semantics consumed by the Month 9-10 checker bridge.  Codes are
the searched numeric PA/Hilbert proof codes, checks are decoded accepted proof
codes, and size is the numeric code itself. -/
abbrev PAHilbertAcceptedNatCodeCheckerSemantics
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data where
  Code := Nat
  checks := fun code formulaCode =>
    PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code
  size := id
  complete_at_powerBoundRawCode := completion.complete_at_powerBoundRawCode

theorem PAHilbertAcceptedNatCodeCheckerSemantics_checks_eq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (code : Nat) (formulaCode : _root_.FormulaCode) :
    (PAHilbertAcceptedNatCodeCheckerSemantics
      scale_data checker completion).checks code formulaCode =
      PAHilbertAcceptedProofCodeForFormulaCode
        checker formulaCode code :=
  rfl

theorem PAHilbertAcceptedNatCodeCheckerSemantics_size_eq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (code : Nat) :
    (PAHilbertAcceptedNatCodeCheckerSemantics
      scale_data checker completion).size code = code :=
  rfl

/-- Concrete finite enumeration for numeric proof codes below a cutoff. -/
abbrev PAHilbertAcceptedNatCodeFiniteEnumeration
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion) where
  candidates := fun _ K => List.range K
  complete := by
    intro n K code _hchecks hsize
    exact List.mem_range.mpr hsize

theorem PAHilbertAcceptedNatCodeFiniteEnumeration_candidates_eq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (n K : Nat) :
    (PAHilbertAcceptedNatCodeFiniteEnumeration
      scale_data checker completion).candidates n K =
      List.range K :=
  rfl

/-- Computable finite-search rejection data for the accepted numeric-code
checker.  It is stated as a small-code rejection extractor because the concrete
enumeration is `List.range K`. -/
structure PAHilbertAcceptedNatCodeRejectionExtractorData
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejects_lt_cutoff :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code < cutoff f hf N →
          ¬ PAHilbertAcceptedProofCodeForFormulaCode
            checker (scale_data.powerBoundRawCode (witness f hf N)) code

def PAHilbertAcceptedNatCodeRejectionExtractorData.toCheckerExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (data :
      PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion)
      (PAHilbertAcceptedNatCodeFiniteEnumeration
        scale_data checker completion) where
  witness := data.witness
  cutoff := data.cutoff
  witness_ge := data.witness_ge
  cutoff_gt := data.cutoff_gt
  rejects_candidates := by
    intro f hf N code hmem
    have hlt : code < data.cutoff f hf N := by
      simpa [PAHilbertAcceptedNatCodeFiniteEnumeration] using hmem
    exact data.rejects_lt_cutoff f hf N code hlt

namespace PAHilbertAcceptedNatCodeRejectionExtractorData

/-- Exact constructor trace for the accepted-code rejection data before the
checker-level `rejectsCode` packaging.  The internal extractor preserves the
given witness and cutoff functions, and the finite range semantics is exactly
the concrete `code < cutoff` condition. -/
theorem toCheckerExtractor_exact_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (data :
      PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker) :
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      (data.toCheckerExtractor
          (completion := completion)).witness f hf N =
          data.witness f hf N ∧
        (data.toCheckerExtractor
            (completion := completion)).cutoff f hf N =
            data.cutoff f hf N ∧
          N ≤ data.witness f hf N ∧
            f (data.witness f hf N) < (data.cutoff f hf N : Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        ∀ code : Nat,
          code < data.cutoff f hf N →
            ¬
              (PAHilbertAcceptedNatCodeCheckerSemantics
                scale_data checker completion).checks code
                  (scale_data.powerBoundRawCode (data.witness f hf N))) := by
  refine ⟨?_, ?_⟩
  · intro f hf N
    exact
      ⟨rfl, rfl, data.witness_ge f hf N, data.cutoff_gt f hf N⟩
  · intro f hf N code hlt
    simpa using data.rejects_lt_cutoff f hf N code hlt

end PAHilbertAcceptedNatCodeRejectionExtractorData

/-- Executable rejection input phrased directly in terms of the PA/Hilbert
checker: every numeric code below the cutoff is rejected by `rejectsCode` for
the theorem-5 formula at the chosen witness. -/
structure PAHilbertAcceptedNatCodeCheckerRejectionData
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejectsCode_lt_cutoff :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code < cutoff f hf N →
          checker.rejectsCode code
            (PAHilbertFormula.ofFormulaCode
              (scale_data.powerBoundRawCode (witness f hf N))) = true

namespace PAHilbertAcceptedNatCodeCheckerRejectionData

def toAcceptedNatCodeRejectionExtractorData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (paper :
      PAHilbertCheckerPaperProofInterface checker semantics)
    (data :
      PAHilbertAcceptedNatCodeCheckerRejectionData scale_data checker) :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker where
  witness := data.witness
  cutoff := data.cutoff
  witness_ge := data.witness_ge
  cutoff_gt := data.cutoff_gt
  rejects_lt_cutoff := by
    intro f hf N code hsmall
    let formula :=
      PAHilbertFormula.ofFormulaCode
        (scale_data.powerBoundRawCode (data.witness f hf N))
    let finiteList := PAHilbertFiniteRangeCodeList (data.cutoff f hf N)
    have hrejects :
        ∀ candidate : Nat,
          candidate ∈ finiteList.codes →
            checker.rejectsCode candidate formula = true := by
      intro candidate hmem
      have hcandidate_lt : candidate < data.cutoff f hf N := by
        exact List.mem_range.mp hmem
      exact data.rejectsCode_lt_cutoff f hf N candidate hcandidate_lt
    have hno :
        PAHilbertNoSmallAcceptedProofCodeForFormulaCode
          checker formula.code finiteList.bound :=
      paper.rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
        formula finiteList hrejects
    have hformulaCode :
        formula.code =
          scale_data.powerBoundRawCode (data.witness f hf N) :=
      rfl
    rw [← hformulaCode]
    exact hno code hsmall

def toCheckerExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (paper :
      PAHilbertCheckerPaperProofInterface checker semantics)
    (data :
      PAHilbertAcceptedNatCodeCheckerRejectionData scale_data checker) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion)
      (PAHilbertAcceptedNatCodeFiniteEnumeration
        scale_data checker completion) :=
  (data.toAcceptedNatCodeRejectionExtractorData paper).toCheckerExtractor

theorem toCheckerExtractor_rejects_candidates
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (paper :
      PAHilbertCheckerPaperProofInterface checker semantics)
    (data :
      PAHilbertAcceptedNatCodeCheckerRejectionData scale_data checker)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat)
    (code : Nat)
    (hmem :
      code ∈
        (PAHilbertAcceptedNatCodeFiniteEnumeration
          scale_data checker completion).candidates
            (data.witness f hf N) (data.cutoff f hf N)) :
    ¬
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).checks code
          (scale_data.powerBoundRawCode (data.witness f hf N)) :=
  (data.toCheckerExtractor paper).rejects_candidates
    f hf N code hmem

/-- Exact constructor trace for the executable accepted-code rejection route.
The generated internal rejection extractor keeps the same witness and cutoff
functions as the checker-level rejection data, and a concrete `code < cutoff`
bound is enough to obtain the internal semantic rejection. -/
theorem toCheckerExtractor_exact_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (paper :
      PAHilbertCheckerPaperProofInterface checker semantics)
    (data :
      PAHilbertAcceptedNatCodeCheckerRejectionData scale_data checker) :
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      (data.toCheckerExtractor
          (completion := completion) paper).witness f hf N =
          data.witness f hf N ∧
        (data.toCheckerExtractor
            (completion := completion) paper).cutoff f hf N =
            data.cutoff f hf N ∧
          N ≤ data.witness f hf N ∧
            f (data.witness f hf N) < (data.cutoff f hf N : Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        ∀ code : Nat,
          code < data.cutoff f hf N →
            ¬
              (PAHilbertAcceptedNatCodeCheckerSemantics
                scale_data checker completion).checks code
                  (scale_data.powerBoundRawCode (data.witness f hf N))) := by
  refine ⟨?_, ?_⟩
  · intro f hf N
    exact
      ⟨rfl, rfl, data.witness_ge f hf N, data.cutoff_gt f hf N⟩
  · intro f hf N code hlt
    simpa [
      PAHilbertAcceptedNatCodeCheckerRejectionData.toAcceptedNatCodeRejectionExtractorData]
      using
      (data.toAcceptedNatCodeRejectionExtractorData paper).rejects_lt_cutoff
        f hf N code hlt

end PAHilbertAcceptedNatCodeCheckerRejectionData

/-- The proof-length exactness residual for the accepted numeric-code checker,
kept separate from the computable finite-search data exactly as required by
the Month 9-10 bridge. -/
structure PAHilbertAcceptedNatCodeProofLengthExactnessData
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker) : Prop where
  proof_length_eq_minProofCodeSize :
    ∀ code : _root_.FormulaCode,
      ∀ hcode : InternalPudlakTheorem5PowerBoundRelevantCode scale_data code,
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize code =
          (((PAHilbertAcceptedNatCodeCheckerSemantics
              scale_data checker completion).toProofCodeSemantics
              |>.minProofCodeSize code hcode) : Real)

theorem PAHilbertAcceptedNatCodeProofLengthExactnessData.toCheckerExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (data :
      PAHilbertAcceptedNatCodeProofLengthExactnessData
        scale_data checker completion) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion) where
  proof_length_eq_minProofCodeSize :=
    data.proof_length_eq_minProofCodeSize

/-- The four pieces expected by the Month 9-10 checker-native bridge:
checker semantics, finite enumeration, rejection extractor, and proof-length
exactness. -/
structure PAHilbertAcceptedNatCodeFourPiece
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker) : Type (q + 1) where
  completion :
    PAHilbertAcceptedNatCodeCompletion scale_data checker
  rejection_extractor_data :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker
  proof_length_exactness_data :
    PAHilbertAcceptedNatCodeProofLengthExactnessData
      scale_data checker completion

namespace PAHilbertAcceptedNatCodeFourPiece

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (fourPiece :
      PAHilbertAcceptedNatCodeFourPiece scale_data checker) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  PAHilbertAcceptedNatCodeCheckerSemantics
    scale_data checker fourPiece.completion

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (fourPiece :
      PAHilbertAcceptedNatCodeFourPiece scale_data checker) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      fourPiece.checkerSemantics :=
  PAHilbertAcceptedNatCodeFiniteEnumeration
    scale_data checker fourPiece.completion

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (fourPiece :
      PAHilbertAcceptedNatCodeFourPiece scale_data checker) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      fourPiece.checkerSemantics
      fourPiece.finiteEnumeration :=
  fourPiece.rejection_extractor_data.toCheckerExtractor

theorem proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (fourPiece :
      PAHilbertAcceptedNatCodeFourPiece scale_data checker) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      fourPiece.checkerSemantics :=
  fourPiece.proof_length_exactness_data.toCheckerExactness

def computableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (fourPiece :
      PAHilbertAcceptedNatCodeFourPiece scale_data checker) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data :=
  fourPiece.rejectionExtractor.toCheckerComputableSearchProfile

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (fourPiece :
      PAHilbertAcceptedNatCodeFourPiece scale_data checker) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  fourPiece.rejectionExtractor.toComputableFiniteSearchNoSmallCore
    fourPiece.proofLengthExactness

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (fourPiece :
      PAHilbertAcceptedNatCodeFourPiece scale_data checker) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨fourPiece.computableSearchProfile⟩,
    ⟨fourPiece.toComputableFiniteSearchNoSmallCore⟩⟩

end PAHilbertAcceptedNatCodeFourPiece

theorem PAHilbertAcceptedNatCodeCheckerRejectionData.feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (completion :
      PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (paper :
      PAHilbertCheckerPaperProofInterface checker semantics)
    (rejectionData :
      PAHilbertAcceptedNatCodeCheckerRejectionData scale_data checker)
    (proofLengthData :
      PAHilbertAcceptedNatCodeProofLengthExactnessData
        scale_data checker completion) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  let fourPiece : PAHilbertAcceptedNatCodeFourPiece.{0} scale_data checker :=
    { completion := completion
      rejection_extractor_data :=
        rejectionData.toAcceptedNatCodeRejectionExtractorData paper
      proof_length_exactness_data := proofLengthData }
  fourPiece.feeds_month9_month10_checker_bridge

/-! ## Concrete Month 11-12 four-piece package -/

/-- The executable Month 11-12 checker used for the concrete bridge. -/
abbrev concretePAHilbertMonth11Checker : PAHilbertChecker :=
  concretePAHilbertIndexedChecker

/-- Concrete data that turns theorem-5 target formula codes into accepted
canonical PA/Hilbert proof codes for the Month 11 checker. -/
structure ConcretePAHilbertMonth11CompletionInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  codeAt : Nat → Nat
  conclusion_code_eq_powerBoundRawCode :
    ∀ n : Nat,
      (concretePAHilbertCanonicalProofObject (codeAt n)).conclusion.code =
        scale_data.powerBoundRawCode n
  recognizedAt :
    ∀ n : Nat,
      concretePAHilbertAxiomRecognizer.recognizesAny
        (concretePAHilbertCanonicalProofObject (codeAt n)).conclusion =
          true

def ConcretePAHilbertMonth11CompletionInput.toAcceptedNatCodeCompletion
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertMonth11CompletionInput scale_data) :
    PAHilbertAcceptedNatCodeCompletion
      scale_data concretePAHilbertMonth11Checker where
  complete_at_powerBoundRawCode := by
    intro n
    exact
      ⟨input.codeAt n,
        concretePAHilbertIndexedChecker_acceptedProofCode_of_canonical
          (scale_data.powerBoundRawCode n) (input.codeAt n)
          (input.conclusion_code_eq_powerBoundRawCode n)
          (input.recognizedAt n)⟩

/-- Month 9-10 checker semantics induced by the concrete PA/Hilbert checker. -/
abbrev concretePAHilbertMonth11CheckerSemantics
    (scale_data : InternalPudlakTheorem5ScaleData)
    (completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  PAHilbertAcceptedNatCodeCheckerSemantics
    scale_data concretePAHilbertMonth11Checker completion

theorem concretePAHilbertMonth11CheckerSemantics_checks_eq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker)
    (code : Nat) (formulaCode : _root_.FormulaCode) :
    (concretePAHilbertMonth11CheckerSemantics
      scale_data completion).checks code formulaCode =
      PAHilbertAcceptedProofCodeForFormulaCode
        concretePAHilbertMonth11Checker formulaCode code :=
  rfl

/-- Executable finite enumeration for the concrete checker: search all numeric
codes below the cutoff. -/
abbrev concretePAHilbertMonth11FiniteEnumeration
    (scale_data : InternalPudlakTheorem5ScaleData)
    (completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      (concretePAHilbertMonth11CheckerSemantics
        scale_data completion) :=
  PAHilbertAcceptedNatCodeFiniteEnumeration
    scale_data concretePAHilbertMonth11Checker completion

theorem concretePAHilbertMonth11FiniteEnumeration_candidates_eq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker)
    (n K : Nat) :
    (concretePAHilbertMonth11FiniteEnumeration
      scale_data completion).candidates n K =
      List.range K :=
  rfl

/-- Executable rejection fold for a concrete list of numeric codes. -/
def concretePAHilbertMonth11RejectsCodes :
    List Nat → PAHilbertFormula → Bool
  | [], _formula => true
  | code :: codes, formula =>
      concretePAHilbertMonth11Checker.rejectsCode code formula &&
        concretePAHilbertMonth11RejectsCodes codes formula

theorem concretePAHilbertMonth11RejectsCodes_mem
    {codes : List Nat} {formula : PAHilbertFormula}
    (hrejects :
      concretePAHilbertMonth11RejectsCodes codes formula = true)
    {code : Nat}
    (hmem : code ∈ codes) :
    concretePAHilbertMonth11Checker.rejectsCode code formula = true := by
  induction codes with
  | nil =>
      cases hmem
  | cons head tail ih =>
      simp [concretePAHilbertMonth11RejectsCodes] at hrejects
      rcases hrejects with ⟨hhead, htail⟩
      simp at hmem
      rcases hmem with hEq | htailMem
      · simpa [hEq] using hhead
      · exact ih htail htailMem

/-- Executable finite rejection check for all codes below a cutoff. -/
def concretePAHilbertMonth11RejectsBelow
    (scale_data : InternalPudlakTheorem5ScaleData)
    (n K : Nat) : Bool :=
  concretePAHilbertMonth11RejectsCodes
    (List.range K)
    (PAHilbertFormula.ofFormulaCode
      (scale_data.powerBoundRawCode n))

theorem concretePAHilbertMonth11RejectsBelow_sound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {n K code : Nat}
    (hrejects :
      concretePAHilbertMonth11RejectsBelow scale_data n K = true)
    (hsmall : code < K) :
    concretePAHilbertMonth11Checker.rejectsCode code
      (PAHilbertFormula.ofFormulaCode
        (scale_data.powerBoundRawCode n)) = true :=
  concretePAHilbertMonth11RejectsCodes_mem
    (by
      simpa [concretePAHilbertMonth11RejectsBelow] using hrejects)
    (List.mem_range.mpr hsmall)

/-- Concrete residual input for the rejection extractor.  Its payload is fully
executable at the checker boundary: every searched code below the cutoff is
rejected by the concrete checker for the theorem-5 target formula. -/
abbrev ConcretePAHilbertMonth11RejectionExtractorInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type :=
  PAHilbertAcceptedNatCodeCheckerRejectionData
    scale_data concretePAHilbertMonth11Checker

/-- Executable schedule for the concrete rejection extractor: the witness and
cutoff are accompanied by a Boolean finite sweep over `List.range cutoff`. -/
structure ConcretePAHilbertMonth11ExecutableRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejectsBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      concretePAHilbertMonth11RejectsBelow
        scale_data (witness f hf N) (cutoff f hf N) = true

def ConcretePAHilbertMonth11ExecutableRejectionSearchInput.toRejectionExtractorInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertMonth11ExecutableRejectionSearchInput scale_data) :
    ConcretePAHilbertMonth11RejectionExtractorInput scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  rejectsCode_lt_cutoff := by
    intro f hf N code hsmall
    exact
      concretePAHilbertMonth11RejectsBelow_sound
        (input.rejectsBelow f hf N) hsmall

def ConcretePAHilbertMonth11RejectionExtractorInput.toAcceptedNatCodeData
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertMonth11RejectionExtractorInput scale_data) :
    PAHilbertAcceptedNatCodeRejectionExtractorData
      scale_data concretePAHilbertMonth11Checker :=
  PAHilbertAcceptedNatCodeCheckerRejectionData.toAcceptedNatCodeRejectionExtractorData
    concretePAHilbertIndexedPaperProofInterface
    input

def ConcretePAHilbertMonth11RejectionExtractorInput.toCheckerExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker}
    (input :
      ConcretePAHilbertMonth11RejectionExtractorInput scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      (concretePAHilbertMonth11CheckerSemantics scale_data completion)
      (concretePAHilbertMonth11FiniteEnumeration scale_data completion) :=
  PAHilbertAcceptedNatCodeCheckerRejectionData.toCheckerExtractor
    (completion := completion)
    concretePAHilbertIndexedPaperProofInterface
    input

/-- Search-only exact trace for the concrete Month 11 rejection extractor.  This
avoids the four-piece package because that package also carries proof-length
exactness data. -/
theorem ConcretePAHilbertMonth11RejectionExtractorInput.toCheckerExtractor_exact_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker}
    (input :
      ConcretePAHilbertMonth11RejectionExtractorInput scale_data) :
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      (input.toCheckerExtractor
          (completion := completion)).witness f hf N =
          input.witness f hf N ∧
        (input.toCheckerExtractor
            (completion := completion)).cutoff f hf N =
            input.cutoff f hf N ∧
          N ≤ input.witness f hf N ∧
            f (input.witness f hf N) < (input.cutoff f hf N : Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        ∀ code : Nat,
          code < input.cutoff f hf N →
            ¬
              (concretePAHilbertMonth11CheckerSemantics
                scale_data completion).checks code
                  (scale_data.powerBoundRawCode (input.witness f hf N))) := by
  simpa [
    ConcretePAHilbertMonth11RejectionExtractorInput.toCheckerExtractor,
    concretePAHilbertMonth11CheckerSemantics]
    using
      PAHilbertAcceptedNatCodeCheckerRejectionData.toCheckerExtractor_exact_trace
        (completion := completion)
        concretePAHilbertIndexedPaperProofInterface
        input

/-- Concrete residual input for proof-length exactness of the induced numeric
checker semantics. -/
abbrev ConcretePAHilbertMonth11ProofLengthExactnessInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker) : Prop :=
  PAHilbertAcceptedNatCodeProofLengthExactnessData
    scale_data concretePAHilbertMonth11Checker completion

/-- More local proof-length calibration: it is enough to prove equality on
the theorem-5 `powerBoundRawCode` family, because that is exactly the relevant
formula-code family consumed by the Month 9-10 bridge. -/
structure ConcretePAHilbertMonth11ProofLengthCalibrationAtPowerBound
    (scale_data : InternalPudlakTheorem5ScaleData)
    (completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker) : Prop where
  proof_length_eq_minProofCodeSize_at :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        ((concretePAHilbertMonth11CheckerSemantics
            scale_data completion).minProofCodeSizeAt n : Real)

def ConcretePAHilbertMonth11ProofLengthCalibrationAtPowerBound.toExactnessInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker}
    (calibration :
      ConcretePAHilbertMonth11ProofLengthCalibrationAtPowerBound
        scale_data completion) :
    ConcretePAHilbertMonth11ProofLengthExactnessInput
      scale_data completion where
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩
    simpa [hcode_eq,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt] using
      calibration.proof_length_eq_minProofCodeSize_at n

theorem ConcretePAHilbertMonth11ProofLengthExactnessInput.toCheckerExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data concretePAHilbertMonth11Checker}
    (input :
      ConcretePAHilbertMonth11ProofLengthExactnessInput
        scale_data completion) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertMonth11CheckerSemantics scale_data completion) :=
  PAHilbertAcceptedNatCodeProofLengthExactnessData.toCheckerExactness
    input

/-- The four concrete Month 11-12 pieces required by the Month 9-10 checker
bridge: checker semantics, finite enumeration, rejection extractor, and
proof-length exactness. -/
structure ConcretePAHilbertMonth11FourPiece
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  completion :
    PAHilbertAcceptedNatCodeCompletion
      scale_data concretePAHilbertMonth11Checker
  rejection_extractor_input :
    ConcretePAHilbertMonth11RejectionExtractorInput scale_data
  proof_length_exactness_input :
    ConcretePAHilbertMonth11ProofLengthExactnessInput
      scale_data completion

namespace ConcretePAHilbertMonth11FourPiece

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  concretePAHilbertMonth11CheckerSemantics
    scale_data fourPiece.completion

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      fourPiece.checkerSemantics :=
  concretePAHilbertMonth11FiniteEnumeration
    scale_data fourPiece.completion

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      fourPiece.checkerSemantics
      fourPiece.finiteEnumeration :=
  fourPiece.rejection_extractor_input.toCheckerExtractor

theorem proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      fourPiece.checkerSemantics :=
  fourPiece.proof_length_exactness_input.toCheckerExactness

def toAcceptedNatCodeFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    PAHilbertAcceptedNatCodeFourPiece.{0}
      scale_data concretePAHilbertMonth11Checker where
  completion := fourPiece.completion
  rejection_extractor_data :=
    fourPiece.rejection_extractor_input.toAcceptedNatCodeData
  proof_length_exactness_data :=
    fourPiece.proof_length_exactness_input

def computableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data :=
  fourPiece.rejectionExtractor.toCheckerComputableSearchProfile

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  fourPiece.rejectionExtractor.toComputableFiniteSearchNoSmallCore
    fourPiece.proofLengthExactness

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertMonth11FourPiece scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨fourPiece.computableSearchProfile⟩,
    ⟨fourPiece.toComputableFiniteSearchNoSmallCore⟩⟩

end ConcretePAHilbertMonth11FourPiece

/-! ## PowerBound checker four-piece package -/

/-- Rejection input for the scale-dependent powerBound checker. -/
abbrev ConcretePAHilbertPowerBoundRejectionExtractorInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type :=
  PAHilbertAcceptedNatCodeCheckerRejectionData
    scale_data (concretePAHilbertPowerBoundChecker scale_data)

/-- Executable rejection fold for the scale-dependent powerBound checker. -/
def concretePAHilbertPowerBoundRejectsCodes
    (scale_data : InternalPudlakTheorem5ScaleData) :
    List Nat → PAHilbertFormula → Bool
  | [], _formula => true
  | code :: codes, formula =>
      (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
          code formula &&
        concretePAHilbertPowerBoundRejectsCodes scale_data codes formula

theorem concretePAHilbertPowerBoundRejectsCodes_mem
    {scale_data : InternalPudlakTheorem5ScaleData}
    {codes : List Nat} {formula : PAHilbertFormula}
    (hrejects :
      concretePAHilbertPowerBoundRejectsCodes
        scale_data codes formula = true)
    {code : Nat}
    (hmem : code ∈ codes) :
    (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
      code formula = true := by
  induction codes with
  | nil =>
      cases hmem
  | cons head tail ih =>
      simp [concretePAHilbertPowerBoundRejectsCodes] at hrejects
      rcases hrejects with ⟨hhead, htail⟩
      simp at hmem
      rcases hmem with hEq | htailMem
      · simpa [hEq] using hhead
      · exact ih htail htailMem

/-- Executable finite rejection check for all powerBound checker codes below
a cutoff. -/
def concretePAHilbertPowerBoundRejectsBelow
    (scale_data : InternalPudlakTheorem5ScaleData)
    (n K : Nat) : Bool :=
  concretePAHilbertPowerBoundRejectsCodes
    scale_data
    (List.range K)
    (PAHilbertFormula.ofFormulaCode
      (scale_data.powerBoundRawCode n))

theorem concretePAHilbertPowerBoundRejectsBelow_sound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {n K code : Nat}
    (hrejects :
      concretePAHilbertPowerBoundRejectsBelow scale_data n K = true)
    (hsmall : code < K) :
    (concretePAHilbertPowerBoundChecker scale_data).rejectsCode code
      (PAHilbertFormula.ofFormulaCode
        (scale_data.powerBoundRawCode n)) = true :=
  concretePAHilbertPowerBoundRejectsCodes_mem
    (by
      simpa [concretePAHilbertPowerBoundRejectsBelow] using hrejects)
    (List.mem_range.mpr hsmall)

/-- A powerBound checker rejects a numeric code whenever that code decodes to a
different formula code than the queried formula. -/
theorem concretePAHilbertPowerBoundChecker_rejectsCode_of_formulaCode_ne
    {scale_data : InternalPudlakTheorem5ScaleData}
    {code : Nat} {formula : PAHilbertFormula}
    (hne :
      (concretePAHilbertPowerBoundProofObject
        scale_data code).conclusion.code ≠ formula.code) :
    (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
      code formula = true := by
  classical
  simp [concretePAHilbertPowerBoundChecker, hne]

theorem concretePAHilbertPowerBoundChecker_rejectsCode_of_powerBoundRawCode_ne
    {scale_data : InternalPudlakTheorem5ScaleData}
    {code n : Nat}
    (hne :
      scale_data.powerBoundRawCode code ≠
        scale_data.powerBoundRawCode n) :
    (concretePAHilbertPowerBoundChecker scale_data).rejectsCode code
      (PAHilbertFormula.ofFormulaCode
        (scale_data.powerBoundRawCode n)) = true :=
  concretePAHilbertPowerBoundChecker_rejectsCode_of_formulaCode_ne
    (by
      simpa [concretePAHilbertPowerBoundProofObject,
        concretePAHilbertPowerBoundFormula,
        PAHilbertFormula.ofFormulaCode] using hne)

theorem concretePAHilbertPowerBoundRejectsCodes_of_forall
    {scale_data : InternalPudlakTheorem5ScaleData}
    {codes : List Nat} {formula : PAHilbertFormula}
    (hall :
      ∀ code : Nat, code ∈ codes →
        (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
          code formula = true) :
    concretePAHilbertPowerBoundRejectsCodes
      scale_data codes formula = true := by
  induction codes with
  | nil =>
      rfl
  | cons head tail ih =>
      have hhead :
          (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
            head formula = true :=
        hall head (by simp)
      have htail :
          ∀ code : Nat, code ∈ tail →
            (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
              code formula = true := by
        intro code hmem
        exact hall code (by simp [hmem])
      simp [concretePAHilbertPowerBoundRejectsCodes, hhead, ih htail]

theorem concretePAHilbertPowerBoundRejectsBelow_of_forall_lt
    {scale_data : InternalPudlakTheorem5ScaleData}
    {n K : Nat}
    (hall :
      ∀ code : Nat, code < K →
        (concretePAHilbertPowerBoundChecker scale_data).rejectsCode code
          (PAHilbertFormula.ofFormulaCode
            (scale_data.powerBoundRawCode n)) = true) :
    concretePAHilbertPowerBoundRejectsBelow scale_data n K = true :=
  concretePAHilbertPowerBoundRejectsCodes_of_forall
    (by
      intro code hmem
      exact hall code (List.mem_range.mp hmem))

theorem concretePAHilbertPowerBoundRejectsBelow_of_noCollisionBelow
    {scale_data : InternalPudlakTheorem5ScaleData}
    {n K : Nat}
    (hnoCollision :
      ∀ code : Nat, code < K →
        scale_data.powerBoundRawCode code ≠
          scale_data.powerBoundRawCode n) :
    concretePAHilbertPowerBoundRejectsBelow scale_data n K = true :=
  concretePAHilbertPowerBoundRejectsBelow_of_forall_lt
    (by
      intro code hsmall
      exact
        concretePAHilbertPowerBoundChecker_rejectsCode_of_powerBoundRawCode_ne
          (hnoCollision code hsmall))

/-- Executable schedule for the powerBound rejection extractor.  The Prop
payload is reduced to a Boolean sweep over the concrete finite candidate list. -/
structure ConcretePAHilbertPowerBoundExecutableRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejectsBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      concretePAHilbertPowerBoundRejectsBelow
        scale_data (witness f hf N) (cutoff f hf N) = true

def ConcretePAHilbertPowerBoundExecutableRejectionSearchInput.toRejectionExtractorInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundExecutableRejectionSearchInput scale_data) :
    ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  rejectsCode_lt_cutoff := by
    intro f hf N code hsmall
    exact
      concretePAHilbertPowerBoundRejectsBelow_sound
        (input.rejectsBelow f hf N) hsmall

/-- Rejection schedule stated as the exact semantic condition needed by the
powerBound checker: no searched code below the cutoff decodes to the target
formula code. -/
structure ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  noCollisionBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code < cutoff f hf N →
          scale_data.powerBoundRawCode code ≠
            scale_data.powerBoundRawCode (witness f hf N)

def ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput.toExecutableRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundExecutableRejectionSearchInput
      scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  rejectsBelow := by
    intro f hf N
    exact
      concretePAHilbertPowerBoundRejectsBelow_of_noCollisionBelow
        (input.noCollisionBelow f hf N)

def ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput.toRejectionExtractorInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data :=
  input.toExecutableRejectionSearchInput.toRejectionExtractorInput

/-- A convenient sufficient condition for no-collision search: the theorem-5
formula-code family is injective and the cutoff stays at or below the witness. -/
structure ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  cutoff_le_witness :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      cutoff f hf N ≤ witness f hf N
  powerBoundRawCode_injective :
    Function.Injective scale_data.powerBoundRawCode

def ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput.toNoCollisionRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput
      scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  noCollisionBelow := by
    intro f hf N code hsmall heq
    have hcode_eq :
        code = input.witness f hf N :=
      input.powerBoundRawCode_injective heq
    have hlt :
        code < input.witness f hf N :=
      lt_of_lt_of_le hsmall (input.cutoff_le_witness f hf N)
    rw [hcode_eq] at hlt
    exact (Nat.lt_irrefl (input.witness f hf N)) hlt

def ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput.toExecutableRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundExecutableRejectionSearchInput
      scale_data :=
  input.toNoCollisionRejectionSearchInput.toExecutableRejectionSearchInput

def ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput.toRejectionExtractorInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data :=
  input.toNoCollisionRejectionSearchInput.toRejectionExtractorInput

/-- Search input stated on the underlying theorem-5 scale values.  This is
weaker than requiring a global injective scale plus `cutoff ≤ witness`: it only
requires no scale collision inside the finite search interval. -/
structure ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  scaleNoCollisionBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code < cutoff f hf N →
          scale_data.scale code ≠ scale_data.scale (witness f hf N)

def ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput.toNoCollisionRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput
      scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  noCollisionBelow := by
    intro f hf N code hsmall
    exact
      concretePAHilbert_powerBoundRawCode_ne_of_scale_ne
        scale_data (input.scaleNoCollisionBelow f hf N code hsmall)

def ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput.toExecutableRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundExecutableRejectionSearchInput
      scale_data :=
  input.toNoCollisionRejectionSearchInput.toExecutableRejectionSearchInput

def ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput.toRejectionExtractorInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data :=
  input.toNoCollisionRejectionSearchInput.toRejectionExtractorInput

/-- Proof-length exactness input for the scale-dependent powerBound checker.
The completion field is now concrete, not supplied by the caller. -/
abbrev ConcretePAHilbertPowerBoundProofLengthExactnessInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  PAHilbertAcceptedNatCodeProofLengthExactnessData
    scale_data
    (concretePAHilbertPowerBoundChecker scale_data)
    (concretePAHilbertPowerBoundCompletion scale_data)

/-- Checker semantics induced by the scale-dependent powerBound checker. -/
abbrev concretePAHilbertPowerBoundCheckerSemantics
    (scale_data : InternalPudlakTheorem5ScaleData) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  PAHilbertAcceptedNatCodeCheckerSemantics
    scale_data
    (concretePAHilbertPowerBoundChecker scale_data)
    (concretePAHilbertPowerBoundCompletion scale_data)

/-- Soundness of the concrete powerBound checker semantics, stated directly at
the Month 9-10 checker interface and proved through the paper-proof interface
only. -/
theorem concretePAHilbertPowerBoundCheckerSemantics_checks_to_formulaCode_derivable
    (scale_data : InternalPudlakTheorem5ScaleData)
    (code : (concretePAHilbertPowerBoundCheckerSemantics scale_data).Code)
    (formulaCode : _root_.FormulaCode)
    (hchecks :
      (concretePAHilbertPowerBoundCheckerSemantics scale_data).checks
        code formulaCode) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics formulaCode :=
  concretePAHilbertPowerBoundPaperProofInterface_accepted_code_to_formulaCode_derivable
    scale_data formulaCode code hchecks

/-- The same soundness bridge after forgetting the concrete checker to the
generic `ProofCodeSemantics` surface consumed by the Month 9-10 lower-bound
machinery. -/
theorem concretePAHilbertPowerBoundProofCodeSemantics_checks_to_formulaCode_derivable
    (scale_data : InternalPudlakTheorem5ScaleData)
    (code :
      (concretePAHilbertPowerBoundCheckerSemantics
        scale_data).toProofCodeSemantics.Code)
    (formulaCode : _root_.FormulaCode)
    (hchecks :
      (concretePAHilbertPowerBoundCheckerSemantics
        scale_data).toProofCodeSemantics.checks code formulaCode) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics formulaCode :=
  concretePAHilbertPowerBoundCheckerSemantics_checks_to_formulaCode_derivable
    scale_data code formulaCode hchecks

theorem concretePAHilbertPowerBound_acceptedProofCode_to_powerBoundRawCode_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {formulaCode : _root_.FormulaCode} {code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode code) :
    scale_data.powerBoundRawCode code = formulaCode := by
  rcases haccepted with
    ⟨proof, hdecode, hconclusionCode, _haccepts⟩
  simp [concretePAHilbertPowerBoundChecker,
    concretePAHilbertPowerBoundProofObjectDecoder] at hdecode
  subst proof
  simpa [concretePAHilbertPowerBoundProofObject,
    concretePAHilbertPowerBoundFormula,
    PAHilbertFormula.ofFormulaCode] using hconclusionCode

theorem concretePAHilbertPowerBound_minProofCodeSizeAt_le_self
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
      (concretePAHilbertPowerBoundCheckerSemantics scale_data) n ≤ n := by
  let sem :=
    (concretePAHilbertPowerBoundCheckerSemantics
      scale_data).toProofCodeSemantics
  have hhas :
      sem.HasProofCodeOfSize (scale_data.powerBoundRawCode n) n := by
    refine ⟨n, ?_, le_rfl⟩
    change
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) n
    exact
      concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
        scale_data n
  simpa [InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt,
    sem] using
    sem.minProofCodeSize_le_of_hasProofCodeOfSize
      (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ hhas

theorem concretePAHilbertPowerBound_minProofCodeSizeAt_ge_self_of_noCollisionBelow
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat)
    (hnoCollisionBelow :
      ∀ code : Nat, code < n →
        scale_data.powerBoundRawCode code ≠
          scale_data.powerBoundRawCode n) :
    n ≤
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        (concretePAHilbertPowerBoundCheckerSemantics scale_data) n := by
  classical
  let checkerSem :=
    concretePAHilbertPowerBoundCheckerSemantics scale_data
  let sem := checkerSem.toProofCodeSemantics
  let minSize :=
    sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩
  by_contra hnot
  have hmin_lt : minSize < n := by
    exact Nat.lt_of_not_ge hnot
  have hspec :
      ∃ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          (concretePAHilbertPowerBoundChecker scale_data)
          (scale_data.powerBoundRawCode n) code ∧
            code ≤ minSize := by
    have hfind :
        sem.HasProofCodeOfSize
          (scale_data.powerBoundRawCode n) minSize :=
      sem.hasProofCodeOfSize_minProofCodeSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    simpa [ProofCodeSemantics.HasProofCodeOfSize, sem, checkerSem,
      InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
      concretePAHilbertPowerBoundCheckerSemantics,
      PAHilbertAcceptedNatCodeCheckerSemantics] using hfind
  rcases hspec with ⟨code, haccepted, hcode_le_min⟩
  have hcode_eq :
      scale_data.powerBoundRawCode code =
        scale_data.powerBoundRawCode n :=
    concretePAHilbertPowerBound_acceptedProofCode_to_powerBoundRawCode_eq
      haccepted
  have hcode_lt : code < n :=
    lt_of_le_of_lt hcode_le_min hmin_lt
  exact (hnoCollisionBelow code hcode_lt) hcode_eq

theorem concretePAHilbertPowerBound_minProofCodeSizeAt_eq_self_of_noCollisionBelow
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat)
    (hnoCollisionBelow :
      ∀ code : Nat, code < n →
        scale_data.powerBoundRawCode code ≠
          scale_data.powerBoundRawCode n) :
    InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
      (concretePAHilbertPowerBoundCheckerSemantics scale_data) n = n :=
  le_antisymm
    (concretePAHilbertPowerBound_minProofCodeSizeAt_le_self scale_data n)
    (concretePAHilbertPowerBound_minProofCodeSizeAt_ge_self_of_noCollisionBelow
      scale_data n hnoCollisionBelow)

theorem concretePAHilbertPowerBound_noCollisionBelowSelf_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    ∀ n : Nat, ∀ code : Nat, code < n →
      scale_data.powerBoundRawCode code ≠
        scale_data.powerBoundRawCode n := by
  intro n code hlt heq
  have hcode_eq : code = n :=
    hinjective heq
  rw [hcode_eq] at hlt
  exact (Nat.lt_irrefl n) hlt

/-- Local proof-length calibration for the concrete powerBound checker.  This
is exactly the theorem-5 target family; the conversion below expands it to the
relevant-code statement consumed by Month 9-10. -/
structure ConcretePAHilbertPowerBoundProofLengthCalibrationAtPowerBound
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop where
  proof_length_eq_minProofCodeSize_at :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
          (PAHilbertAcceptedNatCodeCheckerSemantics
            scale_data
            (concretePAHilbertPowerBoundChecker scale_data)
            (concretePAHilbertPowerBoundCompletion scale_data))
          n : Real)

def ConcretePAHilbertPowerBoundProofLengthCalibrationAtPowerBound.toExactnessInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (calibration :
      ConcretePAHilbertPowerBoundProofLengthCalibrationAtPowerBound
        scale_data) :
    ConcretePAHilbertPowerBoundProofLengthExactnessInput scale_data where
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩
    simpa [hcode_eq,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt] using
      calibration.proof_length_eq_minProofCodeSize_at n

/-- More concrete proof-length input for the powerBound checker: once the
checker's minimum code for `powerBoundRawCode n` is computed to be `n`, it is
enough to calibrate the project-level proof length against that same index. -/
structure ConcretePAHilbertPowerBoundProofLengthByIndexInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop where
  noCollisionBelowSelf :
    ∀ n : Nat, ∀ code : Nat, code < n →
      scale_data.powerBoundRawCode code ≠
        scale_data.powerBoundRawCode n
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

def ConcretePAHilbertPowerBoundProofLengthByIndexInput.toCalibrationAtPowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundProofLengthByIndexInput scale_data) :
    ConcretePAHilbertPowerBoundProofLengthCalibrationAtPowerBound
      scale_data where
  proof_length_eq_minProofCodeSize_at := by
    intro n
    have hmin :
        InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
          (concretePAHilbertPowerBoundCheckerSemantics scale_data) n = n :=
      concretePAHilbertPowerBound_minProofCodeSizeAt_eq_self_of_noCollisionBelow
        scale_data n (input.noCollisionBelowSelf n)
    simpa [hmin] using input.proof_length_eq_index n

def ConcretePAHilbertPowerBoundProofLengthByIndexInput.toExactnessInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundProofLengthByIndexInput scale_data) :
    ConcretePAHilbertPowerBoundProofLengthExactnessInput scale_data :=
  input.toCalibrationAtPowerBound.toExactnessInput

def ConcretePAHilbertPowerBoundRejectionExtractorInput.toAcceptedNatCodeData
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data) :
    PAHilbertAcceptedNatCodeRejectionExtractorData
      scale_data (concretePAHilbertPowerBoundChecker scale_data) :=
  PAHilbertAcceptedNatCodeCheckerRejectionData.toAcceptedNatCodeRejectionExtractorData
    (concretePAHilbertPowerBoundPaperProofInterface scale_data)
    input

def ConcretePAHilbertPowerBoundRejectionExtractorInput.toCheckerExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data
        (concretePAHilbertPowerBoundChecker scale_data)
        (concretePAHilbertPowerBoundCompletion scale_data))
      (PAHilbertAcceptedNatCodeFiniteEnumeration
        scale_data
        (concretePAHilbertPowerBoundChecker scale_data)
        (concretePAHilbertPowerBoundCompletion scale_data)) :=
  PAHilbertAcceptedNatCodeCheckerRejectionData.toCheckerExtractor
    (completion := concretePAHilbertPowerBoundCompletion scale_data)
    (concretePAHilbertPowerBoundPaperProofInterface scale_data)
    input

/-- Search-only exact trace for the scale-dependent powerBound rejection
extractor.  This is the clean witness/cutoff trace before any proof-length
calibration package is added. -/
theorem ConcretePAHilbertPowerBoundRejectionExtractorInput.toCheckerExtractor_exact_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data) :
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      input.toCheckerExtractor.witness f hf N =
          input.witness f hf N ∧
        input.toCheckerExtractor.cutoff f hf N =
            input.cutoff f hf N ∧
          N ≤ input.witness f hf N ∧
            f (input.witness f hf N) < (input.cutoff f hf N : Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        ∀ code : Nat,
          code < input.cutoff f hf N →
            ¬
              (concretePAHilbertPowerBoundCheckerSemantics
                scale_data).checks code
                  (scale_data.powerBoundRawCode (input.witness f hf N))) := by
  refine ⟨?_, ?_⟩
  · intro f hf N
    exact
      ⟨rfl, rfl,
        input.witness_ge f hf N,
        input.cutoff_gt f hf N⟩
  · intro f hf N code hsmall
    simpa [
      concretePAHilbertPowerBoundCheckerSemantics,
      PAHilbertAcceptedNatCodeCheckerSemantics,
      ConcretePAHilbertPowerBoundRejectionExtractorInput.toAcceptedNatCodeData,
      PAHilbertAcceptedNatCodeCheckerRejectionData.toAcceptedNatCodeRejectionExtractorData] using
      (input.toAcceptedNatCodeData
        |>.rejects_lt_cutoff f hf N code hsmall)

/-- Four-piece package for the theorem-5 powerBound checker.  Compared with
`ConcretePAHilbertMonth11FourPiece`, the completion proof is already concrete:
code `n` decodes to a proof object whose conclusion is exactly
`scale_data.powerBoundRawCode n`. -/
structure ConcretePAHilbertPowerBoundFourPiece
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_extractor_input :
    ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data
  proof_length_exactness_input :
    ConcretePAHilbertPowerBoundProofLengthExactnessInput scale_data

/-- Fully constructive-facing input for the powerBound route.  The rejection
side is a Boolean finite sweep, while the length side is a pointwise
calibration on the theorem-5 target family. -/
structure ConcretePAHilbertPowerBoundExecutableFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundExecutableRejectionSearchInput scale_data
  proof_length_calibration :
    ConcretePAHilbertPowerBoundProofLengthCalibrationAtPowerBound scale_data

/-- Four-piece input using the exact no-collision condition for finite
rejection. -/
structure ConcretePAHilbertPowerBoundNoCollisionFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput scale_data
  proof_length_calibration :
    ConcretePAHilbertPowerBoundProofLengthCalibrationAtPowerBound scale_data

/-- Four-piece input using the injective-family sufficient condition for finite
rejection. -/
structure ConcretePAHilbertPowerBoundInjectiveFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput scale_data
  proof_length_calibration :
    ConcretePAHilbertPowerBoundProofLengthCalibrationAtPowerBound scale_data

/-- Four-piece input with proof-length calibration reduced to the index of the
powerBound formula code. -/
structure ConcretePAHilbertPowerBoundByIndexFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundNoCollisionRejectionSearchInput scale_data
  proof_length_by_index :
    ConcretePAHilbertPowerBoundProofLengthByIndexInput scale_data

/-- By-index input using scale-level no-collision both for finite rejection and
for the minimum-code computation in proof-length calibration. -/
structure ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundScaleNoCollisionRejectionSearchInput scale_data
  scaleNoCollisionBelowSelf :
    ∀ n : Nat, ∀ code : Nat, code < n →
      scale_data.scale code ≠ scale_data.scale n
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

/-- Most compressed current powerBound input: one injectivity proof drives both
the finite rejection no-collision condition and the proof-length minimum-code
calculation; the remaining proof-length payload is the project-level equality
`proof_length (powerBoundRawCode n) = n`. -/
structure ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput scale_data
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

/-- Scale-injective variant of the compressed powerBound input.  The raw-code
injectivity needed by finite rejection and proof-length minimality is derived
from injectivity of the theorem-5 scale itself. -/
structure ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  cutoff_le_witness :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      cutoff f hf N ≤ witness f hf N
  scale_injective : Function.Injective scale_data.scale
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

namespace ConcretePAHilbertPowerBoundFourPiece

def completion
    {scale_data : InternalPudlakTheorem5ScaleData}
    (_fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    PAHilbertAcceptedNatCodeCompletion
      scale_data (concretePAHilbertPowerBoundChecker scale_data) :=
  concretePAHilbertPowerBoundCompletion scale_data

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  PAHilbertAcceptedNatCodeCheckerSemantics
    scale_data
    (concretePAHilbertPowerBoundChecker scale_data)
    fourPiece.completion

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      fourPiece.checkerSemantics :=
  PAHilbertAcceptedNatCodeFiniteEnumeration
    scale_data
    (concretePAHilbertPowerBoundChecker scale_data)
    fourPiece.completion

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      fourPiece.checkerSemantics
      fourPiece.finiteEnumeration :=
  fourPiece.rejection_extractor_input.toCheckerExtractor

theorem proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      fourPiece.checkerSemantics :=
  fourPiece.proof_length_exactness_input.toCheckerExactness

def toAcceptedNatCodeFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    PAHilbertAcceptedNatCodeFourPiece.{0}
      scale_data (concretePAHilbertPowerBoundChecker scale_data) where
  completion := fourPiece.completion
  rejection_extractor_data :=
    fourPiece.rejection_extractor_input.toAcceptedNatCodeData
  proof_length_exactness_data :=
    fourPiece.proof_length_exactness_input

def computableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data :=
  fourPiece.rejectionExtractor.toCheckerComputableSearchProfile

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  fourPiece.rejectionExtractor.toComputableFiniteSearchNoSmallCore
    fourPiece.proofLengthExactness

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨fourPiece.computableSearchProfile⟩,
    ⟨fourPiece.toComputableFiniteSearchNoSmallCore⟩⟩

end ConcretePAHilbertPowerBoundFourPiece

namespace ConcretePAHilbertPowerBoundExecutableFourPieceInput

def toFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundExecutableFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundFourPiece scale_data where
  rejection_extractor_input :=
    input.rejection_search.toRejectionExtractorInput
  proof_length_exactness_input :=
    input.proof_length_calibration.toExactnessInput

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundExecutableFourPieceInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundExecutableFourPieceInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundExecutableFourPieceInput

namespace ConcretePAHilbertPowerBoundNoCollisionFourPieceInput

def toExecutableFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundExecutableFourPieceInput scale_data where
  rejection_search :=
    input.rejection_search.toExecutableRejectionSearchInput
  proof_length_calibration :=
    input.proof_length_calibration

def toFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundFourPiece scale_data :=
  input.toExecutableFourPieceInput.toFourPiece

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundNoCollisionFourPieceInput

namespace ConcretePAHilbertPowerBoundInjectiveFourPieceInput

def toNoCollisionFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data where
  rejection_search :=
    input.rejection_search.toNoCollisionRejectionSearchInput
  proof_length_calibration :=
    input.proof_length_calibration

def toExecutableFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundExecutableFourPieceInput scale_data :=
  input.toNoCollisionFourPieceInput.toExecutableFourPieceInput

def toFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundFourPiece scale_data :=
  input.toNoCollisionFourPieceInput.toFourPiece

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveFourPieceInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveFourPieceInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundInjectiveFourPieceInput

namespace ConcretePAHilbertPowerBoundByIndexFourPieceInput

def toNoCollisionFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data where
  rejection_search := input.rejection_search
  proof_length_calibration :=
    input.proof_length_by_index.toCalibrationAtPowerBound

def toExecutableFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundExecutableFourPieceInput scale_data :=
  input.toNoCollisionFourPieceInput.toExecutableFourPieceInput

def toFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data) :
    ConcretePAHilbertPowerBoundFourPiece scale_data :=
  input.toNoCollisionFourPieceInput.toFourPiece

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundByIndexFourPieceInput

namespace ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput

def toByIndexProofLengthInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundProofLengthByIndexInput scale_data where
  noCollisionBelowSelf := by
    intro n code hsmall
    exact
      concretePAHilbert_powerBoundRawCode_ne_of_scale_ne
        scale_data (input.scaleNoCollisionBelowSelf n code hsmall)
  proof_length_eq_index :=
    input.proof_length_eq_index

def toByIndexFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data where
  rejection_search :=
    input.rejection_search.toNoCollisionRejectionSearchInput
  proof_length_by_index :=
    input.toByIndexProofLengthInput

def toNoCollisionFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data :=
  input.toByIndexFourPieceInput.toNoCollisionFourPieceInput

def toFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundFourPiece scale_data :=
  input.toByIndexFourPieceInput.toFourPiece

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundScaleNoCollisionByIndexFourPieceInput

namespace ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput

def toByIndexProofLengthInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundProofLengthByIndexInput scale_data where
  noCollisionBelowSelf :=
    concretePAHilbertPowerBound_noCollisionBelowSelf_of_injective
      input.rejection_search.powerBoundRawCode_injective
  proof_length_eq_index :=
    input.proof_length_eq_index

def toByIndexFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data where
  rejection_search :=
    input.rejection_search.toNoCollisionRejectionSearchInput
  proof_length_by_index :=
    input.toByIndexProofLengthInput

def toNoCollisionFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundNoCollisionFourPieceInput scale_data :=
  input.toByIndexFourPieceInput.toNoCollisionFourPieceInput

def toExecutableFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundExecutableFourPieceInput scale_data :=
  input.toByIndexFourPieceInput.toExecutableFourPieceInput

def toFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundFourPiece scale_data :=
  input.toByIndexFourPieceInput.toFourPiece

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput

namespace ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput

def toInjectiveRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundInjectiveRejectionSearchInput
      scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  cutoff_le_witness := input.cutoff_le_witness
  powerBoundRawCode_injective :=
    concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
      scale_data input.scale_injective

def toInjectiveByIndexFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundInjectiveByIndexFourPieceInput
      scale_data where
  rejection_search :=
    input.toInjectiveRejectionSearchInput
  proof_length_eq_index :=
    input.proof_length_eq_index

def toByIndexFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundByIndexFourPieceInput scale_data :=
  input.toInjectiveByIndexFourPieceInput.toByIndexFourPieceInput

def toFourPiece
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundFourPiece scale_data :=
  input.toInjectiveByIndexFourPieceInput.toFourPiece

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFourPiece.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundScaleInjectiveByIndexFourPieceInput

/-! ## Calibrated-size powerBound checker route -/

/-- PowerBound checker semantics with a calibrated Nat-valued size for each
numeric proof code.  This avoids forcing proof length to equal the numeric code
itself. -/
abbrev concretePAHilbertPowerBoundCalibratedCheckerSemantics
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data where
  Code := Nat
  checks := fun code formulaCode =>
    PAHilbertAcceptedProofCodeForFormulaCode
      (concretePAHilbertPowerBoundChecker scale_data)
      formulaCode code
  size := lengthCodeAt
  complete_at_powerBoundRawCode := by
    intro n
    exact
      ⟨n,
        concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
          scale_data n⟩

theorem concretePAHilbertPowerBound_rejectsCode_to_not_acceptedProofCodeForFormulaCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {formulaCode : _root_.FormulaCode} {code : Nat}
    (hrejects :
      (concretePAHilbertPowerBoundChecker scale_data).rejectsCode code
        (PAHilbertFormula.ofFormulaCode formulaCode) = true) :
    ¬ PAHilbertAcceptedProofCodeForFormulaCode
      (concretePAHilbertPowerBoundChecker scale_data)
      formulaCode code := by
  intro haccepted
  rcases haccepted with
    ⟨proof, hdecode, hconclusionCode, haccepts⟩
  let formula := PAHilbertFormula.ofFormulaCode formulaCode
  have hproofCode : proof.code = code :=
    (concretePAHilbertPowerBoundChecker scale_data).decoder.decodedCode_eq
      code proof hdecode
  have hrejectProof :
      (concretePAHilbertPowerBoundChecker scale_data).rejectsCode
        proof.code formula = true := by
    simpa [formula, hproofCode] using hrejects
  have hnot :
      (concretePAHilbertPowerBoundChecker scale_data).accepts
        proof formula = false :=
    concretePAHilbertPowerBoundChecker_rejectsCode_to_accepts_false
      scale_data proof formula hrejectProof
  have hformula : proof.conclusion = formula :=
    PAHilbertFormula.eq_of_code_eq
      (by
        simpa [formula, PAHilbertFormula.ofFormulaCode] using
          hconclusionCode)
  have hacceptsFormula :
      (concretePAHilbertPowerBoundChecker scale_data).accepts
        proof formula = true := by
    simpa [hformula] using haccepts
  rw [hnot] at hacceptsFormula
  cases hacceptsFormula

/-- Finite enumeration data for calibrated-size semantics.  A caller provides
a computable code bound large enough to contain all accepted codes whose
calibrated size is below the search cutoff. -/
structure ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) : Type where
  codeBound : Nat → Nat → Nat
  complete_code_lt_bound :
    ∀ n K code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) code →
      lengthCodeAt code < K →
        code < codeBound n K

def ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput.toFiniteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt) where
  candidates := fun n K => List.range (input.codeBound n K)
  complete := by
    intro n K code hchecks hsize
    exact List.mem_range.mpr
      (input.complete_code_lt_bound n K code hchecks hsize)

/-- Computable rejection schedule for calibrated-size semantics.  Rejection is
still executed by a concrete Boolean sweep over numeric codes, but the finite
enumeration may use a code bound different from the size cutoff. -/
structure ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejectsBelowCodeBound :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      concretePAHilbertPowerBoundRejectsBelow
        scale_data
        (witness f hf N)
        (enumeration.codeBound (witness f hf N) (cutoff f hf N)) =
          true

def ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput.toCheckerExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt)
      enumeration.toFiniteEnumeration where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  rejects_candidates := by
    intro f hf N code hmem hchecks
    have hcode_lt :
        code <
          enumeration.codeBound
            (input.witness f hf N) (input.cutoff f hf N) :=
      List.mem_range.mp hmem
    have hrejects :
        (concretePAHilbertPowerBoundChecker scale_data).rejectsCode code
          (PAHilbertFormula.ofFormulaCode
            (scale_data.powerBoundRawCode (input.witness f hf N))) =
          true :=
      concretePAHilbertPowerBoundRejectsBelow_sound
        (input.rejectsBelowCodeBound f hf N) hcode_lt
    exact
      concretePAHilbertPowerBound_rejectsCode_to_not_acceptedProofCodeForFormulaCode
        hrejects hchecks

/-- Exact constructor trace for the calibrated executable rejection search.  It
records that the internal Month 9-10 rejection extractor keeps the executable
`witness` and `cutoff` functions unchanged, and that its candidate-rejection
field is precisely the Boolean sweep over the calibrated finite enumeration. -/
theorem ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput.toCheckerExtractor_exact_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      input.toCheckerExtractor.witness f hf N =
          input.witness f hf N ∧
        input.toCheckerExtractor.cutoff f hf N =
            input.cutoff f hf N ∧
          N ≤ input.witness f hf N ∧
            f (input.witness f hf N) < (input.cutoff f hf N : Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        ∀ code : Nat,
          code ∈
              enumeration.toFiniteEnumeration.candidates
                (input.witness f hf N) (input.cutoff f hf N) →
            ¬
              (concretePAHilbertPowerBoundCalibratedCheckerSemantics
                scale_data lengthCodeAt).checks code
                  (scale_data.powerBoundRawCode (input.witness f hf N))) := by
  refine ⟨?_, ?_⟩
  · intro f hf N
    exact
      ⟨rfl, rfl,
        input.witness_ge f hf N,
        input.cutoff_gt f hf N⟩
  · intro f hf N code hmem
    exact input.toCheckerExtractor.rejects_candidates f hf N code hmem

/-- Code-bound form of the calibrated executable rejection sweep.  This is the
lowest-level audit statement used by the finite-search route: every numeric
code below the calibrated enumeration bound is rejected by the concrete
powerBound checker, hence cannot satisfy the calibrated Month 9-10 checker
semantics at the same theorem-5 target. -/
theorem ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput.rejects_of_code_lt_codeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat)
    (code : Nat)
    (hcode_lt :
      code <
        enumeration.codeBound
          (input.witness f hf N) (input.cutoff f hf N)) :
    (concretePAHilbertPowerBoundChecker scale_data).rejectsCode code
        (PAHilbertFormula.ofFormulaCode
          (scale_data.powerBoundRawCode (input.witness f hf N))) = true ∧
      ¬
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).checks code
            (scale_data.powerBoundRawCode (input.witness f hf N)) := by
  have hrejects :
      (concretePAHilbertPowerBoundChecker scale_data).rejectsCode code
        (PAHilbertFormula.ofFormulaCode
          (scale_data.powerBoundRawCode (input.witness f hf N))) = true :=
    concretePAHilbertPowerBoundRejectsBelow_sound
      (input.rejectsBelowCodeBound f hf N) hcode_lt
  exact
    ⟨hrejects,
      fun hchecks =>
        concretePAHilbertPowerBound_rejectsCode_to_not_acceptedProofCodeForFormulaCode
          hrejects hchecks⟩

/-- Proof-length exactness for calibrated-size semantics reduced to a
family-level equality against the calibrated minimum. -/
structure ConcretePAHilbertPowerBoundCalibratedProofLengthInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) : Prop where
  proof_length_eq_minProofCodeSizeAt :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt)
          n : Real)

def ConcretePAHilbertPowerBoundCalibratedProofLengthInput.toCheckerExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt) where
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩
    simpa [hcode_eq,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt] using
      input.proof_length_eq_minProofCodeSizeAt n

theorem concretePAHilbertPowerBoundCalibratedId_minProofCodeSizeAt_eq_self_of_noCollisionBelow
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat)
    (hnoCollisionBelow :
      ∀ code : Nat, code < n →
        scale_data.powerBoundRawCode code ≠
          scale_data.powerBoundRawCode n) :
    InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data id)
      n = n := by
  simpa [concretePAHilbertPowerBoundCheckerSemantics,
    concretePAHilbertPowerBoundCalibratedCheckerSemantics,
    PAHilbertAcceptedNatCodeCheckerSemantics] using
    concretePAHilbertPowerBound_minProofCodeSizeAt_eq_self_of_noCollisionBelow
      scale_data n hnoCollisionBelow

def ConcretePAHilbertPowerBoundProofLengthByIndexInput.toCalibratedIdentityProofLengthInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundProofLengthByIndexInput scale_data) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data id where
  proof_length_eq_minProofCodeSizeAt := by
    intro n
    have hmin :
        InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data id)
          n = n :=
      concretePAHilbertPowerBoundCalibratedId_minProofCodeSizeAt_eq_self_of_noCollisionBelow
        scale_data n (input.noCollisionBelowSelf n)
    simpa [hmin] using input.proof_length_eq_index n

/-- Calibrated-size four-piece package.  This is the non-artificial route for
proof-length exactness: the checker size is calibrated explicitly instead of
being forced to be the numeric code. -/
structure ConcretePAHilbertPowerBoundCalibratedFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  enumeration :
    ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
      scale_data lengthCodeAt
  rejection_search :
    ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
      scale_data lengthCodeAt enumeration
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data lengthCodeAt

namespace ConcretePAHilbertPowerBoundCalibratedFourPieceInput

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  concretePAHilbertPowerBoundCalibratedCheckerSemantics
    scale_data input.lengthCodeAt

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      input.checkerSemantics :=
  input.enumeration.toFiniteEnumeration

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      input.checkerSemantics
      input.finiteEnumeration :=
  input.rejection_search.toCheckerExtractor

theorem proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      input.checkerSemantics :=
  input.proof_length.toCheckerExactness

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.rejectionExtractor.toComputableFiniteSearchNoSmallCore
    input.proofLengthExactness

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨input.rejectionExtractor.toCheckerComputableSearchProfile⟩,
    ⟨input.toComputableFiniteSearchNoSmallCore⟩⟩

end ConcretePAHilbertPowerBoundCalibratedFourPieceInput

/-! ## Dominating-size specialization for calibrated powerBound semantics -/

/-- A calibrated size function that dominates the numeric proof code.  This is
a useful concrete specialization: all codes with calibrated size below `K` are
already contained in `List.range K`, so no separate code-bound function is
needed. -/
structure ConcretePAHilbertPowerBoundDominatingLengthInput
    (_scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  code_le_lengthCodeAt : ∀ code : Nat, code ≤ lengthCodeAt code

def ConcretePAHilbertPowerBoundDominatingLengthInput.toCalibratedFiniteEnumerationInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingLengthInput scale_data) :
    ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
      scale_data input.lengthCodeAt where
  codeBound := fun _n K => K
  complete_code_lt_bound := by
    intro _n _K code _haccepted hsize
    exact lt_of_le_of_lt (input.code_le_lengthCodeAt code) hsize

/-- Rejection schedule for a dominating calibrated size.  Since small
calibrated size implies small numeric code, the executable rejection sweep is
again over `List.range cutoff`. -/
structure ConcretePAHilbertPowerBoundDominatingExecutableRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (length_input :
      ConcretePAHilbertPowerBoundDominatingLengthInput scale_data) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejectsBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      concretePAHilbertPowerBoundRejectsBelow
        scale_data (witness f hf N) (cutoff f hf N) = true

def ConcretePAHilbertPowerBoundDominatingExecutableRejectionSearchInput.toCalibratedRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {length_input :
      ConcretePAHilbertPowerBoundDominatingLengthInput scale_data}
    (input :
      ConcretePAHilbertPowerBoundDominatingExecutableRejectionSearchInput
        scale_data length_input) :
    ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
      scale_data
      length_input.lengthCodeAt
      length_input.toCalibratedFiniteEnumerationInput where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  rejectsBelowCodeBound := by
    intro f hf N
    simpa [
      ConcretePAHilbertPowerBoundDominatingLengthInput.toCalibratedFiniteEnumerationInput]
      using input.rejectsBelow f hf N

/-- Dominating-size calibrated four-piece input.  This keeps the non-artificial
calibrated proof-length route while making finite enumeration/rejection as
simple as the original numeric-code route. -/
structure ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  length_input :
    ConcretePAHilbertPowerBoundDominatingLengthInput scale_data
  rejection_search :
    ConcretePAHilbertPowerBoundDominatingExecutableRejectionSearchInput
      scale_data length_input
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data length_input.lengthCodeAt

namespace ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput

def toCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data where
  lengthCodeAt := input.length_input.lengthCodeAt
  enumeration :=
    input.length_input.toCalibratedFiniteEnumerationInput
  rejection_search :=
    input.rejection_search.toCalibratedRejectionSearchInput
  proof_length :=
    input.proof_length

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput

/-! ## Dominating calibrated route from scale no-collision -/

/-- Rejection schedule for the dominating calibrated route, stated using
scale-level no-collision instead of a precomputed Boolean sweep. -/
structure ConcretePAHilbertPowerBoundDominatingScaleNoCollisionRejectionSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (length_input :
      ConcretePAHilbertPowerBoundDominatingLengthInput scale_data) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  scaleNoCollisionBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code < cutoff f hf N →
          scale_data.scale code ≠ scale_data.scale (witness f hf N)

def ConcretePAHilbertPowerBoundDominatingScaleNoCollisionRejectionSearchInput.toDominatingExecutableRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {length_input :
      ConcretePAHilbertPowerBoundDominatingLengthInput scale_data}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionRejectionSearchInput
        scale_data length_input) :
    ConcretePAHilbertPowerBoundDominatingExecutableRejectionSearchInput
      scale_data length_input where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  rejectsBelow := by
    intro f hf N
    exact
      concretePAHilbertPowerBoundRejectsBelow_of_noCollisionBelow
        (by
          intro code hsmall
          exact
            concretePAHilbert_powerBoundRawCode_ne_of_scale_ne
              scale_data
              (input.scaleNoCollisionBelow f hf N code hsmall))

def ConcretePAHilbertPowerBoundDominatingScaleNoCollisionRejectionSearchInput.toCalibratedRejectionSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {length_input :
      ConcretePAHilbertPowerBoundDominatingLengthInput scale_data}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionRejectionSearchInput
        scale_data length_input) :
    ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
      scale_data
      length_input.lengthCodeAt
      length_input.toCalibratedFiniteEnumerationInput :=
  input.toDominatingExecutableRejectionSearchInput
    |>.toCalibratedRejectionSearchInput

/-- Dominating calibrated four-piece with finite rejection generated from
scale-level no-collision. -/
structure ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  length_input :
    ConcretePAHilbertPowerBoundDominatingLengthInput scale_data
  rejection_search :
    ConcretePAHilbertPowerBoundDominatingScaleNoCollisionRejectionSearchInput
      scale_data length_input
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data length_input.lengthCodeAt

namespace ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput

def toDominatingCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
      scale_data where
  length_input :=
    input.length_input
  rejection_search :=
    input.rejection_search.toDominatingExecutableRejectionSearchInput
  proof_length :=
    input.proof_length

def toCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data :=
  input.toDominatingCalibratedFourPieceInput.toCalibratedFourPieceInput

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput

/-! ## Identity-size specialization for calibrated powerBound semantics -/

/-- Concrete dominating calibrated size: the size of a numeric proof code is
the numeric code itself.  This closes the `lengthCodeAt` selection field while
leaving proof-length exactness as an explicit residual. -/
def concretePAHilbertPowerBoundIdentityDominatingLengthInput
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundDominatingLengthInput scale_data where
  lengthCodeAt := id
  code_le_lengthCodeAt := by
    intro code
    rfl

/-- Identity-size calibrated four-piece input with a direct Boolean finite
rejection sweep. -/
structure ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundDominatingExecutableRejectionSearchInput
      scale_data
      (concretePAHilbertPowerBoundIdentityDominatingLengthInput scale_data)
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data id

namespace ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput

def toDominatingCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
      scale_data where
  length_input :=
    concretePAHilbertPowerBoundIdentityDominatingLengthInput scale_data
  rejection_search :=
    input.rejection_search
  proof_length :=
    input.proof_length

def toCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data :=
  input.toDominatingCalibratedFourPieceInput.toCalibratedFourPieceInput

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput

/-- Identity-size calibrated input whose finite rejection sweep is generated
from scale-level no-collision. -/
structure ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  rejection_search :
    ConcretePAHilbertPowerBoundDominatingScaleNoCollisionRejectionSearchInput
      scale_data
      (concretePAHilbertPowerBoundIdentityDominatingLengthInput scale_data)
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data id

namespace ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput

def toDominatingScaleNoCollisionCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
      scale_data where
  length_input :=
    concretePAHilbertPowerBoundIdentityDominatingLengthInput scale_data
  rejection_search :=
    input.rejection_search
  proof_length :=
    input.proof_length

def toCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data :=
  input.toDominatingScaleNoCollisionCalibratedFourPieceInput
    |>.toCalibratedFourPieceInput

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCalibratedFourPieceInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput

/-! ## Canonical calibrated exactness core -/

/-- Constructive canonical replacement for the impossible unrestricted checker
core.  It keeps the PA/Hilbert checker, recognizer exactness, and
canonical/code-indexed checker interface together with the Month 9-10
checker-native four-piece package. -/
structure PAHilbertCanonicalCalibratedExactnessCore : Type 2 where
  checker : PAHilbertChecker
  semantics : PAHilbertDerivabilitySemantics
  recognizerExactness :
    PAHilbertAxiomRecognizerExactness checker.recognizer semantics
  canonicalInterface :
    PAHilbertCanonicalCheckerInterface checker semantics
  scale_data : InternalPudlakTheorem5ScaleData
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration
  proofLengthExactness :
    InternalPudlakTheorem5CheckerProofLengthExactness checkerSemantics

namespace PAHilbertCanonicalCalibratedExactnessCore

def computableSearchProfile
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      core.scale_data :=
  core.rejectionExtractor.toCheckerComputableSearchProfile

def toComputableFiniteSearchNoSmallCore
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  core.rejectionExtractor.toComputableFiniteSearchNoSmallCore
    core.proofLengthExactness

theorem feeds_month9_month10_checker_bridge
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        core.scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨core.computableSearchProfile⟩,
    ⟨core.toComputableFiniteSearchNoSmallCore⟩⟩

theorem accepted_decoded_code_to_formulaCode_derivable
    (core : PAHilbertCanonicalCalibratedExactnessCore)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        core.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable core.semantics formulaCode :=
  core.canonicalInterface.accepted_decoded_code_to_formulaCode_derivable
    formulaCode code haccepted

end PAHilbertCanonicalCalibratedExactnessCore

def ConcretePAHilbertPowerBoundCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore where
  checker :=
    concretePAHilbertPowerBoundChecker scale_data
  semantics :=
    concretePAHilbertTheorem5DerivabilitySemantics
  recognizerExactness :=
    concretePAHilbertTheorem5AxiomRecognizerExactness
  canonicalInterface :=
    concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data
  scale_data :=
    scale_data
  checkerSemantics :=
    input.checkerSemantics
  finiteEnumeration :=
    input.finiteEnumeration
  rejectionExtractor :=
    input.rejectionExtractor
  proofLengthExactness :=
    input.proofLengthExactness

theorem ConcretePAHilbertPowerBoundCalibratedFourPieceInput.canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

def ConcretePAHilbertPowerBoundFourPiece.toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore where
  checker :=
    concretePAHilbertPowerBoundChecker scale_data
  semantics :=
    concretePAHilbertTheorem5DerivabilitySemantics
  recognizerExactness :=
    concretePAHilbertTheorem5AxiomRecognizerExactness
  canonicalInterface :=
    concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data
  scale_data :=
    scale_data
  checkerSemantics :=
    fourPiece.checkerSemantics
  finiteEnumeration :=
    fourPiece.finiteEnumeration
  rejectionExtractor :=
    fourPiece.rejectionExtractor
  proofLengthExactness :=
    fourPiece.proofLengthExactness

theorem ConcretePAHilbertPowerBoundFourPiece.canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fourPiece : ConcretePAHilbertPowerBoundFourPiece scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨fourPiece.toCanonicalCalibratedExactnessCore⟩

def ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore

theorem ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput.canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

def ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore

theorem ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput.canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

def ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore

theorem ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput.canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityDominatingCalibratedFourPieceInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

def ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toCalibratedFourPieceInput.toCanonicalCalibratedExactnessCore

theorem ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput.canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

/-- Final residual package for the current constructive powerBound route.
Everything already constructed in Month 11-12 is fixed: the checker, decoder,
recognizer, canonical interface, proof-code size `id`, finite enumeration, and
Boolean rejection checker.  The remaining caller-supplied data are exactly the
computed witness/cutoff, scale no-collision over the searched interval, and
calibrated proof-length exactness. -/
structure ConcretePAHilbertPowerBoundFinalResidualInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  scaleNoCollisionBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code < cutoff f hf N →
          scale_data.scale code ≠ scale_data.scale (witness f hf N)
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data id

namespace ConcretePAHilbertPowerBoundFinalResidualInput

def toIdentityScaleNoCollisionCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
      scale_data where
  rejection_search :=
    { witness := input.witness
      cutoff := input.cutoff
      witness_ge := input.witness_ge
      cutoff_gt := input.cutoff_gt
      scaleNoCollisionBelow := input.scaleNoCollisionBelow }
  proof_length :=
    input.proof_length

def toCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data :=
  input.toIdentityScaleNoCollisionCalibratedFourPieceInput
    |>.toCalibratedFourPieceInput

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toIdentityScaleNoCollisionCalibratedFourPieceInput
    |>.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toIdentityScaleNoCollisionCalibratedFourPieceInput
    |>.toComputableFiniteSearchNoSmallCore

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  input.toIdentityScaleNoCollisionCalibratedFourPieceInput
    |>.canonical_core_nonempty

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toIdentityScaleNoCollisionCalibratedFourPieceInput
    |>.feeds_month9_month10_checker_bridge

/-- Materialized certificate for the final residual route.  Unlike the input
record, this stores the concrete canonical core and records that it is still
the same powerBound checker, same derivability semantics, and same Month 9-10
scale data. -/
structure Certificate
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  input :
    ConcretePAHilbertPowerBoundFinalResidualInput scale_data
  canonicalCore :
    PAHilbertCanonicalCalibratedExactnessCore
  sameChecker :
    canonicalCore.checker =
      concretePAHilbertPowerBoundChecker scale_data
  sameSemantics :
    canonicalCore.semantics =
      concretePAHilbertTheorem5DerivabilitySemantics
  sameScaleData :
    canonicalCore.scale_data = scale_data
  noSmallCore :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    Certificate scale_data where
  input := input
  canonicalCore := input.toCanonicalCalibratedExactnessCore
  sameChecker := rfl
  sameSemantics := rfl
  sameScaleData := rfl
  noSmallCore := input.toComputableFiniteSearchNoSmallCore

theorem certificate_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    Nonempty (Certificate scale_data) :=
  ⟨input.toCertificate⟩

theorem Certificate.accepted_code_to_formulaCode_derivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    (cert : Certificate scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode
        code) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics
      formulaCode := by
  have hcore :
      PAHilbertAcceptedProofCodeForFormulaCode
        cert.canonicalCore.checker formulaCode code := by
    simpa [cert.sameChecker] using haccepted
  have hderivable :
      PAHilbertFormulaCodeDerivable
        cert.canonicalCore.semantics formulaCode :=
    cert.canonicalCore.accepted_decoded_code_to_formulaCode_derivable
      formulaCode code hcore
  simpa [cert.sameSemantics] using hderivable

theorem Certificate.feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (cert : Certificate scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  cert.input.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalResidualInput

/-! ## Final residual variants with generated proof-length exactness -/

/-- Final residual input with proof-length exactness reduced to the by-index
calibration `proof_length (powerBoundRawCode n) = n`.  The calibrated
proof-length exactness for size `id` is generated by the checker minimum-code
theorem above. -/
structure ConcretePAHilbertPowerBoundFinalByIndexResidualInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  scaleNoCollisionBelow :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code < cutoff f hf N →
          scale_data.scale code ≠ scale_data.scale (witness f hf N)
  scaleNoCollisionBelowSelf :
    ∀ n : Nat, ∀ code : Nat, code < n →
      scale_data.scale code ≠ scale_data.scale n
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

namespace ConcretePAHilbertPowerBoundFinalByIndexResidualInput

def toProofLengthByIndexInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data) :
    ConcretePAHilbertPowerBoundProofLengthByIndexInput scale_data where
  noCollisionBelowSelf := by
    intro n code hsmall
    exact
      concretePAHilbert_powerBoundRawCode_ne_of_scale_ne
        scale_data (input.scaleNoCollisionBelowSelf n code hsmall)
  proof_length_eq_index :=
    input.proof_length_eq_index

def toFinalResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  scaleNoCollisionBelow := input.scaleNoCollisionBelow
  proof_length :=
    input.toProofLengthByIndexInput
      |>.toCalibratedIdentityProofLengthInput

theorem generated_calibrated_proof_length_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data id) :=
  input.toProofLengthByIndexInput
    |>.toCalibratedIdentityProofLengthInput
    |>.toCheckerExactness

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput.Certificate scale_data :=
  input.toFinalResidualInput.toCertificate

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toFinalResidualInput.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalByIndexResidualInput

/-- Final by-index residual generated from one scale-injectivity certificate.
Injectivity supplies both the searched-interval rejection separation and the
self separation used in the minimum-code proof-length calculation. -/
structure ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  cutoff_le_witness :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      cutoff f hf N ≤ witness f hf N
  scale_injective : Function.Injective scale_data.scale
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

namespace ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput

def toFinalByIndexResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  scaleNoCollisionBelow := by
    intro f hf N code hsmall hcollision
    have hcode_eq :
        code = input.witness f hf N :=
      input.scale_injective hcollision
    have hcode_lt_witness :
        code < input.witness f hf N :=
      lt_of_lt_of_le hsmall (input.cutoff_le_witness f hf N)
    rw [hcode_eq] at hcode_lt_witness
    exact (Nat.lt_irrefl _) hcode_lt_witness
  scaleNoCollisionBelowSelf := by
    intro n code hsmall hcollision
    have hcode_eq : code = n :=
      input.scale_injective hcollision
    rw [hcode_eq] at hsmall
    exact (Nat.lt_irrefl _) hsmall
  proof_length_eq_index :=
    input.proof_length_eq_index

def toFinalResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput scale_data :=
  input.toFinalByIndexResidualInput.toFinalResidualInput

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput.Certificate scale_data :=
  input.toFinalResidualInput.toCertificate

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toFinalResidualInput.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.toComputableFiniteSearchNoSmallCore

theorem generated_calibrated_proof_length_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
        scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data id) :=
  input.toFinalByIndexResidualInput
    |>.generated_calibrated_proof_length_exactness

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput

/-- Final by-index residual generated from a strictly increasing theorem-5
scale.  This is often the most natural arithmetic-code certificate: strict
increase gives injectivity, which then feeds both finite rejection separation
and proof-length minimum-code separation. -/
structure ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  cutoff_le_witness :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      cutoff f hf N ≤ witness f hf N
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

namespace ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput

theorem scale_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    Function.Injective scale_data.scale := by
  intro a b hscale_eq
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hstrict :
        scale_data.scale a < scale_data.scale b :=
      input.scale_strict hlt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)
  · exact heq
  · have hstrict :
        scale_data.scale b < scale_data.scale a :=
      input.scale_strict hgt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)

def toFinalScaleInjectiveByIndexResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
      scale_data where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := input.witness_ge
  cutoff_gt := input.cutoff_gt
  cutoff_le_witness := input.cutoff_le_witness
  scale_injective := input.scale_injective
  proof_length_eq_index :=
    input.proof_length_eq_index

def toFinalByIndexResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data :=
  input.toFinalScaleInjectiveByIndexResidualInput
    |>.toFinalByIndexResidualInput

def toFinalResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput scale_data :=
  input.toFinalScaleInjectiveByIndexResidualInput
    |>.toFinalResidualInput

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput.Certificate scale_data :=
  input.toFinalResidualInput.toCertificate

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toFinalResidualInput.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.toComputableFiniteSearchNoSmallCore

theorem generated_calibrated_proof_length_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data id) :=
  input.toFinalScaleInjectiveByIndexResidualInput
    |>.generated_calibrated_proof_length_exactness

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput

/-- Final strict-scale by-index residual with the witness and cutoff generated
from one computable bound.  The generated schedule uses
`witness f hf N = bound f hf N` and `cutoff f hf N = bound f hf N`, so the
caller only has to prove that the bound is above `N` and dominates the
polynomial at that same index. -/
structure ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  bound : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  bound_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ bound f hf N
  bound_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (bound f hf N) < (bound f hf N : Real)
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  proof_length_eq_index :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (n : Real)

namespace ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput

def toFinalStrictScaleByIndexResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
      scale_data where
  witness := input.bound
  cutoff := input.bound
  witness_ge := input.bound_ge
  cutoff_gt := input.bound_gt
  cutoff_le_witness := by
    intro f hf N
    rfl
  scale_strict := input.scale_strict
  proof_length_eq_index :=
    input.proof_length_eq_index

def toFinalScaleInjectiveByIndexResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
      scale_data :=
  input.toFinalStrictScaleByIndexResidualInput
    |>.toFinalScaleInjectiveByIndexResidualInput

def toFinalByIndexResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data :=
  input.toFinalStrictScaleByIndexResidualInput
    |>.toFinalByIndexResidualInput

def toFinalResidualInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput scale_data :=
  input.toFinalStrictScaleByIndexResidualInput
    |>.toFinalResidualInput

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalResidualInput.Certificate scale_data :=
  input.toFinalResidualInput.toCertificate

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toFinalResidualInput.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.toComputableFiniteSearchNoSmallCore

theorem generated_calibrated_proof_length_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data id) :=
  input.toFinalStrictScaleByIndexResidualInput
    |>.generated_calibrated_proof_length_exactness

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalResidualInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput

/-! ## Singleton calibrated finite enumeration route -/

theorem concretePAHilbertPowerBound_acceptedProofCode_to_code_eq_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n)
        code) :
    code = n := by
  exact
    hinjective
      (concretePAHilbertPowerBound_acceptedProofCode_to_powerBoundRawCode_eq
        haccepted)

/-- Executable singleton candidate list for calibrated powerBound semantics.
If the canonical proof code for formula index `n` is smaller than cutoff `K`,
the only possible accepted code is enumerated; otherwise the list is empty. -/
def concretePAHilbertPowerBoundCalibratedSingletonCandidates
    (lengthCodeAt : Nat → Nat) (n K : Nat) : List Nat :=
  if lengthCodeAt n < K then [n] else []

theorem concretePAHilbertPowerBoundCalibratedSingletonCandidates_self_empty
    (lengthCodeAt : Nat → Nat) (n : Nat) :
    concretePAHilbertPowerBoundCalibratedSingletonCandidates
      lengthCodeAt n (lengthCodeAt n) = [] := by
  simp [concretePAHilbertPowerBoundCalibratedSingletonCandidates]

def concretePAHilbertPowerBoundCalibratedSingletonFiniteEnumeration
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt) where
  candidates :=
    concretePAHilbertPowerBoundCalibratedSingletonCandidates lengthCodeAt
  complete := by
    intro n K code hchecks hsize
    have hcode_eq : code = n :=
      concretePAHilbertPowerBound_acceptedProofCode_to_code_eq_of_injective
        hinjective hchecks
    subst code
    simp [concretePAHilbertPowerBoundCalibratedSingletonCandidates,
      hsize]

/-- Rejection extractor for singleton calibrated enumeration.  At the selected
witness the cutoff is definitionally the calibrated size of the canonical
proof code, so the singleton candidate list is empty and rejection is immediate
for every enumerated candidate. -/
structure ConcretePAHilbertPowerBoundSingletonGapRejectionInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) : Type where
  powerBoundRawCode_injective :
    Function.Injective scale_data.powerBoundRawCode
  gap :
    ComputableSearchGapCertificate
      (fun n : Nat => (lengthCodeAt n : Real))

namespace ConcretePAHilbertPowerBoundSingletonGapRejectionInput

def witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    Nat :=
  (input.gap.gap_for_polynomial_upper f hf).witness N

def cutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    Nat :=
  lengthCodeAt (input.witness f hf N)

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt) :=
  concretePAHilbertPowerBoundCalibratedSingletonFiniteEnumeration
    scale_data lengthCodeAt input.powerBoundRawCode_injective

theorem candidates_at_witness_empty
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    input.finiteEnumeration.candidates
        (input.witness f hf N) (input.cutoff f hf N) = [] := by
  simp [finiteEnumeration,
    concretePAHilbertPowerBoundCalibratedSingletonFiniteEnumeration,
    cutoff,
    concretePAHilbertPowerBoundCalibratedSingletonCandidates_self_empty]

theorem no_candidate_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat)
    (code : Nat) :
    code ∈
        input.finiteEnumeration.candidates
          (input.witness f hf N) (input.cutoff f hf N) →
      False := by
  intro hmem
  rw [input.candidates_at_witness_empty f hf N] at hmem
  simp at hmem

def toCheckerExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt)
      input.finiteEnumeration where
  witness := input.witness
  cutoff := input.cutoff
  witness_ge := by
    intro f hf N
    exact (input.gap.gap_for_polynomial_upper f hf).witness_ge N
  cutoff_gt := by
    intro f hf N
    exact (input.gap.gap_for_polynomial_upper f hf).strict_at_witness N
  rejects_candidates := by
    intro f hf N code hmem _hchecks
    exact False.elim (input.no_candidate_at_witness f hf N code hmem)

theorem toCheckerExtractor_candidates_at_witness_empty
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    input.finiteEnumeration.candidates
        (input.toCheckerExtractor.witness f hf N)
        (input.toCheckerExtractor.cutoff f hf N) = [] := by
  simpa [toCheckerExtractor] using
    input.candidates_at_witness_empty f hf N

theorem toCheckerExtractor_rejects_candidates_from_empty
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat)
    (code : Nat)
    (hmem :
      code ∈
        input.finiteEnumeration.candidates
          (input.toCheckerExtractor.witness f hf N)
          (input.toCheckerExtractor.cutoff f hf N)) :
    ¬ (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt).checks code
        (scale_data.powerBoundRawCode
          (input.toCheckerExtractor.witness f hf N)) := by
  have hfalse : False := by
    rw [input.toCheckerExtractor_candidates_at_witness_empty f hf N] at hmem
    simp at hmem
  exact False.elim hfalse

/-- Exact gap-to-extractor trace for the singleton calibrated rejection input.
The extractor witness is exactly the computable gap witness, and the cutoff is
exactly the calibrated size at that same witness. -/
theorem toCheckerExtractor_gap_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt) :
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      input.toCheckerExtractor.witness f hf N =
          (input.gap.gap_for_polynomial_upper f hf).witness N ∧
        input.toCheckerExtractor.cutoff f hf N =
          lengthCodeAt ((input.gap.gap_for_polynomial_upper f hf).witness N) ∧
          N ≤ (input.gap.gap_for_polynomial_upper f hf).witness N ∧
            f ((input.gap.gap_for_polynomial_upper f hf).witness N) <
              (lengthCodeAt
                ((input.gap.gap_for_polynomial_upper f hf).witness N) : Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        ∀ code :
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt).Code,
          code ∈
            input.finiteEnumeration.candidates
              (input.toCheckerExtractor.witness f hf N)
              (input.toCheckerExtractor.cutoff f hf N) →
            ¬ (concretePAHilbertPowerBoundCalibratedCheckerSemantics
                scale_data lengthCodeAt).checks code
                (scale_data.powerBoundRawCode
                  (input.toCheckerExtractor.witness f hf N))) := by
  refine ⟨?_, ?_⟩
  · intro f hf N
    exact
      ⟨rfl, rfl,
        (input.gap.gap_for_polynomial_upper f hf).witness_ge N,
        (input.gap.gap_for_polynomial_upper f hf).strict_at_witness N⟩
  · intro f hf N code hmem
    exact input.toCheckerExtractor.rejects_candidates f hf N code hmem

end ConcretePAHilbertPowerBoundSingletonGapRejectionInput

/-- Four-piece calibrated route driven by a search-gap certificate for the
chosen calibrated proof-code size.  This avoids the stronger numeric-code
condition `cutoff ≤ witness`: finite enumeration is singleton/empty depending
on the calibrated size itself. -/
structure ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  rejection_search :
    ConcretePAHilbertPowerBoundSingletonGapRejectionInput
      scale_data lengthCodeAt
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data lengthCodeAt

namespace ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  concretePAHilbertPowerBoundCalibratedCheckerSemantics
    scale_data input.lengthCodeAt

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      input.checkerSemantics :=
  input.rejection_search.finiteEnumeration

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      input.checkerSemantics
      input.finiteEnumeration :=
  input.rejection_search.toCheckerExtractor

theorem rejectionExtractor_candidates_at_witness_empty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    input.finiteEnumeration.candidates
        (input.rejectionExtractor.witness f hf N)
        (input.rejectionExtractor.cutoff f hf N) = [] := by
  simpa [checkerSemantics, finiteEnumeration, rejectionExtractor] using
    input.rejection_search.toCheckerExtractor_candidates_at_witness_empty
      f hf N

theorem proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      input.checkerSemantics :=
  input.proof_length.toCheckerExactness

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore where
  checker :=
    concretePAHilbertPowerBoundChecker scale_data
  semantics :=
    concretePAHilbertTheorem5DerivabilitySemantics
  recognizerExactness :=
    concretePAHilbertTheorem5AxiomRecognizerExactness
  canonicalInterface :=
    concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data
  scale_data :=
    scale_data
  checkerSemantics :=
    input.checkerSemantics
  finiteEnumeration :=
    input.finiteEnumeration
  rejectionExtractor :=
    input.rejectionExtractor
  proofLengthExactness :=
    input.proofLengthExactness

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCanonicalCalibratedExactnessCore.toComputableFiniteSearchNoSmallCore

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toCanonicalCalibratedExactnessCore
    |>.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput

/-- Singleton calibrated route with raw-code injectivity generated from strict
increase of the theorem-5 scale.  This packages the current most useful
constructive endpoint: a caller supplies the calibrated size, a computable
search gap for that size, strict scale growth, and proof-length exactness; the
PA/Hilbert checker layer then produces the canonical calibrated core and the
Month 9-10 finite-search no-small-code core. -/
structure ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  gap :
    ComputableSearchGapCertificate
      (fun n : Nat => (lengthCodeAt n : Real))
  proof_length :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data lengthCodeAt

namespace ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput

theorem scale_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    Function.Injective scale_data.scale := by
  intro a b hscale_eq
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hstrict :
        scale_data.scale a < scale_data.scale b :=
      input.scale_strict hlt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)
  · exact heq
  · have hstrict :
        scale_data.scale b < scale_data.scale a :=
      input.scale_strict hgt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)

theorem powerBoundRawCode_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    Function.Injective scale_data.powerBoundRawCode :=
  concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
    scale_data input.scale_injective

def toSingletonGapRejectionInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    ConcretePAHilbertPowerBoundSingletonGapRejectionInput
      scale_data input.lengthCodeAt where
  powerBoundRawCode_injective :=
    input.powerBoundRawCode_injective
  gap :=
    input.gap

def toSingletonGapCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
      scale_data where
  lengthCodeAt :=
    input.lengthCodeAt
  rejection_search :=
    input.toSingletonGapRejectionInput
  proof_length :=
    input.proof_length

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toSingletonGapCalibratedFourPieceInput
    |>.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toSingletonGapCalibratedFourPieceInput
    |>.toComputableFiniteSearchNoSmallCore

theorem generated_finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerFiniteEnumeration
        input.toSingletonGapCalibratedFourPieceInput.checkerSemantics) :=
  ⟨input.toSingletonGapCalibratedFourPieceInput.finiteEnumeration⟩

theorem generated_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableRejectionExtractor
        input.toSingletonGapCalibratedFourPieceInput.checkerSemantics
        input.toSingletonGapCalibratedFourPieceInput.finiteEnumeration) :=
  ⟨input.toSingletonGapCalibratedFourPieceInput.rejectionExtractor⟩

theorem generated_proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      input.toSingletonGapCalibratedFourPieceInput.checkerSemantics :=
  input.toSingletonGapCalibratedFourPieceInput.proofLengthExactness

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toSingletonGapCalibratedFourPieceInput
    |>.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput

/-! ## Singleton calibrated proof-length generated from calibrated size -/

theorem concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) (n : Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt)
      n =
        lengthCodeAt n := by
  classical
  let checkerSem :=
    concretePAHilbertPowerBoundCalibratedCheckerSemantics
      scale_data lengthCodeAt
  let sem := checkerSem.toProofCodeSemantics
  apply le_antisymm
  · have hhas_explicit :
        ∃ code : Nat,
          PAHilbertAcceptedProofCodeForFormulaCode
            (concretePAHilbertPowerBoundChecker scale_data)
            (scale_data.powerBoundRawCode n)
            code ∧
          lengthCodeAt code ≤ lengthCodeAt n := by
      exact
        ⟨n,
          concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
            scale_data n,
          le_rfl⟩
    have hhas :
        sem.HasProofCodeOfSize
          (scale_data.powerBoundRawCode n) (lengthCodeAt n) := by
      simpa [ProofCodeSemantics.HasProofCodeOfSize, sem, checkerSem,
        InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
        concretePAHilbertPowerBoundCalibratedCheckerSemantics] using
        hhas_explicit
    simpa [InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt,
      sem, checkerSem] using
      sem.minProofCodeSize_le_of_hasProofCodeOfSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ hhas
  · let minSize :=
      sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    have hfind :
        sem.HasProofCodeOfSize
          (scale_data.powerBoundRawCode n) minSize :=
      sem.hasProofCodeOfSize_minProofCodeSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    have hspec :
        ∃ code : Nat,
          PAHilbertAcceptedProofCodeForFormulaCode
            (concretePAHilbertPowerBoundChecker scale_data)
            (scale_data.powerBoundRawCode n)
            code ∧
          lengthCodeAt code ≤ minSize := by
      simpa [ProofCodeSemantics.HasProofCodeOfSize, sem, checkerSem,
        InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
        concretePAHilbertPowerBoundCalibratedCheckerSemantics] using
        hfind
    rcases hspec with ⟨code, haccepted, hsize⟩
    have hcode_eq : code = n :=
      concretePAHilbertPowerBound_acceptedProofCode_to_code_eq_of_injective
        hinjective haccepted
    subst code
    simpa [InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt,
      sem, checkerSem, minSize] using hsize

/-- Expanded audit trace for the calibrated singleton route.  It records the
canonical accepted proof code, uniqueness of accepted proof codes at the same
raw formula code, the concrete `HasProofCodeOfSize` witness, and the resulting
minimum-size equality in one theorem. -/
theorem concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_trace_of_injective
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) (n : Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    let checkerSem :=
      concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt
    let sem := checkerSem.toProofCodeSemantics
    PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) n ∧
      (∀ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          (concretePAHilbertPowerBoundChecker scale_data)
          (scale_data.powerBoundRawCode n) code →
        code = n) ∧
      sem.HasProofCodeOfSize
        (scale_data.powerBoundRawCode n) (lengthCodeAt n) ∧
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        checkerSem n = lengthCodeAt n := by
  classical
  let checkerSem :=
    concretePAHilbertPowerBoundCalibratedCheckerSemantics
      scale_data lengthCodeAt
  let sem := checkerSem.toProofCodeSemantics
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) n :=
    concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data n
  have hunique :
      ∀ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          (concretePAHilbertPowerBoundChecker scale_data)
          (scale_data.powerBoundRawCode n) code →
        code = n := by
    intro code hcode
    exact
      concretePAHilbertPowerBound_acceptedProofCode_to_code_eq_of_injective
        hinjective hcode
  have hhas_explicit :
      ∃ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          (concretePAHilbertPowerBoundChecker scale_data)
          (scale_data.powerBoundRawCode n) code ∧
        lengthCodeAt code ≤ lengthCodeAt n :=
    ⟨n, haccepted, le_rfl⟩
  have hhas :
      sem.HasProofCodeOfSize
        (scale_data.powerBoundRawCode n) (lengthCodeAt n) := by
    simpa [ProofCodeSemantics.HasProofCodeOfSize, sem, checkerSem,
      InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
      concretePAHilbertPowerBoundCalibratedCheckerSemantics] using
      hhas_explicit
  have hmin :
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        checkerSem n = lengthCodeAt n := by
    simpa [checkerSem] using
      concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
        scale_data lengthCodeAt n hinjective
  exact ⟨haccepted, hunique, hhas, hmin⟩

/-- Proof-length-free calibration target: the project length induced directly by
the checker semantics agrees with the calibrated size on the theorem-5 raw-code
family.  This is the local replacement shape for the remaining root
`proof_length` bridge. -/
theorem concretePAHilbertPowerBoundCalibrated_projectLengthAt_eq_lengthCodeAt_of_injective
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) (fallback : _root_.FormulaCode → Nat)
    (n : Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt).toProofCodeSemantics.projectLength
      fallback (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) := by
  classical
  let checkerSem :=
    concretePAHilbertPowerBoundCalibratedCheckerSemantics
      scale_data lengthCodeAt
  let sem := checkerSem.toProofCodeSemantics
  have hproject :
      sem.projectLength fallback (scale_data.powerBoundRawCode n) =
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
    simpa [sem] using
      (sem.projectLength_eq_minProofCodeSize
        fallback (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩)
  have hmin_nat :
      sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ =
        lengthCodeAt n := by
    have hmin :
        InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
          checkerSem n = lengthCodeAt n :=
      concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
        scale_data lengthCodeAt n hinjective
    simpa [InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt,
      sem, checkerSem] using hmin
  exact hproject.trans (by exact_mod_cast hmin_nat)

/-- Project-level proof-length calibration by the chosen calibrated size.
The minimum-size theorem above turns this direct family equality into the
checker proof-length exactness expected by Month 9-10. -/
structure ConcretePAHilbertPowerBoundCalibratedProofLengthBySizeInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat) : Prop where
  powerBoundRawCode_injective :
    Function.Injective scale_data.powerBoundRawCode
  proof_length_eq_lengthCodeAt :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real)

def ConcretePAHilbertPowerBoundCalibratedProofLengthBySizeInput.toCalibratedProofLengthInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundCalibratedProofLengthBySizeInput
        scale_data lengthCodeAt) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data lengthCodeAt where
  proof_length_eq_minProofCodeSizeAt := by
    intro n
    have hmin :
        InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt)
          n =
            lengthCodeAt n :=
      concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
        scale_data lengthCodeAt n input.powerBoundRawCode_injective
    simpa [hmin] using input.proof_length_eq_lengthCodeAt n

/-- A calibrated proof-length input is exactly the pointwise root
`proof_length = lengthCodeAt` equation once the theorem-5 raw-code family is
injective.  This is the central form of the proof-length residual: the checker
minimum has already been computed proof-length-free by
`concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective`. -/
theorem ConcretePAHilbertPowerBoundCalibratedProofLengthInput.rootProofLength_eq_lengthCodeAt_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) := by
  intro n
  calc
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
      (InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        n : Real) :=
        input.proof_length_eq_minProofCodeSizeAt n
    _ = (lengthCodeAt n : Real) := by
        exact_mod_cast
          concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
            scale_data lengthCodeAt n hinjective

/-- The pointwise root proof-length equation builds the calibrated checker
proof-length input when raw codes are injective. -/
theorem ConcretePAHilbertPowerBoundCalibratedProofLengthInput.of_rootProofLength_eq_lengthCodeAt_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (hroot :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data lengthCodeAt where
  proof_length_eq_minProofCodeSizeAt := by
    intro n
    calc
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) :=
          hroot n
      _ =
        (InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt)
          n : Real) := by
          exact_mod_cast
            (concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
              scale_data lengthCodeAt n hinjective).symm

/-- Central iff form of the proof-length residual for the calibrated PA/Hilbert
checker.  It isolates the only remaining root `proof_length` content from the
already-unconditional checker minimum computation. -/
theorem concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) := by
  constructor
  · intro input
    exact
      input.rootProofLength_eq_lengthCodeAt_of_injective
        hinjective
  · intro hroot
    exact
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput.of_rootProofLength_eq_lengthCodeAt_of_injective
        lengthCodeAt hinjective hroot

/-- Strict-scale singleton route where proof-length exactness is generated
from the direct by-size calibration
`proof_length (powerBoundRawCode n) = lengthCodeAt n`. -/
structure ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  gap :
    ComputableSearchGapCertificate
      (fun n : Nat => (lengthCodeAt n : Real))
  proof_length_eq_lengthCodeAt :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real)

namespace ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput

theorem scale_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    Function.Injective scale_data.scale := by
  intro a b hscale_eq
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hstrict :
        scale_data.scale a < scale_data.scale b :=
      input.scale_strict hlt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)
  · exact heq
  · have hstrict :
        scale_data.scale b < scale_data.scale a :=
      input.scale_strict hgt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)

theorem powerBoundRawCode_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    Function.Injective scale_data.powerBoundRawCode :=
  concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
    scale_data input.scale_injective

def toProofLengthBySizeInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthBySizeInput
      scale_data input.lengthCodeAt where
  powerBoundRawCode_injective :=
    input.powerBoundRawCode_injective
  proof_length_eq_lengthCodeAt :=
    input.proof_length_eq_lengthCodeAt

def toStrictScaleSingletonGapCalibratedInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
      scale_data where
  lengthCodeAt :=
    input.lengthCodeAt
  scale_strict :=
    input.scale_strict
  gap :=
    input.gap
  proof_length :=
    input.toProofLengthBySizeInput.toCalibratedProofLengthInput

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toStrictScaleSingletonGapCalibratedInput
    |>.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonGapCalibratedInput
    |>.toComputableFiniteSearchNoSmallCore

theorem generated_proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      ((input.toStrictScaleSingletonGapCalibratedInput
          |>.toSingletonGapCalibratedFourPieceInput)
          |>.checkerSemantics) :=
  input.toStrictScaleSingletonGapCalibratedInput
    |>.generated_proofLengthExactness

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonGapCalibratedInput
    |>.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput

/-! ## Exact proof-length gap transport for singleton calibrated route -/

/-- Final singleton route when the available lower-bound machine gives a
search gap for the actual project proof length.  The equality
`proof_length (powerBoundRawCode n) = lengthCodeAt n` transports that gap to
the calibrated checker size, and the by-size route then produces the
PA/Hilbert checker core. -/
structure ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  proof_length_gap :
    ComputableSearchGapCertificate
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n))
  proof_length_eq_lengthCodeAt :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real)

namespace ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput

def transportedGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
        scale_data) :
    ComputableSearchGapCertificate
      (fun n : Nat => (input.lengthCodeAt n : Real)) where
  gap_for_polynomial_upper := by
    intro f hf
    let gap := input.proof_length_gap.gap_for_polynomial_upper f hf
    exact
      { witness := gap.witness
        witness_ge := gap.witness_ge
        strict_at_witness := by
          intro N
          have hgap := gap.strict_at_witness N
          simpa [input.proof_length_eq_lengthCodeAt (gap.witness N)] using
            hgap }

def toStrictScaleSingletonBySizeInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
        scale_data) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
      scale_data where
  lengthCodeAt :=
    input.lengthCodeAt
  scale_strict :=
    input.scale_strict
  gap :=
    input.transportedGap
  proof_length_eq_lengthCodeAt :=
    input.proof_length_eq_lengthCodeAt

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toStrictScaleSingletonBySizeInput
    |>.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonBySizeInput
    |>.toComputableFiniteSearchNoSmallCore

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((input.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (input.proof_length_gap.gap_for_polynomial_upper f hf).witness N :=
  rfl

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonBySizeInput
    |>.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput

/-! ## Final powered-scale exact proof-length checker core input -/

theorem concretePAHilbert_scale_strict_of_timeConstructiblePower_strict
    (scale_data : InternalPudlakTheorem5ScaleData)
    (hpower :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent) :
    ∀ {a b : Nat}, a < b →
      scale_data.scale a < scale_data.scale b := by
  intro a b hlt
  rw [scale_data.scale_eq a, scale_data.scale_eq b]
  exact hpower hlt

/-- Strict growth of the primitive time-constructible bound plus a nonzero
exponent gives strict growth of the theorem-5 scale.  This local version keeps
the checker surface independent of the proof-length gap frontier. -/
theorem concretePAHilbert_scale_strict_of_timeConstructibleBound_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b := by
  intro a b hlt
  rw [scale_data.scale_eq a, scale_data.scale_eq b]
  exact
    pow_lt_pow_left₀
      (time_bound_strict hlt)
      (Nat.zero_le (scale_data.time_constructible_bound a))
      exponent_ne_zero

/-- The central proof-length residual with the raw-code injectivity premise
discharged from strict growth of the theorem-5 scale. -/
theorem concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) := by
  have hscale_injective : Function.Injective scale_data.scale := by
    intro a b hscale_eq
    rcases Nat.lt_trichotomy a b with hlt | heq | hgt
    · have hstrict :
          scale_data.scale a < scale_data.scale b :=
        scale_strict hlt
      rw [hscale_eq] at hstrict
      exact False.elim ((Nat.lt_irrefl _) hstrict)
    · exact heq
    · have hstrict :
          scale_data.scale b < scale_data.scale a :=
        scale_strict hgt
      rw [hscale_eq] at hstrict
      exact False.elim ((Nat.lt_irrefl _) hstrict)
  exact
    concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_injective
      lengthCodeAt
      (concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
        scale_data hscale_injective)

/-- Powered time-bound strictness is enough to put the calibrated checker input
and the root proof-length equation in exact correspondence. -/
theorem concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructiblePower_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hpower :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :=
  concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_scale_strict
    lengthCodeAt
    (concretePAHilbert_scale_strict_of_timeConstructiblePower_strict
      scale_data hpower)

/-- Primitive time-bound strictness and nonzero exponent are enough to put the
calibrated checker input and the root proof-length equation in exact
correspondence.  This is the common project-scale version used by the endpoint
residual eliminators. -/
theorem concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructibleBound_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :=
  concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_scale_strict
    lengthCodeAt
    (concretePAHilbert_scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero)

/-- Family-level checker exactness is exactly the root proof-length equation
under the standard time-bound strictness hypotheses. -/
theorem concretePAHilbertPowerBoundCalibratedFamilyExactness_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructibleBound_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) := by
  constructor
  · intro family
    have input :
        ConcretePAHilbertPowerBoundCalibratedProofLengthInput
          scale_data lengthCodeAt :=
      { proof_length_eq_minProofCodeSizeAt := by
          intro n
          exact family.proof_length_eq_minProofCodeSizeAt n }
    exact
      (concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructibleBound_strict
        lengthCodeAt time_bound_strict exponent_ne_zero).mp input
  · intro hroot
    have input :
        ConcretePAHilbertPowerBoundCalibratedProofLengthInput
          scale_data lengthCodeAt :=
      (concretePAHilbertPowerBoundCalibratedProofLengthInput_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructibleBound_strict
        lengthCodeAt time_bound_strict exponent_ne_zero).mpr hroot
    exact
      { proof_length_eq_minProofCodeSizeAt :=
          input.proof_length_eq_minProofCodeSizeAt }

/-- Relevant-code checker exactness is exactly the root proof-length equation
for the calibrated PA/Hilbert checker under the standard project scale
strictness hypotheses. -/
theorem concretePAHilbertPowerBoundCalibratedCheckerExactness_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructibleBound_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) := by
  constructor
  · intro exactness
    have family :
        InternalPudlakTheorem5CheckerProofLengthFamilyExactness
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt) :=
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
        exactness
    exact
      (concretePAHilbertPowerBoundCalibratedFamilyExactness_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructibleBound_strict
        lengthCodeAt time_bound_strict exponent_ne_zero).mp family
  · intro hroot
    have family :
        InternalPudlakTheorem5CheckerProofLengthFamilyExactness
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt) :=
      (concretePAHilbertPowerBoundCalibratedFamilyExactness_iff_rootProofLength_eq_lengthCodeAt_of_timeConstructibleBound_strict
        lengthCodeAt time_bound_strict exponent_ne_zero).mpr hroot
    exact family.toCheckerProofLengthExactness

/-- Current most compressed Month 11-12 constructive checker input.  It keeps
all PA/Hilbert checker machinery concrete and leaves only project-level data:
the calibrated size, the actual proof-length search gap, strict growth of the
scale as stated on the primitive powered time-constructible bound, and the
calibration between actual proof length and the chosen Nat-valued size. -/
structure ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  timeConstructiblePower_strict :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a ^ scale_data.exponent <
        scale_data.time_constructible_bound b ^ scale_data.exponent
  proof_length_gap :
    ComputableSearchGapCertificate
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n))
  proof_length_eq_lengthCodeAt :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real)

namespace ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput

theorem scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    ∀ {a b : Nat}, a < b →
      scale_data.scale a < scale_data.scale b :=
  concretePAHilbert_scale_strict_of_timeConstructiblePower_strict
    scale_data input.timeConstructiblePower_strict

def toStrictScaleSingletonExactProofLengthGapInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
      scale_data where
  lengthCodeAt :=
    input.lengthCodeAt
  scale_strict :=
    input.scale_strict
  proof_length_gap :=
    input.proof_length_gap
  proof_length_eq_lengthCodeAt :=
    input.proof_length_eq_lengthCodeAt

def toStrictScaleSingletonBySizeInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
      scale_data :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.toStrictScaleSingletonBySizeInput

/-- The final exact checker-core input generates the calibrated proof-length
input directly.  This is the explicit bridge from the stored root equation to
the checker minimum-size exactness certificate. -/
def toCalibratedProofLengthInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data input.lengthCodeAt :=
  input.toStrictScaleSingletonBySizeInput
    |>.toProofLengthBySizeInput
    |>.toCalibratedProofLengthInput

/-- The calibrated PA/Hilbert checker minimum at the theorem-5 raw code is the
chosen `lengthCodeAt` from the final exact core. -/
theorem minProofCodeSizeAt_eq_lengthCodeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (n : Nat) :
    InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data input.lengthCodeAt)
      n =
        input.lengthCodeAt n :=
  concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
    scale_data input.lengthCodeAt n
    input.toStrictScaleSingletonBySizeInput.powerBoundRawCode_injective

/-- Direct exactness statement: on the theorem-5 raw-code family, root
`proof_length` equals the calibrated checker minimum. -/
theorem rootProofLength_eq_minProofCodeSizeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
      (InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data input.lengthCodeAt)
        n : Real) :=
  input.toCalibratedProofLengthInput.proof_length_eq_minProofCodeSizeAt n

/-- Direct project-length exactness statement: on the theorem-5 raw-code
family, root `proof_length` equals the checker-defined `projectLength`. -/
theorem rootProofLength_eq_projectLengthAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (fallback : _root_.FormulaCode → Nat) (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data input.lengthCodeAt).toProofCodeSemantics.projectLength
        fallback (scale_data.powerBoundRawCode n) := by
  calc
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
      (input.lengthCodeAt n : Real) :=
        input.proof_length_eq_lengthCodeAt n
    _ =
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data input.lengthCodeAt).toProofCodeSemantics.projectLength
        fallback (scale_data.powerBoundRawCode n) := by
        symm
        exact
          concretePAHilbertPowerBoundCalibrated_projectLengthAt_eq_lengthCodeAt_of_injective
            scale_data input.lengthCodeAt fallback n
            input.toStrictScaleSingletonBySizeInput.powerBoundRawCode_injective

/-- Relevant-code checker proof-length exactness generated by the final exact
checker core. -/
def toCheckerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data input.lengthCodeAt) :=
  input.toCalibratedProofLengthInput.toCheckerExactness

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.toComputableFiniteSearchNoSmallCore

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput

/-! ## Materialized final exact checker core certificate -/

/-- Materialized output of the final exact checker-core input.  This stores the
generated canonical core and no-small core and records the same-object facts
needed by downstream Month 9-10 plumbing. -/
structure ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  input :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data
  canonicalCore :
    PAHilbertCanonicalCalibratedExactnessCore
  sameChecker :
    canonicalCore.checker =
      concretePAHilbertPowerBoundChecker scale_data
  sameSemantics :
    canonicalCore.semantics =
      concretePAHilbertTheorem5DerivabilitySemantics
  sameScaleData :
    canonicalCore.scale_data = scale_data
  noSmallCore :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

namespace ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
      scale_data where
  input := input
  canonicalCore := input.toCanonicalCalibratedExactnessCore
  sameChecker := rfl
  sameSemantics := rfl
  sameScaleData := rfl
  noSmallCore := input.toComputableFiniteSearchNoSmallCore

theorem certificate_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data) :=
  ⟨input.toCertificate⟩

end ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput

namespace ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate

theorem accepted_code_to_formulaCode_derivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    (cert :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode
        code) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics
      formulaCode := by
  have hcore :
      PAHilbertAcceptedProofCodeForFormulaCode
        cert.canonicalCore.checker formulaCode code := by
    simpa [cert.sameChecker] using haccepted
  have hderivable :
      PAHilbertFormulaCodeDerivable
        cert.canonicalCore.semantics formulaCode :=
    cert.canonicalCore.accepted_decoded_code_to_formulaCode_derivable
      formulaCode code hcore
  simpa [cert.sameSemantics] using hderivable

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (cert :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((cert.input.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (cert.input.proof_length_gap.gap_for_polynomial_upper f hf).witness N :=
  rfl

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (cert :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  cert.input.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate

/-! ## Scale-size final exact checker core input -/

/-- Scale-size specialization of the final exact checker input.  Here the
calibrated checker size is not a free choice: it is fixed to
`scale_data.scale`.  A search gap for the scale and the equality between actual
proof length and scale generate the exact proof-length gap required by the
final checker core. -/
structure ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  timeConstructiblePower_strict :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a ^ scale_data.exponent <
        scale_data.time_constructible_bound b ^ scale_data.exponent
  scale_gap :
    ComputableSearchGapCertificate
      (fun n : Nat => (scale_data.scale n : Real))
  proof_length_eq_scale :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real)

namespace ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput

def proofLengthGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data) :
    ComputableSearchGapCertificate
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n)) where
  gap_for_polynomial_upper := by
    intro f hf
    let gap := input.scale_gap.gap_for_polynomial_upper f hf
    exact
      { witness := gap.witness
        witness_ge := gap.witness_ge
        strict_at_witness := by
          intro N
          have hgap := gap.strict_at_witness N
          simpa [input.proof_length_eq_scale (gap.witness N)] using
            hgap }

def toFinalExactCheckerCoreInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data where
  lengthCodeAt :=
    scale_data.scale
  timeConstructiblePower_strict :=
    input.timeConstructiblePower_strict
  proof_length_gap :=
    input.proofLengthGap
  proof_length_eq_lengthCodeAt :=
    input.proof_length_eq_scale

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
      scale_data :=
  input.toFinalExactCheckerCoreInput.toCertificate

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toFinalExactCheckerCoreInput.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalExactCheckerCoreInput.toComputableFiniteSearchNoSmallCore

theorem proofLengthGap_witness_eq_scaleGap_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((input.proofLengthGap).gap_for_polynomial_upper f hf).witness N =
      (input.scale_gap.gap_for_polynomial_upper f hf).witness N :=
  rfl

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalExactCheckerCoreInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalScaleSizeCheckerCoreInput

/-- Scale-size final checker input for the case where the Month 9-10 lower
machine already supplies a search gap for the actual proof length.  This is the
most direct compatibility form for the computable lower-bound machine: the
chosen calibrated checker size is still `scale_data.scale`, while the supplied
gap is already stated for `proof_length (powerBoundRawCode n)`. -/
structure ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  timeConstructiblePower_strict :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a ^ scale_data.exponent <
        scale_data.time_constructible_bound b ^ scale_data.exponent
  proof_length_gap :
    ComputableSearchGapCertificate
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n))
  proof_length_eq_scale :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real)

namespace ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput

def toFinalExactCheckerCoreInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data where
  lengthCodeAt :=
    scale_data.scale
  timeConstructiblePower_strict :=
    input.timeConstructiblePower_strict
  proof_length_gap :=
    input.proof_length_gap
  proof_length_eq_lengthCodeAt :=
    input.proof_length_eq_scale

def toCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
      scale_data :=
  input.toFinalExactCheckerCoreInput.toCertificate

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toFinalExactCheckerCoreInput.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalExactCheckerCoreInput.toComputableFiniteSearchNoSmallCore

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((input.toFinalExactCheckerCoreInput
        |>.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (input.proof_length_gap.gap_for_polynomial_upper f hf).witness N :=
  rfl

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toFinalExactCheckerCoreInput.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput

/-! ## Closure record for direct exact proof-gap checker input -/

namespace ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput

def toSingletonGapCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
      scale_data :=
  input.toFinalExactCheckerCoreInput
    |>.toStrictScaleSingletonBySizeInput
    |>.toStrictScaleSingletonGapCalibratedInput
    |>.toSingletonGapCalibratedFourPieceInput

end ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput

/-- Materialized checklist closure for the final direct exact proof-gap input.
It stores every generated component consumed by the checker-native Month 9-10
bridge, not just the terminal no-small core. -/
structure ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  input :
    ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
      scale_data
  certificate :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
      scale_data
  canonicalCore :
    PAHilbertCanonicalCalibratedExactnessCore
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration
  proofLengthExactness :
    InternalPudlakTheorem5CheckerProofLengthExactness checkerSemantics
  noSmallCore :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

namespace ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput

def toClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
      scale_data where
  input :=
    input
  certificate :=
    input.toCertificate
  canonicalCore :=
    input.toCanonicalCalibratedExactnessCore
  checkerSemantics :=
    input.toSingletonGapCalibratedFourPieceInput.checkerSemantics
  finiteEnumeration :=
    input.toSingletonGapCalibratedFourPieceInput.finiteEnumeration
  rejectionExtractor :=
    input.toSingletonGapCalibratedFourPieceInput.rejectionExtractor
  proofLengthExactness :=
    input.toSingletonGapCalibratedFourPieceInput.proofLengthExactness
  noSmallCore :=
    input.toComputableFiniteSearchNoSmallCore

theorem closure_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
        scale_data) :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data) :=
  ⟨input.toClosure⟩

end ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput

namespace ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((closure.input.toFinalExactCheckerCoreInput
        |>.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (closure.input.proof_length_gap.gap_for_polynomial_upper f hf).witness
        N :=
  rfl

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  closure.input.feeds_month9_month10_checker_bridge

def computableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data :=
  closure.rejectionExtractor.toCheckerComputableSearchProfile

theorem generated_components_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data) :
    Nonempty
        (InternalPudlakTheorem5CheckerFiniteEnumeration
          closure.checkerSemantics) ∧
      Nonempty
        (InternalPudlakTheorem5CheckerComputableRejectionExtractor
          closure.checkerSemantics closure.finiteEnumeration) ∧
        Nonempty
          (InternalPudlakTheorem5CheckerProofLengthExactness
            closure.checkerSemantics) ∧
          Nonempty
            (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
              scale_data) ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨closure.finiteEnumeration⟩,
    ⟨closure.rejectionExtractor⟩,
    ⟨closure.proofLengthExactness⟩,
    ⟨closure.computableSearchProfile⟩,
    ⟨closure.noSmallCore⟩⟩

theorem accepted_code_to_formulaCode_derivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode
        code) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics
      formulaCode :=
  closure.certificate.accepted_code_to_formulaCode_derivable
    formulaCode code haccepted

end ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure

/-! ## Direct scale-strict exact proof-gap checker closure -/

/-- Scale-size exact proof-gap input with strictness stated directly for
`scale_data.scale`.  This is useful when the Month 9-10 side proves strict
growth of the scale itself rather than of the powered time-constructible
presentation. -/
structure ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  proof_length_gap :
    ComputableSearchGapCertificate
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n))
  proof_length_eq_scale :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real)

namespace ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput

def toStrictScaleSingletonExactProofLengthGapInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonExactProofLengthGapInput
      scale_data where
  lengthCodeAt :=
    scale_data.scale
  scale_strict :=
    input.scale_strict
  proof_length_gap :=
    input.proof_length_gap
  proof_length_eq_lengthCodeAt :=
    input.proof_length_eq_scale

def toSingletonGapCalibratedFourPieceInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    ConcretePAHilbertPowerBoundSingletonGapCalibratedFourPieceInput
      scale_data :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.toStrictScaleSingletonBySizeInput
    |>.toStrictScaleSingletonGapCalibratedInput
    |>.toSingletonGapCalibratedFourPieceInput

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.toComputableFiniteSearchNoSmallCore

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((input.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (input.proof_length_gap.gap_for_polynomial_upper f hf).witness N :=
  rfl

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨input.toCanonicalCalibratedExactnessCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  input.toStrictScaleSingletonExactProofLengthGapInput
    |>.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput

/-- Materialized closure for the direct scale-strict exact proof-gap input. -/
structure ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  input :
    ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
      scale_data
  canonicalCore :
    PAHilbertCanonicalCalibratedExactnessCore
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration
  proofLengthExactness :
    InternalPudlakTheorem5CheckerProofLengthExactness checkerSemantics
  noSmallCore :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

namespace ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput

def toClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
      scale_data where
  input :=
    input
  canonicalCore :=
    input.toCanonicalCalibratedExactnessCore
  checkerSemantics :=
    input.toSingletonGapCalibratedFourPieceInput.checkerSemantics
  finiteEnumeration :=
    input.toSingletonGapCalibratedFourPieceInput.finiteEnumeration
  rejectionExtractor :=
    input.toSingletonGapCalibratedFourPieceInput.rejectionExtractor
  proofLengthExactness :=
    input.toSingletonGapCalibratedFourPieceInput.proofLengthExactness
  noSmallCore :=
    input.toComputableFiniteSearchNoSmallCore

theorem closure_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
        scale_data) :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data) :=
  ⟨input.toClosure⟩

end ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput

namespace ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure

def computableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data :=
  closure.rejectionExtractor.toCheckerComputableSearchProfile

theorem generated_components_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data) :
    Nonempty
        (InternalPudlakTheorem5CheckerFiniteEnumeration
          closure.checkerSemantics) ∧
      Nonempty
        (InternalPudlakTheorem5CheckerComputableRejectionExtractor
          closure.checkerSemantics closure.finiteEnumeration) ∧
        Nonempty
          (InternalPudlakTheorem5CheckerProofLengthExactness
            closure.checkerSemantics) ∧
          Nonempty
            (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
              scale_data) ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨closure.finiteEnumeration⟩,
    ⟨closure.rejectionExtractor⟩,
    ⟨closure.proofLengthExactness⟩,
    ⟨closure.computableSearchProfile⟩,
    ⟨closure.noSmallCore⟩⟩

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((closure.input.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (closure.input.proof_length_gap.gap_for_polynomial_upper f hf).witness
        N :=
  rfl

theorem accepted_code_to_formulaCode_derivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode
        code) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics
      formulaCode :=
  closure.input.toCanonicalCalibratedExactnessCore
    |>.accepted_decoded_code_to_formulaCode_derivable
      formulaCode code haccepted

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  closure.input.feeds_month9_month10_checker_bridge

end ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure

/-! ## Final three-certificate endpoint -/

/-- Final named endpoint for the Month 11-12 constructive checker route.  The
fields are exactly the three remaining project-level certificates: strict
growth of the scale, an actual proof-length search gap, and calibration of
actual proof length to the scale.  Everything else is generated below. -/
structure ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  proof_length_gap :
    ComputableSearchGapCertificate
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n))
  proof_length_eq_scale :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real)

namespace ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint

def toScaleStrictSizeExactProofGapInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapInput
      scale_data where
  scale_strict :=
    endpoint.scale_strict
  proof_length_gap :=
    endpoint.proof_length_gap
  proof_length_eq_scale :=
    endpoint.proof_length_eq_scale

def toClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
      scale_data :=
  endpoint.toScaleStrictSizeExactProofGapInput.toClosure

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  endpoint.toScaleStrictSizeExactProofGapInput
    |>.toCanonicalCalibratedExactnessCore

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  endpoint.toScaleStrictSizeExactProofGapInput
    |>.toComputableFiniteSearchNoSmallCore

theorem closure_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data) :=
  endpoint.toScaleStrictSizeExactProofGapInput.closure_nonempty

theorem canonical_core_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨endpoint.toCanonicalCalibratedExactnessCore⟩

theorem generated_components_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    Nonempty
        (InternalPudlakTheorem5CheckerFiniteEnumeration
          endpoint.toClosure.checkerSemantics) ∧
      Nonempty
        (InternalPudlakTheorem5CheckerComputableRejectionExtractor
          endpoint.toClosure.checkerSemantics
          endpoint.toClosure.finiteEnumeration) ∧
        Nonempty
          (InternalPudlakTheorem5CheckerProofLengthExactness
            endpoint.toClosure.checkerSemantics) ∧
          Nonempty
            (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
              scale_data) ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  endpoint.toClosure.generated_components_nonempty

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((endpoint.toScaleStrictSizeExactProofGapInput
        |>.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (endpoint.proof_length_gap.gap_for_polynomial_upper f hf).witness N :=
  rfl

theorem accepted_code_to_formulaCode_derivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode
        code) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics
      formulaCode :=
  endpoint.toClosure.accepted_code_to_formulaCode_derivable
    formulaCode code haccepted

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  endpoint.toScaleStrictSizeExactProofGapInput
    |>.feeds_month9_month10_checker_bridge

theorem final_month11_month12_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    Nonempty
        (ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
          scale_data) ∧
      Nonempty PAHilbertCanonicalCalibratedExactnessCore ∧
        Nonempty
          (InternalPudlakTheorem5CheckerFiniteEnumeration
            endpoint.toClosure.checkerSemantics) ∧
          Nonempty
            (InternalPudlakTheorem5CheckerComputableRejectionExtractor
              endpoint.toClosure.checkerSemantics
              endpoint.toClosure.finiteEnumeration) ∧
            Nonempty
              (InternalPudlakTheorem5CheckerProofLengthExactness
                endpoint.toClosure.checkerSemantics) ∧
              Nonempty
                (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
                  scale_data) ∧
                Nonempty
                  InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} := by
  have hcomponents := endpoint.generated_components_nonempty
  exact
    ⟨endpoint.closure_nonempty,
      endpoint.canonical_core_nonempty,
      hcomponents.1,
      hcomponents.2.1,
      hcomponents.2.2.1,
      hcomponents.2.2.2.1,
      hcomponents.2.2.2.2⟩

end ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint

/-- Materialized handoff payload generated from the final three-certificate
endpoint.  It bundles the closure, canonical core, checker-native four-piece,
Month 9-10 search profile, no-small core, accepted-code exactness, and the
same-witness equation for the transported proof-length gap. -/
structure ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  endpoint :
    ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data
  closure :
    ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
      scale_data
  canonicalCore :
    PAHilbertCanonicalCalibratedExactnessCore
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      closure.checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      closure.checkerSemantics closure.finiteEnumeration
  proofLengthExactness :
    InternalPudlakTheorem5CheckerProofLengthExactness
      closure.checkerSemantics
  computableSearchProfile :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data
  noSmallCore :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}
  acceptedCodeExactness :
    ∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode
        code →
      PAHilbertFormulaCodeDerivable
        concretePAHilbertTheorem5DerivabilitySemantics
        formulaCode
  transportedGapWitnessEq :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ((endpoint.toScaleStrictSizeExactProofGapInput
          |>.toStrictScaleSingletonExactProofLengthGapInput
          |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
        (endpoint.proof_length_gap.gap_for_polynomial_upper f hf).witness N

namespace ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint

def toDeliverables
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
      scale_data where
  endpoint :=
    endpoint
  closure :=
    endpoint.toClosure
  canonicalCore :=
    endpoint.toCanonicalCalibratedExactnessCore
  finiteEnumeration :=
    endpoint.toClosure.finiteEnumeration
  rejectionExtractor :=
    endpoint.toClosure.rejectionExtractor
  proofLengthExactness :=
    endpoint.toClosure.proofLengthExactness
  computableSearchProfile :=
    endpoint.toClosure.computableSearchProfile
  noSmallCore :=
    endpoint.toComputableFiniteSearchNoSmallCore
  acceptedCodeExactness :=
    endpoint.accepted_code_to_formulaCode_derivable
  transportedGapWitnessEq :=
    endpoint.transported_gap_witness_eq

theorem deliverables_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
        scale_data) :=
  ⟨endpoint.toDeliverables⟩

end ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint

/-- Month 11-12 exactness core.  This is the isolated bridge from the
PA/Hilbert checker layer to the Month 9-10 finite-search no-small-code core.
The fields record exactly what remains to be supplied by the detailed
internalization of the checker. -/
structure PAHilbertCheckerExactnessCore : Type (q + 1) where
  checker : PAHilbertChecker
  semantics : PAHilbertDerivabilitySemantics
  recognizerExactness :
    PAHilbertAxiomRecognizerExactness checker.recognizer semantics
  checkerInterface :
    PAHilbertCheckerInterface checker semantics
  scale_data : InternalPudlakTheorem5ScaleData
  proof_code_semantics :
    ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  proof_code_semantics_bridge :
    PAHilbertProofCodeSemanticsBridge.{q}
      checker scale_data proof_code_semantics
  small_code_enumeration :
    PAHilbertSmallCodeEnumeration.{q} scale_data proof_code_semantics
  finite_search_exclusion :
    InternalPudlakTheorem5FiniteSearchExclusion
      scale_data proof_code_semantics
      small_code_enumeration.toInternalPudlakTheorem5SmallCodeSearch
  computable_search_exclusion :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data proof_code_semantics
      small_code_enumeration.toInternalPudlakTheorem5SmallCodeSearch
  computable_finite_search_no_small_core :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}
  no_small_core_scale_data_eq :
    computable_finite_search_no_small_core.scale_data = scale_data
  no_small_core_proof_code_semantics_heq :
    HEq
      computable_finite_search_no_small_core.proof_length_model.proof_code_semantics
      proof_code_semantics
  no_small_core_small_code_search_heq :
    HEq
      computable_finite_search_no_small_core.small_code_search
      small_code_enumeration.toInternalPudlakTheorem5SmallCodeSearch
  no_small_core_computable_search_exclusion_heq :
    HEq
      computable_finite_search_no_small_core.computable_search_exclusion
      computable_search_exclusion

namespace PAHilbertCheckerExactnessCore

def toInternalPudlakTheorem5SmallCodeSearch
    (core : PAHilbertCheckerExactnessCore.{q}) :
    InternalPudlakTheorem5SmallCodeSearch
      core.scale_data core.proof_code_semantics :=
  core.small_code_enumeration.toInternalPudlakTheorem5SmallCodeSearch

theorem formulaAt_code_eq_powerBoundRawCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat) :
    (core.small_code_enumeration.formulaAt n).code =
      core.scale_data.powerBoundRawCode n :=
  core.small_code_enumeration.formulaAt_code_eq_powerBoundRawCode n

theorem noSmallCore_scale_data_eq
    (core : PAHilbertCheckerExactnessCore.{q}) :
    core.computable_finite_search_no_small_core.scale_data =
      core.scale_data :=
  core.no_small_core_scale_data_eq

theorem noSmallCore_proof_code_semantics_heq
    (core : PAHilbertCheckerExactnessCore.{q}) :
    HEq
      core.computable_finite_search_no_small_core.proof_length_model.proof_code_semantics
      core.proof_code_semantics :=
  core.no_small_core_proof_code_semantics_heq

theorem noSmallCore_small_code_search_heq
    (core : PAHilbertCheckerExactnessCore.{q}) :
    HEq
      core.computable_finite_search_no_small_core.small_code_search
      core.toInternalPudlakTheorem5SmallCodeSearch :=
  core.no_small_core_small_code_search_heq

theorem noSmallCore_computable_search_exclusion_heq
    (core : PAHilbertCheckerExactnessCore.{q}) :
    HEq
      core.computable_finite_search_no_small_core.computable_search_exclusion
      core.computable_search_exclusion :=
  core.no_small_core_computable_search_exclusion_heq

theorem noSmallCore_powerBoundRawCode_eq
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat) :
    core.computable_finite_search_no_small_core.scale_data.powerBoundRawCode n =
      core.scale_data.powerBoundRawCode n := by
  rw [core.noSmallCore_scale_data_eq]

theorem small_code_search_nonempty
    (core : PAHilbertCheckerExactnessCore.{q}) :
    Nonempty
      (InternalPudlakTheorem5SmallCodeSearch
        core.scale_data core.proof_code_semantics) :=
  ⟨core.toInternalPudlakTheorem5SmallCodeSearch⟩

/-- Projection of the exactness core to the minimal paper-proof checker
interface. -/
def paperProofInterface
    (core : PAHilbertCheckerExactnessCore.{q}) :
    PAHilbertCheckerPaperProofInterface core.checker core.semantics :=
  core.checkerInterface.toPaperProofInterface

theorem paperProofInterface_nonempty
    (core : PAHilbertCheckerExactnessCore.{q}) :
    Nonempty
      (PAHilbertCheckerPaperProofInterface core.checker core.semantics) :=
  ⟨core.paperProofInterface⟩

theorem paperProofInterface_acceptedDecodedCode_to_formulaCodeDerivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode core.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable core.semantics formulaCode :=
  core.paperProofInterface.accepted_decoded_code_to_formulaCode_derivable
    formulaCode code haccepted

theorem paperProofInterface_rejectsFiniteList_to_noSmallAcceptedProofCodeForFormulaCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        core.checker.rejectsCode code formula = true) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode
      core.checker formula.code finiteList.bound :=
  core.paperProofInterface
    |>.rejects_finite_list_to_no_small_accepted_proof_code_for_formula_code
      formula finiteList hrejects

theorem acceptedProofObject_to_derivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : core.checker.accepts proof formula = true) :
    core.semantics.Derivable formula :=
  PAHilbertCheckerInterface.accepts_to_derivable
    core.checkerInterface proof formula haccepts

theorem acceptedProofObject_conclusion_eq
    (core : PAHilbertCheckerExactnessCore.{q})
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : core.checker.accepts proof formula = true) :
    proof.conclusion = formula :=
  PAHilbertCheckerInterface.accepts_to_conclusion_eq
    core.checkerInterface proof formula haccepts

theorem acceptedProofObject_to_formulaCodeDerivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : core.checker.accepts proof formula = true) :
    PAHilbertFormulaCodeDerivable core.semantics formula.code :=
  PAHilbertCheckerInterface.accepts_to_formulaCode_derivable
    core.checkerInterface proof formula haccepts

theorem decodeProofCode_complete
    (core : PAHilbertCheckerExactnessCore.{q})
    (proof : PAHilbertProofObject) :
    core.checker.decoder.decode proof.code = some proof :=
  PAHilbertCheckerInterface.decode_proof_code_complete
    core.checkerInterface proof

theorem rejectsUndecodable
    (core : PAHilbertCheckerExactnessCore.{q})
    (code : Nat) (formula : PAHilbertFormula)
    (hdecode : core.checker.decoder.decode code = none) :
    core.checker.rejectsCode code formula = true :=
  PAHilbertCheckerInterface.rejects_undecodable
    core.checkerInterface code formula hdecode

theorem recognizesAny_iff_schemeDisjunction
    (core : PAHilbertCheckerExactnessCore.{q})
    (formula : PAHilbertFormula) :
    core.checker.recognizer.recognizesAny formula = true ↔
      core.recognizerExactness.schemeSemantics.IsLogicalAxiom formula ∨
        core.recognizerExactness.schemeSemantics.IsEqualityAxiom formula ∨
          core.recognizerExactness.schemeSemantics.IsInductionSchema formula ∨
            core.recognizerExactness.schemeSemantics.IsPAArithmeticAxiom formula :=
  PAHilbertAxiomRecognizerExactness.recognizes_any_iff
    core.recognizerExactness formula

theorem recognizedAny_to_derivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (formula : PAHilbertFormula)
    (hrecognized :
      core.checker.recognizer.recognizesAny formula = true) :
    core.semantics.Derivable formula :=
  PAHilbertAxiomRecognizerExactness.recognizes_any_to_derivable
    core.recognizerExactness formula hrecognized

theorem recognizerSchemeSoundness_statements
    (core : PAHilbertCheckerExactnessCore.{q}) :
    (∀ formula : PAHilbertFormula,
      core.checker.recognizer.recognizesLogical formula = true →
        core.semantics.Derivable formula) ∧
      (∀ formula : PAHilbertFormula,
        core.checker.recognizer.recognizesEquality formula = true →
          core.semantics.Derivable formula) ∧
        (∀ formula : PAHilbertFormula,
          core.checker.recognizer.recognizesInduction formula = true →
            core.semantics.Derivable formula) ∧
          (∀ formula : PAHilbertFormula,
            core.checker.recognizer.recognizesPAArithmetic formula = true →
              core.semantics.Derivable formula) ∧
            (∀ formula : PAHilbertFormula,
              core.checker.recognizer.recognizesAny formula = true →
                core.semantics.Derivable formula) :=
  ⟨core.recognizerExactness.logicalSound,
    core.recognizerExactness.equalitySound,
    core.recognizerExactness.inductionSound,
    core.recognizerExactness.paArithmeticSound,
    core.recognizerExactness.recognizesAnySound⟩

theorem acceptedProofObject_to_checkedTrace
    (core : PAHilbertCheckerExactnessCore.{q})
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : core.checker.accepts proof formula = true) :
    ∃ trace : PAHilbertCheckedProofTrace,
      core.checkerInterface.traceOf proof = some trace ∧
        trace.proof = proof ∧
          core.checkerInterface.traceChecker.checkTrace trace = true :=
  PAHilbertCheckerInterface.accepts_to_checked_trace
    core.checkerInterface proof formula haccepts

theorem checkedTrace_to_derivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (trace : PAHilbertCheckedProofTrace)
    (htrace :
      core.checkerInterface.traceChecker.checkTrace trace = true) :
    core.semantics.Derivable trace.proof.conclusion :=
  PAHilbertCheckerInterface.checked_trace_to_derivable
    core.checkerInterface trace htrace

theorem checkedTrace_steps_checked
    (core : PAHilbertCheckerExactnessCore.{q})
    (trace : PAHilbertCheckedProofTrace)
    (htrace :
      core.checkerInterface.traceChecker.checkTrace trace = true)
    (step : PAHilbertProofStep)
    (hstep : step ∈ trace.decodedSteps) :
    core.checkerInterface.traceChecker.checkStep trace step = true :=
  PAHilbertCheckerInterface.checked_trace_steps_checked
    core.checkerInterface trace htrace step hstep

theorem checkedStep_to_derivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (trace : PAHilbertCheckedProofTrace)
    (step : PAHilbertProofStep)
    (hstep : step ∈ trace.decodedSteps)
    (hchecked :
      core.checkerInterface.traceChecker.checkStep trace step = true) :
    core.semantics.Derivable step.formula :=
  PAHilbertCheckerInterface.checked_step_to_derivable
    core.checkerInterface trace step hstep hchecked

theorem checkedTrace_to_derivable_via_steps
    (core : PAHilbertCheckerExactnessCore.{q})
    (trace : PAHilbertCheckedProofTrace)
    (htrace :
      core.checkerInterface.traceChecker.checkTrace trace = true) :
    core.semantics.Derivable trace.proof.conclusion :=
  PAHilbertCheckerInterface.checked_trace_to_derivable_via_steps
    core.checkerInterface trace htrace

theorem allowedRuleApplication_to_derivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (rule : PAHilbertInferenceRule)
    (premises : List PAHilbertFormula)
    (conclusion : PAHilbertFormula)
    (hallowed : core.checker.ruleAllowed rule = true)
    (happlication :
      core.checkerInterface.inferenceRuleSemantics.RuleApplication
        rule premises conclusion)
    (hpremises :
      ∀ premise : PAHilbertFormula,
        premise ∈ premises → core.semantics.Derivable premise) :
    core.semantics.Derivable conclusion :=
  PAHilbertCheckerInterface.allowed_rule_application_to_derivable
    core.checkerInterface rule premises conclusion
    hallowed happlication hpremises

theorem ruleAllowed_to_exists_ruleApplication
    (core : PAHilbertCheckerExactnessCore.{q})
    (rule : PAHilbertInferenceRule)
    (hallowed : core.checker.ruleAllowed rule = true) :
    ∃ premises : List PAHilbertFormula,
      ∃ conclusion : PAHilbertFormula,
        core.checkerInterface.inferenceRuleSemantics.RuleApplication
          rule premises conclusion :=
  PAHilbertCheckerInterface.ruleAllowed_to_exists_ruleApplication
    core.checkerInterface rule hallowed

theorem ruleApplication_to_ruleAllowed
    (core : PAHilbertCheckerExactnessCore.{q})
    (rule : PAHilbertInferenceRule)
    (premises : List PAHilbertFormula)
    (conclusion : PAHilbertFormula)
    (happlication :
      core.checkerInterface.inferenceRuleSemantics.RuleApplication
        rule premises conclusion) :
    core.checker.ruleAllowed rule = true :=
  PAHilbertCheckerInterface.ruleApplication_to_ruleAllowed
    core.checkerInterface rule premises conclusion happlication

theorem decodedRejects_to_notAccepted
    (core : PAHilbertCheckerExactnessCore.{q})
    (code : Nat) (proof : PAHilbertProofObject)
    (formula : PAHilbertFormula)
    (hdecode : core.checker.decoder.decode code = some proof)
    (hconclusion : proof.conclusion = formula)
    (hrejects : core.checker.rejectsCode code formula = true) :
    core.checker.accepts proof formula = false :=
  PAHilbertCheckerInterface.decoded_rejects_to_not_accepted
    core.checkerInterface code proof formula hdecode hconclusion hrejects

theorem acceptedDecodedCode_to_formulaCodeDerivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        core.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable core.semantics formulaCode :=
  PAHilbertCheckerInterface.accepted_decoded_code_to_formulaCode_derivable
    core.checkerInterface formulaCode code haccepted

theorem semanticCheck_to_acceptedProofCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (code : core.proof_code_semantics.Code)
    (formulaCode : _root_.FormulaCode)
    (hchecks : core.proof_code_semantics.checks code formulaCode) :
    PAHilbertAcceptedProofCodeForFormulaCode core.checker
      formulaCode (core.proof_code_semantics_bridge.toNatCode code) :=
  core.proof_code_semantics_bridge.checks_to_acceptedProofCode
    code formulaCode hchecks

theorem semanticCheck_to_formulaCodeDerivable
    (core : PAHilbertCheckerExactnessCore.{q})
    (code : core.proof_code_semantics.Code)
    (formulaCode : _root_.FormulaCode)
    (hchecks : core.proof_code_semantics.checks code formulaCode) :
    PAHilbertFormulaCodeDerivable core.semantics formulaCode :=
  PAHilbertProofCodeSemanticsBridge.checks_to_formulaCodeDerivable
    core.checkerInterface core.proof_code_semantics_bridge
    code formulaCode hchecks

theorem acceptedProofCode_iff_existsSemanticCheck
    (core : PAHilbertCheckerExactnessCore.{q})
    (formulaCode : _root_.FormulaCode) (natCode : Nat) :
    PAHilbertAcceptedProofCodeForFormulaCode core.checker formulaCode natCode ↔
      ∃ code : core.proof_code_semantics.Code,
        core.proof_code_semantics_bridge.toNatCode code = natCode ∧
          core.proof_code_semantics.checks code formulaCode :=
  PAHilbertProofCodeSemanticsBridge.acceptedProofCode_iff_existsSemanticCheck
    core.proof_code_semantics_bridge formulaCode natCode

theorem finiteListRejects_to_noAcceptedDecodedCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        core.checker.rejectsCode code formula = true)
    (code : Nat) (proof : PAHilbertProofObject)
    (hsmall : code < finiteList.bound)
    (hdecode : core.checker.decoder.decode code = some proof)
    (hconclusion : proof.conclusion = formula) :
    core.checker.accepts proof formula = false :=
  PAHilbertCheckerInterface.rejects_finite_list_to_no_accepted_decoded_code
    core.checkerInterface formula finiteList hrejects
    code proof hsmall hdecode hconclusion

theorem noSmallProofCodeAt
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat)
    (hrejects :
      core.small_code_enumeration.rejectsAllAt core.checker n) :
    PAHilbertNoSmallProofCode core.checker
      (core.small_code_enumeration.formulaAt n)
      (core.small_code_enumeration.finiteListAt n).bound :=
  PAHilbertSmallCodeEnumeration.noSmallProofCodeAt
    core.checkerInterface core.small_code_enumeration n hrejects

theorem noSmallProofCodeAt_powerBoundRawCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat)
    (hrejects :
      core.small_code_enumeration.rejectsAllAt core.checker n) :
    PAHilbertNoSmallProofCodeForFormulaCode core.checker
      (core.scale_data.powerBoundRawCode n)
      (core.small_code_enumeration.finiteListAt n).bound :=
  PAHilbertSmallCodeEnumeration.noSmallProofCodeAt_powerBoundRawCode
    core.checkerInterface core.small_code_enumeration n hrejects

theorem noSmallAcceptedProofCodeAt_powerBoundRawCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat)
    (hrejects :
      core.small_code_enumeration.rejectsAllAt core.checker n) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode core.checker
      (core.scale_data.powerBoundRawCode n)
      (core.small_code_enumeration.finiteListAt n).bound :=
  PAHilbertSmallCodeEnumeration.noSmallAcceptedProofCodeAt_powerBoundRawCode
    core.checkerInterface core.small_code_enumeration n hrejects

theorem paperProofInterface_noSmallAcceptedProofCodeAt_powerBoundRawCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat)
    (hrejects :
      core.small_code_enumeration.rejectsAllAt core.checker n) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode core.checker
      (core.scale_data.powerBoundRawCode n)
      (core.small_code_enumeration.finiteListAt n).bound :=
  PAHilbertSmallCodeEnumeration.noSmallAcceptedProofCodeAt_powerBoundRawCode_fromPaperProofInterface
    core.paperProofInterface core.small_code_enumeration n hrejects

theorem paperProofInterface_finiteListRejects_to_noSemanticCheckAt_powerBoundRawCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat)
    (hrejects :
      core.small_code_enumeration.rejectsAllAt core.checker n)
    (code : core.proof_code_semantics.Code)
    (hsize :
      core.proof_code_semantics.size code <
        (core.small_code_enumeration.finiteListAt n).bound)
    (hchecks :
      core.proof_code_semantics.checks code
        (core.scale_data.powerBoundRawCode n)) :
    False :=
  PAHilbertProofCodeSemanticsBridge.noSmallAcceptedProofCode_to_noSemanticCheck_of_size_lt
    core.proof_code_semantics_bridge
    (core.paperProofInterface_noSmallAcceptedProofCodeAt_powerBoundRawCode
      n hrejects)
    code hsize hchecks

theorem finiteListRejects_to_noSemanticCheckAt_powerBoundRawCode
    (core : PAHilbertCheckerExactnessCore.{q})
    (n : Nat)
    (hrejects :
      core.small_code_enumeration.rejectsAllAt core.checker n)
    (code : core.proof_code_semantics.Code)
    (hsize :
      core.proof_code_semantics.size code <
        (core.small_code_enumeration.finiteListAt n).bound)
    (hchecks :
      core.proof_code_semantics.checks code
        (core.scale_data.powerBoundRawCode n)) :
    False :=
  PAHilbertProofCodeSemanticsBridge.noSmallAcceptedProofCode_to_noSemanticCheck_of_size_lt
    core.proof_code_semantics_bridge
    (core.noSmallAcceptedProofCodeAt_powerBoundRawCode n hrejects)
    code hsize hchecks

theorem toInternalPudlakTheorem5FiniteSearchExclusion
    (core : PAHilbertCheckerExactnessCore.{q}) :
    InternalPudlakTheorem5FiniteSearchExclusion
      core.scale_data core.proof_code_semantics
      core.toInternalPudlakTheorem5SmallCodeSearch :=
  core.finite_search_exclusion

def toInternalPudlakTheorem5ComputableFiniteSearchExclusion
    (core : PAHilbertCheckerExactnessCore.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      core.scale_data core.proof_code_semantics
      core.toInternalPudlakTheorem5SmallCodeSearch :=
  core.computable_search_exclusion

def computableSearchWitness
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) : Nat :=
  core.toInternalPudlakTheorem5ComputableFiniteSearchExclusion
    |>.witness f hf N

def computableSearchCutoff
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) : Nat :=
  core.toInternalPudlakTheorem5ComputableFiniteSearchExclusion
    |>.cutoff f hf N

theorem computableSearchWitness_ge
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    N ≤ core.computableSearchWitness f hf N :=
  core.toInternalPudlakTheorem5ComputableFiniteSearchExclusion
    |>.witness_ge f hf N

theorem computableSearchCutoff_gt
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    f (core.computableSearchWitness f hf N) <
      (core.computableSearchCutoff f hf N : Real) :=
  core.toInternalPudlakTheorem5ComputableFiniteSearchExclusion
    |>.cutoff_gt f hf N

theorem computableSearchRejects_candidates
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat)
    (c : core.proof_code_semantics.Code)
    (hc :
      c ∈
        core.toInternalPudlakTheorem5SmallCodeSearch.candidates
          (core.computableSearchWitness f hf N)
          (core.computableSearchCutoff f hf N)) :
    ¬ core.proof_code_semantics.checks c
      (core.scale_data.powerBoundRawCode
        (core.computableSearchWitness f hf N)) :=
  core.toInternalPudlakTheorem5ComputableFiniteSearchExclusion
    |>.rejects_candidates f hf N c hc

theorem computableSearchNoSmall_at_witness
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat)
    (c : core.proof_code_semantics.Code)
    (hchecks :
      core.proof_code_semantics.checks c
        (core.scale_data.powerBoundRawCode
          (core.computableSearchWitness f hf N))) :
    f (core.computableSearchWitness f hf N) <
      (core.proof_code_semantics.size c : Real) := by
  by_contra hnot
  push Not at hnot
  have hsize_lt_cutoff_real :
      (core.proof_code_semantics.size c : Real) <
        (core.computableSearchCutoff f hf N : Real) :=
    lt_of_le_of_lt hnot (core.computableSearchCutoff_gt f hf N)
  have hsize_lt_cutoff :
      core.proof_code_semantics.size c <
        core.computableSearchCutoff f hf N := by
    exact_mod_cast hsize_lt_cutoff_real
  have hcandidates :
      c ∈
        core.toInternalPudlakTheorem5SmallCodeSearch.candidates
          (core.computableSearchWitness f hf N)
          (core.computableSearchCutoff f hf N) :=
    core.toInternalPudlakTheorem5SmallCodeSearch.complete
      (core.computableSearchWitness f hf N)
      (core.computableSearchCutoff f hf N)
      c hchecks hsize_lt_cutoff
  exact
    (core.computableSearchRejects_candidates f hf N c hcandidates)
      hchecks

theorem computableSearchMinProofCodeSize_gt
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    (core.proof_code_semantics.minProofCodeSize
      (core.scale_data.powerBoundRawCode
        (core.computableSearchWitness f hf N))
      ⟨core.computableSearchWitness f hf N, rfl⟩ : Real) >
      f (core.computableSearchWitness f hf N) := by
  classical
  let n : Nat := core.computableSearchWitness f hf N
  let code : _root_.FormulaCode := core.scale_data.powerBoundRawCode n
  let hcode :
      InternalPudlakTheorem5PowerBoundRelevantCode core.scale_data code :=
    ⟨n, rfl⟩
  have hspec :
      core.proof_code_semantics.HasProofCodeOfSize code
        (core.proof_code_semantics.minProofCodeSize code hcode) :=
    Nat.find_spec
      (ProofCodeSemantics.exists_hasProofCodeOfSize
        core.proof_code_semantics hcode)
  rcases hspec with ⟨c, hchecks, hsize_le⟩
  have hno_small :
      f n < (core.proof_code_semantics.size c : Real) := by
    exact core.computableSearchNoSmall_at_witness f hf N c hchecks
  have hsize_le_min :
      (core.proof_code_semantics.size c : Real) ≤
        (core.proof_code_semantics.minProofCodeSize code hcode : Real) := by
    exact_mod_cast hsize_le
  exact lt_of_lt_of_le hno_small hsize_le_min

def computedLowerSearchWitness
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      core.scale_data
      core.proof_code_semantics
      core.toInternalPudlakTheorem5SmallCodeSearch
      f hf N where
  n := core.computableSearchWitness f hf N
  K := core.computableSearchCutoff f hf N
  n_ge := core.computableSearchWitness_ge f hf N
  cutoff_gt := core.computableSearchCutoff_gt f hf N
  rejects_candidates :=
    core.computableSearchRejects_candidates f hf N
  no_small_at_n :=
    core.computableSearchNoSmall_at_witness f hf N
  minProofCodeSize_gt :=
    core.computableSearchMinProofCodeSize_gt f hf N

theorem computedLowerSearchWitness_nonempty
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    Nonempty
      (InternalPudlakTheorem5ComputedLowerSearchWitness
        core.scale_data
        core.proof_code_semantics
        core.toInternalPudlakTheorem5SmallCodeSearch
        f hf N) :=
  ⟨core.computedLowerSearchWitness f hf N⟩

def toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
    (core : PAHilbertCheckerExactnessCore.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  core.computable_finite_search_no_small_core

theorem computable_finite_search_no_small_core_nonempty
    (core : PAHilbertCheckerExactnessCore.{q}) :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  ⟨core.toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore⟩

end PAHilbertCheckerExactnessCore

/-- Month 11-12 checklist wrapper.  It keeps the exactness core as the single
source of mathematical assumptions, then exposes the paper-facing closure
statements needed by later integration files. -/
structure Month11Month12PAHilbertCheckerChecklist : Type (q + 1) where
  exactness_core : PAHilbertCheckerExactnessCore.{q}

namespace Month11Month12PAHilbertCheckerChecklist

def checker
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    PAHilbertChecker :=
  h.exactness_core.checker

def semantics
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    PAHilbertDerivabilitySemantics :=
  h.exactness_core.semantics

def paperProofInterface
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    PAHilbertCheckerPaperProofInterface h.checker h.semantics :=
  h.exactness_core.paperProofInterface

theorem paperProofInterface_nonempty
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    Nonempty
      (PAHilbertCheckerPaperProofInterface h.checker h.semantics) :=
  ⟨h.paperProofInterface⟩

theorem paperProofInterface_acceptedDecodedCode_to_formulaCodeDerivable
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode h.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable h.semantics formulaCode :=
  h.exactness_core.paperProofInterface_acceptedDecodedCode_to_formulaCodeDerivable
    formulaCode code haccepted

theorem paperProofInterface_rejectsFiniteList_to_noSmallAcceptedProofCodeForFormulaCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (formula : PAHilbertFormula) (finiteList : PAHilbertFiniteCodeList)
    (hrejects :
      ∀ code : Nat, code ∈ finiteList.codes →
        h.checker.rejectsCode code formula = true) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode
      h.checker formula.code finiteList.bound :=
  h.exactness_core
    |>.paperProofInterface_rejectsFiniteList_to_noSmallAcceptedProofCodeForFormulaCode
      formula finiteList hrejects

theorem decodeProofCode_complete
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (proof : PAHilbertProofObject) :
    h.checker.decoder.decode proof.code = some proof :=
  h.exactness_core.decodeProofCode_complete proof

theorem rejectsUndecodable
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (code : Nat) (formula : PAHilbertFormula)
    (hdecode : h.checker.decoder.decode code = none) :
    h.checker.rejectsCode code formula = true :=
  h.exactness_core.rejectsUndecodable code formula hdecode

theorem acceptedProofObject_conclusion_eq
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : h.checker.accepts proof formula = true) :
    proof.conclusion = formula :=
  h.exactness_core.acceptedProofObject_conclusion_eq
    proof formula haccepts

theorem acceptedProofObject_to_formulaCodeDerivable
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (proof : PAHilbertProofObject) (formula : PAHilbertFormula)
    (haccepts : h.checker.accepts proof formula = true) :
    PAHilbertFormulaCodeDerivable h.semantics formula.code :=
  h.exactness_core.acceptedProofObject_to_formulaCodeDerivable
    proof formula haccepts

def toInternalPudlakTheorem5SmallCodeSearch
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    InternalPudlakTheorem5SmallCodeSearch
      h.exactness_core.scale_data
      h.exactness_core.proof_code_semantics :=
  h.exactness_core.toInternalPudlakTheorem5SmallCodeSearch

theorem formulaAt_code_eq_powerBoundRawCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (n : Nat) :
    (h.exactness_core.small_code_enumeration.formulaAt n).code =
      h.exactness_core.scale_data.powerBoundRawCode n :=
  h.exactness_core.formulaAt_code_eq_powerBoundRawCode n

theorem noSmallCore_scale_data_eq
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    h.exactness_core.computable_finite_search_no_small_core.scale_data =
      h.exactness_core.scale_data :=
  h.exactness_core.noSmallCore_scale_data_eq

theorem noSmallCore_proof_code_semantics_heq
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    HEq
      h.exactness_core.computable_finite_search_no_small_core.proof_length_model.proof_code_semantics
      h.exactness_core.proof_code_semantics :=
  h.exactness_core.noSmallCore_proof_code_semantics_heq

theorem noSmallCore_small_code_search_heq
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    HEq
      h.exactness_core.computable_finite_search_no_small_core.small_code_search
      h.toInternalPudlakTheorem5SmallCodeSearch :=
  h.exactness_core.noSmallCore_small_code_search_heq

theorem noSmallCore_computable_search_exclusion_heq
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    HEq
      h.exactness_core.computable_finite_search_no_small_core.computable_search_exclusion
      h.exactness_core.computable_search_exclusion :=
  h.exactness_core.noSmallCore_computable_search_exclusion_heq

theorem noSmallCore_powerBoundRawCode_eq
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (n : Nat) :
    h.exactness_core.computable_finite_search_no_small_core.scale_data.powerBoundRawCode n =
      h.exactness_core.scale_data.powerBoundRawCode n :=
  h.exactness_core.noSmallCore_powerBoundRawCode_eq n

theorem noSmallCore_dependency_coherence
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    h.exactness_core.computable_finite_search_no_small_core.scale_data =
      h.exactness_core.scale_data ∧
      HEq
        h.exactness_core.computable_finite_search_no_small_core.proof_length_model.proof_code_semantics
        h.exactness_core.proof_code_semantics ∧
        HEq
          h.exactness_core.computable_finite_search_no_small_core.small_code_search
          h.toInternalPudlakTheorem5SmallCodeSearch ∧
          HEq
            h.exactness_core.computable_finite_search_no_small_core.computable_search_exclusion
            h.exactness_core.computable_search_exclusion :=
  ⟨h.noSmallCore_scale_data_eq,
    h.noSmallCore_proof_code_semantics_heq,
    h.noSmallCore_small_code_search_heq,
    h.noSmallCore_computable_search_exclusion_heq⟩

theorem noSmallProofCodeAt_powerBoundRawCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (n : Nat)
    (hrejects :
      h.exactness_core.small_code_enumeration.rejectsAllAt h.checker n) :
    PAHilbertNoSmallProofCodeForFormulaCode h.checker
      (h.exactness_core.scale_data.powerBoundRawCode n)
      (h.exactness_core.small_code_enumeration.finiteListAt n).bound :=
  h.exactness_core.noSmallProofCodeAt_powerBoundRawCode n hrejects

theorem noSmallAcceptedProofCodeAt_powerBoundRawCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (n : Nat)
    (hrejects :
      h.exactness_core.small_code_enumeration.rejectsAllAt h.checker n) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode h.checker
      (h.exactness_core.scale_data.powerBoundRawCode n)
      (h.exactness_core.small_code_enumeration.finiteListAt n).bound :=
  h.exactness_core.noSmallAcceptedProofCodeAt_powerBoundRawCode n hrejects

theorem paperProofInterface_noSmallAcceptedProofCodeAt_powerBoundRawCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (n : Nat)
    (hrejects :
      h.exactness_core.small_code_enumeration.rejectsAllAt h.checker n) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode h.checker
      (h.exactness_core.scale_data.powerBoundRawCode n)
      (h.exactness_core.small_code_enumeration.finiteListAt n).bound :=
  h.exactness_core
    |>.paperProofInterface_noSmallAcceptedProofCodeAt_powerBoundRawCode
      n hrejects

theorem paperProofInterface_finiteListRejects_to_noSemanticCheckAt_powerBoundRawCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (n : Nat)
    (hrejects :
      h.exactness_core.small_code_enumeration.rejectsAllAt h.checker n)
    (code : h.exactness_core.proof_code_semantics.Code)
    (hsize :
      h.exactness_core.proof_code_semantics.size code <
        (h.exactness_core.small_code_enumeration.finiteListAt n).bound)
    (hchecks :
      h.exactness_core.proof_code_semantics.checks code
        (h.exactness_core.scale_data.powerBoundRawCode n)) :
    False :=
  h.exactness_core
    |>.paperProofInterface_finiteListRejects_to_noSemanticCheckAt_powerBoundRawCode
      n hrejects code hsize hchecks

theorem finiteListRejects_to_noSemanticCheckAt_powerBoundRawCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (n : Nat)
    (hrejects :
      h.exactness_core.small_code_enumeration.rejectsAllAt h.checker n)
    (code : h.exactness_core.proof_code_semantics.Code)
    (hsize :
      h.exactness_core.proof_code_semantics.size code <
        (h.exactness_core.small_code_enumeration.finiteListAt n).bound)
    (hchecks :
      h.exactness_core.proof_code_semantics.checks code
        (h.exactness_core.scale_data.powerBoundRawCode n)) :
    False :=
  h.exactness_core.finiteListRejects_to_noSemanticCheckAt_powerBoundRawCode
    n hrejects code hsize hchecks

theorem acceptedDecodedCode_to_formulaCodeDerivable
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode h.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable h.semantics formulaCode :=
  h.exactness_core.acceptedDecodedCode_to_formulaCodeDerivable
    formulaCode code haccepted

theorem semanticCheck_to_acceptedProofCode
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (code : h.exactness_core.proof_code_semantics.Code)
    (formulaCode : _root_.FormulaCode)
    (hchecks :
      h.exactness_core.proof_code_semantics.checks code formulaCode) :
    PAHilbertAcceptedProofCodeForFormulaCode h.checker
      formulaCode
      (h.exactness_core.proof_code_semantics_bridge.toNatCode code) :=
  h.exactness_core.semanticCheck_to_acceptedProofCode
    code formulaCode hchecks

theorem semanticCheck_to_formulaCodeDerivable
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (code : h.exactness_core.proof_code_semantics.Code)
    (formulaCode : _root_.FormulaCode)
    (hchecks :
      h.exactness_core.proof_code_semantics.checks code formulaCode) :
    PAHilbertFormulaCodeDerivable h.semantics formulaCode :=
  h.exactness_core.semanticCheck_to_formulaCodeDerivable
    code formulaCode hchecks

theorem acceptedProofCode_iff_existsSemanticCheck
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (formulaCode : _root_.FormulaCode) (natCode : Nat) :
    PAHilbertAcceptedProofCodeForFormulaCode h.checker formulaCode natCode ↔
      ∃ code : h.exactness_core.proof_code_semantics.Code,
        h.exactness_core.proof_code_semantics_bridge.toNatCode code =
          natCode ∧
          h.exactness_core.proof_code_semantics.checks
            code formulaCode :=
  h.exactness_core.acceptedProofCode_iff_existsSemanticCheck
    formulaCode natCode

theorem recognizer_exactness_statements
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    (∀ formula : PAHilbertFormula,
      h.checker.recognizer.recognizesLogical formula = true ↔
        h.exactness_core.recognizerExactness.schemeSemantics.IsLogicalAxiom
          formula) ∧
      (∀ formula : PAHilbertFormula,
        h.checker.recognizer.recognizesEquality formula = true ↔
          h.exactness_core.recognizerExactness.schemeSemantics.IsEqualityAxiom
            formula) ∧
        (∀ formula : PAHilbertFormula,
          h.checker.recognizer.recognizesInduction formula = true ↔
            h.exactness_core.recognizerExactness.schemeSemantics.IsInductionSchema
              formula) ∧
          (∀ formula : PAHilbertFormula,
            h.checker.recognizer.recognizesPAArithmetic formula = true ↔
              h.exactness_core.recognizerExactness.schemeSemantics.IsPAArithmeticAxiom
                formula) := by
  exact
    ⟨h.exactness_core.recognizerExactness.logicalExact,
      h.exactness_core.recognizerExactness.equalityExact,
      h.exactness_core.recognizerExactness.inductionExact,
      h.exactness_core.recognizerExactness.paArithmeticExact⟩

theorem recognizesAny_exactness_statement
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    ∀ formula : PAHilbertFormula,
      h.checker.recognizer.recognizesAny formula = true ↔
        h.exactness_core.recognizerExactness.schemeSemantics.IsLogicalAxiom formula ∨
          h.exactness_core.recognizerExactness.schemeSemantics.IsEqualityAxiom formula ∨
            h.exactness_core.recognizerExactness.schemeSemantics.IsInductionSchema formula ∨
              h.exactness_core.recognizerExactness.schemeSemantics.IsPAArithmeticAxiom formula :=
  h.exactness_core.recognizesAny_iff_schemeDisjunction

theorem recognizer_soundness_statements
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    (∀ formula : PAHilbertFormula,
      h.checker.recognizer.recognizesLogical formula = true →
        h.semantics.Derivable formula) ∧
      (∀ formula : PAHilbertFormula,
        h.checker.recognizer.recognizesEquality formula = true →
          h.semantics.Derivable formula) ∧
        (∀ formula : PAHilbertFormula,
          h.checker.recognizer.recognizesInduction formula = true →
            h.semantics.Derivable formula) ∧
          (∀ formula : PAHilbertFormula,
            h.checker.recognizer.recognizesPAArithmetic formula = true →
              h.semantics.Derivable formula) ∧
            (∀ formula : PAHilbertFormula,
              h.checker.recognizer.recognizesAny formula = true →
                h.semantics.Derivable formula) :=
  h.exactness_core.recognizerSchemeSoundness_statements

theorem checker_interface_soundness_statements
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    (∀ proof : PAHilbertProofObject,
      ∀ formula : PAHilbertFormula,
        h.checker.accepts proof formula = true →
          h.semantics.Derivable formula) ∧
      (∀ trace : PAHilbertCheckedProofTrace,
        h.exactness_core.checkerInterface.traceChecker.checkTrace trace = true →
          h.semantics.Derivable trace.proof.conclusion) := by
  exact
    ⟨h.exactness_core.acceptedProofObject_to_derivable,
      h.exactness_core.checkedTrace_to_derivable⟩

theorem decoder_exactness_statements
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    (∀ proof : PAHilbertProofObject,
      h.checker.decoder.decode proof.code = some proof) ∧
      (∀ code : Nat,
        ∀ formula : PAHilbertFormula,
          h.checker.decoder.decode code = none →
            h.checker.rejectsCode code formula = true) ∧
        (∀ code : Nat,
          ∀ proof : PAHilbertProofObject,
            ∀ formula : PAHilbertFormula,
              h.checker.decoder.decode code = some proof →
                proof.conclusion = formula →
                  h.checker.rejectsCode code formula = true →
                    h.checker.accepts proof formula = false) :=
  ⟨h.exactness_core.decodeProofCode_complete,
    h.exactness_core.rejectsUndecodable,
    h.exactness_core.decodedRejects_to_notAccepted⟩

theorem trace_checker_exactness_statements
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    (∀ trace : PAHilbertCheckedProofTrace,
      h.exactness_core.checkerInterface.traceChecker.checkTrace trace = true →
        ∀ step : PAHilbertProofStep,
          step ∈ trace.decodedSteps →
            h.exactness_core.checkerInterface.traceChecker.checkStep trace step = true) ∧
      (∀ trace : PAHilbertCheckedProofTrace,
        ∀ step : PAHilbertProofStep,
          step ∈ trace.decodedSteps →
            h.exactness_core.checkerInterface.traceChecker.checkStep trace step = true →
              h.semantics.Derivable step.formula) ∧
        (∀ trace : PAHilbertCheckedProofTrace,
          h.exactness_core.checkerInterface.traceChecker.checkTrace trace = true →
            h.semantics.Derivable trace.proof.conclusion) :=
  ⟨h.exactness_core.checkedTrace_steps_checked,
    h.exactness_core.checkedStep_to_derivable,
    h.exactness_core.checkedTrace_to_derivable⟩

theorem allowedRuleApplication_to_derivable
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (rule : PAHilbertInferenceRule)
    (premises : List PAHilbertFormula)
    (conclusion : PAHilbertFormula)
    (hallowed : h.checker.ruleAllowed rule = true)
    (happlication :
      h.exactness_core.checkerInterface.inferenceRuleSemantics.RuleApplication
        rule premises conclusion)
    (hpremises :
      ∀ premise : PAHilbertFormula,
        premise ∈ premises → h.semantics.Derivable premise) :
    h.semantics.Derivable conclusion :=
  h.exactness_core.allowedRuleApplication_to_derivable
    rule premises conclusion hallowed happlication hpremises

theorem inference_rule_exactness_statements
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    (∀ rule : PAHilbertInferenceRule,
      h.checker.ruleAllowed rule = true →
        ∃ premises : List PAHilbertFormula,
          ∃ conclusion : PAHilbertFormula,
            h.exactness_core.checkerInterface.inferenceRuleSemantics.RuleApplication
              rule premises conclusion) ∧
      (∀ rule : PAHilbertInferenceRule,
        ∀ premises : List PAHilbertFormula,
          ∀ conclusion : PAHilbertFormula,
            h.exactness_core.checkerInterface.inferenceRuleSemantics.RuleApplication
              rule premises conclusion →
              h.checker.ruleAllowed rule = true) :=
  ⟨h.exactness_core.ruleAllowed_to_exists_ruleApplication,
    h.exactness_core.ruleApplication_to_ruleAllowed⟩

theorem finite_search_exclusion_statement
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    InternalPudlakTheorem5FiniteSearchExclusion
      h.exactness_core.scale_data
      h.exactness_core.proof_code_semantics
      h.toInternalPudlakTheorem5SmallCodeSearch :=
  h.exactness_core.toInternalPudlakTheorem5FiniteSearchExclusion

def computable_search_exclusion
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      h.exactness_core.scale_data
      h.exactness_core.proof_code_semantics
      h.toInternalPudlakTheorem5SmallCodeSearch :=
  h.exactness_core.toInternalPudlakTheorem5ComputableFiniteSearchExclusion

def computableSearchWitness
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) : Nat :=
  h.exactness_core.computableSearchWitness f hf N

def computableSearchCutoff
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) : Nat :=
  h.exactness_core.computableSearchCutoff f hf N

theorem computableSearchWitness_ge
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    N ≤ h.computableSearchWitness f hf N :=
  h.exactness_core.computableSearchWitness_ge f hf N

theorem computableSearchCutoff_gt
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    f (h.computableSearchWitness f hf N) <
      (h.computableSearchCutoff f hf N : Real) :=
  h.exactness_core.computableSearchCutoff_gt f hf N

theorem computableSearchRejects_candidates
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat)
    (c : h.exactness_core.proof_code_semantics.Code)
    (hc :
      c ∈
        h.toInternalPudlakTheorem5SmallCodeSearch.candidates
          (h.computableSearchWitness f hf N)
          (h.computableSearchCutoff f hf N)) :
    ¬ h.exactness_core.proof_code_semantics.checks c
      (h.exactness_core.scale_data.powerBoundRawCode
        (h.computableSearchWitness f hf N)) :=
  h.exactness_core.computableSearchRejects_candidates f hf N c hc

theorem computableSearchNoSmall_at_witness
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat)
    (c : h.exactness_core.proof_code_semantics.Code)
    (hchecks :
      h.exactness_core.proof_code_semantics.checks c
        (h.exactness_core.scale_data.powerBoundRawCode
          (h.computableSearchWitness f hf N))) :
    f (h.computableSearchWitness f hf N) <
      (h.exactness_core.proof_code_semantics.size c : Real) :=
  h.exactness_core.computableSearchNoSmall_at_witness
    f hf N c hchecks

theorem computableSearchMinProofCodeSize_gt
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    (h.exactness_core.proof_code_semantics.minProofCodeSize
      (h.exactness_core.scale_data.powerBoundRawCode
        (h.computableSearchWitness f hf N))
      ⟨h.computableSearchWitness f hf N, rfl⟩ : Real) >
      f (h.computableSearchWitness f hf N) :=
  h.exactness_core.computableSearchMinProofCodeSize_gt f hf N

def computedLowerSearchWitness
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      h.exactness_core.scale_data
      h.exactness_core.proof_code_semantics
      h.toInternalPudlakTheorem5SmallCodeSearch
      f hf N :=
  h.exactness_core.computedLowerSearchWitness f hf N

theorem computedLowerSearchWitness_nonempty
    (h : Month11Month12PAHilbertCheckerChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    Nonempty
      (InternalPudlakTheorem5ComputedLowerSearchWitness
        h.exactness_core.scale_data
        h.exactness_core.proof_code_semantics
        h.toInternalPudlakTheorem5SmallCodeSearch
        f hf N) :=
  ⟨h.computedLowerSearchWitness f hf N⟩

def toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  h.exactness_core.toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

theorem month11_month12_pa_hilbert_checker_closure
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    Nonempty PAHilbertCheckerExactnessCore.{q} ∧
      h.exactness_core.computable_finite_search_no_small_core.scale_data =
        h.exactness_core.scale_data ∧
        HEq
          h.exactness_core.computable_finite_search_no_small_core.proof_length_model.proof_code_semantics
          h.exactness_core.proof_code_semantics ∧
          HEq
            h.exactness_core.computable_finite_search_no_small_core.small_code_search
            h.toInternalPudlakTheorem5SmallCodeSearch ∧
            (∀ n : Nat,
              h.exactness_core.computable_finite_search_no_small_core.scale_data.powerBoundRawCode n =
                h.exactness_core.scale_data.powerBoundRawCode n) ∧
              (∀ n : Nat,
                (h.exactness_core.small_code_enumeration.formulaAt n).code =
                  h.exactness_core.scale_data.powerBoundRawCode n) ∧
                Nonempty
                  (InternalPudlakTheorem5SmallCodeSearch
                    h.exactness_core.scale_data
                    h.exactness_core.proof_code_semantics) ∧
                  InternalPudlakTheorem5FiniteSearchExclusion
                    h.exactness_core.scale_data
                    h.exactness_core.proof_code_semantics
                    h.toInternalPudlakTheorem5SmallCodeSearch ∧
                    Nonempty
                      (InternalPudlakTheorem5ComputableFiniteSearchExclusion
                        h.exactness_core.scale_data
                        h.exactness_core.proof_code_semantics
                        h.toInternalPudlakTheorem5SmallCodeSearch) ∧
                      (∀ f : Nat → Real,
                        ∀ hf : _root_.is_polynomial_bound f,
                          ∀ N : Nat, N ≤ h.computableSearchWitness f hf N) ∧
                        (∀ f : Nat → Real,
                          ∀ hf : _root_.is_polynomial_bound f,
                            ∀ N : Nat,
                              f (h.computableSearchWitness f hf N) <
                                (h.computableSearchCutoff f hf N : Real)) ∧
                          (∀ f : Nat → Real,
                            ∀ hf : _root_.is_polynomial_bound f,
                              ∀ N : Nat,
                                ∀ c : h.exactness_core.proof_code_semantics.Code,
                                  h.exactness_core.proof_code_semantics.checks c
                                    (h.exactness_core.scale_data.powerBoundRawCode
                                      (h.computableSearchWitness f hf N)) →
                                    f (h.computableSearchWitness f hf N) <
                                      (h.exactness_core.proof_code_semantics.size c : Real)) ∧
                            (∀ f : Nat → Real,
                              ∀ hf : _root_.is_polynomial_bound f,
                                ∀ N : Nat,
                                  (h.exactness_core.proof_code_semantics.minProofCodeSize
                                    (h.exactness_core.scale_data.powerBoundRawCode
                                      (h.computableSearchWitness f hf N))
                                    ⟨h.computableSearchWitness f hf N, rfl⟩ : Real) >
                                    f (h.computableSearchWitness f hf N)) ∧
                              (∀ f : Nat → Real,
                                ∀ hf : _root_.is_polynomial_bound f,
                                  ∀ N : Nat,
                                    Nonempty
                                      (InternalPudlakTheorem5ComputedLowerSearchWitness
                                        h.exactness_core.scale_data
                                        h.exactness_core.proof_code_semantics
                                        h.toInternalPudlakTheorem5SmallCodeSearch
                                        f hf N)) ∧
                                Nonempty
                                  InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  ⟨⟨h.exactness_core⟩,
    h.noSmallCore_scale_data_eq,
    h.noSmallCore_proof_code_semantics_heq,
    h.noSmallCore_small_code_search_heq,
    h.noSmallCore_powerBoundRawCode_eq,
    h.formulaAt_code_eq_powerBoundRawCode,
    h.exactness_core.small_code_search_nonempty,
    h.finite_search_exclusion_statement,
    ⟨h.computable_search_exclusion⟩,
    h.computableSearchWitness_ge,
    h.computableSearchCutoff_gt,
    h.computableSearchNoSmall_at_witness,
    h.computableSearchMinProofCodeSize_gt,
    h.computedLowerSearchWitness_nonempty,
    ⟨h.toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore⟩⟩

/-- Compact Lean-level inventory of the Month 11-12 implementation obligations
that remain behind the conditional checker surface. -/
structure ImplementationObligationSummary
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) : Prop where
  exactnessCore :
    Nonempty PAHilbertCheckerExactnessCore.{q}
  checkerInterface :
    Nonempty (PAHilbertCheckerInterface h.checker h.semantics)
  paperProofInterface :
    Nonempty
      (PAHilbertCheckerPaperProofInterface h.checker h.semantics)
  decoderExactness :
    Nonempty (PAHilbertCheckerDecoderExactness h.checker)
  recognizerExactness :
    Nonempty
      (PAHilbertAxiomRecognizerExactness
        h.checker.recognizer h.semantics)
  inferenceRuleExactness :
    Nonempty
      (PAHilbertInferenceRuleExactness h.checker h.semantics
        h.exactness_core.checkerInterface.inferenceRuleSemantics)
  traceCheckerExactness :
    Nonempty
      (PAHilbertTraceCheckerExactness h.checker h.semantics
        h.exactness_core.checkerInterface.traceChecker)
  traceStepSoundness :
    Nonempty
      (PAHilbertTraceStepSoundness h.checker h.semantics
        h.exactness_core.checkerInterface.inferenceRuleSemantics)
  proofCodeSemanticsBridge :
    Nonempty
      (PAHilbertProofCodeSemanticsBridge.{q}
        h.checker
        h.exactness_core.scale_data
        h.exactness_core.proof_code_semantics)
  smallCodeEnumeration :
    Nonempty
      (PAHilbertSmallCodeEnumeration.{q}
        h.exactness_core.scale_data
        h.exactness_core.proof_code_semantics)

theorem implementation_obligation_summary
    (h : Month11Month12PAHilbertCheckerChecklist.{q}) :
    ImplementationObligationSummary h where
  exactnessCore := ⟨h.exactness_core⟩
  checkerInterface := ⟨h.exactness_core.checkerInterface⟩
  paperProofInterface := h.paperProofInterface_nonempty
  decoderExactness :=
    ⟨h.exactness_core.checkerInterface.decoderExactness⟩
  recognizerExactness := ⟨h.exactness_core.recognizerExactness⟩
  inferenceRuleExactness :=
    ⟨h.exactness_core.checkerInterface.inferenceRuleExactness⟩
  traceCheckerExactness :=
    ⟨h.exactness_core.checkerInterface.traceCheckerExactness⟩
  traceStepSoundness :=
    ⟨h.exactness_core.checkerInterface.traceStepSoundness⟩
  proofCodeSemanticsBridge :=
    ⟨h.exactness_core.proof_code_semantics_bridge⟩
  smallCodeEnumeration :=
    ⟨h.exactness_core.small_code_enumeration⟩

def checklistOfExactnessCore
    (core : PAHilbertCheckerExactnessCore.{q}) :
    Month11Month12PAHilbertCheckerChecklist.{q} where
  exactness_core := core

theorem checklistOfExactnessCore_summary
    (core : PAHilbertCheckerExactnessCore.{q}) :
    ImplementationObligationSummary
      (checklistOfExactnessCore core) :=
  implementation_obligation_summary
    (checklistOfExactnessCore core)

def checklistOfExactnessCore_toNoSmallCore
    (core : PAHilbertCheckerExactnessCore.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  (checklistOfExactnessCore core)
    |>.toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

theorem checklistOfExactnessCore_noSmallCore_eq
    (core : PAHilbertCheckerExactnessCore.{q}) :
    checklistOfExactnessCore_toNoSmallCore core =
      core.toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore :=
  rfl

theorem checklistOfExactnessCore_computedLowerSearchWitness_nonempty
    (core : PAHilbertCheckerExactnessCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f)
    (N : Nat) :
    Nonempty
      (InternalPudlakTheorem5ComputedLowerSearchWitness
        core.scale_data
        core.proof_code_semantics
        core.toInternalPudlakTheorem5SmallCodeSearch
        f hf N) :=
  (checklistOfExactnessCore core)
    |>.computedLowerSearchWitness_nonempty f hf N

/-- Stable integration summary for downstream Month 9-10 closure files.  This
keeps the main handoff theorem compact while still exposing the core artifacts
needed by the computable finite-search route. -/
theorem stableIntegrationSurface
    (core : PAHilbertCheckerExactnessCore.{q}) :
    Nonempty Month11Month12PAHilbertCheckerChecklist.{q} ∧
      ImplementationObligationSummary (checklistOfExactnessCore core) ∧
        Nonempty
          (InternalPudlakTheorem5SmallCodeSearch
            core.scale_data core.proof_code_semantics) ∧
          Nonempty
            (InternalPudlakTheorem5ComputableFiniteSearchExclusion
              core.scale_data core.proof_code_semantics
              core.toInternalPudlakTheorem5SmallCodeSearch) ∧
            (∀ f : Nat → Real,
              ∀ hf : _root_.is_polynomial_bound f,
                ∀ N : Nat,
                  Nonempty
                    (InternalPudlakTheorem5ComputedLowerSearchWitness
                      core.scale_data
                      core.proof_code_semantics
                      core.toInternalPudlakTheorem5SmallCodeSearch
                      f hf N)) ∧
              Nonempty
                InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  ⟨⟨checklistOfExactnessCore core⟩,
    checklistOfExactnessCore_summary core,
    core.small_code_search_nonempty,
    ⟨core.toInternalPudlakTheorem5ComputableFiniteSearchExclusion⟩,
    checklistOfExactnessCore_computedLowerSearchWitness_nonempty core,
    ⟨core.toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore⟩⟩

end Month11Month12PAHilbertCheckerChecklist

/-- Top-level downstream-facing shape of the Month 11-12 checker handoff.
It records the conditional artifacts made available by a supplied
`PAHilbertCheckerExactnessCore` without claiming the checker exactness core is
constructed unconditionally. -/
abbrev Month11Month12StableIntegrationSurface
    (core : PAHilbertCheckerExactnessCore.{q}) : Prop :=
  Nonempty Month11Month12PAHilbertCheckerChecklist.{q} ∧
    Month11Month12PAHilbertCheckerChecklist.ImplementationObligationSummary
      (Month11Month12PAHilbertCheckerChecklist.checklistOfExactnessCore core) ∧
      Nonempty
        (InternalPudlakTheorem5SmallCodeSearch
          core.scale_data core.proof_code_semantics) ∧
        Nonempty
          (InternalPudlakTheorem5ComputableFiniteSearchExclusion
            core.scale_data core.proof_code_semantics
            core.toInternalPudlakTheorem5SmallCodeSearch) ∧
          (∀ f : Nat → Real,
            ∀ hf : _root_.is_polynomial_bound f,
              ∀ N : Nat,
                Nonempty
                  (InternalPudlakTheorem5ComputedLowerSearchWitness
                    core.scale_data
                    core.proof_code_semantics
                    core.toInternalPudlakTheorem5SmallCodeSearch
                    f hf N)) ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}

/-- Namespace-free stable integration theorem for downstream importers. -/
theorem month11_month12_stable_integration_surface
    (core : PAHilbertCheckerExactnessCore.{q}) :
    Month11Month12StableIntegrationSurface core :=
  Month11Month12PAHilbertCheckerChecklist.stableIntegrationSurface core

/-- Final Month 11-12 surface theorem: once the PA/Hilbert checker exactness
core is supplied, the Month 9-10 computable finite-search no-small-code core is
available.  This definition is deliberately conditional on the exactness core;
the theorem below records the corresponding inhabited proposition. -/
def PAHilbertCheckerExactnessCore_to_InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
    (core : PAHilbertCheckerExactnessCore.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  core.toInternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

theorem PAHilbertCheckerExactnessCore_to_InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore_nonempty
    (core : PAHilbertCheckerExactnessCore.{q}) :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  ⟨PAHilbertCheckerExactnessCore_to_InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
    core⟩

end SondowProjectMonth11PAHilbertCheckerSurface
end SondowMainCheckedCodeBridge

end
