import integration.FoundationCompactNumericFixedPAAxiomSentence
import integration.FoundationCompactNumericListedDirectLiteralNatListFormula

/-!
# Direct bounded relation for fixed PA-axiom candidates

The twenty parameter-free PA-axiom tags and the six ordered-ring
function/relation instances are compiled into one finite Delta-zero
disjunction.  Each branch contains the literal canonical sentence tokens;
no generated sentence or sentence-equality proposition is an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFixedPAAxiomCandidate

open FoundationCompactSyntaxTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectLiteralNatListFormula

structure CompactFixedPAAxiomCaseSpec where
  tag : Nat
  usesParameters : Bool
  arity : Nat
  symbolCode : Nat
  expected : List Nat

def CompactFixedPAAxiomCaseRows
    (tokenTable width tokenCount candidateStart candidateCount
      paTag arity symbolCode : Nat)
    (spec : CompactFixedPAAxiomCaseSpec) : Prop :=
  if spec.usesParameters then
    paTag = spec.tag ∧ arity = spec.arity ∧
      symbolCode = spec.symbolCode ∧
      CompactAdditiveLiteralNatListRows
        tokenTable width tokenCount candidateStart candidateCount
          spec.expected
  else
    paTag = spec.tag ∧
      CompactAdditiveLiteralNatListRows
        tokenTable width tokenCount candidateStart candidateCount
          spec.expected

def CompactFixedPAAxiomCasesRows
    (tokenTable width tokenCount candidateStart candidateCount
      paTag arity symbolCode : Nat) :
    List CompactFixedPAAxiomCaseSpec → Prop
  | [] => False
  | spec :: specs =>
      CompactFixedPAAxiomCaseRows
          tokenTable width tokenCount candidateStart candidateCount
            paTag arity symbolCode spec ∨
        CompactFixedPAAxiomCasesRows
          tokenTable width tokenCount candidateStart candidateCount
            paTag arity symbolCode specs

def compactFixedPAAxiomCasesRowsDef :
    List CompactFixedPAAxiomCaseSpec → 𝚺₀.Semisentence 8
  | [] =>
      .mkSigma
        “tokenTable width tokenCount candidateStart candidateCount
            paTag arity symbolCode. ⊥”
  | spec :: specs =>
      let expectedDef :=
        compactAdditiveLiteralNatListRowsDef spec.expected
      let tailDef := compactFixedPAAxiomCasesRowsDef specs
      if spec.usesParameters then
        .mkSigma
          “tokenTable width tokenCount candidateStart candidateCount
              paTag arity symbolCode.
            (paTag = ↑spec.tag ∧ arity = ↑spec.arity ∧
              symbolCode = ↑spec.symbolCode ∧
              !(expectedDef)
                tokenTable width tokenCount candidateStart candidateCount) ∨
            !(tailDef)
              tokenTable width tokenCount candidateStart candidateCount
                paTag arity symbolCode”
      else
        .mkSigma
          “tokenTable width tokenCount candidateStart candidateCount
              paTag arity symbolCode.
            (paTag = ↑spec.tag ∧
              !(expectedDef)
                tokenTable width tokenCount candidateStart candidateCount) ∨
            !(tailDef)
              tokenTable width tokenCount candidateStart candidateCount
                paTag arity symbolCode”

@[simp] theorem compactFixedPAAxiomCasesRowsDef_spec
    (specs : List CompactFixedPAAxiomCaseSpec)
    (tokenTable width tokenCount candidateStart candidateCount
      paTag arity symbolCode : Nat) :
    (compactFixedPAAxiomCasesRowsDef specs).val.Evalb
        ![tokenTable, width, tokenCount, candidateStart, candidateCount,
          paTag, arity, symbolCode] ↔
      CompactFixedPAAxiomCasesRows
        tokenTable width tokenCount candidateStart candidateCount
          paTag arity symbolCode specs := by
  induction specs with
  | nil =>
      simp [compactFixedPAAxiomCasesRowsDef,
        CompactFixedPAAxiomCasesRows]
  | cons spec specs ih =>
      let env : Fin 8 → Nat :=
        ![tokenTable, width, tokenCount, candidateStart, candidateCount,
          paTag, arity, symbolCode]
      have hexpectedEnv :
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 8), #1, #2, #3, #4]) =
            ![tokenTable, width, tokenCount,
              candidateStart, candidateCount] := by
        funext coordinate
        fin_cases coordinate <;> rfl
      have htailEnv :
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 8), #1, #2, #3,
              #4, #5, #6, #7]) = env := by
        funext coordinate
        fin_cases coordinate <;> rfl
      change (compactFixedPAAxiomCasesRowsDef
        (spec :: specs)).val.Evalb env ↔ _
      cases hparameters : spec.usesParameters <;>
        simp [compactFixedPAAxiomCasesRowsDef,
          CompactFixedPAAxiomCasesRows, CompactFixedPAAxiomCaseRows,
          hparameters, hexpectedEnv, htailEnv, ih, env]

theorem compactFixedPAAxiomCasesRowsDef_sigmaZero
    (specs : List CompactFixedPAAxiomCaseSpec) :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      (compactFixedPAAxiomCasesRowsDef specs).val := by
  induction specs with
  | nil => simp [compactFixedPAAxiomCasesRowsDef]
  | cons spec specs ih =>
      cases hparameters : spec.usesParameters <;>
        simp [compactFixedPAAxiomCasesRowsDef, hparameters]

def compactFixedPAAxiomCaseSpecs : List CompactFixedPAAxiomCaseSpec :=
  [ ⟨0, false, 0, 0,
      compactSentenceTokens (LO.FirstOrder.Theory.Eq.refl ℒₒᵣ)⟩,
    ⟨1, false, 0, 0,
      compactSentenceTokens (LO.FirstOrder.Theory.Eq.symm ℒₒᵣ)⟩,
    ⟨2, false, 0, 0,
      compactSentenceTokens (LO.FirstOrder.Theory.Eq.trans ℒₒᵣ)⟩,
    ⟨3, true, 0, 0,
      compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.zero)⟩,
    ⟨3, true, 0, 1,
      compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.one)⟩,
    ⟨3, true, 2, 0,
      compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.add)⟩,
    ⟨3, true, 2, 1,
      compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.mul)⟩,
    ⟨4, true, 2, 0,
      compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.eq)⟩,
    ⟨4, true, 2, 1,
      compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.lt)⟩,
    ⟨5, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.addZero⟩,
    ⟨6, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.addAssoc⟩,
    ⟨7, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.addComm⟩,
    ⟨8, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.addEqOfLt⟩,
    ⟨9, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.zeroLe⟩,
    ⟨10, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.zeroLtOne⟩,
    ⟨11, false, 0, 0,
      compactSentenceTokens PeanoMinus.Axiom.oneLeOfZeroLt⟩,
    ⟨12, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.addLtAdd⟩,
    ⟨13, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.mulZero⟩,
    ⟨14, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.mulOne⟩,
    ⟨15, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.mulAssoc⟩,
    ⟨16, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.mulComm⟩,
    ⟨17, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.mulLtMul⟩,
    ⟨18, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.distr⟩,
    ⟨19, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.ltIrrefl⟩,
    ⟨20, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.ltTrans⟩,
    ⟨21, false, 0, 0, compactSentenceTokens PeanoMinus.Axiom.ltTri⟩ ]

def CompactFixedPAAxiomCandidateRows
    (tokenTable width tokenCount candidateStart candidateCount
      paTag arity symbolCode : Nat) : Prop :=
  CompactFixedPAAxiomCasesRows
    tokenTable width tokenCount candidateStart candidateCount
      paTag arity symbolCode compactFixedPAAxiomCaseSpecs

def compactFixedPAAxiomCandidateRowsDef : 𝚺₀.Semisentence 8 :=
  compactFixedPAAxiomCasesRowsDef compactFixedPAAxiomCaseSpecs

@[simp] theorem compactFixedPAAxiomCandidateRowsDef_spec
    (tokenTable width tokenCount candidateStart candidateCount
      paTag arity symbolCode : Nat) :
    compactFixedPAAxiomCandidateRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, candidateStart, candidateCount,
          paTag, arity, symbolCode] ↔
      CompactFixedPAAxiomCandidateRows
        tokenTable width tokenCount candidateStart candidateCount
          paTag arity symbolCode := by
  exact compactFixedPAAxiomCasesRowsDef_spec
    compactFixedPAAxiomCaseSpecs tokenTable width tokenCount
      candidateStart candidateCount paTag arity symbolCode

theorem compactFixedPAAxiomCandidateRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFixedPAAxiomCandidateRowsDef.val := by
  exact compactFixedPAAxiomCasesRowsDef_sigmaZero
    compactFixedPAAxiomCaseSpecs

theorem CompactFixedPAAxiomCaseRows.iff_candidate_eq
    {tokenTable width tokenCount candidateStart candidateFinish
      candidateCount paTag arity symbolCode : Nat}
    {candidate : List Nat}
    (spec : CompactFixedPAAxiomCaseSpec)
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateStart candidateFinish candidate)
    (hcount : candidateCount = candidate.length) :
    CompactFixedPAAxiomCaseRows
        tokenTable width tokenCount candidateStart candidateCount
          paTag arity symbolCode spec ↔
      if spec.usesParameters then
        paTag = spec.tag ∧ arity = spec.arity ∧
          symbolCode = spec.symbolCode ∧ candidate = spec.expected
      else
        paTag = spec.tag ∧ candidate = spec.expected := by
  cases hparameters : spec.usesParameters <;>
    simp [CompactFixedPAAxiomCaseRows, hparameters,
      compactAdditiveLiteralNatListRows_iff_eq hlayout hcount]

theorem compactFixedPAAxiomCandidateRows_canonical_iff
    {tokenTable width tokenCount candidateStart candidateFinish
      candidateCount : Nat}
    {candidate : List Nat}
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate)
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateStart candidateFinish candidate)
    (hcount : candidateCount = candidate.length) :
    CompactFixedPAAxiomCandidateRows
        tokenTable width tokenCount candidateStart candidateCount
          (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate)) ↔
      candidate = compactSentenceTokens certificate.sentence := by
  cases certificate with
  | eqFuncExt functionSymbol =>
      cases functionSymbol <;>
        simp [CompactFixedPAAxiomCandidateRows,
          compactFixedPAAxiomCaseSpecs, CompactFixedPAAxiomCasesRows,
          CompactFixedPAAxiomCaseRows,
          compactPAAxiomCertificateTokens, compactTokenAt,
          PAAxiomCertificate.sentence,
          compactAdditiveLiteralNatListRows_iff_eq hlayout hcount] <;>
        intro _ <;> rfl
  | eqRelExt relationSymbol =>
      cases relationSymbol <;>
        simp [CompactFixedPAAxiomCandidateRows,
          compactFixedPAAxiomCaseSpecs, CompactFixedPAAxiomCasesRows,
          CompactFixedPAAxiomCaseRows,
          compactPAAxiomCertificateTokens, compactTokenAt,
          PAAxiomCertificate.sentence,
          compactAdditiveLiteralNatListRows_iff_eq hlayout hcount] <;>
        intro _ <;> rfl
  | induction body =>
      simp [FixedPAAxiomCertificate] at hfixed
  | eqRefl | eqSymm | eqTrans | addZero | addAssoc | addComm |
      addEqOfLt | zeroLe | zeroLtOne | oneLeOfZeroLt | addLtAdd |
      mulZero | mulOne | mulAssoc | mulComm | mulLtMul | distr |
      ltIrrefl | ltTrans | ltTri =>
      simp [CompactFixedPAAxiomCandidateRows,
        compactFixedPAAxiomCaseSpecs, CompactFixedPAAxiomCasesRows,
        CompactFixedPAAxiomCaseRows,
        compactPAAxiomCertificateTokens, compactTokenAt,
        PAAxiomCertificate.sentence,
        compactAdditiveLiteralNatListRows_iff_eq hlayout hcount]

#print axioms compactFixedPAAxiomCasesRowsDef_spec
#print axioms compactFixedPAAxiomCasesRowsDef_sigmaZero
#print axioms compactFixedPAAxiomCandidateRowsDef_spec
#print axioms compactFixedPAAxiomCandidateRowsDef_sigmaZero
#print axioms CompactFixedPAAxiomCaseRows.iff_candidate_eq
#print axioms compactFixedPAAxiomCandidateRows_canonical_iff

end FoundationCompactNumericListedDirectFixedPAAxiomCandidate
