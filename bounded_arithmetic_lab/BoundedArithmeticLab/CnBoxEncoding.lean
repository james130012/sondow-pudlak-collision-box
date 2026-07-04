/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import BoundedArithmeticLab.BoundedSyntax

/-!
# Finite-consistency Cn boxes with executable syntax coding

This module gives the bounded-arithmetic side a small, executable syntax-code
layer.  It is intentionally narrower than a full PA proof predicate: the goal is
to make the audit-facing finite-consistency target a concrete same-object box
with a checked encoder/decoder roundtrip and an explicit S21-to-PA proof-object
certificate.
-/

namespace BoundedArithmeticLab

namespace FormulaFamily

def encode : FormulaFamily → Nat
  | partialConsistency => 0
  | sondowCertificateValid => 1
  | sondowReflectionGraft => 2
  | externalPudlak => 3
  | sondowProduct => 4
  | sondowLogRelation => 5
  | sondowDecomposition => 6
  | sondowThreePow => 7
  | sondowPayload => 8
  | tailOneLe => 9
  | tailLcmDoubleLeNinePow => 10
  | tailGeometricTailLtOne => 11
  | tailAnalyticTailBound => 12

def decode : Nat → Option FormulaFamily
  | 0 => some partialConsistency
  | 1 => some sondowCertificateValid
  | 2 => some sondowReflectionGraft
  | 3 => some externalPudlak
  | 4 => some sondowProduct
  | 5 => some sondowLogRelation
  | 6 => some sondowDecomposition
  | 7 => some sondowThreePow
  | 8 => some sondowPayload
  | 9 => some tailOneLe
  | 10 => some tailLcmDoubleLeNinePow
  | 11 => some tailGeometricTailLtOne
  | 12 => some tailAnalyticTailBound
  | _ => none

theorem decode_encode (family : FormulaFamily) :
    decode (encode family) = some family := by
  cases family <;> rfl

end FormulaFamily

namespace BATerm

def syntaxDepth : BATerm → Nat
  | var _ => 1
  | zero => 1
  | one => 1
  | succ t => t.syntaxDepth + 1
  | add t u => max t.syntaxDepth u.syntaxDepth + 1
  | mul t u => max t.syntaxDepth u.syntaxDepth + 1
  | length t => t.syntaxDepth + 1
  | smash t u => max t.syntaxDepth u.syntaxDepth + 1

def syntaxSize : BATerm → Nat
  | var _ => 1
  | zero => 1
  | one => 1
  | succ t => t.syntaxSize + 1
  | add t u => t.syntaxSize + u.syntaxSize + 1
  | mul t u => t.syntaxSize + u.syntaxSize + 1
  | length t => t.syntaxSize + 1
  | smash t u => t.syntaxSize + u.syntaxSize + 1

def rawCode : BATerm → Nat
  | var n => Nat.pair 0 n
  | zero => Nat.pair 1 0
  | one => Nat.pair 2 0
  | succ t => Nat.pair 3 t.rawCode
  | add t u => Nat.pair 4 (Nat.pair t.rawCode u.rawCode)
  | mul t u => Nat.pair 5 (Nat.pair t.rawCode u.rawCode)
  | length t => Nat.pair 6 t.rawCode
  | smash t u => Nat.pair 7 (Nat.pair t.rawCode u.rawCode)

def decodeRawWithFuel : Nat → Nat → Option BATerm
  | 0, _ => none
  | fuel + 1, code =>
      let tagPayload := Nat.unpair code
      match tagPayload.1 with
      | 0 => some (var tagPayload.2)
      | 1 => some zero
      | 2 => some one
      | 3 =>
          match decodeRawWithFuel fuel tagPayload.2 with
          | some t => some (succ t)
          | none => none
      | 4 =>
          let args := Nat.unpair tagPayload.2
          match decodeRawWithFuel fuel args.1, decodeRawWithFuel fuel args.2 with
          | some t, some u => some (add t u)
          | _, _ => none
      | 5 =>
          let args := Nat.unpair tagPayload.2
          match decodeRawWithFuel fuel args.1, decodeRawWithFuel fuel args.2 with
          | some t, some u => some (mul t u)
          | _, _ => none
      | 6 =>
          match decodeRawWithFuel fuel tagPayload.2 with
          | some t => some (length t)
          | none => none
      | 7 =>
          let args := Nat.unpair tagPayload.2
          match decodeRawWithFuel fuel args.1, decodeRawWithFuel fuel args.2 with
          | some t, some u => some (smash t u)
          | _, _ => none
      | _ => none

theorem decodeRawWithFuel_rawCode_of_syntaxDepth_le
    (t : BATerm) :
    ∀ fuel, t.syntaxDepth ≤ fuel →
      decodeRawWithFuel fuel t.rawCode = some t := by
  induction t with
  | var n =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel => simp [decodeRawWithFuel, rawCode, Nat.unpair_pair]
  | zero =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel => simp [decodeRawWithFuel, rawCode, Nat.unpair_pair]
  | one =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel => simp [decodeRawWithFuel, rawCode, Nat.unpair_pair]
  | succ t ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have ht : t.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, ih fuel ht]
  | add t u iht ihu =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have ht : t.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hu : u.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, iht fuel ht,
            ihu fuel hu]
  | mul t u iht ihu =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have ht : t.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hu : u.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, iht fuel ht,
            ihu fuel hu]
  | length t ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have ht : t.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, ih fuel ht]
  | smash t u iht ihu =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have ht : t.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hu : u.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, iht fuel ht,
            ihu fuel hu]

def encode (t : BATerm) : Nat :=
  Nat.pair t.syntaxDepth t.rawCode

def decode (code : Nat) : Option BATerm :=
  let payload := Nat.unpair code
  decodeRawWithFuel payload.1 payload.2

theorem decode_encode (t : BATerm) :
    decode t.encode = some t := by
  simpa [decode, encode, Nat.unpair_pair] using
    decodeRawWithFuel_rawCode_of_syntaxDepth_le t t.syntaxDepth le_rfl

end BATerm

namespace BAFormula

def syntaxDepth : BAFormula → Nat
  | atom _ _ => 1
  | falsum => 1
  | equal t u => max t.syntaxDepth u.syntaxDepth + 1
  | le t u => max t.syntaxDepth u.syntaxDepth + 1
  | not A => A.syntaxDepth + 1
  | and A B => max A.syntaxDepth B.syntaxDepth + 1
  | or A B => max A.syntaxDepth B.syntaxDepth + 1
  | imp A B => max A.syntaxDepth B.syntaxDepth + 1
  | forallBounded _ bound body => max bound.syntaxDepth body.syntaxDepth + 1
  | existsBounded _ bound body => max bound.syntaxDepth body.syntaxDepth + 1

def syntaxSize : BAFormula → Nat
  | atom _ _ => 1
  | falsum => 1
  | equal t u => t.syntaxSize + u.syntaxSize + 1
  | le t u => t.syntaxSize + u.syntaxSize + 1
  | not A => A.syntaxSize + 1
  | and A B => A.syntaxSize + B.syntaxSize + 1
  | or A B => A.syntaxSize + B.syntaxSize + 1
  | imp A B => A.syntaxSize + B.syntaxSize + 1
  | forallBounded _ bound body => bound.syntaxSize + body.syntaxSize + 1
  | existsBounded _ bound body => bound.syntaxSize + body.syntaxSize + 1

def rawCode : BAFormula → Nat
  | atom family idx => Nat.pair 0 (Nat.pair family.encode idx)
  | falsum => Nat.pair 1 0
  | equal t u => Nat.pair 2 (Nat.pair t.rawCode u.rawCode)
  | le t u => Nat.pair 3 (Nat.pair t.rawCode u.rawCode)
  | not A => Nat.pair 4 A.rawCode
  | and A B => Nat.pair 5 (Nat.pair A.rawCode B.rawCode)
  | or A B => Nat.pair 6 (Nat.pair A.rawCode B.rawCode)
  | imp A B => Nat.pair 7 (Nat.pair A.rawCode B.rawCode)
  | forallBounded idx bound body =>
      Nat.pair 8 (Nat.pair idx (Nat.pair bound.rawCode body.rawCode))
  | existsBounded idx bound body =>
      Nat.pair 9 (Nat.pair idx (Nat.pair bound.rawCode body.rawCode))

def decodeRawWithFuel : Nat → Nat → Option BAFormula
  | 0, _ => none
  | fuel + 1, code =>
      let tagPayload := Nat.unpair code
      match tagPayload.1 with
      | 0 =>
          let args := Nat.unpair tagPayload.2
          match FormulaFamily.decode args.1 with
          | some family => some (atom family args.2)
          | none => none
      | 1 => some falsum
      | 2 =>
          let args := Nat.unpair tagPayload.2
          match BATerm.decodeRawWithFuel fuel args.1,
              BATerm.decodeRawWithFuel fuel args.2 with
          | some t, some u => some (equal t u)
          | _, _ => none
      | 3 =>
          let args := Nat.unpair tagPayload.2
          match BATerm.decodeRawWithFuel fuel args.1,
              BATerm.decodeRawWithFuel fuel args.2 with
          | some t, some u => some (le t u)
          | _, _ => none
      | 4 =>
          match decodeRawWithFuel fuel tagPayload.2 with
          | some A => some (not A)
          | none => none
      | 5 =>
          let args := Nat.unpair tagPayload.2
          match decodeRawWithFuel fuel args.1, decodeRawWithFuel fuel args.2 with
          | some A, some B => some (and A B)
          | _, _ => none
      | 6 =>
          let args := Nat.unpair tagPayload.2
          match decodeRawWithFuel fuel args.1, decodeRawWithFuel fuel args.2 with
          | some A, some B => some (or A B)
          | _, _ => none
      | 7 =>
          let args := Nat.unpair tagPayload.2
          match decodeRawWithFuel fuel args.1, decodeRawWithFuel fuel args.2 with
          | some A, some B => some (imp A B)
          | _, _ => none
      | 8 =>
          let args := Nat.unpair tagPayload.2
          let sub := Nat.unpair args.2
          match BATerm.decodeRawWithFuel fuel sub.1,
              decodeRawWithFuel fuel sub.2 with
          | some bound, some body => some (forallBounded args.1 bound body)
          | _, _ => none
      | 9 =>
          let args := Nat.unpair tagPayload.2
          let sub := Nat.unpair args.2
          match BATerm.decodeRawWithFuel fuel sub.1,
              decodeRawWithFuel fuel sub.2 with
          | some bound, some body => some (existsBounded args.1 bound body)
          | _, _ => none
      | _ => none

theorem decodeRawWithFuel_rawCode_of_syntaxDepth_le
    (A : BAFormula) :
    ∀ fuel, A.syntaxDepth ≤ fuel →
      decodeRawWithFuel fuel A.rawCode = some A := by
  induction A with
  | atom family idx =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair,
            FormulaFamily.decode_encode]
  | falsum =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel => simp [decodeRawWithFuel, rawCode, Nat.unpair_pair]
  | equal t u =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have ht : t.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hu : u.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair,
            BATerm.decodeRawWithFuel_rawCode_of_syntaxDepth_le t fuel ht,
            BATerm.decodeRawWithFuel_rawCode_of_syntaxDepth_le u fuel hu]
  | le t u =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have ht : t.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hu : u.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair,
            BATerm.decodeRawWithFuel_rawCode_of_syntaxDepth_le t fuel ht,
            BATerm.decodeRawWithFuel_rawCode_of_syntaxDepth_le u fuel hu]
  | not A ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have hA : A.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, ih fuel hA]
  | and A B ihA ihB =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have hA : A.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hB : B.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, ihA fuel hA,
            ihB fuel hB]
  | or A B ihA ihB =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have hA : A.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hB : B.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, ihA fuel hA,
            ihB fuel hB]
  | imp A B ihA ihB =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have hA : A.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hB : B.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair, ihA fuel hA,
            ihB fuel hB]
  | forallBounded idx bound body ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have hbound : bound.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hbody : body.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair,
            BATerm.decodeRawWithFuel_rawCode_of_syntaxDepth_le
              bound fuel hbound,
            ih fuel hbody]
  | existsBounded idx bound body ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp [syntaxDepth] at hfuel
      | succ fuel =>
          have hbound : bound.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          have hbody : body.syntaxDepth ≤ fuel := by
            simp [syntaxDepth] at hfuel
            omega
          simp [decodeRawWithFuel, rawCode, Nat.unpair_pair,
            BATerm.decodeRawWithFuel_rawCode_of_syntaxDepth_le
              bound fuel hbound,
            ih fuel hbody]

def encode (A : BAFormula) : Nat :=
  Nat.pair A.syntaxDepth A.rawCode

def decode (code : Nat) : Option BAFormula :=
  let payload := Nat.unpair code
  decodeRawWithFuel payload.1 payload.2

theorem decode_encode (A : BAFormula) :
    decode A.encode = some A := by
  simpa [decode, encode, Nat.unpair_pair] using
    decodeRawWithFuel_rawCode_of_syntaxDepth_le A A.syntaxDepth le_rfl

end BAFormula

def finiteConsistencyFormula (n : Nat) : BAFormula :=
  BAFormula.atom FormulaFamily.partialConsistency n

structure CnBox where
  n : Nat
  formula : BAFormula
  code : Nat
  length : Nat
  formulaCode : FormulaCode

namespace CnBox

def HasRoundTrip (box : CnBox) : Prop :=
  BAFormula.decode box.code = some box.formula

def HasFiniteConsistencyTarget (box : CnBox) : Prop :=
  box.formula = finiteConsistencyFormula box.n ∧
    box.formulaCode = partialConsistencyCode box.n

def HasLengthBridge (box : CnBox) : Prop :=
  box.length = box.formula.syntaxSize

def Certifies (box : CnBox) : Prop :=
  box.HasRoundTrip ∧ box.HasFiniteConsistencyTarget ∧ box.HasLengthBridge

theorem certifies_iff_components (box : CnBox) :
    box.Certifies ↔
      box.HasRoundTrip ∧ box.HasFiniteConsistencyTarget ∧
        box.HasLengthBridge :=
  Iff.rfl

theorem certifies_iff_expanded (box : CnBox) :
    box.Certifies ↔
      BAFormula.decode box.code = some box.formula ∧
        (box.formula = finiteConsistencyFormula box.n ∧
          box.formulaCode = partialConsistencyCode box.n) ∧
        box.length = box.formula.syntaxSize :=
  Iff.rfl

end CnBox

def mkFiniteConsistencyCnBox (n : Nat) : CnBox where
  n := n
  formula := finiteConsistencyFormula n
  code := (finiteConsistencyFormula n).encode
  length := (finiteConsistencyFormula n).syntaxSize
  formulaCode := partialConsistencyCode n

theorem finiteConsistencyFormula_decode_encode (n : Nat) :
    BAFormula.decode (finiteConsistencyFormula n).encode =
      some (finiteConsistencyFormula n) :=
  BAFormula.decode_encode (finiteConsistencyFormula n)

theorem mkFiniteConsistencyCnBox_certifies (n : Nat) :
    (mkFiniteConsistencyCnBox n).Certifies := by
  simp [mkFiniteConsistencyCnBox, CnBox.Certifies, CnBox.HasRoundTrip,
    CnBox.HasFiniteConsistencyTarget, CnBox.HasLengthBridge,
    BAFormula.decode_encode]

theorem mkFiniteConsistencyCnBox_certifies_iff_expanded (n : Nat) :
    (mkFiniteConsistencyCnBox n).Certifies ↔
      BAFormula.decode (mkFiniteConsistencyCnBox n).code =
          some (mkFiniteConsistencyCnBox n).formula ∧
        ((mkFiniteConsistencyCnBox n).formula = finiteConsistencyFormula n ∧
          (mkFiniteConsistencyCnBox n).formulaCode = partialConsistencyCode n) ∧
        (mkFiniteConsistencyCnBox n).length =
          (mkFiniteConsistencyCnBox n).formula.syntaxSize := by
  exact CnBox.certifies_iff_expanded (mkFiniteConsistencyCnBox n)

namespace BAProofObject

def mapS21ToPA (p : BAProofObject BussS21Axiom) : BAProofObject PAAxiom :=
  p.mapAxioms bussS21Axiom_subset_pa

theorem size_mapS21ToPA (p : BAProofObject BussS21Axiom) :
    p.mapS21ToPA.size = p.size :=
  BAProofObject.size_mapAxioms bussS21Axiom_subset_pa p

end BAProofObject

structure S21ToPAProofCertificate where
  s21Proof : BAProofObject BussS21Axiom
  paProof : BAProofObject PAAxiom
  sameConclusion : paProof.conclusion = s21Proof.conclusion
  sizePreserved : paProof.size = s21Proof.size

namespace S21ToPAProofCertificate

def Certifies (cert : S21ToPAProofCertificate) : Prop :=
  cert.paProof.conclusion = cert.s21Proof.conclusion ∧
    cert.paProof.size = cert.s21Proof.size

def ofS21Proof (p : BAProofObject BussS21Axiom) : S21ToPAProofCertificate where
  s21Proof := p
  paProof := p.mapS21ToPA
  sameConclusion := rfl
  sizePreserved := BAProofObject.size_mapS21ToPA p

theorem certifies_iff_components (cert : S21ToPAProofCertificate) :
    cert.Certifies ↔
      cert.paProof.conclusion = cert.s21Proof.conclusion ∧
        cert.paProof.size = cert.s21Proof.size :=
  Iff.rfl

theorem ofS21Proof_certifies (p : BAProofObject BussS21Axiom) :
    (ofS21Proof p).Certifies := by
  exact ⟨rfl, BAProofObject.size_mapS21ToPA p⟩

end S21ToPAProofCertificate

end BoundedArithmeticLab
