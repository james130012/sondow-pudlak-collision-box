import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality

/-!
# Generated bounded formulas for literal natural-number lists

A fixed Lean list is compiled into one finite conjunction of fixed-width table
entries.  This lets later arithmetic graphs expose fixed PA-axiom sentences
without trusting an auxiliary table parameter.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectLiteralNatListFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality

def CompactFixedWidthLiteralEntries
    (tokenTable width tokenCount start : Nat) : List Nat → Prop
  | [] => True
  | value :: values =>
      CompactFixedWidthEntry tokenTable width start value ∧
        CompactFixedWidthLiteralEntries
          tokenTable width tokenCount (start + 1) values

def compactFixedWidthLiteralEntriesDef :
    List Nat → 𝚺₀.Semisentence 4
  | [] => .mkSigma “tokenTable width tokenCount start. ⊤”
  | value :: values =>
      let tailDef := compactFixedWidthLiteralEntriesDef values
      .mkSigma
        “tokenTable width tokenCount start.
          !(compactFixedWidthEntryDef)
            tokenTable width start ↑value ∧
          !(tailDef) tokenTable width tokenCount (start + 1)”

@[simp] theorem compactFixedWidthLiteralEntriesDef_spec
    (values : List Nat)
    (tokenTable width tokenCount start : Nat) :
    (compactFixedWidthLiteralEntriesDef values).val.Evalb
        ![tokenTable, width, tokenCount, start] ↔
      CompactFixedWidthLiteralEntries
        tokenTable width tokenCount start values := by
  induction values generalizing start with
  | nil =>
      simp [compactFixedWidthLiteralEntriesDef,
        CompactFixedWidthLiteralEntries]
  | cons value values ih =>
      let env : Fin 4 → Nat := ![tokenTable, width, tokenCount, start]
      have htailEnv :
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 4), #1, #2, ‘(#3 + 1)’]) =
            ![tokenTable, width, tokenCount, start + 1] := by
        funext coordinate
        fin_cases coordinate <;> rfl
      change (compactFixedWidthLiteralEntriesDef
        (value :: values)).val.Evalb env ↔ _
      simp [compactFixedWidthLiteralEntriesDef,
        CompactFixedWidthLiteralEntries, htailEnv, ih, env]

theorem compactFixedWidthLiteralEntriesDef_sigmaZero
    (values : List Nat) :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      (compactFixedWidthLiteralEntriesDef values).val := by
  induction values with
  | nil =>
      simp [compactFixedWidthLiteralEntriesDef]
  | cons value values ih =>
      simp [compactFixedWidthLiteralEntriesDef, ih]

theorem CompactFixedWidthLiteralEntries.getI
    {tokenTable width tokenCount start : Nat}
    {values : List Nat}
    (hentries : CompactFixedWidthLiteralEntries
      tokenTable width tokenCount start values)
    (index : Nat) (hindex : index < values.length) :
    CompactFixedWidthEntry tokenTable width (start + index)
      (values.getI index) := by
  induction values generalizing start index with
  | nil => simp at hindex
  | cons value values ih =>
      rcases hentries with ⟨hhead, htail⟩
      cases index with
      | zero => simpa using hhead
      | succ index =>
          have hindexTail : index < values.length := by simpa using hindex
          have hentry := ih htail index hindexTail
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hentry

theorem CompactFixedWidthLiteralEntries.of_getI
    {tokenTable width tokenCount start : Nat}
    {values : List Nat}
    (hentries : ∀ index, index < values.length →
      CompactFixedWidthEntry tokenTable width (start + index)
        (values.getI index)) :
    CompactFixedWidthLiteralEntries
      tokenTable width tokenCount start values := by
  induction values generalizing start with
  | nil => simp [CompactFixedWidthLiteralEntries]
  | cons value values ih =>
      constructor
      · simpa using hentries 0 (by simp)
      · apply ih
        intro index hindex
        have hentry := hentries (index + 1) (by simpa using hindex)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hentry

theorem CompactFixedWidthLiteralEntries.of_directLayout
    {tokenTable width tokenCount listStart listFinish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount listStart listFinish values) :
    CompactFixedWidthLiteralEntries
      tokenTable width tokenCount (listStart + 1) values := by
  apply CompactFixedWidthLiteralEntries.of_getI
  intro index hindex
  have hentry := CompactAdditiveNatListDirectLayout.valueEntry
    hlayout index hindex
  simpa [Nat.add_assoc] using hentry

theorem CompactFixedWidthLiteralEntries.eq_of_directLayout
    {tokenTable width tokenCount listStart listFinish : Nat}
    {actual expected : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount listStart listFinish actual)
    (hlength : actual.length = expected.length)
    (hentries : CompactFixedWidthLiteralEntries
      tokenTable width tokenCount (listStart + 1) expected) :
    actual = expected := by
  apply List.ext_getElem
  · exact hlength
  · intro index hactualIndex hexpectedIndex
    have hactualEntry := CompactAdditiveNatListDirectLayout.valueEntry
      hlayout index hactualIndex
    have hexpectedEntry := hentries.getI index hexpectedIndex
    have hvalue : actual.getI index = expected.getI index :=
      (CompactFixedWidthEntry.value_eq_tableValue hactualEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          (by simpa [Nat.add_assoc] using hexpectedEntry)).symm
    rw [List.getI_eq_getElem actual hactualIndex,
      List.getI_eq_getElem expected hexpectedIndex] at hvalue
    exact hvalue

def CompactAdditiveLiteralNatListRows
    (tokenTable width tokenCount listStart actualCount : Nat)
    (expected : List Nat) : Prop :=
  actualCount = expected.length ∧
    CompactFixedWidthLiteralEntries tokenTable width tokenCount
      (listStart + 1) expected

def compactAdditiveLiteralNatListRowsDef
    (expected : List Nat) : 𝚺₀.Semisentence 5 :=
  let entriesDef := compactFixedWidthLiteralEntriesDef expected
  .mkSigma
    “tokenTable width tokenCount listStart actualCount.
      actualCount = ↑(expected.length) ∧
      !(entriesDef) tokenTable width tokenCount (listStart + 1)”

@[simp] theorem compactAdditiveLiteralNatListRowsDef_spec
    (expected : List Nat)
    (tokenTable width tokenCount listStart actualCount : Nat) :
    (compactAdditiveLiteralNatListRowsDef expected).val.Evalb
        ![tokenTable, width, tokenCount, listStart, actualCount] ↔
      CompactAdditiveLiteralNatListRows
        tokenTable width tokenCount listStart actualCount expected := by
  let env : Fin 5 → Nat :=
    ![tokenTable, width, tokenCount, listStart, actualCount]
  change (compactAdditiveLiteralNatListRowsDef expected).val.Evalb env ↔ _
  have hentriesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 5), #1, #2, ‘(#3 + 1)’]) =
        ![tokenTable, width, tokenCount, listStart + 1] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcount : env 4 = actualCount := rfl
  simp [compactAdditiveLiteralNatListRowsDef,
    CompactAdditiveLiteralNatListRows, hentriesEnv, hcount]

theorem compactAdditiveLiteralNatListRowsDef_sigmaZero
    (expected : List Nat) :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      (compactAdditiveLiteralNatListRowsDef expected).val := by
  simp [compactAdditiveLiteralNatListRowsDef]

theorem compactAdditiveLiteralNatListRows_iff_eq
    {tokenTable width tokenCount listStart listFinish actualCount : Nat}
    {actual expected : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount listStart listFinish actual)
    (hactualCount : actualCount = actual.length) :
    CompactAdditiveLiteralNatListRows
        tokenTable width tokenCount listStart actualCount expected ↔
      actual = expected := by
  constructor
  · rintro ⟨hcount, hentries⟩
    exact hentries.eq_of_directLayout hlayout (by omega)
  · intro hvalue
    subst actual
    exact ⟨hactualCount,
      CompactFixedWidthLiteralEntries.of_directLayout hlayout⟩

#print axioms compactFixedWidthLiteralEntriesDef_spec
#print axioms compactFixedWidthLiteralEntriesDef_sigmaZero
#print axioms CompactFixedWidthLiteralEntries.getI
#print axioms CompactFixedWidthLiteralEntries.of_directLayout
#print axioms CompactFixedWidthLiteralEntries.eq_of_directLayout
#print axioms compactAdditiveLiteralNatListRowsDef_spec
#print axioms compactAdditiveLiteralNatListRowsDef_sigmaZero
#print axioms compactAdditiveLiteralNatListRows_iff_eq

end FoundationCompactNumericListedDirectLiteralNatListFormula
