import integration.FoundationCompactCertificateCanonicalDecodeLength

/-!
# Costed bit-string primitives for the compact verifier

These functions expose both the Boolean result and the number of charged
bit/list steps.  They are the comparison layer for a later verifier that
retains the decoded sequent lists instead of invoking opaque `Finset`
decision procedures.
-/

namespace FoundationCompactVerifierBitCostPrimitives

/-- Bitwise equality with one charged step per inspected pair or endpoint. -/
def bitStringEqTrace : List Bool -> List Bool -> Bool × Nat
  | [], [] => (true, 1)
  | [], _ :: _ => (false, 1)
  | _ :: _, [] => (false, 1)
  | left :: leftTail, right :: rightTail =>
      if left = right then
        let result := bitStringEqTrace leftTail rightTail
        (result.1, result.2 + 1)
      else
        (false, 1)

theorem bitStringEqTrace_result_eq_true_iff
    (left right : List Bool) :
    (bitStringEqTrace left right).1 = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [bitStringEqTrace]
  | cons left leftTail ih =>
      cases right with
      | nil => simp [bitStringEqTrace]
      | cons right rightTail =>
          simp only [bitStringEqTrace]
          split
          · subst right
            simp [ih]
          · simp_all

theorem bitStringEqTrace_cost_pos
    (left right : List Bool) :
    1 <= (bitStringEqTrace left right).2 := by
  induction left generalizing right with
  | nil => cases right <;> simp [bitStringEqTrace]
  | cons left leftTail ih =>
      cases right with
      | nil => simp [bitStringEqTrace]
      | cons right rightTail =>
          simp only [bitStringEqTrace]
          split
          · have htail := ih rightTail
            omega
          · simp

theorem bitStringEqTrace_cost_le
    (left right : List Bool) :
    (bitStringEqTrace left right).2 <= left.length + 1 := by
  induction left generalizing right with
  | nil => cases right <;> simp [bitStringEqTrace]
  | cons left leftTail ih =>
      cases right with
      | nil => simp [bitStringEqTrace]
      | cons right rightTail =>
          simp only [bitStringEqTrace]
          split
          · have htail := ih rightTail
            simp only [List.length_cons]
            omega
          · simp

def natOfBitsList : List Bool -> Nat
  | [] => 0
  | bit :: bits => Nat.bit bit (natOfBitsList bits)

@[simp] theorem natOfBitsList_bits (n : Nat) :
    natOfBitsList n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [natOfBitsList]
  | bit bit n hn ih =>
      simp [Nat.bits_append_bit n bit hn, natOfBitsList, ih]

theorem natBits_injective : Function.Injective Nat.bits := by
  intro left right hbits
  have := congrArg natOfBitsList hbits
  simpa using this

/-- Natural-number equality by canonical binary digits, charging both digit
traversals as well as the bitwise comparison. -/
def natEqTrace (left right : Nat) : Bool × Nat :=
  let comparison := bitStringEqTrace left.bits right.bits
  (comparison.1,
    comparison.2 + left.bits.length + right.bits.length + 1)

theorem natEqTrace_result_eq_true_iff (left right : Nat) :
    (natEqTrace left right).1 = true ↔ left = right := by
  rw [natEqTrace, bitStringEqTrace_result_eq_true_iff]
  exact natBits_injective.eq_iff

theorem natEqTrace_cost_le (left right : Nat) :
    (natEqTrace left right).2 <=
      2 * left.bits.length + right.bits.length + 2 := by
  have hcomparison := bitStringEqTrace_cost_le left.bits right.bits
  simp only [natEqTrace]
  omega

/-- Membership in a list of bit strings.  Failed comparisons continue to the
tail; successful comparisons stop immediately. -/
def bitStringMemTrace : List Bool -> List (List Bool) -> Bool × Nat
  | _, [] => (false, 1)
  | needle, head :: tail =>
      let comparison := bitStringEqTrace needle head
      if comparison.1 then
        (true, comparison.2 + 1)
      else
        let rest := bitStringMemTrace needle tail
        (rest.1, comparison.2 + rest.2 + 1)

theorem bitStringMemTrace_result_eq_true_iff
    (needle : List Bool) (items : List (List Bool)) :
    (bitStringMemTrace needle items).1 = true ↔ needle ∈ items := by
  induction items with
  | nil => simp [bitStringMemTrace]
  | cons head tail ih =>
      simp only [bitStringMemTrace]
      split <;> rename_i hcomparison
      · have heq : needle = head :=
          (bitStringEqTrace_result_eq_true_iff needle head).mp
            (by simpa using hcomparison)
        simp [heq]
      · have hne : needle ≠ head := by
          intro heq
          subst head
          simp [bitStringEqTrace_result_eq_true_iff] at hcomparison
        simp [hne, ih]

theorem bitStringMemTrace_cost_pos
    (needle : List Bool) (items : List (List Bool)) :
    1 <= (bitStringMemTrace needle items).2 := by
  induction items with
  | nil => simp [bitStringMemTrace]
  | cons head tail ih =>
      simp only [bitStringMemTrace]
      split
      · have hcomparison := bitStringEqTrace_cost_pos needle head
        omega
      · have hcomparison := bitStringEqTrace_cost_pos needle head
        omega

theorem bitStringMemTrace_cost_le
    (needle : List Bool) (items : List (List Bool)) :
    (bitStringMemTrace needle items).2 <=
      (needle.length + 2) * (items.length + 1) := by
  induction items with
  | nil => simp [bitStringMemTrace]
  | cons head tail ih =>
      have hcomparison := bitStringEqTrace_cost_le needle head
      simp only [bitStringMemTrace]
      split
      · simp only [List.length_cons]
        rw [Nat.mul_succ]
        omega
      · simp only [List.length_cons]
        rw [Nat.mul_succ]
        omega

/-- Input weight used by the list-set comparison bounds.  The three units per
entry pay for list traversal, endpoint tests, and comparison dispatch. -/
def bitStringFamilyWeight (items : List (List Bool)) : Nat :=
  (items.map fun item => item.length + 3).sum

@[simp] theorem bitStringFamilyWeight_nil :
    bitStringFamilyWeight [] = 0 := rfl

@[simp] theorem bitStringFamilyWeight_cons
    (head : List Bool) (tail : List (List Bool)) :
    bitStringFamilyWeight (head :: tail) =
      head.length + 3 + bitStringFamilyWeight tail := by
  simp [bitStringFamilyWeight]

theorem length_le_bitStringFamilyWeight
    (items : List (List Bool)) :
    items.length <= bitStringFamilyWeight items := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, bitStringFamilyWeight_cons]
      omega

/-- Extensional list inclusion, treating the lists as finite sets. -/
def bitStringSubsetTrace :
    List (List Bool) -> List (List Bool) -> Bool × Nat
  | [], _ => (true, 1)
  | head :: tail, right =>
      let membership := bitStringMemTrace head right
      if membership.1 then
        let rest := bitStringSubsetTrace tail right
        (rest.1, membership.2 + rest.2 + 1)
      else
        (false, membership.2 + 1)

theorem bitStringSubsetTrace_result_eq_true_iff
    (left right : List (List Bool)) :
    (bitStringSubsetTrace left right).1 = true ↔
      forall item, item ∈ left -> item ∈ right := by
  induction left with
  | nil => simp [bitStringSubsetTrace]
  | cons head tail ih =>
      simp only [bitStringSubsetTrace]
      split <;> rename_i hmembership
      · have hhead : head ∈ right :=
          (bitStringMemTrace_result_eq_true_iff head right).mp
            (by simpa using hmembership)
        simp [hhead, ih]
      · have hhead : head ∉ right := by
          intro hmem
          have : (bitStringMemTrace head right).1 = true :=
            (bitStringMemTrace_result_eq_true_iff head right).2 hmem
          simp [this] at hmembership
        simp [hhead]

theorem bitStringSubsetTrace_cost_pos
    (left right : List (List Bool)) :
    1 <= (bitStringSubsetTrace left right).2 := by
  induction left with
  | nil => simp [bitStringSubsetTrace]
  | cons head tail ih =>
      have hmembership := bitStringMemTrace_cost_pos head right
      simp only [bitStringSubsetTrace]
      split <;> omega

theorem bitStringSubsetTrace_cost_le
    (left right : List (List Bool)) :
    (bitStringSubsetTrace left right).2 <=
      1 + (right.length + 1) * bitStringFamilyWeight left := by
  induction left with
  | nil => simp [bitStringSubsetTrace]
  | cons head tail ih =>
      have hmembership := bitStringMemTrace_cost_le head right
      simp only [bitStringSubsetTrace]
      split
      · rw [bitStringFamilyWeight_cons]
        rw [Nat.mul_comm (head.length + 2) (right.length + 1)] at hmembership
        simp only [Nat.mul_add, Nat.mul_succ] at hmembership ⊢
        omega
      · rw [bitStringFamilyWeight_cons]
        rw [Nat.mul_comm (head.length + 2) (right.length + 1)] at hmembership
        simp only [Nat.mul_add, Nat.mul_succ] at hmembership ⊢
        omega

/-- Extensional equality of two lists regarded as finite sets. -/
def bitStringSetEqTrace
    (left right : List (List Bool)) : Bool × Nat :=
  let forward := bitStringSubsetTrace left right
  if forward.1 then
    let backward := bitStringSubsetTrace right left
    (backward.1, forward.2 + backward.2 + 1)
  else
    (false, forward.2 + 1)

theorem bitStringSetEqTrace_result_eq_true_iff
    (left right : List (List Bool)) :
    (bitStringSetEqTrace left right).1 = true ↔
      left.toFinset = right.toFinset := by
  simp only [bitStringSetEqTrace]
  split <;> rename_i hforward
  · have hforward' :=
      (bitStringSubsetTrace_result_eq_true_iff left right).mp
        (by simpa using hforward)
    rw [Finset.ext_iff]
    simp only [List.mem_toFinset]
    constructor
    · intro hbackward item
      constructor
      · exact hforward' item
      · exact (bitStringSubsetTrace_result_eq_true_iff right left).mp
          hbackward item
    · intro heq
      apply (bitStringSubsetTrace_result_eq_true_iff right left).2
      intro item hitem
      exact (heq item).mpr hitem
  · simp only [Bool.false_eq_true, false_iff]
    intro heq
    apply hforward
    apply (bitStringSubsetTrace_result_eq_true_iff left right).2
    intro item hitem
    have : item ∈ left.toFinset := by simpa
    rw [heq] at this
    simpa using this

theorem bitStringSetEqTrace_cost_pos
    (left right : List (List Bool)) :
    1 <= (bitStringSetEqTrace left right).2 := by
  have hforward := bitStringSubsetTrace_cost_pos left right
  simp only [bitStringSetEqTrace]
  split
  · have hbackward := bitStringSubsetTrace_cost_pos right left
    omega
  · omega

theorem bitStringSetEqTrace_cost_le
    (left right : List (List Bool)) :
    (bitStringSetEqTrace left right).2 <=
      3 + (right.length + 1) * bitStringFamilyWeight left +
        (left.length + 1) * bitStringFamilyWeight right := by
  have hforward := bitStringSubsetTrace_cost_le left right
  have hbackward := bitStringSubsetTrace_cost_le right left
  simp only [bitStringSetEqTrace]
  split <;> omega

#print axioms bitStringEqTrace_result_eq_true_iff
#print axioms natEqTrace_result_eq_true_iff
#print axioms bitStringMemTrace_cost_le
#print axioms bitStringSubsetTrace_result_eq_true_iff
#print axioms bitStringSetEqTrace_cost_le

end FoundationCompactVerifierBitCostPrimitives
