import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

/-!
# Generic size bounds for a checked syntax-task cons head

The three task fields are not restricted to parser-specific tags here.  Their
binary sizes are nevertheless bounded by the checked token-cell width.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadSizeBounds

open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

theorem compactSyntaxTaskDirectLayout_fieldSizes_le_width
    (tokenTable width tokenCount start finish
      headKind headBinderArity headRepeatCount : Nat)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (headKind, headBinderArity, headRepeatCount)) :
    Nat.size headKind <= width ∧
      Nat.size headBinderArity <= width ∧
      Nat.size headRepeatCount <= width := by
  rcases hlayout with
    ⟨binderStart, countStart, hkind, hbinder, hrepeat⟩
  exact ⟨hkind.2.2.1, hbinder.2.2.1, hrepeat.2.2.1⟩

theorem compactSyntaxTaskDirectLayout_internalCursors_le_tokenCount
    (tokenTable width tokenCount start finish
      headKind headBinderArity headRepeatCount : Nat)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (headKind, headBinderArity, headRepeatCount)) :
    let binderStart := Classical.choose hlayout
    let countStart := Classical.choose (Classical.choose_spec hlayout)
    binderStart <= tokenCount ∧ countStart <= tokenCount := by
  let binderStart := Classical.choose hlayout
  have hbinderSpec := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderSpec
  have hcells := Classical.choose_spec hbinderSpec
  have hbinderEq : binderStart = start + 1 := hcells.1.2.1
  have hcountEq : countStart = binderStart + 1 := hcells.2.1.2.1
  have hstartLt : start < tokenCount := hcells.1.1
  have hbinderLt : binderStart < tokenCount := hcells.2.1.1
  dsimp only [binderStart, countStart]
  exact ⟨by omega, by omega⟩

theorem taskConsHeadData_fieldSizes_le_numericBound
    (tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount numericBound : Nat)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount)
    (hwidth : width <= numericBound) :
    Nat.size headKind <= numericBound ∧
      Nat.size headBinderArity <= numericBound ∧
      Nat.size headRepeatCount <= numericBound := by
  have h :=
    compactSyntaxTaskDirectLayout_fieldSizes_le_width tokenTable width
      tokenCount data.targetLeft data.targetRight headKind headBinderArity
      headRepeatCount data.layout
  exact ⟨h.1.trans hwidth, h.2.1.trans hwidth,
    h.2.2.trans hwidth⟩

theorem taskConsHeadData_boundaryValues_size_le_numericBound
    (tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount numericBound : Nat)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount)
    (htokenCount : tokenCount <= numericBound) :
    Nat.size data.targetLeft <= numericBound ∧
      Nat.size data.targetRight <= numericBound := by
  exact ⟨data.targetLeft_entry.1.trans htokenCount,
    data.targetRight_entry.1.trans htokenCount⟩

#print axioms compactSyntaxTaskDirectLayout_fieldSizes_le_width
#print axioms compactSyntaxTaskDirectLayout_internalCursors_le_tokenCount
#print axioms taskConsHeadData_fieldSizes_le_numericBound
#print axioms taskConsHeadData_boundaryValues_size_le_numericBound

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadSizeBounds
