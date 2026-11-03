import Blotto.BinaryOrderedThreeFactoryWork

/-! Three-variable ordering caches its comparison and restores the original
coordinate order. Canonical original fields determine all heights and the
ordered descriptor's primitive price; coordinate copying is a separate cost. -/

namespace Blotto.BinaryUnorderedThreeFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryFactoryHeight
open BinaryOrderedThreeFactoryWork

theorem ordered_height (input : BinaryThreeInputCompiler.Input) (s : ℕ) (h : InputHeight input s) :
    InputHeight (BinaryThreeSpecCompiler.ordered input) s := by
  unfold BinaryThreeSpecCompiler.ordered
  split
  · exact h
  · exact ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩

theorem swap_height (table : BinaryStoredOverlapEnvironment.Segment 3 9) (s : ℕ) (h : SegmentHeight table s) :
    SegmentHeight (BinaryThreeSpecCompiler.swap table) s := by
  refine ⟨h.1,?_⟩
  intro slot j
  simp only [BinaryThreeSpecCompiler.swap,FixedArrayTable.read_ofFn]
  fin_cases j <;> exact h.2 _ _

def descriptorWithWork (input : BinaryThreeInputCompiler.Input) : BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  let order := BinaryRationalArithmetic.lessEqual input.a input.d
  let child := if order then input else ⟨input.B,input.d,input.a,input.c,input.p⟩
  let table := BinaryOrderedThreeFactoryWork.descriptorWithWork child
  (if order then table.1 else BinaryThreeSpecCompiler.swap table.1,
    BinaryRationalArithmetic.lessEqualWork input.a input.d + table.2)

theorem descriptorWithWork_state (input : BinaryThreeInputCompiler.Input) :
    (descriptorWithWork input).1 = BinaryThreeSpecCompiler.descriptor input := by
  unfold descriptorWithWork BinaryThreeSpecCompiler.descriptor BinaryThreeSpecCompiler.ordered
  simp only [BinaryOrderedThreeFactoryWork.descriptorWithWork_state]

theorem descriptor_height (input : BinaryThreeInputCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    SegmentHeight (BinaryThreeSpecCompiler.descriptor input) (expressionHeightBudget s 18) := by
  have ht := BinaryOrderedThreeFactoryWork.descriptor_height _ (BinaryThreeSpecCompiler.ordered_canonical input hC)
    s hs (ordered_height input s h)
  unfold BinaryThreeSpecCompiler.descriptor
  split
  · exact ht
  · exact swap_height _ _ ht

def bound (s : ℕ) : ℕ := compareBound s + BinaryOrderedThreeFactoryWork.bound s

theorem descriptorWithWork_bound (input : BinaryThreeInputCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) : (descriptorWithWork input).2 ≤ bound s := by
  have hg := comparator_bound input.a input.d hC.2.1 hC.2.2.1 s h.2.1 h.2.2.1
  have ht := BinaryOrderedThreeFactoryWork.arithmeticWork_bound _ (BinaryThreeSpecCompiler.ordered_canonical input hC)
    s hs (ordered_height input s h)
  exact Nat.add_le_add hg ht

end Blotto.BinaryUnorderedThreeFactoryWork
