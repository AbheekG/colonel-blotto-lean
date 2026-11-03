import Blotto.BinaryNestedOrderedFactoryWork
import Blotto.BinaryUnorderedThreeFactoryWork
import Blotto.RationalPreparationCommonPrice

/-! The full nested-spec factory retains both endpoint branches, actual native
sorting, the ordered interior producer and coordinate restoration. Original
canonical fields derive the complete eighteen-slot table height and primitive
ledger. Source feasibility/law guarantees transfer through the exact old table;
copying, metadata and physical execution costs remain separate. -/

namespace Blotto.BinaryNestedSpecFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryNestedParameters BinaryNestedParameterWork BinaryFactoryHeight
open BinaryNestedTerminalInput BinaryNestedSpecProfile

theorem sortedInput_height (input : Input) (hC : input.Canonical) (s : ℕ) (hH : InputHeight input s) :
    InputHeight (sortedInput input) s := by
  refine ⟨hH.1,?_,?_,hH.2.2.2.1,hH.2.2.2.2.1,hH.2.2.2.2.2⟩
  · change RationalHeight (value (apply .minimum input.a input.d)) s
    rw [apply_value .minimum _ _ hC.2.1.1 hC.2.2.1.1]
    change RationalHeight (min (value input.a) (value input.d)) s
    by_cases h : value input.a ≤ value input.d
    · simpa only [min_eq_left h] using hH.2.1
    · simpa only [min_eq_right (le_of_not_ge h)] using hH.2.2.1
  · change RationalHeight (value (apply .maximum input.a input.d)) s
    rw [apply_value .maximum _ _ hC.2.1.1 hC.2.2.1.1]
    change RationalHeight (max (value input.a) (value input.d)) s
    by_cases h : value input.a ≤ value input.d
    · simpa only [max_eq_right h] using hH.2.2.1
    · simpa only [max_eq_left (le_of_not_ge h)] using hH.2.1

theorem swap_height {k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment 3 k) (s : ℕ)
    (h : SegmentHeight table s) : SegmentHeight (swap table) s := by
  refine ⟨h.1,?_⟩
  intro slot j
  simp only [swap,FixedArrayTable.read_ofFn]
  fin_cases j <;> exact h.2 _ _

theorem longInput_height (input : Input) (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    BinaryOrderedThreeFactoryWork.InputHeight (longInput input) s :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,one_height s hs⟩

theorem shortInput_height (input : Input) (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    BinaryOrderedThreeFactoryWork.InputHeight (shortInput input) s :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,one_height s hs⟩

def sortedWithWork (input : Input) : Input × ℕ :=
  let low := applyWithWork .minimum input.a input.d
  let high := applyWithWork .maximum input.a input.d
  ({ input with a := low.1, d := high.1 },low.2 + high.2)

theorem sortedWithWork_state (input : Input) : (sortedWithWork input).1 = sortedInput input := by
  unfold sortedWithWork sortedInput
  simp only [applyWithWork_state]

theorem sortedWithWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hH : InputHeight input s) :
    (sortedWithWork input).2 ≤ 2 * opcodeBound s := by
  have hl := opcode_bound .minimum input.a input.d hC.2.1 hC.2.2.1 s hH.2.1 hH.2.2.1
  have hh := opcode_bound .maximum input.a input.d hC.2.1 hC.2.2.1 s hH.2.1 hH.2.2.1
  unfold sortedWithWork
  dsimp only
  omega

def profileWithWork (input : Input) (K : ℕ) (bits : Fin K → Bool) : BinaryStoredOverlapEnvironment.Segment 3 18 × ℕ :=
  let zeroGuard := BinaryRationalArithmetic.lessEqualWork input.q zero
  if qZero input then
    let table := BinaryUnorderedThreeFactoryWork.descriptorWithWork (longInput input)
    (BinarySegmentAssembly.padRight table.1 9 0,zeroGuard + table.2)
  else
    let oneGuard := BinaryRationalArithmetic.lessEqualWork BinaryExpressionCompiler.Constant.one.word input.q
    if qOne input then
      let table := BinaryUnorderedThreeFactoryWork.descriptorWithWork (shortInput input)
      (BinarySegmentAssembly.padRight table.1 9 0,zeroGuard + oneGuard + table.2)
    else
      let sorted := sortedWithWork input
      let table := BinaryNestedOrderedFactoryWork.profileWithWork sorted.1 K bits
      (if ordered input then table.1 else swap table.1,
        zeroGuard + oneGuard + sorted.2 + table.2 + BinaryRationalArithmetic.lessEqualWork input.a input.d)

theorem profileWithWork_state (input : Input) (K : ℕ) (bits : Fin K → Bool) :
    (profileWithWork input K bits).1 = profile input K bits := by
  unfold profileWithWork profile
  split_ifs <;> simp only [BinaryUnorderedThreeFactoryWork.descriptorWithWork_state,
    BinaryNestedOrderedFactoryWork.profileWithWork_state,sortedWithWork_state]

theorem profile_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s)
    (K : ℕ) (bits : Fin K → Bool) :
    SegmentHeight (profile input K bits) (BinaryNestedOrderedFactoryWork.height s K 83) := by
  have hm : expressionHeightBudget s 18 ≤ BinaryNestedOrderedFactoryWork.height s K 83 :=
    (expressionHeightBudget_input_mono (le_max_left s (K + 2)) 18).trans
      (expressionHeightBudget_mono _ (by decide : 18 ≤ 83))
  have ht := BinaryNestedOrderedFactoryWork.profile_height _ (sortedInput_canonical input hC) s hs
    (sortedInput_height input hC s hH) K bits
  unfold profile
  split
  · exact BinaryAssemblyArithmeticWork.pad_height _ 9 0 _ (height_three (hs.trans (le_max_left _ _)))
      ((BinaryUnorderedThreeFactoryWork.descriptor_height _ (longInput_canonical input hC) s hs
        (longInput_height input s hs hH)).mono hm)
  · split
    · exact BinaryAssemblyArithmeticWork.pad_height _ 9 0 _ (height_three (hs.trans (le_max_left _ _)))
        ((BinaryUnorderedThreeFactoryWork.descriptor_height _ (shortInput_canonical input hC) s hs
          (shortInput_height input s hs hH)).mono hm)
    · dsimp only
      split
      · exact ht
      · exact swap_height _ _ ht

def bound (s K : ℕ) : ℕ := 3 * compareBound s + BinaryUnorderedThreeFactoryWork.bound s +
  2 * opcodeBound s + BinaryNestedOrderedFactoryWork.bound s K

theorem profileWithWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s)
    (K : ℕ) (bits : Fin K → Bool) : (profileWithWork input K bits).2 ≤ bound s K := by
  have hg0 := comparator_bound input.q zero hC.2.2.2.2.2 zero_canonical s hH.2.2.2.2.2 (zero_height s hs)
  have hg1 := comparator_bound BinaryExpressionCompiler.Constant.one.word input.q
    (BinaryExpressionCompiler.Constant.word_canonical .one) hC.2.2.2.2.2 s (one_height s hs) hH.2.2.2.2.2
  have hgOrder := comparator_bound input.a input.d hC.2.1 hC.2.2.1 s hH.2.1 hH.2.2.1
  have hLong := BinaryUnorderedThreeFactoryWork.descriptorWithWork_bound _ (longInput_canonical input hC)
    s hs (longInput_height input s hs hH)
  have hShort := BinaryUnorderedThreeFactoryWork.descriptorWithWork_bound _ (shortInput_canonical input hC)
    s hs (shortInput_height input s hs hH)
  have hSort := sortedWithWork_bound input hC s hH
  have hInterior := BinaryNestedOrderedFactoryWork.profileWithWork_bound _ (sortedInput_canonical input hC)
    s hs (sortedInput_height input hC s hH) K bits
  unfold profileWithWork
  dsimp only
  split_ifs <;> simp only [sortedWithWork_state] <;> unfold bound <;> omega

theorem profileWithWork_canonical (input : Input) (hC : input.Canonical) (K : ℕ) (bits : Fin K → Bool) :
    (profileWithWork input K bits).1.Canonical := by
  rw [profileWithWork_state]
  exact profile_canonical input hC K bits

theorem profileWithWork_refines (input : Input) (source : RationalNestedSpec) (hC : input.Canonical)
    (hR : InputRefinesSpec input source) (K : ℕ) (bits : Fin K → Bool) :
    (profileWithWork input K bits).1.Refines (source.profile K bits) := by
  rw [profileWithWork_state]
  exact profile_refines input source hC hR K bits

end Blotto.BinaryNestedSpecFactoryWork
