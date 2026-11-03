import Blotto.GeneralPaperStoredInterpolation

/-! A single interpolation pass charges every arithmetic operand and result
copy, followed by one materialization of the group vector. Generic bounds
retain dimension, address and rational precision as separate parameters. -/
namespace Blotto.GeneralPaperStoredInterpolationWork
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def perElement (model : RationalCostModel) (A s : ℕ) : ℕ :=
  26 * model.rat (1 + 2 * expressionHeightBudget s 3) + 208 * (A + 1)

def bound (model : RationalCostModel) (A m s : ℕ) : ℕ :=
  m * perElement model A s + 64 * (m + 1) * A + 192 * (A + 1)

theorem coordinate_height (model : RationalCostModel) (A : ℕ) (B t P Q : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hB : RationalHeight B s) (ht : RationalHeight t s) (hP : RationalHeight P s) (hQ : RationalHeight Q s) :
    RationalHeight (GeneralPaperEqualBitGroups.coordinate model A B t P Q).1 (expressionHeightBudget s 3) := by
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hValue := hB.mul (((hOne.sub ht).mul hP).add (ht.mul hQ))
  exact hValue.mono (by unfold expressionHeightBudget; norm_num; omega)

theorem price_bound (model : RationalCostModel) (A s : ℕ) (budget midpoint : ℚ) (left right : List ℚ)
    (hLength : left.length = right.length) (hs : 2 ≤ s) (hB : RationalHeight budget s) (ht : RationalHeight midpoint s)
    (hP : ∀ p ∈ left,RationalHeight p s) (hQ : ∀ q ∈ right,RationalHeight q s) :
    GeneralPaperStoredInterpolation.price model A budget midpoint left right ≤ left.length * perElement model A s + 64 * (A + 1) := by
  induction left generalizing right with
  | nil =>
    have hr : right = [] := List.eq_nil_of_length_eq_zero hLength.symm
    subst right
    simp only [GeneralPaperStoredInterpolation.price,List.length_nil,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons p left ih =>
    cases right with
    | nil => simp only [List.length_cons,List.length_nil] at hLength; omega
    | cons q right =>
      have hTail : left.length = right.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hLength
      have hLater := ih right hTail (fun p hp => hP p (List.mem_cons_of_mem _ hp)) (fun q hq => hQ q (List.mem_cons_of_mem _ hq))
      have hArithmetic := GeneralPaperEqualBitGroups.coordinate_work model A budget midpoint p q s hs hB ht
        (hP p (List.mem_cons_self ..)) (hQ q (List.mem_cons_self ..))
      have hCopy := (rationalWordWidth_of_height (coordinate_height model A budget midpoint p q s hs hB ht
        (hP p (List.mem_cons_self ..)) (hQ q (List.mem_cons_self ..)))).trans (model.word_le _)
      simp only [GeneralPaperStoredInterpolation.price,List.length_cons]
      unfold perElement at *
      nlinarith only [hLater,hArithmetic,hCopy]

theorem array_work (model : RationalCostModel) (A s : ℕ) (budget midpoint : ℚ) (left right : List ℚ)
    (hLength : left.length = right.length) (hA : 0 < A) (hIndex : binaryWordWidth (left.length + 1) ≤ A)
    (hs : 2 ≤ s) (hB : RationalHeight budget s) (ht : RationalHeight midpoint s)
    (hP : ∀ p ∈ left,RationalHeight p s) (hQ : ∀ q ∈ right,RationalHeight q s) :
    (GeneralPaperStoredInterpolation.array model A budget midpoint left right).2 ≤ bound model A left.length s := by
  let rows := List.zipWith (fun p q => budget * ((1 - midpoint) * p + midpoint * q)) left right
  have hRows : rows.length = left.length := by simp only [rows,List.length_zipWith,← hLength,min_self]
  have hBuffer := PaperListReferenceArray.bit_work A rows hA (by rw [hRows]; exact hIndex)
  rw [hRows] at hBuffer
  have hPrice := price_bound model A s budget midpoint left right hLength hs hB ht hP hQ
  obtain ⟨hv,hw⟩ := GeneralPaperStoredInterpolation.source model A budget midpoint left right hLength
  simp only [GeneralPaperStoredInterpolation.array,hv,hw]
  unfold bound
  dsimp only [rows] at hBuffer
  omega

theorem array_rows_work {m : ℕ} (model : RationalCostModel) (A s : ℕ) (budget midpoint : ℚ)
    (left right : FixedArrayTable m ℚ) (hA : 0 < A) (hIndex : binaryWordWidth (m + 1) ≤ A)
    (hs : 2 ≤ s) (hB : RationalHeight budget s) (ht : RationalHeight midpoint s)
    (hP : ∀ g,RationalHeight (left.read g) s) (hQ : ∀ g,RationalHeight (right.read g) s) :
    (GeneralPaperStoredInterpolation.array model A budget midpoint left.data.toList right.data.toList).2 ≤ bound model A m s := by
  have hLeft : ∀ p ∈ left.data.toList,RationalHeight p s := by
    intro p hp
    rw [← GeneralPaperRowPrefix.list_ofFn left] at hp
    obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hp
    exact hP g
  have hRight : ∀ q ∈ right.data.toList,RationalHeight q s := by
    intro q hq
    rw [← GeneralPaperRowPrefix.list_ofFn right] at hq
    obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hq
    exact hQ g
  simpa only [Array.length_toList,left.size] using array_work model A s budget midpoint left.data.toList right.data.toList
    (by rw [Array.length_toList,Array.length_toList,left.size,right.size]) hA
    (by simpa only [Array.length_toList,left.size] using hIndex) hs hB ht hLeft hRight

end Blotto.GeneralPaperStoredInterpolationWork
