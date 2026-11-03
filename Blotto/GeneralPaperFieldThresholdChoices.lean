import Blotto.FiniteAnchorResponseTransport

/-! Field-dependent finite thresholds, including zero. The definitions
allow arbitrary real thresholds and different cardinalities by field. -/
namespace Blotto.GeneralPaperFieldThresholdChoices
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2800000

structure Thresholds (m : ℕ) where
  field : Fin m → Finset ℝ
  zero : ∀ j, 0 ∈ field j
  nonnegative : ∀ j t, t ∈ field j → 0 ≤ t

def Pattern {m : ℕ} (T : Thresholds m) := ∀ j, {t // t ∈ T.field j} × Bool

def threshold {m : ℕ} {T : Thresholds m} (p : Pattern T) (j : Fin m) : ℝ := (p j).1.val

def opened {m : ℕ} {T : Thresholds m} (p : Pattern T) (j : Fin m) : Bool := (p j).2

def Makes {m : ℕ} {T : Thresholds m} (p : Pattern T) (y : Allocation m) : Prop :=
  ∀ j, if opened p j then
    threshold p j < y j ∧ ∀ s ∈ T.field j, threshold p j < s → y j < s
  else y j = threshold p j

def Affordable {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ) : Prop :=
  (∑ j, threshold p j) < budget ∨
    (∑ j, threshold p j) = budget ∧ ∀ j, opened p j = false

noncomputable def gaps {m : ℕ} (T : Thresholds m) : Finset ℝ :=
  insert 1 (Finset.univ.biUnion fun j : Fin m =>
    ((T.field j).product (T.field j)).image fun pair =>
      if pair.1 < pair.2 then pair.2 - pair.1 else 1)

noncomputable def gap {m : ℕ} (T : Thresholds m) : ℝ :=
  (gaps T).inf' (Finset.insert_nonempty _ _) id

theorem gap_positive {m : ℕ} (T : Thresholds m) : 0 < gap T := by
  apply (Finset.lt_inf'_iff _).mpr
  intro value hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · norm_num
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨pair, _, rfl⟩ := Finset.mem_image.mp hj
    split_ifs with h
    · exact sub_pos.mpr h
    · norm_num

theorem gap_le {m : ℕ} (T : Thresholds m) (j : Fin m) (s t : ℝ)
    (hs : s ∈ T.field j) (ht : t ∈ T.field j) (h : s < t) : gap T ≤ t - s := by
  apply Finset.inf'_le
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, ?_⟩⟩
  simp [h]

noncomputable def bump {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ) : ℝ :=
  min (gap T / 2) ((budget - ∑ j, threshold p j) / (m + 1))

noncomputable def realize {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ) : Allocation m :=
  fun j => threshold p j + if opened p j then bump p budget else 0

theorem bump_positive {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ)
    (h : (∑ j, threshold p j) < budget) : 0 < bump p budget := by
  exact lt_min (by positivity [gap_positive T]) (by positivity)

theorem bump_budget {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ)
    (h : (∑ j, threshold p j) < budget) :
    (m : ℝ) * bump p budget ≤ budget - ∑ j, threshold p j := by
  have hp := bump_positive p budget h
  have hb := min_le_right (gap T / 2) ((budget - ∑ j, threshold p j) / (m + 1))
  have hd : (0 : ℝ) < m + 1 := by positivity
  have hv : bump p budget * (m + 1) ≤ budget - ∑ j, threshold p j := (le_div_iff₀ hd).mp hb
  nlinarith

theorem makes_lower {m : ℕ} {T : Thresholds m} (p : Pattern T) (y : Allocation m)
    (h : Makes p y) (j : Fin m) : threshold p j ≤ y j := by
  have hj := h j
  cases ho : opened p j with
  | false => simp only [ho, Bool.false_eq_true, ite_false] at hj; exact hj.ge
  | true => simp only [ho, ite_true] at hj; exact hj.1.le

end Blotto.GeneralPaperFieldThresholdChoices
