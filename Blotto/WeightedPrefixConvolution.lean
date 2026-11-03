import Blotto.Model

/-! Finite weighted resource prefixes and their convolution order. Labels remain
distinct when resources coincide. Every cutoff uses the closed `≤` convention.
Masses need not sum to one, and guide atoms need not be true state bins. -/

namespace Blotto
open scoped BigOperators Classical

structure WeightedResourceFamily (n : ℕ) where
  resource : Fin n → ℝ
  mass : Fin n → ℝ
  mass_nonnegative : ∀ i, 0 ≤ mass i

namespace WeightedResourceFamily

noncomputable def prefixMass {n : ℕ} (a : WeightedResourceFamily n) (t : ℝ) : ℝ :=
  ∑ i, if a.resource i ≤ t then a.mass i else 0

def PrefixLE {n m : ℕ} (a : WeightedResourceFamily n) (b : WeightedResourceFamily m) : Prop :=
  ∀ t, a.prefixMass t ≤ b.prefixMass t

noncomputable def convolution {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, if a.resource i + b.resource j ≤ t then a.mass i * b.mass j else 0

theorem prefix_nonnegative {n : ℕ} (a : WeightedResourceFamily n) (t : ℝ) :
    0 ≤ a.prefixMass t := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact a.mass_nonnegative i
  · exact le_rfl

theorem prefix_monotone {n : ℕ} (a : WeightedResourceFamily n) : Monotone a.prefixMass := by
  intro s t hst
  apply Finset.sum_le_sum
  intro i _
  by_cases hs : a.resource i ≤ s
  · simp only [hs, hs.trans hst, ite_true]
    exact le_rfl
  · simp only [hs, ite_false]
    split_ifs
    · exact a.mass_nonnegative i
    · exact le_rfl

theorem convolution_nonnegative {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (t : ℝ) : 0 ≤ a.convolution b t := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (a.mass_nonnegative i) (b.mass_nonnegative j)
  · exact le_rfl

theorem convolution_prefix_right {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (t : ℝ) :
    a.convolution b t = ∑ i, a.mass i * b.prefixMass (t - a.resource i) := by
  unfold convolution prefixMass
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : a.resource i + b.resource j ≤ t ↔ b.resource j ≤ t - a.resource i := by
    constructor <;> intro h <;> linarith
  simp only [h]
  split_ifs <;> simp

theorem convolution_comm {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (t : ℝ) : a.convolution b t = b.convolution a t := by
  unfold convolution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm, mul_comm]

theorem convolution_prefix_left {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (t : ℝ) :
    a.convolution b t = ∑ j, b.mass j * a.prefixMass (t - b.resource j) := by
  rw [convolution_comm]
  exact b.convolution_prefix_right a t

theorem convolution_right_mono {n m k : ℕ} (a : WeightedResourceFamily n)
    {b : WeightedResourceFamily m} {c : WeightedResourceFamily k} (h : b.PrefixLE c)
    (t : ℝ) : a.convolution b t ≤ a.convolution c t := by
  rw [convolution_prefix_right, convolution_prefix_right]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h _) (a.mass_nonnegative i)

theorem convolution_left_mono {n m k : ℕ} {a : WeightedResourceFamily n}
    {b : WeightedResourceFamily m} (h : a.PrefixLE b) (c : WeightedResourceFamily k)
    (t : ℝ) : a.convolution c t ≤ b.convolution c t := by
  rw [convolution_prefix_left, convolution_prefix_left]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (h _) (c.mass_nonnegative j)

theorem convolution_mono {n m k l : ℕ} {a : WeightedResourceFamily n}
    {b : WeightedResourceFamily m} {c : WeightedResourceFamily k}
    {d : WeightedResourceFamily l} (hab : a.PrefixLE b) (hcd : c.PrefixLE d)
    (t : ℝ) : a.convolution c t ≤ b.convolution d t :=
  (convolution_left_mono hab c t).trans (convolution_right_mono b hcd t)

/- A nonnegative linear combination of closed prefix indicators is an
antitone finite step test. This is the exact test representation needed by
the convolution argument, without any normalization assumption. -/
theorem prefix_step_test_mono {n m k : ℕ} {a : WeightedResourceFamily n}
    {b : WeightedResourceFamily m} (h : a.PrefixLE b)
    (cutoff coefficient : Fin k → ℝ) (hc : ∀ j, 0 ≤ coefficient j) :
    (∑ i, a.mass i * ∑ j, if a.resource i ≤ cutoff j then coefficient j else 0) ≤
      ∑ i, b.mass i * ∑ j, if b.resource i ≤ cutoff j then coefficient j else 0 := by
  have he : ∀ {p : ℕ} (x : WeightedResourceFamily p),
      (∑ i, x.mass i * ∑ j, if x.resource i ≤ cutoff j then coefficient j else 0) =
        ∑ j, coefficient j * x.prefixMass (cutoff j) := by
    intro p x
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    unfold prefixMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [mul_comm]
  rw [he a, he b]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (h _) (hc j)

def scale {n : ℕ} (a : WeightedResourceFamily n) (c : ℝ) (hc : 0 ≤ c) :
    WeightedResourceFamily n :=
  ⟨a.resource, fun i => c * a.mass i, fun i => mul_nonneg hc (a.mass_nonnegative i)⟩

theorem prefix_scale {n : ℕ} (a : WeightedResourceFamily n) (c : ℝ) (hc : 0 ≤ c)
    (t : ℝ) : (a.scale c hc).prefixMass t = c * a.prefixMass t := by
  unfold prefixMass scale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem convolution_scale {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (t : ℝ) :
    (a.scale c hc).convolution (b.scale d hd) t = (c * d) * a.convolution b t := by
  unfold convolution scale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · ring
  · simp

/- Upper envelopes on the child CDFs multiply under convolution. The
resources and label counts of the guides may differ from the true families. -/
theorem convolution_upper_envelope {n m k l : ℕ} {a : WeightedResourceFamily n}
    {b : WeightedResourceFamily m} {c : WeightedResourceFamily k}
    {d : WeightedResourceFamily l} (g h : ℝ) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hab : ∀ t, a.prefixMass t ≤ g * b.prefixMass t)
    (hcd : ∀ t, c.prefixMass t ≤ h * d.prefixMass t) (t : ℝ) :
    a.convolution c t ≤ (g * h) * b.convolution d t := by
  have ha : a.PrefixLE (b.scale g hg) := by
    intro s
    rw [prefix_scale]
    exact hab s
  have hc : c.PrefixLE (d.scale h hh) := by
    intro s
    rw [prefix_scale]
    exact hcd s
  have he := convolution_mono ha hc t
  rw [convolution_scale] at he
  exact he

theorem local_lower_guide_envelope {n m k l p : ℕ}
    (guide : WeightedResourceFamily p) (leftGuide : WeightedResourceFamily n)
    (rightGuide : WeightedResourceFamily m) (leftTrue : WeightedResourceFamily k)
    (rightTrue : WeightedResourceFamily l) (g h gamma : ℝ)
    (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hleftLower : leftGuide.PrefixLE leftTrue)
    (hrightLower : rightGuide.PrefixLE rightTrue)
    (hleftUpper : ∀ t, leftTrue.prefixMass t ≤ g * leftGuide.prefixMass t)
    (hrightUpper : ∀ t, rightTrue.prefixMass t ≤ h * rightGuide.prefixMass t)
    (hlocalLower : ∀ t, guide.prefixMass t ≤ leftGuide.convolution rightGuide t)
    (hlocalUpper : ∀ t, leftGuide.convolution rightGuide t ≤ gamma * guide.prefixMass t)
    (t : ℝ) :
    guide.prefixMass t ≤ leftTrue.convolution rightTrue t ∧
      leftTrue.convolution rightTrue t ≤ (g * h * gamma) * guide.prefixMass t := by
  constructor
  · exact (hlocalLower t).trans (convolution_mono hleftLower hrightLower t)
  · calc
      leftTrue.convolution rightTrue t ≤ (g * h) * leftGuide.convolution rightGuide t :=
        convolution_upper_envelope g h hg hh hleftUpper hrightUpper t
      _ ≤ (g * h) * (gamma * guide.prefixMass t) :=
        mul_le_mul_of_nonneg_left (hlocalUpper t) (mul_nonneg hg hh)
      _ = (g * h * gamma) * guide.prefixMass t := by ring

/- The upper-guide orientation used by the maintained counting learner has
the same product envelope, with the inequalities reversed locally. -/
theorem local_upper_guide_envelope {n m k l p : ℕ}
    (guide : WeightedResourceFamily p) (leftGuide : WeightedResourceFamily n)
    (rightGuide : WeightedResourceFamily m) (leftTrue : WeightedResourceFamily k)
    (rightTrue : WeightedResourceFamily l) (g h gamma : ℝ)
    (hg : 0 ≤ g) (hh : 0 ≤ h) (hgamma : 0 ≤ gamma)
    (hleftLower : leftTrue.PrefixLE leftGuide)
    (hrightLower : rightTrue.PrefixLE rightGuide)
    (hleftUpper : ∀ t, leftGuide.prefixMass t ≤ g * leftTrue.prefixMass t)
    (hrightUpper : ∀ t, rightGuide.prefixMass t ≤ h * rightTrue.prefixMass t)
    (hlocalLower : ∀ t, leftGuide.convolution rightGuide t ≤ guide.prefixMass t)
    (hlocalUpper : ∀ t, guide.prefixMass t ≤ gamma * leftGuide.convolution rightGuide t)
    (t : ℝ) :
    leftTrue.convolution rightTrue t ≤ guide.prefixMass t ∧
      guide.prefixMass t ≤ (gamma * g * h) * leftTrue.convolution rightTrue t := by
  constructor
  · exact (convolution_mono hleftLower hrightLower t).trans (hlocalLower t)
  · calc
      guide.prefixMass t ≤ gamma * leftGuide.convolution rightGuide t := hlocalUpper t
      _ ≤ gamma * ((g * h) * leftTrue.convolution rightTrue t) :=
        mul_le_mul_of_nonneg_left
          (convolution_upper_envelope g h hg hh hleftUpper hrightUpper t) hgamma
      _ = (gamma * g * h) * leftTrue.convolution rightTrue t := by ring

theorem prefix_zero_iff_of_envelope {n m : ℕ} {a : WeightedResourceFamily n}
    {b : WeightedResourceFamily m} (g : ℝ) (hab : a.PrefixLE b)
    (hba : ∀ t, b.prefixMass t ≤ g * a.prefixMass t) (t : ℝ) :
    a.prefixMass t = 0 ↔ b.prefixMass t = 0 := by
  constructor
  · intro ha
    have he := hba t
    rw [ha, mul_zero] at he
    exact le_antisymm he (b.prefix_nonnegative t)
  · intro hb
    have he := hab t
    rw [hb] at he
    exact le_antisymm he (a.prefix_nonnegative t)

theorem prefix_positive_iff_of_envelope {n m : ℕ} {a : WeightedResourceFamily n}
    {b : WeightedResourceFamily m} (g : ℝ) (hab : a.PrefixLE b)
    (hba : ∀ t, b.prefixMass t ≤ g * a.prefixMass t) (t : ℝ) :
    0 < a.prefixMass t ↔ 0 < b.prefixMass t := by
  have he := prefix_zero_iff_of_envelope g hab hba t
  constructor
  · intro ha
    exact ha.trans_le (hab t)
  · intro hb
    have ha : a.prefixMass t ≠ 0 := fun ha => (ne_of_gt hb) (he.mp ha)
    exact lt_of_le_of_ne (a.prefix_nonnegative t) (Ne.symm ha)

end WeightedResourceFamily
end Blotto
