import Blotto.QuantileCDFWitness
import Blotto.RealCDFDistance
import Mathlib.Algebra.Order.Floor.Semiring

/-! The actual deterministic downward quantile floor map uses zero and the
lower quantiles i/K, 1 <= i < K. Duplicate anchors are permitted. Its finite
image has at most K anchors and its pushforward changes both closed and
strict CDFs by at most 1/K, including endpoint atoms. No equal label masses
or independent-coordinate coupling is asserted. The original whole draw
must be retained when this scalar map is lifted to budget-feasible vectors.
Finite rational order-cell representation and the minimax comparator remain
separate, as do any algorithm/encoding/runtime claims. -/

namespace Blotto.DeterministicQuantileRounding
open MeasureTheory Set ProbabilityTheory QuantileCDFWitness
open scoped BigOperators Classical

noncomputable def anchor (ρ : ProbabilityMeasure ℝ) (K : ℕ) (j : Fin K) : ℝ :=
  if j.val = 0 then 0 else quantile ρ ((j.val : ℝ) / K)

theorem level_positive (K : ℕ) (hK : 0 < K) (j : Fin K) (hj : j.val ≠ 0) :
    0 < (j.val : ℝ) / K :=
  div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hj)) (by exact_mod_cast hK)

theorem level_lt_one (K : ℕ) (hK : 0 < K) (j : Fin K) : (j.val : ℝ) / K < 1 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_lt_one hk]
  exact_mod_cast j.isLt

theorem anchor_nonnegative (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (j : Fin K) : 0 ≤ anchor ρ K j := by
  unfold anchor
  split
  · exact le_rfl
  · rename_i hj
    exact quantile_nonnegative ρ hρ _ (level_positive K hK j hj) (level_lt_one K hK j).le

theorem anchor_le_one (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (j : Fin K) : anchor ρ K j ≤ 1 := by
  unfold anchor
  split
  · norm_num
  · rename_i hj
    exact quantile_le_one ρ hρ _ (level_positive K hK j hj) (level_lt_one K hK j).le

noncomputable def candidate (ρ : ProbabilityMeasure ℝ) (K : ℕ) (j : Fin K) (x : ℝ) : ℝ :=
  if anchor ρ K j ≤ x then anchor ρ K j else 0

noncomputable def round (ρ : ProbabilityMeasure ℝ) (K : ℕ) (hK : 0 < K) (x : ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0,hK⟩,Finset.mem_univ _⟩ (fun j => candidate ρ K j x)

theorem candidate_le_round (ρ : ProbabilityMeasure ℝ) (K : ℕ) (hK : 0 < K) (j : Fin K) (x : ℝ) :
    candidate ρ K j x ≤ round ρ K hK x :=
  Finset.le_sup' (fun k => candidate ρ K k x) (Finset.mem_univ j)

theorem round_nonnegative (ρ : ProbabilityMeasure ℝ) (K : ℕ) (hK : 0 < K) (x : ℝ) :
    0 ≤ round ρ K hK x := by
  have h := candidate_le_round ρ K hK ⟨0,hK⟩ x
  simpa [candidate,anchor] using h

theorem round_le (ρ : ProbabilityMeasure ℝ) (K : ℕ) (hK : 0 < K)
    (x : ℝ) (hx : 0 ≤ x) : round ρ K hK x ≤ x := by
  apply Finset.sup'_le
  intro j _
  unfold candidate
  split
  · exact ‹anchor ρ K j ≤ x›
  · exact hx

theorem round_le_threshold (ρ : ProbabilityMeasure ℝ) (K : ℕ) (hK : 0 < K)
    (x t : ℝ) (ht : 0 ≤ t) (hxt : x ≤ t) : round ρ K hK x ≤ t := by
  apply Finset.sup'_le
  intro j _
  unfold candidate
  split
  · exact (‹anchor ρ K j ≤ x›).trans hxt
  · exact ht

theorem round_mem_anchors (ρ : ProbabilityMeasure ℝ) (K : ℕ) (hK : 0 < K) (x : ℝ) :
    ∃ j : Fin K, round ρ K hK x = anchor ρ K j := by
  obtain ⟨j,_hj,he⟩ := Finset.exists_mem_eq_sup'
    (⟨⟨0,hK⟩,Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin K)).Nonempty)
    (fun j => candidate ρ K j x)
  unfold round
  rw [he]
  unfold candidate
  split
  · exact ⟨j,rfl⟩
  · exact ⟨⟨0,hK⟩,by simp [anchor]⟩

theorem round_monotone (ρ : ProbabilityMeasure ℝ) (_hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) : Monotone (round ρ K hK) := by
  intro x y hxy
  apply Finset.sup'_le
  intro j _
  unfold candidate
  split
  · rename_i hx
    have h := candidate_le_round ρ K hK j y
    simpa only [candidate,ite_eq_left (hx.trans hxy)] using h
  · exact round_nonnegative ρ K hK y

theorem round_measurable (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) : Measurable (round ρ K hK) :=
  (round_monotone ρ hρ K hK).measurable

/-- The next strictly higher grid level lies within one mesh of any CDF
value whose distance to one is larger than the mesh. -/
theorem next_level (K : ℕ) (hK : 0 < K) (f : ℝ) (hf : 0 ≤ f)
    (hTail : f + 1 / K < 1) :
    ∃ j : Fin K, j.val ≠ 0 ∧ f < (j.val : ℝ) / K ∧ (j.val : ℝ) / K ≤ f + 1 / K := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hFloor := Nat.floor_le (mul_nonneg hk.le hf)
  have hNext := Nat.lt_floor_add_one ((K : ℝ) * f)
  have hMul := mul_lt_mul_of_pos_right hTail hk
  have hDiv : (f + 1 / (K : ℝ)) * K = f * K + 1 := by
    field_simp
  rw [hDiv,one_mul] at hMul
  have hi : Nat.floor ((K : ℝ) * f) + 1 < K := by
    have hCast : ((Nat.floor ((K : ℝ) * f) + 1 : ℕ) : ℝ) < K := by
      push_cast
      nlinarith
    exact_mod_cast hCast
  refine ⟨⟨Nat.floor ((K : ℝ) * f) + 1,hi⟩,?_,?_,?_⟩
  · change Nat.floor ((K : ℝ) * f) + 1 ≠ 0
    omega
  · apply (lt_div_iff₀ hk).mpr
    push_cast
    nlinarith
  · apply (div_le_iff₀ hk).mpr
    rw [hDiv]
    push_cast
    nlinarith

noncomputable def roundedLaw (ρ : ProbabilityMeasure ℝ) (K : ℕ) (hK : 0 < K) : ProbabilityMeasure ℝ :=
  ρ.map (round ρ K hK)

noncomputable def anchors (ρ : ProbabilityMeasure ℝ) (K : ℕ) : Finset ℝ :=
  Finset.univ.image (anchor ρ K)

theorem anchors_card (ρ : ProbabilityMeasure ℝ) (K : ℕ) : (anchors ρ K).card ≤ K := by
  exact Finset.card_image_le.trans_eq (by simp)

theorem round_mem_unit (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (x : ℝ) : round ρ K hK x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨j,hj⟩ := round_mem_anchors ρ K hK x
  rw [hj]
  exact ⟨anchor_nonnegative ρ hρ K hK j,anchor_le_one ρ hρ K hK j⟩

theorem roundedLaw_unitSupported (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) : UnitSupported (roundedLaw ρ K hK) := by
  change ∀ᵐ x ∂Measure.map (round ρ K hK) (ρ : Measure ℝ), x ∈ Icc (0 : ℝ) 1
  apply (ae_map_iff (p := fun x => x ∈ Icc (0 : ℝ) 1)
    (round_measurable ρ hρ K hK).aemeasurable measurableSet_Icc).mpr
  exact Filter.Eventually.of_forall (round_mem_unit ρ hρ K hK)

theorem roundedLaw_finite_support (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) :
    ∀ᵐ x ∂(roundedLaw ρ K hK : Measure ℝ), x ∈ (anchors ρ K : Set ℝ) := by
  change ∀ᵐ x ∂Measure.map (round ρ K hK) (ρ : Measure ℝ), x ∈ (anchors ρ K : Set ℝ)
  have hSet : MeasurableSet {x : ℝ | x ∈ (anchors ρ K : Set ℝ)} := by
    change MeasurableSet (anchors ρ K : Set ℝ)
    exact (Finset.finite_toSet (anchors ρ K)).measurableSet
  apply (ae_map_iff (p := fun x => x ∈ (anchors ρ K : Set ℝ))
    (round_measurable ρ hρ K hK).aemeasurable hSet).mpr
  apply Filter.Eventually.of_forall
  intro x
  obtain ⟨j,hj⟩ := round_mem_anchors ρ K hK x
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.symm⟩

theorem closed_mass_lower (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (t : ℝ) (ht : 0 ≤ t) :
    (ρ : Measure ℝ).real (Iic t) ≤ (roundedLaw ρ K hK : Measure ℝ).real (Iic t) := by
  change _ ≤ (Measure.map (round ρ K hK) (ρ : Measure ℝ)).real (Iic t)
  rw [map_measureReal_apply (round_measurable ρ hρ K hK) measurableSet_Iic]
  exact measureReal_mono (fun x hx => round_le_threshold ρ K hK x t ht hx)

theorem closed_mass_upper (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (t : ℝ) :
    (roundedLaw ρ K hK : Measure ℝ).real (Iic t) ≤ (ρ : Measure ℝ).real (Iic t) + 1 / K := by
  by_cases hTail : cdf (ρ : Measure ℝ) t + 1 / K < 1
  · obtain ⟨j,hj,hLower,hUpper⟩ := next_level K hK _ (cdf_nonneg _ _) hTail
    have hLevel0 := level_positive K hK j hj
    have hLevel1 := level_lt_one K hK j
    have hAnchor : anchor ρ K j = quantile ρ ((j.val : ℝ) / K) := by simp only [anchor,hj,ite_false]
    have htq : t < quantile ρ ((j.val : ℝ) / K) :=
      (below_quantile_iff_cdf ρ hρ _ hLevel0 hLevel1.le t).mpr hLower
    have hEvent : round ρ K hK ⁻¹' Iic t ⊆ Iio (quantile ρ ((j.val : ℝ) / K)) := by
      intro x hx
      change x < quantile ρ ((j.val : ℝ) / K)
      change round ρ K hK x ≤ t at hx
      apply lt_of_not_ge
      intro hqx
      have hc := candidate_le_round ρ K hK j x
      have hax : anchor ρ K j ≤ x := hAnchor.symm ▸ hqx
      rw [candidate,ite_eq_left hax,hAnchor] at hc
      exact (not_le_of_gt htq) (hc.trans hx)
    change (Measure.map (round ρ K hK) (ρ : Measure ℝ)).real (Iic t) ≤ _
    rw [map_measureReal_apply (round_measurable ρ hρ K hK) measurableSet_Iic]
    have hMass := (measureReal_mono (μ := (ρ : Measure ℝ)) hEvent).trans
      (strict_mass_quantile_le ρ hρ _ hLevel0)
    rw [← cdf_eq_real]
    exact hMass.trans hUpper
  · have ht : 1 ≤ (ρ : Measure ℝ).real (Iic t) + 1 / K := by
      rw [← cdf_eq_real]
      exact le_of_not_gt hTail
    exact measureReal_le_one.trans ht

theorem closed_cdf_error (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) : RealCDFClose ρ (roundedLaw ρ K hK) (1 / K) := by
  intro t
  by_cases ht : 0 ≤ t
  · have hLower := closed_mass_lower ρ hρ K hK t ht
    have hUpper := closed_mass_upper ρ hρ K hK t
    apply abs_le.mpr
    constructor <;> linarith
  · have hOld : (ρ : Measure ℝ).real (Iic t) = 0 := by
      rw [← cdf_eq_real]
      exact cdf_below_zero ρ hρ t (lt_of_not_ge ht)
    have hEvent : round ρ K hK ⁻¹' Iic t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ht ((round_nonnegative ρ K hK x).trans hx)
    change |(ρ : Measure ℝ).real (Iic t) - (Measure.map (round ρ K hK) (ρ : Measure ℝ)).real (Iic t)| ≤ _
    rw [hOld,map_measureReal_apply (round_measurable ρ hρ K hK) measurableSet_Iic,hEvent,measureReal_empty]
    simp only [sub_self,abs_zero]
    positivity

theorem strict_cdf_error (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (t : ℝ) :
    |(ρ : Measure ℝ).real (Iio t) - (roundedLaw ρ K hK : Measure ℝ).real (Iio t)| ≤ 1 / K :=
  (closed_cdf_error ρ hρ K hK).strict t

theorem closed_mass_lower_all (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (t : ℝ) :
    (ρ : Measure ℝ).real (Iic t) ≤ (roundedLaw ρ K hK : Measure ℝ).real (Iic t) := by
  by_cases ht : 0 ≤ t
  · exact closed_mass_lower ρ hρ K hK t ht
  · rw [← cdf_eq_real,cdf_below_zero ρ hρ t (lt_of_not_ge ht)]
    exact measureReal_nonneg

theorem strict_mass_lower (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (t : ℝ) :
    (ρ : Measure ℝ).real (Iio t) ≤ (roundedLaw ρ K hK : Measure ℝ).real (Iio t) := by
  rw [real_Iio_eq_leftLim,real_Iio_eq_leftLim]
  apply le_of_tendsto_of_tendsto ((monotone_cdf (ρ : Measure ℝ)).tendsto_leftLim t)
    ((monotone_cdf (roundedLaw ρ K hK : Measure ℝ)).tendsto_leftLim t)
  apply Filter.Eventually.of_forall
  intro x
  simpa only [cdf_eq_real] using closed_mass_lower_all ρ hρ K hK x

theorem both_cdf_increases (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (K : ℕ) (hK : 0 < K) (t : ℝ) :
    0 ≤ (roundedLaw ρ K hK : Measure ℝ).real (Iic t) - (ρ : Measure ℝ).real (Iic t) ∧
      (roundedLaw ρ K hK : Measure ℝ).real (Iic t) - (ρ : Measure ℝ).real (Iic t) ≤ 1 / K ∧
    0 ≤ (roundedLaw ρ K hK : Measure ℝ).real (Iio t) - (ρ : Measure ℝ).real (Iio t) ∧
      (roundedLaw ρ K hK : Measure ℝ).real (Iio t) - (ρ : Measure ℝ).real (Iio t) ≤ 1 / K := by
  have hc := closed_mass_lower_all ρ hρ K hK t
  have hu := closed_mass_upper ρ hρ K hK t
  have hs := strict_mass_lower ρ hρ K hK t
  have hsu := abs_le.mp (strict_cdf_error ρ hρ K hK t)
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end Blotto.DeterministicQuantileRounding
