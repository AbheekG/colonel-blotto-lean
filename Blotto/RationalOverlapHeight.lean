import Blotto.RationalOverlapDescriptor
import Blotto.RationalLotteryHeight
import Blotto.RationalHeightBudget

/-! Reduced-rational bounds for every native gluing endpoint and weight.
Inverse parameters and zero divisions retain total rational semantics. Safe
inactive endpoints are budget rows, without a claim of coordinate boxes. -/

namespace Blotto.RationalOverlapGluing

theorem reflected_endpoint_heights {k h : ℕ} (G : RationalOverlapGluing k h) (s : ℕ)
    (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s) (j : Fin h) :
    RationalHeight (G.d - G.second.P j 0) (expressionHeightBudget s 1) ∧
      RationalHeight (G.d - G.second.Q j 0) (expressionHeightBudget s 1) := by
  have hD0 : RationalHeight G.d (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hD
  have hP : RationalHeight (G.second.P j 0) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using (hSecond.2 j 0).1
  have hQ : RationalHeight (G.second.Q j 0) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using (hSecond.2 j 0).2
  exact ⟨hD0.sub_level hP, hD0.sub_level hQ⟩

theorem interval_heights {k h : ℕ} (G : RationalOverlapGluing k h) (s : ℕ)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s)
    (i : Fin k) (j : Fin h) :
    RationalHeight (G.lower i j) (expressionHeightBudget s 1) ∧
      RationalHeight (G.upper i j) (expressionHeightBudget s 1) := by
  have hR := reflected_endpoint_heights G s hSecond hD j
  have hm := expressionHeightBudget_ge_input s 1
  have hP := (hFirst.2 i 2).1.mono hm
  have hQ := (hFirst.2 i 2).2.mono hm
  exact ⟨(hP.min hQ).max (hR.1.min hR.2), (hP.max hQ).min (hR.1.max hR.2)⟩

theorem weight_height {k h : ℕ} (G : RationalOverlapGluing k h) (s : ℕ) (hs : 2 ≤ s)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s)
    (i : Fin k) (j : Fin h) : RationalHeight (G.weight i j) (expressionHeightBudget s 4) := by
  have hInterval := interval_heights G s hFirst hSecond hD i j
  have hSpan := hInterval.2.sub_level hInterval.1
  have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 2) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 2))
  have hGap := hSpan.max hZero
  have hD0 : RationalHeight G.d (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hD
  have hFW : RationalHeight (G.first.weight i) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using hFirst.1 i
  have hSW : RationalHeight (G.second.weight j) (expressionHeightBudget s 1) :=
    (hSecond.1 j).mono (expressionHeightBudget_ge_input s 1)
  have hProduct := (hD0.mul_level hFW).mul_level hSW
  have hNumerator := hProduct.mul_level hGap
  have hFP : RationalHeight (G.first.P i 2) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using (hFirst.2 i 2).1
  have hFQ : RationalHeight (G.first.Q i 2) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using (hFirst.2 i 2).2
  have hReflected := reflected_endpoint_heights G s hSecond hD j
  have hFirstSpan := (hFQ.sub_level hFP).abs.mono (expressionHeightBudget_mono s (by decide : 1 ≤ 2))
  have hSecondSpan := (hReflected.2.sub_level hReflected.1).abs
  have hDenominator := hFirstSpan.mul_level hSecondSpan
  exact hNumerator.div_level hDenominator

theorem inverse_heights {k h : ℕ} (G : RationalOverlapGluing k h) (s : ℕ)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s)
    (i : Fin k) (j : Fin h) (z : ℚ) (hZ : RationalHeight z (expressionHeightBudget s 1)) :
    RationalHeight ((z - G.first.P i 2) / (G.first.Q i 2 - G.first.P i 2)) (expressionHeightBudget s 3) ∧
      RationalHeight ((z - (G.d - G.second.P j 0)) / ((G.d - G.second.Q j 0) - (G.d - G.second.P j 0)))
        (expressionHeightBudget s 3) := by
  have hm := expressionHeightBudget_ge_input s 1
  have hFP := (hFirst.2 i 2).1.mono hm
  have hFQ := (hFirst.2 i 2).2.mono hm
  have hR := reflected_endpoint_heights G s hSecond hD j
  exact ⟨(hZ.sub_level hFP).div_level (hFQ.sub_level hFP),
    (hZ.sub_level hR.1).div_level (hR.2.sub_level hR.1)⟩

theorem curve_height {k h : ℕ} (G : RationalOverlapGluing k h) (s : ℕ) (hs : 2 ≤ s)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s)
    (i : Fin k) (j : Fin h) (z : ℚ) (hZ : RationalHeight z (expressionHeightBudget s 1)) (r : Fin 4) :
    RationalHeight (G.curve i j z r) (expressionHeightBudget s 6) := by
  have hInv := inverse_heights G s hFirst hSecond hD i j z hZ
  have hm := expressionHeightBudget_ge_input s 3
  have hs3 := hs.trans hm
  have hX : ∀ a, RationalHeight (rationalSegmentPoint (G.first.P i) (G.first.Q i)
      ((z - G.first.P i 2) / (G.first.Q i 2 - G.first.P i 2)) a) (expressionHeightBudget s 6) := by
    intro a
    have hValue := RationalInterpolationCode.output_height _ _ _ _ hs3
      ((hFirst.2 i a).1.mono hm) ((hFirst.2 i a).2.mono hm) hInv.1
    rw [expressionHeightBudget_comp] at hValue
    exact hValue
  have hY : ∀ a, RationalHeight (rationalSegmentPoint (G.second.P j) (G.second.Q j)
      ((z - (G.d - G.second.P j 0)) / ((G.d - G.second.Q j 0) - (G.d - G.second.P j 0))) a)
      (expressionHeightBudget s 6) := by
    intro a
    have hValue := RationalInterpolationCode.output_height _ _ _ _ hs3
      ((hSecond.2 j a).1.mono hm) ((hSecond.2 j a).2.mono hm) hInv.2
    rw [expressionHeightBudget_comp] at hValue
    exact hValue
  fin_cases r
  · exact hX 0
  · exact hX 1
  · exact hY 1
  · exact hY 2

theorem safe_endpoint_heights {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s)
    (hB : RationalHeight B s) (i : Fin k) (j : Fin h) (r : Fin 4) :
    RationalHeight (G.safeP B i j r) (expressionHeightBudget s 6) ∧
      RationalHeight (G.safeQ B i j r) (expressionHeightBudget s 6) := by
  have hInterval := interval_heights G s hFirst hSecond hD i j
  unfold safeP safeQ
  by_cases hw : 0 < G.weight i j
  · rw [ite_eq_left hw, ite_eq_left hw]
    exact ⟨curve_height G s hs hFirst hSecond hD i j _ hInterval.1 r,
      curve_height G s hs hFirst hSecond hD i j _ hInterval.2 r⟩
  · rw [ite_eq_right hw, ite_eq_right hw]
    have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 6) :=
      (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 6))
    fin_cases r
    · exact ⟨hB.mono (expressionHeightBudget_ge_input s 6), hB.mono (expressionHeightBudget_ge_input s 6)⟩
    · exact ⟨hZero, hZero⟩
    · exact ⟨hZero, hZero⟩
    · exact ⟨hZero, hZero⟩

theorem descriptor_height {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s)
    (hB : RationalHeight B s) : (G.descriptor B).HeightAt (expressionHeightBudget s 6) := by
  constructor
  · intro slot
    exact (weight_height G s hs hFirst hSecond hD _ _).mono (expressionHeightBudget_mono s (by decide : 4 ≤ 6))
  · intro slot r
    exact safe_endpoint_heights G B s hs hFirst hSecond hD hB _ _ r

end Blotto.RationalOverlapGluing
