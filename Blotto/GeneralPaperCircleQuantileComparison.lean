import Blotto.GeneralPaperCyclicQuantileDeviation

/-! The paper's weighted light-field comparison is realized, up to V/R,
by fixed named cyclic deviations. No defender row is used to choose the
quantiles or a deviation. This is the pointwise payoff join; the full
canonical lifting-law/security and finite-shift joins remain separate. -/
namespace Blotto.GeneralPaperCircleQuantileComparison
open GeneralPaperCircleFiniteAverage GeneralPaperCircleCoordinatePayoff
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem scaled_share (R W w : ℕ) (hW : 0<W) (hw : 0<w) (y x : ℝ) :
    share y (coefficient R W w*x)=share (y/((w:ℝ)/W)) ((R:ℝ)*x) := by
  have hp : (0:ℝ)<(w:ℝ)/W := div_pos (by exact_mod_cast hw) (by exact_mod_cast hW)
  have h := share_scale hp (y/((w:ℝ)/W)) ((R:ℝ)*x)
  have he : ((w:ℝ)/W)*((R:ℝ)*x)=coefficient R W w*x := by unfold coefficient; push_cast; ring
  rw [mul_div_cancel₀ _ hp.ne',he] at h
  exact h

theorem comparison_as_weighted {g : ℕ} (R W Q : ℕ) (hW : 0<W) (hQ : 0<Q)
    (weights : Fin g → ℕ) (hp : ∀ j,0<weights j) (y : Fin g → ℝ) (x : Fin R → ℝ) :
    GeneralPaperCircleLightPayoff.comparison R W weights (fun j => (weights j:ℝ)/Q) y x=
      ((W:ℝ)/Q)*average (fun a:Fin R => ∑ j,((weights j:ℝ)/W)*
        share (GeneralPaperWeightedDeviationLaw.deviation W weights y j) ((R:ℝ)*x a)) := by
  have hw : (W:ℝ)≠0 := by exact_mod_cast hW.ne'
  have hq : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  unfold GeneralPaperCircleLightPayoff.comparison
  rw [average_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [scaled_share R W (weights j) hW (hp j)]
  rw [average_mul]
  have he : (weights j:ℝ)/Q=((W:ℝ)/Q)*((weights j:ℝ)/W) := by field_simp
  rw [he,mul_assoc]
  rfl

theorem average_interval {R : ℕ} (hR : 0<R) (F G : Fin R → ℝ) (δ : ℝ)
    (h : ∀ a,0≤F a-G a ∧ F a-G a≤δ) :
    0≤average F-average G ∧ average F-average G≤δ := by
  have hl := Finset.sum_nonneg (s:=Finset.univ) (fun a _ => (h a).1)
  have hu := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => (h a).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hu
  have he : average F-average G=(∑ a,(F a-G a))/(R:ℝ) := by
    unfold average
    rw [Finset.sum_sub_distrib,sub_div]
  rw [he]
  constructor
  · exact div_nonneg hl (Nat.cast_nonneg R)
  · apply (div_le_iff₀ (by exact_mod_cast hR : (0:ℝ)<R)).mpr
    nlinarith only [hu]

theorem cyclic_as_mean (R : ℕ) (hR : 0<R) (q x : Fin R → ℝ) (V : ℝ) :
    average (fun s:Fin R => ∑ a,(V/(R:ℝ))*share (GeneralPaperCyclicQuantileDeviation.representative R hR q s.val a) (x a))=
      V*average (fun a => average (fun l => share (q l) ((R:ℝ)*x a))) := by
  rw [GeneralPaperCyclicQuantileDeviation.payoff_average]
  unfold average
  ring

theorem representative_gap {g : ℕ} (R W Q : ℕ) (hR : 0<R) (hW : 0<W) (hQ : 0<Q)
    (weights : Fin g → ℕ) (hp : ∀ j,0<weights j) (hs : ∑ j,weights j=W)
    (y : Fin g → ℝ) (hy : ∀ j,0≤y j) (x : Fin R → ℝ) :
    let q := GeneralPaperWeightedLowerQuantile.quantiles R W hR hW weights hs y
    let C := average (fun s:Fin R => ∑ a,(((W:ℝ)/Q)/(R:ℝ))*
      share (GeneralPaperCyclicQuantileDeviation.representative R hR q s.val a) (x a))
    0≤GeneralPaperCircleLightPayoff.comparison R W weights (fun j => (weights j:ℝ)/Q) y x-C ∧
      GeneralPaperCircleLightPayoff.comparison R W weights (fun j => (weights j:ℝ)/Q) y x-C≤((W:ℝ)/Q)/R := by
  dsimp only
  rw [comparison_as_weighted R W Q hW hQ weights hp y x,cyclic_as_mean]
  have h := average_interval hR
    (fun a => ∑ j,((weights j:ℝ)/W)*share (GeneralPaperWeightedDeviationLaw.deviation W weights y j) ((R:ℝ)*x a))
    (fun a => average (fun l => share (GeneralPaperWeightedLowerQuantile.quantiles R W hR hW weights hs y l) ((R:ℝ)*x a)))
    (1/(R:ℝ)) (fun a => GeneralPaperWeightedLowerQuantile.attacker_error R W hR hW weights hs y hy ((R:ℝ)*x a))
  have hv : (0:ℝ)≤(W:ℝ)/Q := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hl := mul_nonneg hv h.1
  have hu := mul_le_mul_of_nonneg_left h.2 hv
  constructor
  · simpa only [mul_sub] using hl
  · simpa only [mul_sub,mul_one_div] using hu

theorem reconstruction_bound {g : ℕ} (R W Q : ℕ) (hR : 0<R) (hW : 0<W) (hQ : 0<Q)
    (weights : Fin g → ℕ) (hp : ∀ j,0<weights j) (hs : ∑ j,weights j=W)
    (y : Fin g → ℝ) (hy : ∀ j,0≤y j) (x : Fin R → ℝ) :
    let q := GeneralPaperWeightedLowerQuantile.quantiles R W hR hW weights hs y
    GeneralPaperCircleLightPayoff.reconstructed R W hR hW weights (fun j => (weights j:ℝ)/Q) y
        (GeneralPaperCircleSortedComparison.sorted x)≤
      average (fun s:Fin R => ∑ a,(((W:ℝ)/Q)/(R:ℝ))*
        share (GeneralPaperCyclicQuantileDeviation.representative R hR q s.val a) (x a))+
      GeneralPaperCircleLightPayoff.loss W weights (fun j => (weights j:ℝ)/Q)+((W:ℝ)/Q)/R := by
  have hArc := GeneralPaperCircleSortedComparison.error_sorted R W hR hW weights (fun j => (weights j:ℝ)/Q)
    (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) y x
  have hQuantile := representative_gap R W Q hR hW hQ weights hp hs y hy x
  dsimp only at hQuantile ⊢
  linarith only [hArc.2,hQuantile.2]

end Blotto.GeneralPaperCircleQuantileComparison
