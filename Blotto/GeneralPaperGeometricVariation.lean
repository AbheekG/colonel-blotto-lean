import Blotto.GeneralPaperCDFReweighting

/-! Geometric integer powers contract ordered variation. These are bounds
on the selected natural exponents, rather than an assumed smoothness bound
on exponentials or a different multiplicative-weights update.
-/
namespace Blotto.GeneralPaperGeometricVariation
open scoped BigOperators Classical
open GeneralPaperOrderedVariation GeneralPaperGeometricLevels
set_option autoImplicit false

theorem power_step (base : ℝ) (hBase : 0≤base) (hOne : base≤1) (n : ℕ) :
    |base^(n+1)-base^n|≤1-base := by
  have hn := pow_nonneg hBase n
  have hu : base^n≤1 := pow_le_one₀ hBase hOne
  rw [pow_succ,abs_of_nonpos (by nlinarith)]
  nlinarith [mul_nonneg (by linarith : 0≤1-base) (by linarith : 0≤1-base^n)]

theorem power_gap (base : ℝ) (hBase : 0≤base) (hOne : base≤1) (start gap : ℕ) :
    |base^(start+gap)-base^start|≤(1-base)*gap := by
  induction gap with
  | zero => simp
  | succ gap ih =>
    have hs := power_step base hBase hOne (start+gap)
    have ha := abs_add_le (base^(start+gap+1)-base^(start+gap)) (base^(start+gap)-base^start)
    have he : base^(start+gap+1)-base^(start+gap)+(base^(start+gap)-base^start)=base^(start+gap+1)-base^start := by ring
    rw [he] at ha
    change |base^(start+gap+1)-base^start|≤(1-base)*(gap+1:ℕ)
    push_cast
    nlinarith only [ha,hs,ih]

theorem power_lipschitz (base : ℝ) (hBase : 0≤base) (hOne : base≤1) (a b : ℕ) :
    |base^a-base^b|≤(1-base)*|(a:ℝ)-(b:ℝ)| := by
  rcases le_total a b with hab|hba
  · obtain ⟨gap,rfl⟩ := Nat.exists_eq_add_of_le hab
    have he := power_gap base hBase hOne a gap
    rw [abs_sub_comm (base^a)]
    convert he using 1
    push_cast
    have hg : (0:ℝ)≤gap := Nat.cast_nonneg _
    rw [abs_of_nonpos (by linarith : (a:ℝ)-((a:ℝ)+gap)≤0)]
    ring
  · obtain ⟨gap,rfl⟩ := Nat.exists_eq_add_of_le hba
    have he := power_gap base hBase hOne b gap
    convert he using 1
    push_cast
    have hg : (0:ℝ)≤gap := Nat.cast_nonneg _
    rw [abs_of_nonneg (by linarith : (0:ℝ)≤(b:ℝ)+gap-b)]
    ring

theorem power_lower (base : ℝ) (hBase : 0≤base) (hOne : base≤1) (n : ℕ) :
    1-(1-base)*n≤base^n := by
  have he := power_gap base hBase hOne 0 n
  simp only [zero_add,pow_zero] at he
  have ha := abs_le.mp he
  linarith

theorem power_variation (base : ℝ) (hBase : 0≤base) (hOne : base≤1) (level : ℕ → ℕ) (edges : ℕ) :
    variation (fun i => base^level i) edges≤(1-base)*variation (fun i => (level i:ℝ)) edges := by
  unfold variation
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => power_lipschitz base hBase hOne (level (i+1)) (level i))

def code {n : ℕ} (hn : 0<n) (i : ℕ) : Fin n := ⟨min i (n-1),by omega⟩

theorem code_valid {n : ℕ} (hn : 0<n) (i : Fin n) : code hn i.val=i := by
  apply Fin.ext
  dsimp [code]
  omega

theorem level_scaled_bound {n : ℕ} (hn : 0<n) (increment : ℕ → Fin n → ℕ) (theta : ℚ)
    (hTheta : 0<theta)
    (hLoss : ∀ t i, |(executedLoss theta (increment t i):ℝ)|≤2) (count : ℕ) (i : Fin n) :
    (theta:ℝ)*(levels increment count i)≤8*count := by
  have ht : (0:ℝ)<theta := by exact_mod_cast hTheta
  have hd : ∀ t i, (theta:ℝ)*(increment t i)≤8 := by
    intro t i
    have he := (abs_le.mp (hLoss t i)).2
    dsimp only [executedLoss] at he
    push_cast at he
    nlinarith
  induction count with
  | zero => simp [levels]
  | succ count ih =>
    simp only [levels,Nat.cast_add,Nat.cast_one]
    nlinarith [hd count i]

theorem level_variation_scaled {n : ℕ} (hn : 0<n) (increment : ℕ → Fin n → ℕ) (theta : ℚ)
    (hTheta : 0<theta)
    (hLoss : ∀ t, variation (fun i => (executedLoss theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (count : ℕ) :
    (theta:ℝ)*variation (fun i => (levels increment count (code hn i):ℝ)) (n-1)≤8*count := by
  have ht : (0:ℝ)<theta := by exact_mod_cast hTheta
  have hd : ∀ t, (theta:ℝ)*variation (fun i => (increment t (code hn i):ℝ)) (n-1)≤8 := by
    intro t
    have he := hLoss t
    have hv := variation_scale_shift (fun i => (increment t (code hn i):ℝ)) ((theta:ℝ)/2) (-2) (n-1)
    have hf : (fun i => (executedLoss theta (increment t (code hn i)):ℝ))=
        (fun i => (theta:ℝ)/2*(increment t (code hn i):ℝ)+(-2)) := by
      funext i
      simp only [executedLoss,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast]
      ring
    rw [hf,hv,abs_of_pos (by positivity : (0:ℝ)<(theta:ℝ)/2)] at he
    nlinarith
  induction count with
  | zero => simp [levels,variation]
  | succ count ih =>
    have ha := variation_add (fun i => (levels increment count (code hn i):ℝ))
      (fun i => (increment count (code hn i):ℝ)) (n-1)
    have hm := mul_le_mul_of_nonneg_left ha ht.le
    simp only [levels,Nat.cast_add,Nat.cast_one]
    nlinarith [hd count]

theorem geometric_bounds {n : ℕ} (hn : 0<n) (increment : ℕ → Fin n → ℕ) (eta theta : ℚ)
    (hEta : 0<eta) (hTheta : 0<theta) (hProduct : eta*theta≤1)
    (hLoss : ∀ t i, |(executedLoss theta (increment t i):ℝ)|≤2) (count : ℕ) (i : Fin n) :
    1-4*(eta:ℝ)*count≤(geometricBase eta theta:ℝ)^levels increment count i ∧
      (geometricBase eta theta:ℝ)^levels increment count i≤1 := by
  have hb := base_bounds eta theta hEta hTheta hProduct
  have hb0 : (0:ℝ)≤geometricBase eta theta := by
    have h : (0:ℚ)≤geometricBase eta theta := by linarith [hb.1]
    exact_mod_cast h
  have hb1 : (geometricBase eta theta:ℝ)≤1 := by exact_mod_cast hb.2.le
  have he := power_lower _ hb0 hb1 (levels increment count i)
  have hl := level_scaled_bound hn increment theta hTheta hLoss count i
  have heta : (0:ℝ)≤eta := by exact_mod_cast hEta.le
  have hm := mul_le_mul_of_nonneg_left hl (show (0:ℝ)≤(eta:ℝ)/2 by positivity)
  have heq : 1-(geometricBase eta theta:ℝ)=(eta:ℝ)*(theta:ℝ)/2 := by simp [geometricBase]
  rw [heq] at he
  exact ⟨by nlinarith, pow_le_one₀ hb0 hb1⟩

theorem geometric_variation {n : ℕ} (hn : 0<n) (increment : ℕ → Fin n → ℕ) (eta theta : ℚ)
    (hEta : 0<eta) (hTheta : 0<theta) (hProduct : eta*theta≤1)
    (hLoss : ∀ t, variation (fun i => (executedLoss theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (count : ℕ) :
    variation (fun i => (geometricBase eta theta:ℝ)^levels increment count (code hn i)) (n-1)≤4*(eta:ℝ)*count := by
  have hb := base_bounds eta theta hEta hTheta hProduct
  have hb0 : (0:ℝ)≤geometricBase eta theta := by
    have h : (0:ℚ)≤geometricBase eta theta := by linarith [hb.1]
    exact_mod_cast h
  have hb1 : (geometricBase eta theta:ℝ)≤1 := by exact_mod_cast hb.2.le
  have he := power_variation _ hb0 hb1 (fun i => levels increment count (code hn i)) (n-1)
  have hl := level_variation_scaled hn increment theta hTheta hLoss count
  have heta : (0:ℝ)≤eta := by exact_mod_cast hEta.le
  have hm := mul_le_mul_of_nonneg_left hl (show (0:ℝ)≤(eta:ℝ)/2 by positivity)
  have heq : 1-(geometricBase eta theta:ℝ)=(eta:ℝ)*(theta:ℝ)/2 := by simp [geometricBase]
  rw [heq] at he
  nlinarith

end Blotto.GeneralPaperGeometricVariation
