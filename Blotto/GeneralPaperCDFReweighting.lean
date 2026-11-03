import Blotto.GeneralPaperOrderedVariation

/-! Stability of a finite ordered CDF summary under a shared, possibly
adaptively chosen reweighting function. Its total mass difference vanishes.
The variation and lower-mass hypotheses are quantitative local interfaces to
the selected geometric levels, not assumptions about learner convergence.
-/
namespace Blotto.GeneralPaperCDFReweighting
open scoped BigOperators Classical
open GeneralPaperOrderedVariation
set_option autoImplicit false

def ProbabilityOn (mass : ℕ → ℝ) (last : ℕ) : Prop :=
  (∀ i≤last, 0≤mass i) ∧ prefixMass mass (last+1)=1

def CDFClose (p q : ℕ → ℝ) (last : ℕ) (nu : ℝ) : Prop :=
  ∀ count≤last+1, |prefixMass p count-prefixMass q count|≤nu

def weightedPrefix (p value : ℕ → ℝ) (count : ℕ) : ℝ :=
  prefixMass (fun i => value i*p i) count

noncomputable def reweightedCDF (p value : ℕ → ℝ) (last count : ℕ) : ℝ :=
  weightedPrefix p value count/weightedPrefix p value (last+1)

theorem close_nonnegative (p q : ℕ → ℝ) (last : ℕ) (nu : ℝ) (h : CDFClose p q last nu) : 0≤nu := by
  have he := h 0 (by omega)
  simpa [prefixMass] using he

theorem weighted_difference (p q value : ℕ → ℝ) (count : ℕ) :
    weightedPrefix p value count-weightedPrefix q value count=
      prefixMass (fun i => value i*(p i-q i)) count := by
  simp only [weightedPrefix,prefixMass,mul_sub,Finset.sum_sub_distrib]

theorem mass_difference_bound (p q value : ℕ → ℝ) (last : ℕ) (nu : ℝ)
    (hp : ProbabilityOn p last) (hq : ProbabilityOn q last) (hClose : CDFClose p q last nu) :
    |weightedPrefix p value (last+1)-weightedPrefix q value (last+1)|≤nu*variation value last := by
  rw [weighted_difference]
  apply full_pairing_bound
  · rw [prefix_sub,hp.2,hq.2,sub_self]
  · intro count hc
    rw [prefix_sub]
    exact hClose count hc

theorem prefix_difference_bound (p q value : ℕ → ℝ) (last count : ℕ) (nu cap : ℝ)
    (hCount : count≤last+1) (hClose : CDFClose p q last nu)
    (hCap : ∀ i≤last, |value i|≤cap) :
    |weightedPrefix p value count-weightedPrefix q value count|≤nu*(variation value last+cap) := by
  rw [weighted_difference]
  apply prefix_pairing_bound value _ last count nu cap hCount (close_nonnegative p q last nu hClose)
  · intro k hk
    rw [prefix_sub]
    exact hClose k hk
  · exact hCap

theorem weighted_mass_lower (p value : ℕ → ℝ) (last : ℕ) (lower : ℝ)
    (hp : ProbabilityOn p last) (hLower : ∀ i≤last, lower≤value i) :
    lower≤weightedPrefix p value (last+1) := by
  calc
    _ = ∑ i ∈ Finset.range (last+1), lower*p i := by
      rw [← Finset.mul_sum]
      change lower=lower*prefixMass p (last+1)
      rw [hp.2,mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hr : i≤last := by have := Finset.mem_range.mp hi; omega
      exact mul_le_mul_of_nonneg_right (hLower i hr) (hp.1 i hr)

theorem weighted_prefix_bounds (p value : ℕ → ℝ) (last count : ℕ)
    (hp : ProbabilityOn p last) (hValue : ∀ i≤last, 0≤value i) (hCount : count≤last+1) :
    0≤weightedPrefix p value count ∧ weightedPrefix p value count≤weightedPrefix p value (last+1) := by
  have hn : ∀ i<last+1, 0≤value i*p i := by
    intro i hi
    have hr : i≤last := by omega
    exact mul_nonneg (hValue i hr) (hp.1 i hr)
  exact ⟨prefix_nonnegative _ _ (fun i hi => hn i (by omega)),prefix_monotone _ _ _ hCount hn⟩

theorem normalized_difference (A B C D ep et : ℝ) (hB : 0<B) (hD : 0<D)
    (hC : 0≤C) (hCD : C≤D) (hPrefix : |A-C|≤ep) (hTotal : |B-D|≤et) :
    |A/B-C/D|≤(ep+et)/B := by
  have hp := abs_le.mp hPrefix
  have ht := abs_le.mp hTotal
  have het : 0≤et := (abs_nonneg _).trans hTotal
  have h1 := mul_le_mul_of_nonneg_left hp.2 hD.le
  have h2 := mul_le_mul_of_nonneg_left hp.1 hD.le
  have h3 := mul_le_mul_of_nonneg_left ht.2 hC
  have h4 := mul_le_mul_of_nonneg_left ht.1 hC
  have h5 := mul_le_mul_of_nonneg_right hCD het
  have hNum : |A*D-C*B|≤(ep+et)*D := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hEq : A/B-C/D=(A*D-C*B)/(B*D) := by field_simp
  rw [hEq,abs_div,abs_of_pos (mul_pos hB hD)]
  apply (div_le_iff₀ (mul_pos hB hD)).mpr
  calc
    _ ≤ (ep+et)*D := hNum
    _ = _ := by field_simp

theorem reweighted_close (p q value : ℕ → ℝ) (last : ℕ) (nu lower cap : ℝ)
    (hp : ProbabilityOn p last) (hq : ProbabilityOn q last) (hClose : CDFClose p q last nu)
    (hLower : 0<lower) (hValue : ∀ i≤last, lower≤value i ∧ |value i|≤cap)
    (count : ℕ) (hCount : count≤last+1) :
    |reweightedCDF p value last count-reweightedCDF q value last count|≤
      nu*(2*variation value last+cap)/lower := by
  have hNu := close_nonnegative p q last nu hClose
  have hP := weighted_mass_lower p value last lower hp (fun i hi => (hValue i hi).1)
  have hQ := weighted_mass_lower q value last lower hq (fun i hi => (hValue i hi).1)
  have hPre := prefix_difference_bound p q value last count nu cap hCount hClose (fun i hi => (hValue i hi).2)
  have hMass := mass_difference_bound p q value last nu hp hq hClose
  have hQPre := weighted_prefix_bounds q value last count hq
    (fun i hi => hLower.le.trans (hValue i hi).1) hCount
  have he := normalized_difference _ _ _ _ _ _ (hLower.trans_le hP) (hLower.trans_le hQ)
    hQPre.1 hQPre.2 hPre hMass
  have hCap : 0≤cap := (abs_nonneg (value 0)).trans (hValue 0 (by omega)).2
  have hTop : 0≤nu*(2*variation value last+cap) :=
    mul_nonneg hNu (by nlinarith [variation_nonnegative value last])
  have hDiv := div_le_div_of_nonneg_left hTop hLower hP
  dsimp only [reweightedCDF]
  calc
    _ ≤ (nu*(variation value last+cap)+nu*variation value last)/weightedPrefix p value (last+1) := he
    _ = (nu*(2*variation value last+cap))/weightedPrefix p value (last+1) := by congr 1; ring
    _ ≤ _ := hDiv

theorem epoch_reweighted_close (p q value : ℕ → ℝ) (last : ℕ) (nu : ℝ)
    (hp : ProbabilityOn p last) (hq : ProbabilityOn q last) (hClose : CDFClose p q last nu)
    (hValue : ∀ i≤last, 31/32≤value i ∧ value i≤1)
    (hVariation : variation value last≤1/32) (count : ℕ) (hCount : count≤last+1) :
    |reweightedCDF p value last count-reweightedCDF q value last count|≤34*nu/31 := by
  have hNu := close_nonnegative p q last nu hClose
  have he := reweighted_close p q value last nu (31/32) 1 hp hq hClose (by norm_num)
    (fun i hi => ⟨(hValue i hi).1,by rw [abs_of_nonneg (by linarith [(hValue i hi).1])]; exact (hValue i hi).2⟩)
    count hCount
  have hm := mul_le_mul_of_nonneg_left hVariation hNu
  nlinarith

end Blotto.GeneralPaperCDFReweighting
