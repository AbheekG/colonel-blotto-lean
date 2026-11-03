import Blotto.GeneralPaperSignedPairing

/-! Exact maximization of signed CDF pairings and codePayoff stability on the
full finite code alphabet. A maximizing multiplier is a single probability
mass at one signed threshold. Half ties, including at zero, are retained.
-/
namespace Blotto.GeneralPaperCodeCDFDistance
open scoped BigOperators Classical
open GeneralPaperCodeCDF GeneralPaperSignedPairing
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def extreme {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) : Fin n :=
  Classical.choose (Finset.exists_max_image Finset.univ (fun i => |delta i|) ⟨⟨0,hn⟩,Finset.mem_univ _⟩)

noncomputable def radius {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) : ℝ := |delta (extreme hn delta)|

theorem radius_nonnegative {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) : 0≤radius hn delta := abs_nonneg _

theorem abs_le_radius {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) (i : Fin n) : |delta i|≤radius hn delta :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (fun i => |delta i|)
    ⟨⟨0,hn⟩,Finset.mem_univ _⟩)).2 i (Finset.mem_univ _)

noncomputable def maximizingCode {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) : Fin (n+n) :=
  if 0≤delta (extreme hn delta) then Fin.castAdd n (extreme hn delta) else Fin.natAdd n (extreme hn delta)

noncomputable def maximizing {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) (s : Fin (n+n)) : ℝ :=
  if s=maximizingCode hn delta then 1 else 0

theorem maximizing_probability {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) : Probability (maximizing hn delta) := by
  constructor
  · intro s
    unfold maximizing
    split_ifs <;> norm_num
  · simp only [maximizing,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem maximizing_pair {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) : pair (maximizing hn delta) delta=radius hn delta := by
  unfold pair maximizing
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold maximizingCode radius
  split_ifs with hp
  · rw [signed_positive,abs_of_nonneg hp]
  · rw [signed_negative,abs_of_neg (lt_of_not_ge hp)]

theorem pair_le_radius {n : ℕ} (hn : 0<n) (delta : Fin n → ℝ) (lambda : Fin (n+n) → ℝ) (hl : Probability lambda) :
    pair lambda delta≤radius hn delta := by
  have hs (s : Fin (n+n)) : signed delta s≤radius hn delta := by
    have he := abs_le.mp (abs_le_radius hn delta (project s))
    unfold signed
    split_ifs <;> linarith only [he.1,he.2]
  calc
    _ ≤ ∑ s, lambda s*radius hn delta := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hs s) (hl.1 s))
    _ = _ := by rw [← Finset.sum_mul,hl.2,one_mul]

noncomputable def distance {n : ℕ} (hn : 0<n) (p q : Fin n → ℝ) : ℝ := radius hn (fun a => cdf p a-cdf q a)

theorem cdf_distance {n : ℕ} (hn : 0<n) (p q : Fin n → ℝ) (a : Fin n) :
    |cdf p a-cdf q a|≤distance hn p q := abs_le_radius hn (fun b => cdf p b-cdf q b) a

theorem prefix_distance {n : ℕ} (hn : 0<n) (p q : Fin n → ℝ) (cut : ℕ) (hc : cut≤n) :
    |prefixSum p cut-prefixSum q cut|≤distance hn p q := by
  by_cases hz : cut=0
  · subst cut
    rw [prefix_zero,prefix_zero,sub_self,abs_zero]
    exact radius_nonnegative hn _
  · have he := cdf_distance hn p q (⟨cut-1,by omega⟩:Fin n)
    have hs : cut-1+1=cut := by omega
    simpa only [cdf,hs] using he

theorem half_distance {n : ℕ} (hn : 0<n) (p q : Fin n → ℝ) (a : Fin n) :
    |half p a-half q a|≤distance hn p q := by
  have hp := abs_le.mp (prefix_distance hn p q a.val a.isLt.le)
  have hc := abs_le.mp (cdf_distance hn p q a)
  unfold half
  apply abs_le.mpr
  constructor <;> linarith only [hp.1,hp.2,hc.1,hc.2]

theorem weighted_abs {n : ℕ} (p f : Fin n → ℝ) (hp : Probability p) (bound : ℝ) (hf : ∀ i, |f i|≤bound) :
    |∑ i, p i*f i|≤bound := by
  calc
    _ ≤ ∑ i, |p i*f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i*bound := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (hp.1 i)]
      exact mul_le_mul_of_nonneg_left (hf i) (hp.1 i)
    _ = _ := by rw [← Finset.sum_mul,hp.2,one_mul]

theorem payoff_left {n : ℕ} (hn : 0<n) (p x q : Fin n → ℝ) (hq : Probability q) :
    |codePayoff p q-codePayoff x q|≤distance hn p x := by
  rw [payoff_response,payoff_response,← Finset.sum_sub_distrib]
  have he := weighted_abs q (fun a => half p a-half x a) hq (distance hn p x) (half_distance hn p x)
  simpa only [mul_sub] using he

theorem payoff_right {n : ℕ} (hn : 0<n) (p q y : Fin n → ℝ) (hp : Probability p) (hq : Probability q) (hy : Probability y) :
    |codePayoff p q-codePayoff p y|≤distance hn q y := by
  rw [payoff_defender p q hq.2,payoff_defender p y hy.2,← Finset.sum_sub_distrib]
  have he := weighted_abs p (fun a => half y a-half q a) hp (distance hn q y)
    (fun a => by rw [abs_sub_comm]; exact half_distance hn q y a)
  convert he using 1
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  ring

end Blotto.GeneralPaperCodeCDFDistance
