import Blotto.GeneralPaperCatalogueGlobalRegret
import Blotto.GeneralPaperCodePayoff

/-! Exact finite code CDFs and the half-tie response codePayoff. Invalid codes
remain in the auxiliary alphabet. Prefix sums have a cut between codes;
closed CDFs use cut a+1, and strict CDFs use cut a. No full-budget assumption
or coupling of the auxiliary marginals is made.
-/
namespace Blotto.GeneralPaperCodeCDF
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

def prefixSum {n : ℕ} (p : Fin n → ℝ) (cut : ℕ) : ℝ := ∑ i, if i.val<cut then p i else 0

def cdf {n : ℕ} (p : Fin n → ℝ) (a : Fin n) : ℝ := prefixSum p (a.val+1)

noncomputable def half {n : ℕ} (p : Fin n → ℝ) (a : Fin n) : ℝ := (prefixSum p a.val+cdf p a)/2

noncomputable def kernel {n : ℕ} (a b : Fin n) : ℝ := GeneralPaperCodePayoff.codeShare b.val a.val

noncomputable def codePayoff {n : ℕ} (p q : Fin n → ℝ) : ℝ := ∑ a, ∑ b, p a*q b*kernel a b

def Probability {n : ℕ} (p : Fin n → ℝ) : Prop := (∀ i, 0≤p i) ∧ ∑ i, p i=1

theorem prefix_nat {n : ℕ} (hn : 0<n) (p : Fin n → ℝ) (cut : ℕ) (hc : cut≤n) :
    prefixSum p cut=GeneralPaperOrderedVariation.prefixMass (fun i => p (GeneralPaperGeometricVariation.code hn i)) cut := by
  unfold prefixSum GeneralPaperOrderedVariation.prefixMass
  have he : (∑ i ∈ Finset.range n, if i<cut then p (GeneralPaperGeometricVariation.code hn i) else 0)=
      ∑ i ∈ Finset.range cut, p (GeneralPaperGeometricVariation.code hn i) := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [← Fin.sum_univ_eq_sum_range] at he
  simpa only [GeneralPaperGeometricVariation.code_valid] using he

theorem prefix_zero {n : ℕ} (p : Fin n → ℝ) : prefixSum p 0=0 := by simp [prefixSum]

theorem prefix_total {n : ℕ} (p : Fin n → ℝ) : prefixSum p n=∑ i, p i := by
  simp only [prefixSum,Fin.isLt,ite_true]

theorem prefix_add {n : ℕ} (p q : Fin n → ℝ) (cut : ℕ) :
    prefixSum (fun i => p i+q i) cut=prefixSum p cut+prefixSum q cut := by
  unfold prefixSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

theorem prefix_sub {n : ℕ} (p q : Fin n → ℝ) (cut : ℕ) :
    prefixSum (fun i => p i-q i) cut=prefixSum p cut-prefixSum q cut := by
  unfold prefixSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

theorem kernel_half {n : ℕ} (a b : Fin n) :
    kernel a b=((if a.val<b.val then (1:ℝ) else 0)+(if a.val<b.val+1 then 1 else 0))/2 := by
  unfold kernel GeneralPaperCodePayoff.codeShare
  split_ifs <;> norm_num at * <;> omega

theorem kernel_complement {n : ℕ} (a b : Fin n) : kernel a b+kernel b a=1 := by
  rw [kernel_half,kernel_half]
  split_ifs <;> norm_num at * <;> omega

theorem half_kernel {n : ℕ} (p : Fin n → ℝ) (b : Fin n) :
    half p b=∑ a, p a*kernel a b := by
  unfold half cdf prefixSum
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [kernel_half]
  split_ifs <;> ring

theorem payoff_response {n : ℕ} (p q : Fin n → ℝ) : codePayoff p q=∑ b, q b*half p b := by
  unfold codePayoff
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [half_kernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem payoff_defender {n : ℕ} (p q : Fin n → ℝ) (hq : ∑ i, q i=1) :
    codePayoff p q=∑ a, p a*(1-half q a) := by
  unfold codePayoff
  apply Finset.sum_congr rfl
  intro a ha
  rw [half_kernel,← hq,mul_sub,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have he : kernel a b=1-kernel b a := by linarith only [kernel_complement a b]
  rw [he]
  ring

theorem half_sub {n : ℕ} (p q : Fin n → ℝ) (a : Fin n) :
    half (fun i => p i-q i) a=half p a-half q a := by
  unfold half cdf
  rw [prefix_sub,prefix_sub]
  ring

theorem payoff_sub_left {n : ℕ} (p x q : Fin n → ℝ) :
    codePayoff (fun i => p i-x i) q=codePayoff p q-codePayoff x q := by
  simp only [codePayoff,sub_mul,Finset.sum_sub_distrib]

theorem payoff_sub_right {n : ℕ} (p q y : Fin n → ℝ) :
    codePayoff p (fun i => q i-y i)=codePayoff p q-codePayoff p y := by
  simp only [codePayoff,mul_sub,sub_mul,Finset.sum_sub_distrib]

end Blotto.GeneralPaperCodeCDF
