import Blotto.GeneralPaperSourceParameters
import Mathlib.Algebra.BigOperators.Module

/-! Ordered finite code sums. `last` is the last code, so an alphabet has
last+1 codes and last adjacent edges. Prefixes contain exactly `count` codes.
The empty prefixMass and the last-code endpoint are included explicitly.
-/
namespace Blotto.GeneralPaperOrderedVariation
open scoped BigOperators Classical
set_option autoImplicit false

def prefixMass (mass : ℕ → ℝ) (count : ℕ) : ℝ := ∑ i ∈ Finset.range count, mass i

def variation (value : ℕ → ℝ) (edges : ℕ) : ℝ :=
  ∑ i ∈ Finset.range edges, |value (i+1)-value i|

theorem prefix_zero (mass : ℕ → ℝ) : prefixMass mass 0=0 := by simp [prefixMass]

theorem prefix_succ (mass : ℕ → ℝ) (count : ℕ) :
    prefixMass mass (count+1)=prefixMass mass count+mass count := by simp [prefixMass,Finset.sum_range_succ]

theorem prefix_sub (p q : ℕ → ℝ) (count : ℕ) :
    prefixMass (fun i => p i-q i) count=prefixMass p count-prefixMass q count := by
  simp [prefixMass,Finset.sum_sub_distrib]

theorem prefix_nonnegative (mass : ℕ → ℝ) (count : ℕ)
    (h : ∀ i<count, 0≤mass i) : 0≤prefixMass mass count :=
  Finset.sum_nonneg (fun i hi => h i (Finset.mem_range.mp hi))

theorem prefix_monotone (mass : ℕ → ℝ) (small large : ℕ) (hSize : small≤large)
    (h : ∀ i<large, 0≤mass i) : prefixMass mass small≤prefixMass mass large := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hSize)
  intro i hi _
  exact h i (Finset.mem_range.mp hi)

theorem variation_nonnegative (value : ℕ → ℝ) (edges : ℕ) : 0≤variation value edges :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem variation_monotone (value : ℕ → ℝ) (small large : ℕ) (h : small≤large) :
    variation value small≤variation value large := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro i _ _
  exact abs_nonneg _

theorem variation_add (f g : ℕ → ℝ) (edges : ℕ) :
    variation (fun i => f i+g i) edges≤variation f edges+variation g edges := by
  unfold variation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  convert abs_add_le (f (i+1)-f i) (g (i+1)-g i) using 1 <;> congr 1 <;> ring

theorem variation_scale_shift (f : ℕ → ℝ) (scale shift : ℝ) (edges : ℕ) :
    variation (fun i => scale*f i+shift) edges=|scale| * variation f edges := by
  unfold variation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : scale*f (i+1)+shift-(scale*f i+shift)=scale*(f (i+1)-f i) := by ring
  rw [he,abs_mul]

theorem variation_sum (f : ℕ → ℕ → ℝ) (count edges : ℕ) :
    variation (fun i => ∑ t ∈ Finset.range count, f t i) edges ≤
      ∑ t ∈ Finset.range count, variation (f t) edges := by
  induction count with
  | zero => simp [variation]
  | succ count ih =>
    simp only [Finset.sum_range_succ]
    exact (variation_add _ _ edges).trans (add_le_add ih (le_refl _))

theorem by_parts (value mass : ℕ → ℝ) (last : ℕ) :
    prefixMass (fun i => value i*mass i) (last+1)=value last*prefixMass mass (last+1)+
      ∑ i ∈ Finset.range last, (value i-value (i+1))*prefixMass mass (i+1) := by
  induction last with
  | zero => simp [prefixMass]
  | succ last ih =>
    rw [prefix_succ,ih,Finset.sum_range_succ,prefix_succ mass (last+1)]
    ring

theorem by_parts_zero_mass (value mass : ℕ → ℝ) (last : ℕ)
    (hMass : prefixMass mass (last+1)=0) :
    prefixMass (fun i => value i*mass i) (last+1)=
      ∑ i ∈ Finset.range last, (value i-value (i+1))*prefixMass mass (i+1) := by
  rw [by_parts,hMass,mul_zero,zero_add]

theorem edge_pairing_bound (value mass : ℕ → ℝ) (edges : ℕ) (nu : ℝ)
    (hPrefix : ∀ count≤edges, |prefixMass mass count|≤nu) :
    |∑ i ∈ Finset.range edges, (value i-value (i+1))*prefixMass mass (i+1)|≤nu*variation value edges := by
  calc
    _ ≤ ∑ i ∈ Finset.range edges, |(value i-value (i+1))*prefixMass mass (i+1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range edges, nu*|value (i+1)-value i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_sub_comm (value i)]
      have h := mul_le_mul_of_nonneg_left (hPrefix (i+1) (by have := Finset.mem_range.mp hi; omega))
        (abs_nonneg (value (i+1)-value i))
      nlinarith only [h]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem full_pairing_bound (value mass : ℕ → ℝ) (last : ℕ) (nu : ℝ)
    (hMass : prefixMass mass (last+1)=0)
    (hPrefix : ∀ count≤last+1, |prefixMass mass count|≤nu) :
    |prefixMass (fun i => value i*mass i) (last+1)|≤nu*variation value last := by
  rw [by_parts_zero_mass value mass last hMass]
  exact edge_pairing_bound value mass last nu (fun count hc => hPrefix count (by omega))

theorem prefix_pairing_bound (value mass : ℕ → ℝ) (last count : ℕ) (nu cap : ℝ)
    (hCount : count≤last+1) (hNu : 0≤nu)
    (hPrefix : ∀ k≤last+1, |prefixMass mass k|≤nu)
    (hCap : ∀ i≤last, |value i|≤cap) :
    |prefixMass (fun i => value i*mass i) count|≤nu*(variation value last+cap) := by
  cases count with
  | zero =>
    rw [prefix_zero,abs_zero]
    have hc : 0≤cap := (abs_nonneg (value 0)).trans (hCap 0 (by omega))
    exact mul_nonneg hNu (add_nonneg (variation_nonnegative _ _) hc)
  | succ count =>
    rw [by_parts]
    have he := edge_pairing_bound value mass count nu (fun k hk => hPrefix k (by omega))
    have ht : |value count*prefixMass mass (count+1)|≤cap*nu := by
      rw [abs_mul]
      exact mul_le_mul (hCap count (by omega)) (hPrefix (count+1) hCount)
        (abs_nonneg _) ((abs_nonneg _).trans (hCap count (by omega)))
    have hv := mul_le_mul_of_nonneg_left (variation_monotone value count last (by omega)) hNu
    exact (abs_add_le _ _).trans (by nlinarith only [he,ht,hv])

end Blotto.GeneralPaperOrderedVariation
