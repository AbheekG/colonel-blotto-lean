import Blotto.GeneralPaperLossVariation

/-! Epoch summaries are lists of occurrences, with all duplicates retained.
These identities connect the stored per-occurrence weights to the finite
code-mass CDF semantics used by the reweighting argument. They do not replace
the still-required interval-tree quantile-search procedure.
-/
namespace Blotto.GeneralPaperSummaryOccurrences
open scoped BigOperators Classical
open GeneralPaperOrderedVariation GeneralPaperCDFReweighting
set_option autoImplicit false

noncomputable def mass {s : ℕ} (location : Fin s → ℕ) (weight : Fin s → ℝ) (code : ℕ) : ℝ :=
  ∑ r, if location r=code then weight r else 0

noncomputable def uniform {s : ℕ} (location : Fin s → ℕ) : ℕ → ℝ := mass location (fun _ => 1/(s:ℝ))

noncomputable def occurrencePrefix {s : ℕ} (location : Fin s → ℕ) (weight : Fin s → ℝ) (count : ℕ) : ℝ :=
  ∑ r, if location r<count then weight r else 0

theorem singleton_prefix (location count : ℕ) (weight : ℝ) :
    (∑ i ∈ Finset.range count, if location=i then weight else 0)=if location<count then weight else 0 := by
  by_cases h : location<count
  · rw [if_pos h]
    calc
      _ = (if location=location then weight else 0) := Finset.sum_eq_single location
        (fun i _ hi => by simp [Ne.symm hi])
        (fun hn => False.elim (hn (Finset.mem_range.mpr h)))
      _ = weight := by simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    have hh : location≠i := by intro he; subst i; exact h (Finset.mem_range.mp hi)
    simp [hh]

theorem prefix_identity {s : ℕ} (location : Fin s → ℕ) (weight : Fin s → ℝ) (count : ℕ) :
    prefixMass (mass location weight) count=occurrencePrefix location weight count := by
  unfold prefixMass mass occurrencePrefix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  exact singleton_prefix (location r) count (weight r)

theorem total_mass {s : ℕ} (location : Fin s → ℕ) (weight : Fin s → ℝ) (last : ℕ)
    (hLocation : ∀ r, location r≤last) : prefixMass (mass location weight) (last+1)=∑ r, weight r := by
  rw [prefix_identity]
  unfold occurrencePrefix
  apply Finset.sum_congr rfl
  intro r _
  exact if_pos (by have := hLocation r; omega)

theorem mass_nonnegative {s : ℕ} (location : Fin s → ℕ) (weight : Fin s → ℝ)
    (hWeight : ∀ r, 0≤weight r) (i : ℕ) : 0≤mass location weight i := by
  apply Finset.sum_nonneg
  intro r _
  split
  · exact hWeight r
  · exact le_refl 0

theorem uniform_probability {s : ℕ} (hs : 0<s) (location : Fin s → ℕ) (last : ℕ)
    (hLocation : ∀ r, location r≤last) : ProbabilityOn (uniform location) last := by
  constructor
  · intro i _
    exact mass_nonnegative location (fun _ => 1/(s:ℝ)) (fun _ => by positivity) i
  · unfold uniform
    rw [total_mass location _ last hLocation]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hz : (s:ℝ)≠0 := by exact_mod_cast ne_of_gt hs
    field_simp

theorem weighted_mass_identity {s : ℕ} (location : Fin s → ℕ) (weight : Fin s → ℝ) (value : ℕ → ℝ) :
    (fun i => value i*mass location weight i)=mass location (fun r => value (location r)*weight r) := by
  funext i
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs with h
  · simp only [h]
  · simp

theorem weighted_prefix_identity {s : ℕ} (location : Fin s → ℕ) (weight : Fin s → ℝ)
    (value : ℕ → ℝ) (count : ℕ) :
    weightedPrefix (mass location weight) value count=
      occurrencePrefix location (fun r => value (location r)*weight r) count := by
  unfold weightedPrefix
  rw [weighted_mass_identity,prefix_identity]

theorem uniform_reweighted_cdf {s : ℕ} (location : Fin s → ℕ) (last count : ℕ) (value : ℕ → ℝ)
    (hLocation : ∀ r, location r≤last) :
    reweightedCDF (uniform location) value last count=
      occurrencePrefix location (fun r => value (location r)) count/(∑ r, value (location r)) := by
  have hNumerator : occurrencePrefix location (fun r => value (location r)*(1/(s:ℝ))) count=
      occurrencePrefix location (fun r => value (location r)) count*(1/(s:ℝ)) := by
    unfold occurrencePrefix
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    split <;> simp
  have hDenominator : weightedPrefix (uniform location) value (last+1)=
      (∑ r, value (location r))*(1/(s:ℝ)) := by
    unfold uniform weightedPrefix
    rw [weighted_mass_identity,total_mass location _ last hLocation,Finset.sum_mul]
  unfold reweightedCDF uniform
  rw [weighted_prefix_identity,hNumerator]
  change _/(weightedPrefix (uniform location) value (last+1))=_
  rw [hDenominator]
  by_cases hs : s=0
  · subst s
    simp [occurrencePrefix]
  · have hz : (1/(s:ℝ))≠0 := one_div_ne_zero (by exact_mod_cast hs)
    exact mul_div_mul_right _ _ hz

theorem fresh_power_cdf_error {s : ℕ} (location : Fin s → ℕ) (last : ℕ)
    (hLocation : ∀ r, location r≤last) (exactPower roundedPower : Fin s → ℝ) (error : ℝ)
    (hExact : ∀ r, 1/2≤exactPower r)
    (hRounded : ∀ r, 0≤roundedPower r)
    (hError : ∀ r, |exactPower r-roundedPower r|≤error) (hs : 0<s)
    (count : ℕ) :
    |occurrencePrefix location exactPower count/(∑ r, exactPower r)-
      occurrencePrefix location roundedPower count/(∑ r, roundedPower r)|≤4*error := by
  have hsR : (0:ℝ)<s := by exact_mod_cast hs
  have hExactSum : (s:ℝ)/2≤∑ r, exactPower r := by
    calc
      _ = ∑ _r : Fin s, (1/2:ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun r _ => hExact r)
  have hTotal : |(∑ r, exactPower r)-(∑ r, roundedPower r)|≤(s:ℝ)*error := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ r, |exactPower r-roundedPower r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin s, error := Finset.sum_le_sum (fun r _ => hError r)
      _ = _ := by simp
  have hPrefix : |occurrencePrefix location exactPower count-occurrencePrefix location roundedPower count|≤(s:ℝ)*error := by
    unfold occurrencePrefix
    rw [← Finset.sum_sub_distrib]
    have hE : 0≤error := (abs_nonneg _).trans (hError ⟨0,hs⟩)
    calc
      _ ≤ ∑ r, |(if location r<count then exactPower r else 0)-(if location r<count then roundedPower r else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin s, error := by
        apply Finset.sum_le_sum
        intro r _
        split <;> simp_all
      _ = _ := by simp
  have hC : 0≤occurrencePrefix location roundedPower count := by
    apply Finset.sum_nonneg
    intro r _
    split
    · exact hRounded r
    · exact le_refl 0
  have hCD : occurrencePrefix location roundedPower count≤∑ r, roundedPower r := by
    apply Finset.sum_le_sum
    intro r _
    split <;> simp_all
  by_cases hZero : (∑ r, roundedPower r)=0
  · rw [hZero,div_zero,sub_zero]
    have he : (s:ℝ)/2≤(s:ℝ)*error := by
      have h := (abs_le.mp hTotal).2
      rw [hZero,sub_zero] at h
      linarith
    have hErr : 1≤4*error := by nlinarith
    have hPre : 0≤occurrencePrefix location exactPower count ∧ occurrencePrefix location exactPower count≤∑ r, exactPower r := by
      constructor
      · apply Finset.sum_nonneg
        intro r _
        split <;> linarith [hExact r]
      · apply Finset.sum_le_sum
        intro r _
        split <;> linarith [hExact r]
    rw [abs_of_nonneg (div_nonneg hPre.1 (by linarith))]
    exact ((div_le_one (by linarith : (0:ℝ)<∑ r, exactPower r)).mpr hPre.2).trans hErr
  · have hD : 0<∑ r, roundedPower r := lt_of_le_of_ne (Finset.sum_nonneg (fun r _ => hRounded r)) (Ne.symm hZero)
    have he := normalized_difference _ _ _ _ _ _ (by linarith) hD hC hCD hPrefix hTotal
    have hErr : 0≤error := (abs_nonneg _).trans (hError ⟨0,hs⟩)
    have hDiv := div_le_div_of_nonneg_left (show 0≤(s:ℝ)*error+(s:ℝ)*error by positivity)
      (by linarith : (0:ℝ)<(s:ℝ)/2) hExactSum
    calc
      _ ≤ ((s:ℝ)*error+(s:ℝ)*error)/(∑ r, exactPower r) := he
      _ ≤ ((s:ℝ)*error+(s:ℝ)*error)/((s:ℝ)/2) := hDiv
      _ = _ := by field_simp; ring

end Blotto.GeneralPaperSummaryOccurrences
