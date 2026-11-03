import Blotto.GeneralPaperQuantileWork

/-! Count target occurrences, not distinct returned locations. The largest
inside target and smallest outside target prove the CDF discrepancy bound;
the returned codes need not be monotone in target order.
-/
namespace Blotto.GeneralPaperQuantileOccurrenceCount
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem max_rank_card {s : ℕ} (A : Finset (Fin s)) (hA : A.Nonempty) :
    A.card≤(A.max' hA).val+1 := by
  have hSubset : A.image Fin.val⊆Finset.range ((A.max' hA).val+1) := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_range.mpr
    have he : r.val≤(A.max' hA).val := A.le_max' r hr
    omega
  have hc := Finset.card_le_card hSubset
  simpa only [Finset.card_image_of_injective A Fin.val_injective,Finset.card_range] using hc

theorem min_complement_rank {s : ℕ} (A : Finset (Fin s)) (hB : Aᶜ.Nonempty) :
    (Aᶜ.min' hB).val≤A.card := by
  have hSubset : Aᶜ.image Fin.val⊆Finset.Ico (Aᶜ.min' hB).val s := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ico.mpr ⟨show (Aᶜ.min' hB).val≤r.val from Aᶜ.min'_le r hr,r.isLt⟩
  have hc := Finset.card_le_card hSubset
  simp only [Finset.card_image_of_injective _ Fin.val_injective,Nat.card_Ico] at hc
  have hTotal := Finset.card_add_card_compl A
  simp only [Fintype.card_fin] at hTotal
  have hm := (Aᶜ.min' hB).isLt
  omega

theorem rank_discrepancy {s : ℕ} (hs : 0<s) (A : Finset (Fin s)) (F tolerance : ℚ)
    (hF0 : 0≤F) (hF1 : F≤1) (hTolerance : 0≤tolerance)
    (hInside : ∀ r∈A, ((r.val:ℚ)+1)/s≤F+tolerance)
    (hOutside : ∀ r∉A, F≤((r.val:ℚ)+1)/s+tolerance) :
    |(A.card:ℚ)/s-F|≤1/(s:ℚ)+tolerance := by
  have hsQ : (0:ℚ)<s := by exact_mod_cast hs
  have hUpper : (A.card:ℚ)/s≤F+tolerance := by
    by_cases hA : A.Nonempty
    · have hc : (A.card:ℚ)≤(A.max' hA).val+1 := by exact_mod_cast max_rank_card A hA
      exact (div_le_div_of_nonneg_right hc hsQ.le).trans (hInside _ (A.max'_mem hA))
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hA
      simp only [hz,Finset.card_empty,Nat.cast_zero,zero_div]
      exact add_nonneg hF0 hTolerance
  have hLower : F≤(A.card:ℚ)/s+(1/(s:ℚ)+tolerance) := by
    by_cases hB : Aᶜ.Nonempty
    · have hc : ((Aᶜ.min' hB).val:ℚ)+1≤(A.card:ℚ)+1 := by
        exact_mod_cast Nat.succ_le_succ (min_complement_rank A hB)
      calc
        F ≤ ((Aᶜ.min' hB).val+1)/s+tolerance := hOutside _ (Finset.mem_compl.mp (Aᶜ.min'_mem hB))
        _ ≤ ((A.card:ℚ)+1)/s+tolerance := by
          have hd := div_le_div_of_nonneg_right hc hsQ.le
          linarith
        _ = _ := by ring
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hB
      have hc := Finset.card_add_card_compl A
      simp only [hz,Finset.card_empty,Nat.add_zero,Fintype.card_fin] at hc
      rw [hc,div_self (ne_of_gt hsQ)]
      linarith [div_nonneg (by norm_num : (0:ℚ)≤1) hsQ.le]
  apply abs_le.mpr
  constructor
  · linarith
  · linarith [div_nonneg (by norm_num : (0:ℚ)≤1) hsQ.le]

def count {s : ℕ} (location : Fin s → ℕ) (cut : ℕ) : ℕ :=
  (Finset.univ.filter (fun r => location r<cut)).card

def summaryCDF {s : ℕ} (location : Fin s → ℕ) (cut : ℕ) : ℚ := (count location cut:ℚ)/s

theorem quantile_discrepancy {s U : ℕ} (hs : 0<s) (location : Fin s → ℕ)
    (F : ℕ → ℚ) (tolerance : ℚ) (hTolerance : 0≤tolerance)
    (hMono : Monotone F) (hZero : F 0=0) (hOne : F U=1)
    (hQuantile : ∀ r,
      F (location r)≤((r.val:ℚ)+1)/s+tolerance ∧
      ((r.val:ℚ)+1)/s-tolerance≤F (location r+1))
    (cut : ℕ) (hCut : cut≤U) :
    |summaryCDF location cut-F cut|≤1/(s:ℚ)+tolerance := by
  apply rank_discrepancy hs (Finset.univ.filter (fun r => location r<cut)) (F cut) tolerance
    (by simpa only [hZero] using hMono (Nat.zero_le cut))
    (by simpa only [hOne] using hMono hCut) hTolerance
  · intro r hr
    have he := hQuantile r
    have hc : location r+1≤cut := Nat.succ_le_of_lt (Finset.mem_filter.mp hr).2
    have hm := hMono hc
    linarith
  · intro r hr
    have hc : cut≤location r := by
      by_contra hn
      exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
    exact (hMono hc).trans (hQuantile r).1

end Blotto.GeneralPaperQuantileOccurrenceCount
