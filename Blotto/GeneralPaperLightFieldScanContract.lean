import Blotto.GeneralPaperLightFieldScanPrice

/-! The actual classifier return realizes the light/heavy partition of
the first rounded value vector. It derives the reduced count and retained
integer light mass; no comparison on long original rational encodings is
needed. Native reduced-array construction and circle lifting are later joins. -/
namespace Blotto.GeneralPaperLightFieldScanContract
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def multiplier (k : ℕ) : ℕ := 10*2^k

theorem threshold (w Q k : ℕ) (hQ : 0<Q) :
    (w:ℚ)/Q≤GeneralPaperLightFieldReduction.accuracy k/10 ↔ multiplier k*w≤Q := by
  have hp : (0:ℚ)<multiplier k := by unfold multiplier; positivity
  have hq : (0:ℚ)<Q := by exact_mod_cast hQ
  have he : GeneralPaperLightFieldReduction.accuracy k/10=(1:ℚ)/multiplier k := by
    unfold GeneralPaperLightFieldReduction.accuracy multiplier
    push_cast
    ring
  rw [he,div_le_div_iff₀ hq hp,one_mul]
  norm_cast
  rw [Nat.mul_comm]

theorem light_set {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1.light.toList.toFinset=
      GeneralPaperLightFieldReduction.light (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k := by
  ext j
  simp only [List.mem_toFinset,Array.mem_toList_iff,GeneralPaperLightFieldScan.light_mem,j.isLt,true_and,
    GeneralPaperLightFieldReduction.light_mem,GeneralPaperNativeRationalValues.selector]
  exact (threshold (weights.read j) Q k hQ).symm

theorem heavy_set {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1.heavy.toList.toFinset=
      GeneralPaperLightFieldReduction.heavy (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k := by
  ext j
  simp only [List.mem_toFinset,Array.mem_toList_iff,GeneralPaperLightFieldScan.heavy_mem,j.isLt,true_and,
    GeneralPaperLightFieldReduction.heavy_mem,GeneralPaperNativeRationalValues.selector]
  have h := not_congr (threshold (weights.read j) Q k hQ)
  simpa only [not_le] using h.symm

theorem light_size {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1.light.size=
      (GeneralPaperLightFieldReduction.light (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k).card := by
  have h := List.toFinset_card_of_nodup (GeneralPaperLightFieldScan.light_nodup bits model W (multiplier k) Q weights n le_rfl)
  rw [light_set bits model W Q k hQ weights hp hs] at h
  simpa only [Array.length_toList] using h.symm

theorem heavy_size {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1.heavy.size=
      (GeneralPaperLightFieldReduction.heavy (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k).card := by
  have h := List.toFinset_card_of_nodup (GeneralPaperLightFieldScan.heavy_nodup bits model W (multiplier k) Q weights n le_rfl)
  rw [heavy_set bits model W Q k hQ weights hp hs] at h
  simpa only [Array.length_toList] using h.symm

theorem light_total {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1.lightWeight=
      ∑ j∈GeneralPaperLightFieldReduction.light (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k,weights.read j := by
  rw [GeneralPaperLightFieldScan.light_weight]
  unfold GeneralPaperLightFieldReduction.light
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  change (if multiplier k*weights.read j≤Q then weights.read j else 0)=
    (if (weights.read j:ℚ)/Q≤GeneralPaperLightFieldReduction.accuracy k/10 then weights.read j else 0)
  by_cases h : multiplier k*weights.read j≤Q
  · rw [ite_eq_left h,ite_eq_left ((threshold (weights.read j) Q k hQ).mpr h)]
  · rw [ite_eq_right h,ite_eq_right (fun hc => h ((threshold (weights.read j) Q k hQ).mp hc))]

theorem light_mass {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    ((GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1.lightWeight:ℚ)/Q=
      GeneralPaperLightFieldReduction.mass (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k := by
  rw [light_total bits model W Q k hQ weights hp hs]
  simp only [Nat.cast_sum,Finset.sum_div,GeneralPaperLightFieldReduction.mass,GeneralPaperNativeRationalValues.selector]

theorem reduced_count {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    let state := (GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1
    state.heavy.size+min state.light.size (GeneralPaperLightFieldReduction.representatives k)=
      GeneralPaperLightFieldReduction.count (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k := by
  dsimp only
  rw [heavy_size bits model W Q k hQ weights hp hs,light_size bits model W Q k hQ weights hp hs]
  rfl

theorem reduced_count_bounds {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q k : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    let state := (GeneralPaperLightFieldScan.scan bits model W (multiplier k) Q weights n le_rfl).1
    let m := state.heavy.size+min state.light.size (GeneralPaperLightFieldReduction.representatives k)
    0<m ∧ m≤n ∧ m<18*2^k := by
  dsimp only
  rw [reduced_count bits model W Q k hQ weights hp hs]
  exact ⟨GeneralPaperLightFieldReduction.count_positive _ _,GeneralPaperLightFieldReduction.count_le_original _ _,
    GeneralPaperLightFieldReduction.count_bound _ _⟩

end Blotto.GeneralPaperLightFieldScanContract
