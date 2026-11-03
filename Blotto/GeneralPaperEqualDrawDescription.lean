import Blotto.GeneralPaperEqualInitializedContract

/-! The paper description bound holds at the sampler's actual stored draw
reference, with the full Boolean representation included. This numerical
bound does not assert an allocation schedule across reference widths. -/
namespace Blotto.GeneralPaperEqualDrawDescription
open GeneralPaperEqualNativeRetainedStorage (short)
open GeneralPaperEqualBitDrawRates (address log)
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem profile_bound (A n k b : ℕ) :
    GeneralPaperEqualDrawAddressCapacity.profile A n k b ≤ GeneralPaperEqualDescriptionRates.bound A n k b := by
  let q := short n k
  let D := (n + 1) * q * (A + 1)
  have hq : 1 ≤ q := by dsimp [q, short]; omega
  have hk : k ≤ q := by dsimp [q, short]; omega
  have hNQ : n * q ≤ D := by
    dsimp [D]
    exact (Nat.mul_le_mul_right q (Nat.le_succ n)).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((n + 1) * q) (show 1 ≤ A + 1 by omega))
  have hQ : q ≤ D := by
    have h := Nat.le_mul_of_pos_left q (show 0 < n + 1 by omega)
    exact h.trans (by dsimp [D]; simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left ((n + 1) * q) (show 1 ≤ A + 1 by omega))
  have hQA : q * A ≤ D := by
    dsimp [D]
    calc
      _ ≤ ((n + 1) * q) * A := Nat.mul_le_mul_right A (Nat.le_mul_of_pos_left q (by omega))
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hNA : n * A ≤ D := by
    have hnq : n ≤ n * q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hq
    exact (Nat.mul_le_mul_right A hnq).trans (by
      dsimp [D]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right q (Nat.le_succ n)) (show A ≤ A + 1 by omega))
  have hA : A ≤ D := (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right A hq : A ≤ q * A).trans hQA
  have hN : n ≤ D := (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hq : n ≤ n * q).trans hNQ
  have hOne : 1 ≤ D := hq.trans hQ
  rw [GeneralPaperEqualDrawAddressCapacity.profile_eq]
  unfold GeneralPaperEqualDescriptionRates.bound
  dsimp only [D, q] at hNQ hQ hQA hNA hA hN hOne hk
  nlinarith only [hNQ, hQ, hQA, hNA, hA, hN, hOne, hk]

theorem bound_at_draw (n m k b : ℕ) (hm : m ≤ 3) :
    GeneralPaperEqualDescriptionRates.bound (address n m k b) n k b ≤
      GeneralPaperEqualDescriptionRates.paperBound n k b := by
  have hA := (GeneralPaperEqualBitDrawRates.metadata_bounds n m k b hm).1
  have hL : 1 ≤ log n k b := by unfold log; omega
  have hq : 1 ≤ short n k := by unfold short; omega
  have he : 1 ≤ (n + 1) * short n k := by nlinarith only [hq]
  have hLL : log n k b ≤ (n + 1) * short n k * log n k b := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (log n k b) he
  have hE : 1 ≤ (n + 1) * short n k * log n k b := hL.trans hLL
  have hA1 : address n m k b + 1 ≤ 3 * log n k b := by omega
  have hProduct := Nat.mul_le_mul_left (17179869184 * (n + 1) * short n k) hA1
  unfold GeneralPaperEqualDescriptionRates.bound GeneralPaperEqualDescriptionRates.paperBound
  nlinarith only [hProduct, hLL, hE]

theorem native_description {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    GeneralPaperEqualRetainedStorage.footprint sampler.address sampler ≤
      GeneralPaperEqualDescriptionRates.paperBound n k (rationalWordWidth budget) ∧
    GeneralPaperEqualRetainedStorage.footprint sampler.address sampler < 2 ^ sampler.address := by
  dsimp only
  have h := (GeneralPaperEqualNativeDrawRepresentation.native_bound bits model W k values v hv small budget).trans
    (profile_bound _ n k (rationalWordWidth budget))
  exact ⟨h.trans (bound_at_draw n _ k (rationalWordWidth budget)
    (GeneralPaperEqualNativeCache.group_count _ small)),
    GeneralPaperEqualNativeDrawRepresentation.native_capacity bits model W k values v hv small budget⟩

theorem initialized_description (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualResourceDomain.Problem model) :
    let sampler := (GeneralPaperEqualInitializedPreparation.run model A K p).1
    GeneralPaperEqualRetainedStorage.footprint sampler.address sampler ≤
      GeneralPaperEqualDescriptionRates.paperBound p.n p.k (rationalWordWidth p.budget) ∧
    GeneralPaperEqualRetainedStorage.footprint sampler.address sampler < 2 ^ sampler.address := by
  dsimp only
  rw [GeneralPaperEqualInitializedPreparation.data]
  exact native_description true model _ p.k p.values p.selector p.correct
    (GeneralPaperEqualResourceDomain.small_at_reference p _) p.budget

end Blotto.GeneralPaperEqualDrawDescription
