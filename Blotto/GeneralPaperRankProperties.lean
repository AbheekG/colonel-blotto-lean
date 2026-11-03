import Blotto.GeneralPaperRankSearch

/-! Uniqueness, endpoint and order properties of exact occurrence ranks.
They count occurrences rather than distinct location values.
-/
namespace Blotto.GeneralPaperRankProperties
open scoped Classical
open GeneralPaperRankSearch
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cut_order {n : ℕ} (values : FixedArrayTable n ℕ) (small large rSmall rLarge : ℕ)
    (hCuts : small≤large) (hSmall : ValidRank values small rSmall) (hLarge : ValidRank values large rLarge) :
    rSmall≤rLarge := by
  by_contra hn
  have hBound := hSmall.1
  have hR : rLarge<n := by omega
  let i : Fin n := ⟨rLarge,hR⟩
  have hi : values.read i<small := (hSmall.2 i).mpr (by dsimp only [i]; omega)
  have hh := (hLarge.2 i).mp (hi.trans_le hCuts)
  change rLarge<rLarge at hh
  omega

theorem unique {n : ℕ} (values : FixedArrayTable n ℕ) (cut left right : ℕ)
    (hLeft : ValidRank values cut left) (hRight : ValidRank values cut right) : left=right :=
  Nat.le_antisymm (cut_order values cut cut left right (le_refl _) hLeft hRight)
    (cut_order values cut cut right left (le_refl _) hRight hLeft)

theorem valid_zero {n : ℕ} (values : FixedArrayTable n ℕ) : ValidRank values 0 0 := by
  refine ⟨Nat.zero_le _,?_⟩
  intro i
  simp

theorem valid_full {n : ℕ} (values : FixedArrayTable n ℕ) (cut : ℕ) (hAll : ∀ i, values.read i<cut) :
    ValidRank values cut n := ⟨le_refl _,fun i => iff_of_true (hAll i) i.isLt⟩

theorem count_occurrences {n : ℕ} (values : FixedArrayTable n ℕ) (cut rank : ℕ)
    (hRank : ValidRank values cut rank) : (Finset.univ.filter (fun i => values.read i<cut)).card=rank := by
  have he : (Finset.univ.filter (fun i => values.read i<cut)).image Fin.val=Finset.range rank := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr ((hRank.2 i).mp (Finset.mem_filter.mp hi).2)
    · intro hx
      have hX := Finset.mem_range.mp hx
      let i : Fin n := ⟨x,hX.trans_le hRank.1⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hRank.2 i).mpr hX⟩,rfl⟩
  have hc := congrArg Finset.card he
  simpa only [Finset.card_image_of_injective _ Fin.val_injective,Finset.card_range] using hc

end Blotto.GeneralPaperRankProperties
