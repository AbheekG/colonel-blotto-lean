import Blotto.FairBitBlocks
import Mathlib.MeasureTheory.Measure.Prod

/-! The complete joint law of consecutive finite fresh-bit blocks is the
product measure. Arbitrary measurable output spaces are permitted, so this
also proves independence of whole allocation vectors, not just coordinates. -/
namespace Blotto
open MeasureTheory

def fairBitSplitEquiv (R S : ℕ) : (Fin (R+S) → Bool) ≃ ((Fin R → Bool) × (Fin S → Bool)) :=
  (bitBlockEquiv R S).symm.trans (Equiv.prodComm _ _)

theorem fairBitBlocks_product (R S : ℕ) :
    Measure.map (fun bits => (firstBitBlock R S bits,secondBitBlock R S bits))
      (fairBitLaw (R+S) : Measure (Fin (R+S) → Bool)) =
        (fairBitLaw R : Measure (Fin R → Bool)).prod (fairBitLaw S : Measure (Fin S → Bool)) := by
  change Measure.map (fairBitSplitEquiv R S) _ = _
  apply Measure.ext_of_singleton
  intro pair
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hPre : (fairBitSplitEquiv R S) ⁻¹' {pair} = {(fairBitSplitEquiv R S).symm pair} := by
    ext bits
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    exact (Equiv.eq_symm_apply (fairBitSplitEquiv R S)).symm
  rw [hPre]
  rw [← Set.singleton_prod_singleton,Measure.prod_prod]
  simp only [fairBitLaw_singleton,pow_add]

theorem fairBitBlocks_map_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (R S : ℕ) (f : (Fin R → Bool) → α) (g : (Fin S → Bool) → β) :
    Measure.map (fun bits => (f (firstBitBlock R S bits),g (secondBitBlock R S bits)))
      (fairBitLaw (R+S) : Measure (Fin (R+S) → Bool)) =
        (Measure.map f (fairBitLaw R : Measure (Fin R → Bool))).prod
          (Measure.map g (fairBitLaw S : Measure (Fin S → Bool))) := by
  rw [Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)]
  rw [← fairBitBlocks_product R S,Measure.map_map
    ((measurable_of_countable f).prodMap (measurable_of_countable g)) (measurable_of_countable _)]
  rfl

end Blotto
