import Blotto.GeneralPaperProfitGridRoundExecution

/-! Search operands include raw leaf scaling and the final strict cut.
Native work counters have a depth-derived word. No uniform resource-tag
word is asserted by these integer profit-grid bounds. -/
namespace Blotto.GeneralPaperProfitGridRoundPrice
open GeneralPaperProfitGridPrepare GeneralPaperRankOperands
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem binary_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (depth V : ℕ) (hSize : n<2^depth) (op : ℕ → ℕ → ℕ) (a b : ℕ)
    (ha : a≤magnitude n depth V) (hb : b≤magnitude n depth V) (hc : op a b≤magnitude n depth V) :
    GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive (width depth V) :=
  (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b (magnitude n depth V) ha hb hc).trans
    (Nat.mul_le_mul_left 2 (hMono (word_bound n depth V hSize)))

def profile (primitive : ℕ → ℕ) (W depth V : ℕ) : ℕ := 4096*(depth+1)*(W+primitive (width depth V))

theorem merge_work {q w B : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W V : ℕ)
    (grid : Prepared q w B) (numerator : ℕ) (hCut : numerator+1≤V)
    (hValues : ∀ i,grid.numerators.read i≤V) :
    (GeneralPaperProfitGridRoundExecution.merge true primitive W grid numerator).2≤profile primitive W grid.depth V := by
  let found := GeneralPaperFloorSearchPrice.run true primitive W grid.depth grid.numerators grid.nonempty (numerator+1)
  have hN := basic grid.size grid.depth V
  have hw : found.1.work≤grid.depth*(12*grid.depth+34)+24 := by
    rw [GeneralPaperFloorSearchPrice.data true primitive W grid.depth grid.numerators grid.nonempty (numerator+1) grid.depthCap]
    exact GeneralPaperFloorSearch.lookup_work _ _ _ _
  have hMeta : found.1.work+8≤64*(grid.depth+1)^2 := by nlinarith only [hw,Nat.zero_le grid.depth]
  have a := binary_work primitive hMono grid.depth V grid.depthCap (fun a b => a+b) numerator 1
    (by omega) (by omega) (by omega)
  have b := binary_work primitive hMono grid.depth V grid.depthCap (fun a b => a+b) found.1.work 8
    (by omega) (by omega) (by omega)
  have h := GeneralPaperFloorSearchPrice.bit_work primitive hMono W grid.depth V grid.numerators grid.nonempty
    (numerator+1) grid.depthCap hCut hValues
  change found.2≤2048*(grid.depth+1)*(W+primitive (width grid.depth V)) at h
  change found.2+_+_+64*W≤4096*(grid.depth+1)*(W+primitive (width grid.depth V))
  nlinarith only [h,a,b,Nat.zero_le grid.depth]

theorem leaf_work {q w B : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W V : ℕ)
    (grid : Prepared q w B) (numerator : ℕ) (hNum : numerator≤V) (hDen : grid.profitDenominator≤V)
    (hCut : numerator*grid.profitDenominator+1≤V) (hValues : ∀ i,grid.leafNumerators.read i≤V) :
    (GeneralPaperProfitGridRoundExecution.leaf true primitive W grid numerator).2≤profile primitive W grid.depth V := by
  let found := GeneralPaperFloorSearchPrice.run true primitive W grid.depth grid.leafNumerators grid.nonempty
    (numerator*grid.profitDenominator+1)
  have hN := basic grid.size grid.depth V
  have hw : found.1.work≤grid.depth*(12*grid.depth+34)+24 := by
    rw [GeneralPaperFloorSearchPrice.data true primitive W grid.depth grid.leafNumerators grid.nonempty
      (numerator*grid.profitDenominator+1) grid.depthCap]
    exact GeneralPaperFloorSearch.lookup_work _ _ _ _
  have hMeta : found.1.work+16≤64*(grid.depth+1)^2 := by nlinarith only [hw,Nat.zero_le grid.depth]
  have a := binary_work primitive hMono grid.depth V grid.depthCap (fun a b => a*b) numerator grid.profitDenominator
    (by omega) (by omega) (by omega)
  have b := binary_work primitive hMono grid.depth V grid.depthCap (fun a b => a+b) (numerator*grid.profitDenominator) 1
    (by omega) (by omega) (by omega)
  have c := binary_work primitive hMono grid.depth V grid.depthCap (fun a b => a+b) found.1.work 16
    (by omega) (by omega) (by omega)
  have h := GeneralPaperFloorSearchPrice.bit_work primitive hMono W grid.depth V grid.leafNumerators grid.nonempty
    (numerator*grid.profitDenominator+1) grid.depthCap hCut hValues
  change found.2≤2048*(grid.depth+1)*(W+primitive (width grid.depth V)) at h
  change found.2+_+_+_+64*W≤4096*(grid.depth+1)*(W+primitive (width grid.depth V))
  nlinarith only [h,a,b,c,Nat.zero_le grid.depth]

end Blotto.GeneralPaperProfitGridRoundPrice
