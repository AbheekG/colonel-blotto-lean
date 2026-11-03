import Blotto.GeneralPaperPricedListStream

/-! The actual ordered-pair traversal, with both option constructions,
guarded crossing work, filterMap and output-segment append traffic priced.
-/
namespace Blotto.GeneralPaperCrossingPairsPrice
open GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 4000000

def pairRun {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (options : i → Option Affine × ℕ)
    (a b : i) : Option ℚ × ℕ :=
  let first := options a
  let second := options b
  let root := GeneralPaperAffineCrossingPrice.optionalRun primitive W first.1 second.1
  (root.1,first.2+second.2+root.2+16*W)

theorem pair_data {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (options : i → Option Affine × ℕ) (a b : i) :
    (pairRun primitive W options a b).1=GeneralPaperRayCrossingPairs.optional (options a).1 (options b).1 := by
  simp only [pairRun,GeneralPaperAffineCrossingPrice.optional_data]

def run {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (options : i → Option Affine × ℕ) (xs : List i) : List ℚ × ℕ :=
  GeneralPaperPricedListStream.flatMap W
    (fun a => GeneralPaperPricedListStream.filterMap W (pairRun primitive W options a) xs) xs

theorem data {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (options : i → Option Affine × ℕ) (xs : List i) :
    (run primitive W options xs).1=GeneralPaperRayCrossingPairs.pairs (fun a => (options a).1) xs := by
  simp only [run,GeneralPaperPricedListStream.flatMap_data,GeneralPaperPricedListStream.filterMap_data,
    pair_data,GeneralPaperRayCrossingPairs.pairs]

theorem length {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (options : i → Option Affine × ℕ) (xs : List i) :
    (run primitive W options xs).1.length≤xs.length*xs.length := by
  rw [data]
  exact GeneralPaperRayCrossingPairs.pairs_length _ _

def profile (n W P C : ℕ) : ℕ := n*n*(2*C+104*W+9*P)+(10*n+2)*W

theorem work {i : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D E A B R C : ℕ)
    (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R)
    (options : i → Option Affine × ℕ) (xs : List i)
    (hBound : ∀ a∈xs,∀ f,(options a).1=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (hWork : ∀ a∈xs,(options a).2≤C) :
    (run primitive W options xs).2≤profile xs.length W (primitive (1+2*R)) C := by
  let P := primitive (1+2*R)
  have hPair (a b : i) (ha : a∈xs) (hb : b∈xs) :
      (pairRun primitive W options a b).2≤2*C+88*W+9*P := by
    have hr := GeneralPaperAffineCrossingPrice.optional_work primitive hMono W D E A B R hD hE hR
      (options a).1 (options b).1 (hBound a ha) (hBound b hb)
    have hA := hWork a ha
    have hB := hWork b hb
    change (options a).2+(options b).2+
      (GeneralPaperAffineCrossingPrice.optionalRun primitive W (options a).1 (options b).1).2+16*W≤_
    omega
  have hRow (a : i) (ha : a∈xs) :
      (GeneralPaperPricedListStream.filterMap W (pairRun primitive W options a) xs).2≤
        (2*C+96*W+9*P)*xs.length+2*W := by
    have hh := GeneralPaperPricedListStream.filterMap_work W (2*C+88*W+9*P)
      (pairRun primitive W options a) xs (fun b hb => hPair a b ha hb)
    nlinarith only [hh]
  have hh := GeneralPaperPricedListStream.flatMap_work W xs.length
    ((2*C+96*W+9*P)*xs.length+2*W)
    (fun a => GeneralPaperPricedListStream.filterMap W (pairRun primitive W options a) xs) xs
    (fun a _ => GeneralPaperPricedListStream.filterMap_length W _ xs) hRow
  change (run primitive W options xs).2≤_ at hh
  unfold profile
  nlinarith only [hh]

end Blotto.GeneralPaperCrossingPairsPrice
