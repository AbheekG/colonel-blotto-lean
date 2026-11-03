import Blotto.GeneralPaperCrossingPairsPrice

/-! Per-score crossing batches with exact native list order and all option,
pair, append and score/label-iterator construction costs included.
-/
namespace Blotto.GeneralPaperCrossingBatchPrice
open GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ)
    (options : Fin (S+1) → Fin K → Option Affine × ℕ) : List ℚ × ℕ :=
  let result := GeneralPaperPricedListStream.flatMap W (fun s =>
    let current := GeneralPaperCrossingPairsPrice.run primitive W (options s) (List.finRange K)
    (current.1,current.2+16*(K+1)*W)) (List.finRange (S+1))
  (result.1,result.2+16*(S+2)*W)

theorem data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ)
    (options : Fin (S+1) → Fin K → Option Affine × ℕ) :
    (run primitive W options).1=GeneralPaperRayCrossingPairs.batch (fun s l => (options s l).1) := by
  simp only [run,GeneralPaperPricedListStream.flatMap_data,GeneralPaperCrossingPairsPrice.data,
    GeneralPaperRayCrossingPairs.batch]

theorem length {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ)
    (options : Fin (S+1) → Fin K → Option Affine × ℕ) :
    (run primitive W options).1.length≤(S+1)*(K*K) := by
  rw [data]
  exact GeneralPaperRayCrossingPairs.batch_length _

def profile (S K W P C : ℕ) : ℕ :=
  (S+1)*(GeneralPaperCrossingPairsPrice.profile K W P C+(8*K*K+16*K+24)*W)+(16*(S+2)+2)*W

theorem work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D E A B R C : ℕ)
    (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R)
    (options : Fin (S+1) → Fin K → Option Affine × ℕ)
    (hBound : ∀ s l f,(options s l).1=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (hWork : ∀ s l,(options s l).2≤C) :
    (run primitive W options).2≤profile S K W (primitive (1+2*R)) C := by
  let P := primitive (1+2*R)
  have hPair (s : Fin (S+1)) :
      (GeneralPaperCrossingPairsPrice.run primitive W (options s) (List.finRange K)).2≤
        GeneralPaperCrossingPairsPrice.profile K W P C := by
    simpa only [List.length_finRange] using GeneralPaperCrossingPairsPrice.work primitive hMono W D E A B R C
      hD hE hR (options s) (List.finRange K) (fun l _ => hBound s l) (fun l _ => hWork s l)
  have hh := GeneralPaperPricedListStream.flatMap_work W (K*K)
    (GeneralPaperCrossingPairsPrice.profile K W P C+16*(K+1)*W)
    (fun s => let current := GeneralPaperCrossingPairsPrice.run primitive W (options s) (List.finRange K)
      (current.1,current.2+16*(K+1)*W)) (List.finRange (S+1))
    (by intro s _; simpa only [List.length_finRange] using GeneralPaperCrossingPairsPrice.length primitive W (options s) (List.finRange K))
    (fun s _ => Nat.add_le_add_right (hPair s) _)
  simp only [List.length_finRange] at hh
  change _+16*(S+2)*W≤_
  unfold profile
  nlinarith only [hh]

end Blotto.GeneralPaperCrossingBatchPrice
