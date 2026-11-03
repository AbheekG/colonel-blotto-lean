import Blotto.PlayerSpecificSegmentDiscrepancy

/-! The executing selector lists every slot except the final fallback.
Its exact conditional mean is the full normalized weight sum, including
zero-weight padding and a zero remaining mass. -/
namespace Blotto.PlayerSpecificSegmentEnumeration
set_option autoImplicit false
set_option maxHeartbeats 2500000

def items (m : ℕ) : List (Fin (m+1)) := (List.finRange (m+1)).take m

theorem items_eq (m : ℕ) : items m=(List.finRange m).map Fin.castSucc := by
  rw [items,List.finRange_succ_last]
  exact List.take_left' (by simp)

theorem length (m : ℕ) : (items m).length=m := by rw [items_eq]; simp

theorem weighted_sum (m : ℕ) (f : Fin (m+1) → ℝ) :
    ((items m).map f).sum=∑ j : Fin m,f j.castSucc := by
  rw [items_eq,List.map_map]
  simp [List.finRange, List.sum_ofFn, Function.comp_def]

theorem mass (m : ℕ) (weight : Fin (m+1) → ℝ) (hs : ∑ j,weight j=1) :
    PlayerSpecificSegmentIdealMean.total weight (items m)+weight (Fin.last m)=1 := by
  rw [PlayerSpecificSegmentIdealMean.total,weighted_sum]
  exact (Fin.sum_univ_castSucc weight).symm.trans hs

theorem remaining (m : ℕ) (weight : Fin (m+1) → ℝ) (hn : ∀ j,0 ≤ weight j) (hs : ∑ j,weight j=1) :
    PlayerSpecificSegmentIdealMean.Remaining weight (items m) 1 := by
  refine ⟨fun j _ => hn j,?_⟩
  have hm := mass m weight hs
  have hp := hn (Fin.last m)
  linarith only [hm,hp]

theorem full_mean (m : ℕ) (weight : Fin (m+1) → ℝ) (hn : ∀ j,0 ≤ weight j) (hs : ∑ j,weight j=1)
    (f : Fin (m+1) → ℝ) :
    PlayerSpecificSegmentIdealMean.mean weight (Fin.last m) f (items m) 1=∑ j,weight j*f j := by
  rw [PlayerSpecificSegmentIdealMean.normalized_mean weight (Fin.last m) f (items m) (remaining m weight hn hs),weighted_sum]
  have hm := mass m weight hs
  have he : 1-PlayerSpecificSegmentIdealMean.total weight (items m)=weight (Fin.last m) := by linarith only [hm]
  rw [he]
  exact (Fin.sum_univ_castSucc (fun j => weight j*f j)).symm

end Blotto.PlayerSpecificSegmentEnumeration
