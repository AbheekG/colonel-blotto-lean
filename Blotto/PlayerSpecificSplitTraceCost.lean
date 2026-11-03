import Blotto.PlayerSpecificSplitExecution

/-! Source price of the actual cached split, including midpoint arithmetic,
one cached-row query, both child records and stored variation-count words. -/
namespace Blotto.PlayerSpecificSplitTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificSplitExecution PlayerSpecificPreparedQueryCost
set_option autoImplicit false
set_option maxHeartbeats 5000000

def width (p : Data) (T : ℕ) : ℕ := queryWidth p (2*T+3)+8*T+64

theorem copyInterval_cost (model : RationalCostModel) (node : Interval) (H W : ℕ)
    (hlo : RationalHeight node.lo H) (hhi : RationalHeight node.hi H)
    (hl : node.loValue≤5) (hh : node.hiValue≤5) (hHW : 1+2*H≤W) (hW : 6≤W) :
    price model (copyInterval node)≤15*model.rat W := by
  have hc : node.count≤5 := (Nat.sub_le _ _).trans hl
  have hf : Fits W (copyInterval node) := by
    intro e he
    simp only [copyInterval,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact (rationalWordWidth_of_height hlo).trans hHW
    · exact (rationalWordWidth_of_height hhi).trans hHW
    · exact (control_width _).trans (by omega)
    · exact (control_width _).trans (by omega)
    · exact (control_width _).trans (by omega)
  have hp := price_bound model W (by omega) _ hf
  rw [copyInterval_length] at hp
  exact hp

theorem run_cost (model : RationalCostModel) (p : Data) (prepared : Prepared p) (hlen : p.length≤4)
    (node : Interval) (hv : Valid prepared node) (T : ℕ)
    (hlo : RationalHeight node.lo T) (hhi : RationalHeight node.hi T) :
    price model (run prepared node).2≤5000*model.rat (width p T) := by
  let summed := scalar .add node.lo node.hi
  let middle := scalar .divide summed.1 2
  let counted := PlayerSpecificEndpointExecution.endpoint prepared middle.1
  let left : Interval := ⟨node.lo,middle.1,node.loValue,counted.1⟩
  let right : Interval := ⟨middle.1,node.hi,counted.1,node.hiValue⟩
  let W := width p T
  have hW : 6≤W := by dsimp only [W,width]; omega
  have ht : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hs : RationalHeight summed.1 (2*T+1) := by simpa only [summed,scalar,Arithmetic.apply,two_mul] using hlo.add hhi
  have hm : RationalHeight middle.1 (2*T+3) := by
    simpa only [middle,scalar,Arithmetic.apply,Nat.add_assoc] using hs.div ht
  have hsumfit := fits_mono (scalar_fits_height .add node.lo node.hi T hlo hhi)
    (show 4*T+3≤W by dsimp only [W,width]; omega)
  have hmidfit := fits_mono (scalar_fits_height .divide summed.1 2 (2*T+3) (hs.mono (by omega)) (ht.mono (by omega)))
    (show 4*(2*T+3)+3≤W by dsimp only [W,width]; omega)
  have hsumprice := price_bound model W (by omega) _ hsumfit
  have hmidprice := price_bound model W (by omega) _ hmidfit
  rw [scalar_length] at hsumprice hmidprice
  have hquery := endpoint_cost model p prepared hlen middle.1 (2*T+3) hm
  have hquery' : price model counted.2≤4000*model.rat W :=
    hquery.trans (Nat.mul_le_mul_left 4000 (model.monotone (by dsimp only [W,width]; omega)))
  have hc := stored_counts p prepared hlen node hv
  have hnew := endpoint_count p prepared hlen middle.1
  have hlprice := copyInterval_cost model left (2*T+3) W (hlo.mono (by omega)) hm hc.1 hnew
    (by dsimp only [W,width]; omega) hW
  have hrprice := copyInterval_cost model right (2*T+3) W hm (hhi.mono (by omega)) hnew hc.2.1
    (by dsimp only [W,width]; omega) hW
  have hlenrows := (prepared_bounds p prepared hlen).2
  have hpre : Fits W [.control prepared.sequence.length,.control node.loValue,.control node.hiValue] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl <;> exact (control_width _).trans (by omega)
  have hpreprice := price_bound model W (by omega) _ hpre
  simp only [List.length_cons,List.length_nil] at hpreprice
  change price model
    ([.control prepared.sequence.length,.control node.loValue,.control node.hiValue]++
      summed.2++middle.2++counted.2++copyInterval left++copyInterval right)≤5000*model.rat W
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificSplitTraceCost
