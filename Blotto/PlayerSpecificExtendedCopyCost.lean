import Blotto.PlayerSpecificExtendedGCDExecution

/-! Complete copies of all computed Bezout result fields, including word
metadata. The fixed cap also covers untrimmed coefficient-update lists. -/
namespace Blotto.PlayerSpecificExtendedCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem row_cost (model : RationalCostModel) (row : Data) (H W : ℕ) (hp : HasHeight row H)
    (hlen : row.length≤21) (hHW : 1+2*H≤W) (hW : 32≤W) : price model (copyRow row)≤66*model.rat W := by
  have hf := copyRow_fits W row (fun q hq => (rationalWordWidth_of_height (hp q hq)).trans hHW) (by omega)
  have hc := price_bound model W (by omega) _ hf
  rw [copyRow_length] at hc
  have hm := Nat.mul_le_mul_right (3*model.rat W) (show row.length+1≤22 by omega)
  nlinarith

theorem result_cost (model : RationalCostModel) (r : PlayerSpecificExtendedGCD.Result) (H W : ℕ)
    (hg : HasHeight r.gcd H) (hl : HasHeight r.left H) (hr : HasHeight r.right H)
    (hgl : r.gcd.length≤21) (hll : r.left.length≤21) (hrl : r.right.length≤21)
    (hHW : 1+2*H≤W) (hW : 32≤W) : price model (PlayerSpecificExtendedGCDExecution.copyResult r)≤207*model.rat W := by
  have hgp := row_cost model r.gcd H W hg hgl hHW hW
  have hlp := row_cost model r.left H W hl hll hHW hW
  have hrp := row_cost model r.right H W hr hrl hHW hW
  have hm := PlayerSpecificDenseTraceFits.controls_fits W [r.gcd.length,r.left.length,r.right.length] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> omega)
  have hp := price_bound model W (by omega) _ hm
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hp
  simp only [PlayerSpecificExtendedGCDExecution.copyResult,price_append]
  nlinarith

end Blotto.PlayerSpecificExtendedCopyCost
