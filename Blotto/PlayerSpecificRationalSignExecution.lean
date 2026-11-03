import Blotto.PlayerSpecificSignRetagCost

/-! Executing rational sign uses two actual order tests and copies its
input/result controls. It remains total on exact zero. -/
namespace Blotto.PlayerSpecificRationalSignExecution
open SignType PlayerSpecificRationalTrace PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 1000000

def run (q : ℚ) : SignType×Trace :=
  let low:=PlayerSpecificRationalTrace.compare q 0
  let high:=PlayerSpecificRationalTrace.compare 0 q
  let result:SignType:=if !low.1 then .pos else if !high.1 then .neg else .zero
  (result,low.2++high.2++[.copy q,.control 1])

theorem value (q : ℚ) : (run q).1=sign q := by
  simp only [run,PlayerSpecificRationalTrace.compare,sign_apply]
  by_cases hpos : 0<q
  · simp [hpos,not_le.mpr hpos]
  · have hle:=le_of_not_gt hpos
    by_cases hneg : q<0
    · simp [hpos,hneg,hle,not_le.mpr hneg]
    · have hn:=le_of_not_gt hneg
      simp [hpos,hneg,hle,hn]

theorem run_cost (model : RationalCostModel) (q : ℚ) (H W : ℕ) (hq : RationalHeight q H)
    (hH : 1≤H) (hHW : 1+2*H≤W) (hW : 6≤W) : price model (run q).2≤40*model.rat W := by
  have hqw: rationalWordWidth q≤W := (rationalWordWidth_of_height hq).trans hHW
  have hzero: rationalWordWidth (0:ℚ)≤W := (rationalWordWidth_of_height (zero_height.mono hH)).trans hHW
  have hl:=price_bound model W (by omega) _ (compare_fits W q 0 hqw hzero (by omega))
  have hh:=price_bound model W (by omega) _ (compare_fits W 0 q hzero hqw (by omega))
  rw [compare_length] at hl hh
  have hf : Fits W [.copy q,.control 1] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact hqw
    · exact (PlayerSpecificRationalTrace.control_width 1).trans (by omega)
  have hc:=price_bound model W (by omega) _ hf
  simp only [List.length_cons,List.length_nil] at hc
  simp only [run,price_append]
  nlinarith only [hl,hh,hc]

end Blotto.PlayerSpecificRationalSignExecution
