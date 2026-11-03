import Blotto.PlayerSpecificForestExecution

/-! One original-input width bounds all dyadic split/query/record/control
prices in the actual computed traversal. -/
namespace Blotto.PlayerSpecificTraversalPrice
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude PlayerSpecificSquarefreeHeights
set_option autoImplicit false
set_option maxHeartbeats 5000000

def widthCoefficient : ℕ := 22*certificateConstant+52*PlayerSpecificIsolationDepthHeight.linearConstant+600
def width (p : Data) : ℕ := widthCoefficient*(inputHeight p+1)

theorem width_large (p : Data) : 600 ≤ width p := by unfold width widthCoefficient; nlinarith

theorem depth_width (p : Data) (hlen : p.length≤4) : PlayerSpecificRootIsolation.depth p+8 ≤ width p := by
  have h := PlayerSpecificIsolationDepthHeight.depth_linear p hlen
  unfold width widthCoefficient
  nlinarith

theorem endpoint_width (p : Data) (hlen : p.length≤4) (k : ℕ) (hk : k≤PlayerSpecificRootIsolation.depth p) :
    1+2*(2*inputHeight p+k+4) ≤ width p := by
  have h := PlayerSpecificIsolationDepthHeight.depth_linear p hlen
  unfold width widthCoefficient
  nlinarith

theorem split_width (p : Data) (hlen : p.length≤4) (k : ℕ) (hk : k≤PlayerSpecificRootIsolation.depth p) :
    PlayerSpecificSplitTraceCost.width p (2*inputHeight p+k+4) ≤ width p := by
  have hd := PlayerSpecificIsolationDepthHeight.depth_linear p hlen
  have hc := certificate_linear (inputHeight p)
  unfold PlayerSpecificSplitTraceCost.width PlayerSpecificPreparedQueryCost.queryWidth
    PlayerSpecificPreparedQueryCost.queryHeight width widthCoefficient
  nlinarith

theorem record_cost (model : RationalCostModel) (p : Data) (prepared : Prepared p) (hlen : p.length≤4)
    (node : Interval) (k : ℕ) (hk : k≤PlayerSpecificRootIsolation.depth p)
    (hv : Valid prepared node) (hg : PlayerSpecificDyadicEndpoints.Grid node k)
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificRootMagnitude.rootBound p:ℚ)) :
    price model (PlayerSpecificSplitExecution.copyInterval node) ≤ 15*model.rat (width p) := by
  have h := PlayerSpecificDyadicEndpoints.endpoint_height p prepared node k hv hg hb
  have hc := PlayerSpecificSplitExecution.stored_counts p prepared hlen node hv
  exact PlayerSpecificSplitTraceCost.copyInterval_cost model node _ (width p) h.1 h.2 hc.1 hc.2.1
    (endpoint_width p hlen k hk) ((by omega : 6≤600).trans (width_large p))

theorem split_cost (model : RationalCostModel) (p : Data) (prepared : Prepared p) (hlen : p.length≤4)
    (node : Interval) (k : ℕ) (hk : k≤PlayerSpecificRootIsolation.depth p)
    (hv : Valid prepared node) (hg : PlayerSpecificDyadicEndpoints.Grid node k)
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificRootMagnitude.rootBound p:ℚ)) :
    price model (PlayerSpecificSplitExecution.run prepared node).2 ≤ 5000*model.rat (width p) := by
  have h := PlayerSpecificDyadicEndpoints.endpoint_height p prepared node k hv hg hb
  exact (PlayerSpecificSplitTraceCost.run_cost model p prepared hlen node hv _ h.1 h.2).trans
    (Nat.mul_le_mul_left 5000 (model.monotone (split_width p hlen k hk)))

theorem frame_cost (model : RationalCostModel) (p : Data) (prepared : Prepared p) (hlen : p.length≤4)
    (fuel : ℕ) (node : Interval) (k : ℕ) (hcap : k+fuel≤PlayerSpecificRootIsolation.depth p)
    (hv : Valid prepared node) (hg : PlayerSpecificDyadicEndpoints.Grid node k)
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificRootMagnitude.rootBound p:ℚ)) :
    price model (PlayerSpecificForestExecution.frame fuel node) ≤ 25*model.rat (width p) := by
  have hk : k≤PlayerSpecificRootIsolation.depth p := by omega
  have hr := record_cost model p prepared hlen node k hk hv hg hb
  have hc := PlayerSpecificSplitExecution.stored_counts p prepared hlen node hv
  have hd := depth_width p hlen
  have hw := width_large p
  have hf : Fits (width p) [.control fuel,.control node.count,.control 1] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl <;> exact (control_width _).trans (by omega)
  have hp := price_bound model (width p) (by omega) _ hf
  simp only [List.length_cons,List.length_nil] at hp
  rw [PlayerSpecificForestExecution.frame,price_append]
  nlinarith

theorem price_flatMap {A : Type*} (model : RationalCostModel) (f : A → Trace) (xs : List A) :
    price model (xs.flatMap f)=(xs.map (fun x => price model (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,price_append,ih,List.map_cons,List.sum_cons]

theorem sum_prices (model : RationalCostModel) (W : ℕ) (rows : List Interval)
    (h : ∀ node∈rows,price model (PlayerSpecificSplitExecution.copyInterval node)≤15*model.rat W) :
    (rows.map (fun node => price model (PlayerSpecificSplitExecution.copyInterval node))).sum≤rows.length*(15*model.rat W) := by
  induction rows with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons node rows ih =>
    have hn := h node List.mem_cons_self
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem node hq))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

theorem copyForest_cost (model : RationalCostModel) (W : ℕ) (hW : 6≤W) (rows : List Interval)
    (hlen : rows.length≤3)
    (h : ∀ node∈rows,price model (PlayerSpecificSplitExecution.copyInterval node)≤15*model.rat W) :
    price model (PlayerSpecificForestExecution.copyForest rows) ≤ 50*model.rat W := by
  have hs := sum_prices model W rows h
  have hc := event_price model W (by omega) (.control rows.length)
    ((control_width rows.length).trans (by omega))
  change price model ([.control rows.length]++rows.flatMap PlayerSpecificSplitExecution.copyInterval)≤_
  rw [price_append,price_flatMap]
  change price model [.control rows.length]≤3*model.rat W at hc
  have hm := Nat.mul_le_mul_right (15*model.rat W) hlen
  nlinarith

theorem output_copy_cost (model : RationalCostModel) (p : Data) (prepared : Prepared p) (hp : semantics p≠0)
    (hlen : p.length≤4) (fuel : ℕ) (node : Interval) (k : ℕ) (hcap : k+fuel≤PlayerSpecificRootIsolation.depth p)
    (hv : Valid prepared node) (hg : PlayerSpecificDyadicEndpoints.Grid node k)
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificRootMagnitude.rootBound p:ℚ)) :
    price model (PlayerSpecificForestExecution.copyForest (PlayerSpecificForestExecution.run prepared fuel node).1) ≤
      50*model.rat (width p) := by
  rw [PlayerSpecificForestExecution.value]
  have hc := PlayerSpecificIsolationBounds.count_bound prepared hp node hv
  have hl := PlayerSpecificIsolationForest.length_bound prepared hp fuel node hv
  have hlength : (PlayerSpecificIsolationForest.run prepared fuel node).length≤3 := by omega
  apply copyForest_cost model (width p) ((by omega : 6≤600).trans (width_large p)) _ hlength
  intro leaf hm
  have hvalid := (PlayerSpecificIsolationForest.valid_positive prepared fuel node hv leaf hm).1
  have hgrid := PlayerSpecificDyadicEndpoints.forest_grid prepared fuel node k hg leaf hm
  have hbound := PlayerSpecificDyadicEndpoints.forest_bounded prepared fuel node _ hv hb leaf hm
  exact record_cost model p prepared hlen leaf (k+fuel) hcap hvalid hgrid hbound

end Blotto.PlayerSpecificTraversalPrice
