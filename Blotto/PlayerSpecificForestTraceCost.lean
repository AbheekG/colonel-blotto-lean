import Blotto.PlayerSpecificTraversalPrice

/-! Total source price of the actual pruned bisection traversal. The sequence,
enclosure and depth are the actual computed values; their preparation prices
remain a separate join. No per-node count, height or cost oracle is supplied. -/
namespace Blotto.PlayerSpecificForestTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificForestExecution PlayerSpecificTraversalPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem run_cost (model : RationalCostModel) (p : Data) (prepared : Prepared p) (hp : semantics p≠0)
    (hlen : p.length≤4) (fuel : ℕ) (node : Interval) (k : ℕ) (hcap : k+fuel≤PlayerSpecificRootIsolation.depth p)
    (hv : Valid prepared node) (hg : PlayerSpecificDyadicEndpoints.Grid node k)
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificRootMagnitude.rootBound p:ℚ)) :
    price model (run prepared fuel node).2 ≤
      PlayerSpecificIsolationForest.visits prepared fuel node*(5100*model.rat (width p)) := by
  have hw := width_large p
  have hzprice : price model [.control 0]≤3*model.rat (width p) := by
    exact price_bound model (width p) (by omega) _ (by
      intro e he
      have he' := List.mem_singleton.mp he
      subst e
      exact (control_width 0).trans (by omega))
  induction fuel generalizing node k with
  | zero =>
    have hf := frame_cost model p prepared hlen 0 node k hcap hv hg hb
    have hc := output_copy_cost model p prepared hp hlen 0 node k hcap hv hg hb
    rw [run]
    split
    · rw [price_append,PlayerSpecificIsolationForest.visits]
      nlinarith
    · rename_i hn
      rw [run] at hc
      rw [ite_eq_right hn] at hc
      rw [price_append,PlayerSpecificIsolationForest.visits]
      nlinarith
  | succ fuel ih =>
    have hf := frame_cost model p prepared hlen (fuel+1) node k hcap hv hg hb
    have hc := output_copy_cost model p prepared hp hlen (fuel+1) node k hcap hv hg hb
    rw [run]
    split
    · rename_i hn
      rw [price_append,PlayerSpecificIsolationForest.visits,ite_eq_left hn]
      nlinarith
    · rename_i hn
      have hvalid := split_valid prepared node hv
      have hgrid := PlayerSpecificDyadicEndpoints.split_grid prepared node k hg
      have hbound := PlayerSpecificDyadicEndpoints.split_bounded prepared node _ hv hb
      have hcap' : k+1+fuel≤PlayerSpecificRootIsolation.depth p := by omega
      have hl := ih (split prepared node).1 (k+1) hcap' hvalid.1 hgrid.1 hbound.1
      have hr := ih (split prepared node).2 (k+1) hcap' hvalid.2 hgrid.2 hbound.2
      have hs := split_cost model p prepared hlen node k (by omega) hv hg hb
      rw [run] at hc
      dsimp only at hc
      rw [ite_eq_right hn] at hc
      simp only [PlayerSpecificSplitExecution.value] at hc
      rw [PlayerSpecificIsolationForest.visits,ite_eq_right hn]
      dsimp only
      simp only [price_append,PlayerSpecificSplitExecution.value]
      nlinarith

def traversal (p : Data) : List Interval×Trace :=
  let prepared := prepare p
  run prepared (PlayerSpecificRootIsolation.depth p) (PlayerSpecificRootMagnitude.initial p prepared)

theorem traversal_value (p : Data) : (traversal p).1=PlayerSpecificRootIsolation.run p := value _ _ _

theorem traversal_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    price model (traversal p).2 ≤
      (30600*PlayerSpecificIsolationDepthHeight.linearConstant+5100)*(PlayerSpecificRationalMagnitude.inputHeight p+1)*
        model.rat (widthCoefficient*(PlayerSpecificRationalMagnitude.inputHeight p+1)) := by
  have h := run_cost model p (prepare p) hp hlen (PlayerSpecificRootIsolation.depth p)
    (PlayerSpecificRootMagnitude.initial p (prepare p)) 0 (by omega)
    (PlayerSpecificRootMagnitude.initial_valid p (prepare p))
    (PlayerSpecificDyadicEndpoints.initial_grid p (prepare p)) (PlayerSpecificDyadicEndpoints.initial_bounded p (prepare p))
  have hv := PlayerSpecificIsolationDepthHeight.traversal_linear p hp hlen
  have hm := Nat.mul_le_mul_right (5100*model.rat (width p)) hv
  change price model (traversal p).2≤_ at h
  unfold width at h hm
  nlinarith

end Blotto.PlayerSpecificForestTraceCost
