import Blotto.GeneralPaperProxySelection

/-! Unit-interval correctness of every selected proxy branch. Small-root
uniqueness excludes the dangerous lower-zero and upper-one choices.
The midpoint is strictly inside the unit interval on every valid grid cell.
-/
namespace Blotto.GeneralPaperProxySelectionUnit
open GeneralPaperBucketGeometry GeneralPaperProxyCell GeneralPaperProxyCellEndpoints GeneralPaperProxySelection
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem lower_unit (Q j : ℕ) (hQ : 0<Q) (hj : 0<j ∧ j<Q) : 0<lower Q j ∧ lower Q j<1 := by
  have hq : (0:ℚ)<Q := by exact_mod_cast hQ
  exact ⟨div_pos (by exact_mod_cast hj.1) hq,(div_lt_one hq).mpr (by exact_mod_cast hj.2)⟩

theorem upper_unit (Q j : ℕ) (hQ : 0<Q) (hj : j+1<Q) : 0<upper Q j ∧ upper Q j<1 := by
  have hq : (0:ℚ)<Q := by exact_mod_cast hQ
  unfold upper
  exact ⟨by positivity,(div_lt_one hq).mpr (by exact_mod_cast hj)⟩

theorem midpoint_unit (Q j : ℕ) (hQ : 0<Q) (hj : j<Q) :
    0<GeneralPaperBucketGeometry.midpoint Q j ∧ GeneralPaperBucketGeometry.midpoint Q j<1 := by
  have hq : (0:ℚ)<2*Q := by exact_mod_cast (show 0<2*Q by omega)
  unfold GeneralPaperBucketGeometry.midpoint
  refine ⟨by positivity,(div_lt_one hq).mpr ?_⟩
  exact_mod_cast (show 2*j+1<2*Q by omega)

theorem selected_unit (H Q j : ℕ) (hH : 0<H) (hQ : 0<Q) (hScale : 4*H*H≤Q) (hj : j<Q)
    (b : ℝ) (hb : 0<b ∧ b<1) (root : Option Farey.Fraction)
    (hRoot : ∀ f, root=some f → f.den≤H ∧ Closed Q j f.value) :
    0<(select Q j hQ b root).proxy.value ∧ (select Q j hQ b root).proxy.value<1 := by
  unfold select
  split
  · rename_i he
    change 0<(⟨j,Q,hQ⟩:Farey.Fraction).value ∧ (⟨j,Q,hQ⟩:Farey.Fraction).value<1
    rw [lower_value Q j hQ]
    have hr : (0:ℝ)<(lower Q j:ℝ) ∧ (lower Q j:ℝ)<1 := by rw [←he]; exact hb
    exact_mod_cast hr
  · cases hs : root with
    | none =>
      dsimp only
      split_ifs <;> rw [midpoint_value Q j hQ] <;> exact midpoint_unit Q j hQ hj
    | some f =>
      have hf := hRoot f hs
      dsimp only
      split
      · rename_i he
        change 0<f.value ∧ f.value<1
        have hr : (0:ℝ)<(f.value:ℝ) ∧ (f.value:ℝ)<1 := by rw [←he]; exact hb
        exact_mod_cast hr
      · rename_i hne
        split
        · rename_i hlt
          rw [lower_value Q j hQ]
          have hp : (0:ℚ)<f.value := by exact_mod_cast (hb.1.trans hlt)
          exact lower_unit Q j hQ ⟨lower_positive_from_root H Q j hH hScale f hf.1 hf.2 hp,hj⟩
        · rename_i hlt
          rw [upper_value Q j hQ]
          have hfb : (f.value:ℝ)<b := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
          have hp : f.value<(1:ℚ) := by exact_mod_cast (hfb.trans hb.2)
          exact upper_unit Q j hQ (upper_strict_from_root H Q j hH hScale hj f hf.1 hf.2 hp)

end Blotto.GeneralPaperProxySelectionUnit
