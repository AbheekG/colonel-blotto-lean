import Blotto.PlayerSpecificRationalOutput

/-! The actual finite-bit draw now returns rational allocations, with
downward rounding after the complete computed algebraic allocation. -/
namespace Blotto.PlayerSpecificRationalFiniteDraw
open PlayerSpecificAlgebraicFiniteDraw
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (B : ℚ) (player : Bool) (H K P : ℕ)
    (bits : Fin (bitCount N H K) → Bool) : FixedArrayTable N ℚ :=
  let y := PlayerSpecificAlgebraicFiniteDraw.draw p B player H K bits
  PlayerSpecificRationalOutput.run p.parameters.root y P

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (H K P : ℕ) (bits : Fin (bitCount N H K) → Bool),
        Blotto.Feasible (if player then 1 else (i.budget:ℝ)) (PlayerSpecificRationalOutput.allocation (draw p i.budget player H K P bits)) ∧
          ∀ j,PlayerSpecificRationalOutput.allocation (draw p i.budget player H K P bits) j ≤
              PlayerSpecificSturmVariations.realEvaluate ((PlayerSpecificAlgebraicFiniteDraw.draw p i.budget player H K bits).read j) x ∧
            PlayerSpecificSturmVariations.realEvaluate ((PlayerSpecificAlgebraicFiniteDraw.draw p i.budget player H K bits).read j) x-
              PlayerSpecificRationalOutput.allocation (draw p i.budget player H K P bits) j < 1/(2:ℝ)^P ∧
            RationalHeight ((draw p i.budget player H K P bits).read j) (P+2) := by
  let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  obtain ⟨x,hx,hdraw⟩ := PlayerSpecificAlgebraicFiniteDrawContract.original_input i r hr
  have hs := PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hv : r.root.interval.lo < r.root.interval.hi := by
    have he : (r.root.interval.lo:ℝ) < r.root.interval.hi := lt_of_lt_of_le hx.2.1.1 hx.2.1.2
    exact_mod_cast he
  refine ⟨x,hx,?_⟩
  intro player H K P bits
  have hB : (if player then 1 else (i.budget:ℝ)) ≤ 1 := by
    cases player
    · simpa using (show (i.budget:ℝ) ≤ 1 by exact_mod_cast i.budget_le)
    · exact le_rfl
  exact PlayerSpecificRationalOutput.every_path r.root (PlayerSpecificAlgebraicFiniteDraw.draw p i.budget player H K bits) P
    hs.1 hs.2.1 hv x (if player then 1 else (i.budget:ℝ)) hx (hdraw player H K bits).1 hB

end Blotto.PlayerSpecificRationalFiniteDraw
