import Blotto.GeneralPaperQuantileDescent

/-! The child masses used by the descent satisfy the same structural error
bound, including virtual halves of an already rounded uniform interval.
-/
namespace Blotto.GeneralPaperQuantileChildMass
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperMassApproximation
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
open GeneralPaperQuantileDescent
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem uniform_half_mass (k ancestor height level : ℕ) :
    trueMass k ancestor (.uniform (height+1) level)/2=trueMass k (ancestor+level) (.uniform height 0) := by
  rw [true_uniform,true_uniform]
  simp only [Nat.add_zero,pow_succ]
  ring

theorem left_bound (lambda k ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (storedMass : Number)
    (hHeight : height+1≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (prepare lambda k).format.unit (queryExponent lambda k) (trueMass k ancestor node) storedMass) :
    Bound (prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k (ancestor+offset node) (leftChild node))
      (leftMass (prepare lambda k) ancestor node storedMass).number := by
  cases node with
  | uniform h level =>
    have he := half_bound _ _ _ _ hMass
    rw [uniform_half_mass] at he
    exact he
  | branch level cached left right =>
    exact fresh_bound lambda k (ancestor+level) left (by omega)
      (child_validity lambda k _ hValid).1 (child_paths _ ancestor _ hPath).1

theorem right_bound (lambda k ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (storedMass : Number)
    (hHeight : height+1≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (prepare lambda k).format.unit (queryExponent lambda k) (trueMass k ancestor node) storedMass) :
    Bound (prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k (ancestor+offset node) (rightChild node))
      (rightMass (prepare lambda k) ancestor node storedMass).number := by
  cases node with
  | uniform h level =>
    have he := half_bound _ _ _ _ hMass
    rw [uniform_half_mass] at he
    exact he
  | branch level cached left right =>
    exact fresh_bound lambda k (ancestor+level) right (by omega)
      (child_validity lambda k _ hValid).2 (child_paths _ ancestor _ hPath).2

end Blotto.GeneralPaperQuantileChildMass
