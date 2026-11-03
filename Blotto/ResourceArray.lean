import Blotto.PairStoreMemory
import Blotto.ActiveResourceList

/-! Array representation of resource vectors. A pair update computes its
second value from the old entries, then performs exactly two Array.set calls.
This proves representation correctness; machine costs/ownership are not
inferred from Lean's persistent-array implementation. -/

namespace Blotto
open scoped BigOperators

structure ResourceArray (n : ℕ) where
  data : Array ℝ
  size : data.size = n

namespace ResourceArray

noncomputable def allocation {n : ℕ} (a : ResourceArray n) : Allocation n :=
  fun j => a.data[j.val]'(by rw [a.size]; exact j.isLt)

noncomputable def ofAllocation {n : ℕ} (r : Allocation n) : ResourceArray n :=
  ⟨Array.ofFn r, Array.size_ofFn⟩

theorem allocation_ofAllocation {n : ℕ} (r : Allocation n) : (ofAllocation r).allocation = r := by
  funext j
  simp [allocation, ofAllocation]

noncomputable def updatePairReference {n : ℕ} (a : ResourceArray n) (i j : Fin n) (z : ℝ) : ResourceArray n :=
  let second := a.allocation i + a.allocation j - z
  let first := a.data.set i.val z (by rw [a.size]; exact i.isLt)
  ⟨first.set j.val second (by simp only [first, Array.size_set, a.size]; exact j.isLt), by
    simp only [Array.size_set, first, a.size]⟩

noncomputable def updatePair {n : ℕ} (a : ResourceArray n) (i j : Fin n) (z : ℝ) : ResourceArray n :=
  let next := PairStoreProgram.update (⟨a.data, a.size⟩ : PairStoreBuffer n ℝ) i j z
  ⟨next.data, next.size⟩

theorem updatePair_refines {n : ℕ} (a : ResourceArray n) (i j : Fin n) (z : ℝ) :
    a.updatePair i j z = a.updatePairReference i j z := by
  unfold updatePair
  rw [PairStoreProgram.update_eq]
  rfl

theorem allocation_updatePair {n : ℕ} (a : ResourceArray n) (i j : Fin n) (z : ℝ) :
    (a.updatePair i j z).allocation = Blotto.updatePair a.allocation i j z := by
  rw [a.updatePair_refines]
  funext k
  simp [allocation, updatePairReference, Blotto.updatePair, Function.update_apply, Array.getElem_set, Fin.ext_iff, eq_comm]

theorem updatePair_sum {n : ℕ} (a : ResourceArray n) {i j : Fin n} (hij : i ≠ j) (z : ℝ) :
    (∑ k, (a.updatePair i j z).allocation k) = ∑ k, a.allocation k := by
  rw [a.allocation_updatePair]
  exact Blotto.updatePair_sum a.allocation hij z

theorem updatePair_inBox {n : ℕ} {L : Allocation n} (a : ResourceArray n) {i j : Fin n} (hij : i ≠ j)
    (hbox : InBox L a.allocation) (hi : Fractional L a.allocation i) (hj : Fractional L a.allocation j)
    {z : ℝ} (hz : z = (resourcePair L a.allocation i j hi hj).lower ∨
      z = (resourcePair L a.allocation i j hi hj).upper) : InBox L (a.updatePair i j z).allocation := by
  rw [a.allocation_updatePair]
  exact Blotto.updatePair_inBox hij hbox hi hj hz

end ResourceArray
end Blotto
