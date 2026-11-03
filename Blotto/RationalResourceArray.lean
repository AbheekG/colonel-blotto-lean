import Blotto.PairStoreMemory
import Blotto.ResourceArray
import Blotto.RationalRoundingPair

/-! Native rational resource arrays and their exact real interpretation.
Two Array.set operations implement pair updates in the binary backend. -/

namespace Blotto
open scoped BigOperators

structure RationalResourceArray (n : ℕ) where
  data : Array ℚ
  size : data.size = n

namespace RationalResourceArray

def allocation {n : ℕ} (a : RationalResourceArray n) : Fin n → ℚ :=
  fun j => a.data[j.val]'(by rw [a.size]; exact j.isLt)

def ofAllocation {n : ℕ} (r : Fin n → ℚ) : RationalResourceArray n := ⟨Array.ofFn r, Array.size_ofFn⟩

noncomputable def realAllocation {n : ℕ} (a : RationalResourceArray n) : Allocation n := fun j => a.allocation j

def updatePairReference {n : ℕ} (a : RationalResourceArray n) (i j : Fin n) (z : ℚ) : RationalResourceArray n :=
  let second := a.allocation i + a.allocation j - z
  let first := a.data.set i.val z (by rw [a.size]; exact i.isLt)
  ⟨first.set j.val second (by simp only [first, Array.size_set, a.size]; exact j.isLt), by
    simp only [Array.size_set, first, a.size]⟩

def updatePair {n : ℕ} (a : RationalResourceArray n) (i j : Fin n) (z : ℚ) : RationalResourceArray n :=
  let next := PairStoreProgram.update (⟨a.data, a.size⟩ : PairStoreBuffer n ℚ) i j z
  ⟨next.data, next.size⟩

theorem updatePair_refines {n : ℕ} (a : RationalResourceArray n) (i j : Fin n) (z : ℚ) :
    a.updatePair i j z = a.updatePairReference i j z := by
  unfold updatePair
  rw [PairStoreProgram.update_eq]
  rfl

theorem allocation_ofAllocation {n : ℕ} (r : Fin n → ℚ) : (ofAllocation r).allocation = r := by
  funext j
  simp [allocation, ofAllocation]

theorem realAllocation_ofAllocation {n : ℕ} (r : Fin n → ℚ) :
    (ofAllocation r).realAllocation = fun j => (r j : ℝ) := by
  funext j
  simp [realAllocation, allocation_ofAllocation]

theorem realAllocation_updatePair {n : ℕ} (a : RationalResourceArray n) (i j : Fin n) (z : ℚ) :
    (a.updatePair i j z).realAllocation = Blotto.updatePair a.realAllocation i j z := by
  rw [a.updatePair_refines]
  funext k
  simp [realAllocation, allocation, updatePairReference, Blotto.updatePair, Function.update_apply,
    Array.getElem_set, Fin.ext_iff, eq_comm]
  split_ifs <;> simp

theorem allocation_updatePair {n : ℕ} (a : RationalResourceArray n) (i j : Fin n) (z : ℚ) :
    (a.updatePair i j z).allocation =
      Function.update (Function.update a.allocation i z) j (a.allocation i + a.allocation j - z) := by
  rw [a.updatePair_refines]
  funext k
  simp [allocation, updatePairReference, Function.update_apply, Array.getElem_set, Fin.ext_iff, eq_comm]

theorem updatePair_sum {n : ℕ} (a : RationalResourceArray n) {i j : Fin n} (hij : i ≠ j) (z : ℚ) :
    (∑ k, (a.updatePair i j z).realAllocation k) = ∑ k, a.realAllocation k := by
  rw [a.realAllocation_updatePair]
  exact Blotto.updatePair_sum _ hij _

end RationalResourceArray
end Blotto
