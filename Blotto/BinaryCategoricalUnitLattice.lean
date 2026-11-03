import Blotto.BinaryCategoricalRun
import Blotto.BinaryPRGPreparationWork
import Blotto.RationalPRGResourceBitWidth
import Blotto.RationalExpressionWordWidth

/-! Nonnegative stored categorical weights retain a common denominator and
unit mass through every unselected suffix. Actual mass/probability words then
have widths derived from that fixed denominator, independent of choice count.
No supplied reached-state width or probability-word oracle is used. -/

namespace Blotto.BinaryCategoricalUnitLattice
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryCategoricalPreparation

def UnitLattice {α : Type*} (D : ℕ) (weights : WeightList α) : Prop :=
  (∀ item ∈ weights.items, OnRationalLattice D (value item.2)) ∧ value weights.mass ≤ 1

theorem mass_nonnegative {α : Type*} (weights : WeightList α) : 0 ≤ value weights.mass := by
  rw [WeightList.mass, WeightList.sumWords_value _ weights.canonical]
  apply List.sum_nonneg
  intro q hq
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hq
  exact weights.nonnegative item hi

theorem item_le_mass {α : Type*} (weights : WeightList α) (item : α × SignedWord) (hi : item ∈ weights.items) :
    value item.2 ≤ value weights.mass := by
  rw [WeightList.mass, WeightList.sumWords_value _ weights.canonical]
  have hMem : value item.2 ∈ weights.items.map (fun item => value item.2) := List.mem_map.mpr ⟨item, hi, rfl⟩
  exact List.single_le_sum (by
    intro q hq
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hq
    exact weights.nonnegative entry he) (value item.2) hMem

theorem mass_lattice {α : Type*} (D : ℕ) (weights : WeightList α) (h : UnitLattice D weights) :
    OnRationalLattice D (value weights.mass) := by
  rw [WeightList.mass, WeightList.sumWords_value _ weights.canonical]
  exact OnRationalLattice.list_sum _ _ h.1

theorem item_width {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α) (h : UnitLattice D weights)
    (item : α × SignedWord) (hi : item ∈ weights.items) :
    width item.2 ≤ 1 + 2 * binaryWordWidth D :=
  (weights.canonical item hi).2.trans (rationalWordWidth_lattice_bound hD (h.1 item hi)
    ⟨weights.nonnegative item hi, (item_le_mass weights item hi).trans h.2⟩)

theorem mass_width {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α) (h : UnitLattice D weights) :
    width weights.mass ≤ 1 + 2 * binaryWordWidth D :=
  weights.mass_canonical.2.trans (rationalWordWidth_lattice_bound hD (mass_lattice D weights h)
    ⟨mass_nonnegative weights, h.2⟩)

theorem mass_height {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α) (h : UnitLattice D weights) :
    RationalHeight (value weights.mass) (1 + 2 * binaryWordWidth D) :=
  (rationalHeight_of_wordWidth _).mono (rationalWordWidth_lattice_bound hD (mass_lattice D weights h)
    ⟨mass_nonnegative weights, h.2⟩)

theorem item_height {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α) (h : UnitLattice D weights)
    (item : α × SignedWord) (hi : item ∈ weights.items) :
    RationalHeight (value item.2) (1 + 2 * binaryWordWidth D) :=
  (rationalHeight_of_wordWidth _).mono (rationalWordWidth_lattice_bound hD (h.1 item hi)
    ⟨weights.nonnegative item hi, (item_le_mass weights item hi).trans h.2⟩)

theorem tail_unit {α : Type*} (D : ℕ) (weights : WeightList α) (h : UnitLattice D weights)
    (head : α × SignedWord) (rest : List (α × SignedWord)) (he : weights.items = head :: rest) :
    UnitLattice D (weights.tail head rest he) := by
  refine ⟨?_, ?_⟩
  · intro item hi
    change item ∈ rest at hi
    exact h.1 item (by rw [he]; simp [hi])
  · have hSum : value weights.mass = value head.2 + value (weights.tail head rest he).mass := by
      rw [WeightList.mass, WeightList.sumWords_value _ weights.canonical, he, List.map_cons, List.sum_cons]
      rw [WeightList.mass, WeightList.sumWords_value _ (weights.tail head rest he).canonical]
      rfl
    have hn := weights.nonnegative head (by rw [he]; simp)
    linarith [h.2]

theorem probability_width {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α) (h : UnitLattice D weights)
    (head : α × SignedWord) (hi : head ∈ weights.items) :
    width (weights.probability head) ≤ 5 + 8 * binaryWordWidth D := by
  have hP : RationalHeight (value (weights.probability head))
      ((1 + 2 * binaryWordWidth D) + (1 + 2 * binaryWordWidth D)) := by
    rw [WeightList.probability_value weights head hi, ← weights.mass_value]
    exact (item_height D hD weights h head hi).div (mass_height D hD weights h)
  have hw := (weights.probability_canonical head hi).2.trans (rationalWordWidth_of_height hP)
  omega

theorem choice_rest_unit {α : Type*} (D : ℕ) (choice : BinaryCategoricalRun.Choice α)
    (h : UnitLattice D choice.weights) : UnitLattice D choice.rest :=
  tail_unit D choice.weights h choice.head (choice.next :: choice.tail) choice.head_pair

theorem choice_probability_width {α : Type*} (D : ℕ) (hD : 0 < D) (choice : BinaryCategoricalRun.Choice α)
    (h : UnitLattice D choice.weights) : width choice.probability ≤ 5 + 8 * binaryWordWidth D := by
  rw [choice.probability_correct]
  exact probability_width D hD choice.weights h choice.head (by rw [choice.head_pair]; simp)

end Blotto.BinaryCategoricalUnitLattice
