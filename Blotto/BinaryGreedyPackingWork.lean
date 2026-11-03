import Blotto.BinaryGreedyPackingExecution
import Blotto.BinaryPRGPreparationWork
import Blotto.RationalPRGResourceBitWidth

/-! Next-fit packing retains the actual returned Boolean addition and prices
the following comparison. Live group totals stay on the input lattice and in
the budget box, so per-step widths and cubic arithmetic work are derived and
do not grow with the update count. Structural/list work is separately covered
by BinaryGreedyPackingExecution; table/address/allocator/GC costs are separate. -/

namespace Blotto.BinaryGreedyPackingWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryPRGPreparationWork

def GoodTotal (D : ℕ) (budget total : SignedWord) : Prop :=
  CanonicalWord total ∧ OnRationalLattice D (value total) ∧
    0 ≤ value total ∧ value total ≤ value budget

def packAux {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → SignedWord → List α → List (List α × SignedWord) × ℕ
  | current, total, [] => ([(current.reverse, total)], 0)
  | current, total, item :: rest =>
      let added := applyWithWork .add total (length item)
      let localWork := added.2 + BinaryRationalArithmetic.lessEqualWork added.1 budget
      if BinaryRationalArithmetic.lessEqual added.1 budget then
        let later := packAux length budget (item :: current) added.1 rest
        (later.1, localWork + later.2)
      else
        let later := packAux length budget [item] (length item) rest
        ((current.reverse, total) :: later.1, localWork + later.2)

def pack {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → List (List α × SignedWord) × ℕ
  | [] => ([], 0)
  | item :: rest => packAux length budget [item] (length item) rest

theorem packAux_state {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    (packAux length budget current total rest).1 = BinaryGreedyPacking.packAux length budget current total rest := by
  induction rest generalizing current total with
  | nil => rfl
  | cons item rest ih =>
      unfold packAux BinaryGreedyPacking.packAux
      simp only [applyWithWork_state]
      by_cases hFit : BinaryRationalArithmetic.lessEqual (apply .add total (length item)) budget = true
      · simp [hFit, ih]
      · simp [hFit, ih]

theorem pack_state {α : Type*} (length : α → SignedWord) (budget : SignedWord) (items : List α) :
    (pack length budget items).1 = BinaryGreedyPacking.packedGroups length budget items := by
  cases items
  · rfl
  · exact packAux_state _ _ _ _ _

theorem goodTotal_width (D : ℕ) (hD : 0 < D) (budget total : SignedWord)
    (hBudget : value budget ≤ 1) (h : GoodTotal D budget total) :
    width total ≤ 1 + 2 * binaryWordWidth D :=
  h.1.2.trans (rationalWordWidth_lattice_bound hD h.2.1 ⟨h.2.2.1, h.2.2.2.trans hBudget⟩)

theorem pairStep_work_bound (total leaf budget : SignedWord) (W : ℕ)
    (hT : width total ≤ W) (hL : width leaf ≤ W) (hB : width budget ≤ W) :
    (applyWithWork .add total leaf).2 +
      BinaryRationalArithmetic.lessEqualWork (applyWithWork .add total leaf).1 budget ≤
        20000 * (W + 1) ^ 3 := by
  have hA := operation_uniform_bound .add total leaf W hT hL
  have hNext : width (applyWithWork .add total leaf).1 ≤ 3 * W + 1 := by
    rw [applyWithWork_state]
    exact (apply_stored_width .add total leaf).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le hT hL)) 1)
  have hPair : BinaryRationalArithmetic.pairWidth (applyWithWork .add total leaf).1 budget ≤ 3 * W + 1 :=
    max_le hNext (hB.trans (by omega))
  have hC := (BinaryRationalArithmetic.lessEqualWork_bound (applyWithWork .add total leaf).1 budget).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hPair 1) 2))
  have hQ : 500 * (3 * W + 2) ^ 2 ≤ 8000 * (W + 1) ^ 3 := by
    nlinarith [Nat.zero_le W, Nat.zero_le (W ^ 2), Nat.zero_le (W ^ 3)]
  have hCompare := hC.trans (by simpa only [Nat.add_assoc] using hQ)
  nlinarith

theorem next_good (D : ℕ) (budget total leaf : SignedWord)
    (hB : CanonicalWord budget) (hT : GoodTotal D budget total) (hL : GoodTotal D budget leaf)
    (hFit : BinaryRationalArithmetic.lessEqual (applyWithWork .add total leaf).1 budget = true) :
    GoodTotal D budget (applyWithWork .add total leaf).1 := by
  rw [applyWithWork_state] at hFit ⊢
  have hC := BinaryReflectedFourSetup.opcode_canonical .add total leaf hT.1 hL.1
  have hValue := apply_value .add total leaf hT.1.1 hL.1.1
  refine ⟨hC, ?_, ?_, (BinaryRationalArithmetic.lessEqual_iff _ _ hC.1 hB.1).mp hFit⟩
  · rw [hValue]; exact hT.2.1.add hL.2.1
  · rw [hValue]; exact add_nonneg hT.2.2.1 hL.2.2.1

theorem packAux_boolean_bound {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (D : ℕ) (hD : 0 < D) (hB : CanonicalWord budget)
    (hBLattice : OnRationalLattice D (value budget)) (hBbox : 0 ≤ value budget ∧ value budget ≤ 1)
    (hLength : ∀ item, GoodTotal D budget (length item))
    (current : List α) (total : SignedWord) (rest : List α) (hT : GoodTotal D budget total) :
    (packAux length budget current total rest).2 ≤
      rest.length * (20000 * (2 + 2 * binaryWordWidth D) ^ 3) := by
  induction rest generalizing current total with
  | nil => simp [packAux]
  | cons item rest ih =>
      have hBudgetWidth : width budget ≤ 1 + 2 * binaryWordWidth D :=
        hB.2.trans (rationalWordWidth_lattice_bound hD hBLattice hBbox)
      have hLocal := pairStep_work_bound total (length item) budget (1 + 2 * binaryWordWidth D)
        (goodTotal_width D hD budget total hBbox.2 hT)
        (goodTotal_width D hD budget (length item) hBbox.2 (hLength item)) hBudgetWidth
      have hWidth : 1 + 2 * binaryWordWidth D + 1 = 2 + 2 * binaryWordWidth D := by omega
      rw [hWidth] at hLocal
      unfold packAux
      dsimp only
      split
      · rename_i hFit
        have hNext := next_good D budget total (length item) hB hT (hLength item) hFit
        have hRest := ih (item :: current) (applyWithWork .add total (length item)).1 hNext
        exact (Nat.add_le_add hLocal hRest).trans_eq (by simp only [List.length_cons]; ring)
      · have hRest := ih [item] (length item) (hLength item)
        exact (Nat.add_le_add hLocal hRest).trans_eq (by simp only [List.length_cons]; ring)

theorem pack_boolean_bound {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (D : ℕ) (hD : 0 < D) (hB : CanonicalWord budget)
    (hBLattice : OnRationalLattice D (value budget)) (hBbox : 0 ≤ value budget ∧ value budget ≤ 1)
    (hLength : ∀ item, GoodTotal D budget (length item)) (items : List α) :
    (pack length budget items).2 ≤ (items.length - 1) * (20000 * (2 + 2 * binaryWordWidth D) ^ 3) := by
  cases items with
  | nil => simp [pack]
  | cons item rest =>
      simpa only [pack, List.length_cons, Nat.add_sub_cancel] using
        packAux_boolean_bound length budget D hD hB hBLattice hBbox hLength [item] (length item) rest (hLength item)

end Blotto.BinaryGreedyPackingWork
