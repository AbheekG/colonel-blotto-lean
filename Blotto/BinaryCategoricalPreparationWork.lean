import Blotto.BinaryCategoricalUnitLattice

/-! Actual stored-word categorical preparation retains one computed mass and
uses it for the positive-mass guard and probability division. The result is the
original native preparation, while primitive arithmetic/comparison work is
derived from the closed fixed-D unit invariant. No new fallback or normalization
of supplied weights is introduced. Metadata/list/storage costs are separate. -/

namespace Blotto.BinaryCategoricalPreparationWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryCategoricalPreparation
open BinaryCategoricalRun BinaryCategoricalUnitLattice

def sumWithWork {α : Type*} : List (α × SignedWord) → SignedWord × ℕ
  | [] => (zero, 0)
  | item :: rest =>
      let later := sumWithWork rest
      let added := applyWithWork .add item.2 later.1
      (added.1, added.2 + later.2)

theorem sumWithWork_state {α : Type*} (items : List (α × SignedWord)) :
    (sumWithWork items).1 = WeightList.sumWords items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [sumWithWork, applyWithWork_state, ih, WeightList.sumWords]

theorem sumWithWork_bound {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α)
    (h : UnitLattice D weights) :
    (sumWithWork weights.items).2 ≤ weights.items.length * (12000 * (2 + 2 * binaryWordWidth D) ^ 3) := by
  cases weights with
  | mk items hc hn =>
      induction items with
      | nil => simp [sumWithWork]
      | cons item rest ih =>
          let weights : WeightList α := ⟨item :: rest, hc, hn⟩
          let tail := weights.tail item rest rfl
          have ht := tail_unit D weights h item rest rfl
          have hRest := ih tail.canonical tail.nonnegative ht
          have hItem := item_width D hD weights h item (by simp [weights])
          have hMass := mass_width D hD tail ht
          have hPrice := BinaryPRGPreparationWork.operation_uniform_bound .add item.2 tail.mass
            (1 + 2 * binaryWordWidth D) hItem hMass
          have hTailState : (sumWithWork rest).1 = tail.mass := sumWithWork_state rest
          simp only [sumWithWork]
          rw [hTailState]
          have hw : 1 + 2 * binaryWordWidth D + 1 = 2 + 2 * binaryWordWidth D := by omega
          rw [hw] at hPrice
          exact (Nat.add_le_add hPrice hRest).trans_eq (by simp only [List.length_cons]; ring)

def prepareWithWork {α : Type*} (fallback : α) (weights : WeightList α) : Preparation α × ℕ :=
  match he : weights.items with
  | [] => (.done fallback, 0)
  | [head] => (.done head.1, 0)
  | head :: next :: tail =>
      let computed := sumWithWork weights.items
      have hMass : computed.1 = weights.mass := sumWithWork_state weights.items
      let guardWork := BinaryRationalArithmetic.lessEqualWork computed.1 zero
      if hp : positive computed.1 = true then
        let probability := applyWithWork .div head.2 computed.1
        (.ask ⟨weights, head, next, tail, he,
          (by rw [← weights.mass_value, ← hMass]; exact (positive_iff computed.1 (hMass.symm ▸ weights.mass_canonical)).mp hp),
          probability.1, (by rw [applyWithWork_state, hMass]; rfl)⟩,
          computed.2 + guardWork + probability.2)
      else (.done head.1, computed.2 + guardWork)

theorem prepareWithWork_state {α : Type*} (fallback : α) (weights : WeightList α) :
    (prepareWithWork fallback weights).1 = BinaryCategoricalRun.prepare fallback weights := by
  cases weights with
  | mk items hc hn =>
      cases items with
      | nil => rfl
      | cons head rest =>
          cases rest with
          | nil => rfl
          | cons next tail =>
              unfold prepareWithWork BinaryCategoricalRun.prepare
              dsimp only
              simp only [sumWithWork_state, applyWithWork_state]
              by_cases hp : positive (WeightList.sumWords (head :: next :: tail)) = true
              · simp [WeightList.mass, WeightList.probability, hp]
              · simp [WeightList.mass, hp]

def preparationBound (D length : ℕ) : ℕ :=
  (length + 1) * (12000 * (2 + 2 * binaryWordWidth D) ^ 3) + 500 * (2 + 2 * binaryWordWidth D) ^ 2

theorem prepareWithWork_bound {α : Type*} (D : ℕ) (hD : 0 < D) (fallback : α) (weights : WeightList α)
    (h : UnitLattice D weights) : (prepareWithWork fallback weights).2 ≤ preparationBound D weights.items.length := by
  have hSum := sumWithWork_bound D hD weights h
  have hMass := mass_width D hD weights h
  have hZero : width zero ≤ 1 + 2 * binaryWordWidth D := by change 1 ≤ _; omega
  have hGuard := (BinaryRationalArithmetic.lessEqualWork_bound weights.mass zero).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hMass hZero) 1) 2))
  have hw : 1 + 2 * binaryWordWidth D + 1 = 2 + 2 * binaryWordWidth D := by omega
  rw [hw] at hGuard
  unfold prepareWithWork
  split
  · unfold preparationBound; exact Nat.zero_le _
  · unfold preparationBound; exact Nat.zero_le _
  · rename_i head next tail he
    dsimp only
    have hItem := item_width D hD weights h head (by rw [he]; simp)
    have hDiv := BinaryPRGPreparationWork.operation_uniform_bound .div head.2 weights.mass
      (1 + 2 * binaryWordWidth D) hItem hMass
    rw [hw] at hDiv
    change BinaryRationalArithmetic.lessEqualWork (WeightList.sumWords weights.items) zero ≤ _ at hGuard
    change (applyWithWork .div head.2 (WeightList.sumWords weights.items)).2 ≤ _ at hDiv
    simp only [sumWithWork_state]
    split <;> dsimp only <;> unfold preparationBound <;> nlinarith

theorem prepared_choice_weights {α : Type*} (fallback : α) (weights : WeightList α) (choice : Choice α)
    (h : (prepareWithWork fallback weights).1 = .ask choice) : choice.weights = weights := by
  have hs := prepareWithWork_state fallback weights
  rw [h] at hs
  unfold BinaryCategoricalRun.prepare at hs
  split at hs
  · cases hs
  · cases hs
  · dsimp only at hs
    split at hs
    · cases Preparation.ask.inj hs
      rfl
    · cases hs

end Blotto.BinaryCategoricalPreparationWork
