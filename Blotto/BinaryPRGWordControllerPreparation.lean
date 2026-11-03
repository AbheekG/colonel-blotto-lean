import Blotto.BinaryQuadraticOpcode
import Blotto.BinaryCategoricalPreparationWork

/-! Concrete remaining-mass and probability production for the Boolean-PC
categorical controller. The source list is traversed structurally; quadratic
Boolean rational opcodes produce exactly the retained canonical bytes. Actual
preparation/guard work is derived from the retained unit-lattice invariant,
without a probability-width or primitive-price oracle. -/

namespace Blotto.BinaryPRGWordControllerPreparation
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalUnitLattice

 def sumWithWork {α : Type*} : List (α × SignedWord) → SignedWord × ℕ
  | [] => (zero,1)
  | item :: rest =>
      let later := sumWithWork rest
      let added := BinaryQuadraticOpcode.applyWithWork .add item.2 later.1
      (added.1,added.2 + later.2 + 2)

 theorem sumWithWork_state {α : Type*} (items : List (α × SignedWord))
    (h : ∀ item ∈ items, CanonicalWord item.2) :
    (sumWithWork items).1 = WeightList.sumWords items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have hr : ∀ next ∈ rest, CanonicalWord next.2 := fun next hn => h next (by simp [hn])
      simp only [sumWithWork]
      rw [ih hr,BinaryQuadraticOpcode.applyWithWork_state .add _ _
        (h item (by simp)).1 (WeightList.sumWords_canonical rest hr).1]
      rfl

 theorem sumWithWork_bound {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α)
    (h : UnitLattice D weights) :
    (sumWithWork weights.items).2 ≤
      weights.items.length * (11000 * (2 + 2 * binaryWordWidth D)^2 + 2) + 1 := by
  cases weights with
  | mk items hc hn =>
      induction items with
      | nil => simp [sumWithWork]
      | cons item rest ih =>
          let weights : WeightList α := ⟨item :: rest,hc,hn⟩
          let tail := weights.tail item rest rfl
          have ht := tail_unit D weights h item rest rfl
          have hRest := ih tail.canonical tail.nonnegative ht
          have hItem := item_width D hD weights h item (by simp [weights])
          have hMass := mass_width D hD tail ht
          have hPair : BinaryRationalArithmetic.pairWidth item.2 tail.mass + 1 ≤ 2 + 2 * binaryWordWidth D := by
            unfold BinaryRationalArithmetic.pairWidth
            omega
          have hPrice := (BinaryQuadraticOpcode.applyWithWork_bound .add item.2 tail.mass).trans
            (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hPair 2))
          have hTail : (sumWithWork rest).1 = tail.mass := sumWithWork_state rest tail.canonical
          simp only [sumWithWork]
          rw [hTail]
          simp only [List.length_cons]
          nlinarith

 def prepareWithWork {α : Type*} (fallback : α) (weights : WeightList α) : Preparation α × ℕ :=
  match he : weights.items with
  | [] => (.done fallback,1)
  | [head] => (.done head.1,1)
  | head :: next :: tail =>
      let computed := sumWithWork weights.items
      have hMass : computed.1 = weights.mass := sumWithWork_state weights.items weights.canonical
      let guardWork := BinaryRationalArithmetic.lessEqualWork computed.1 zero
      if hp : positive computed.1 = true then
        let probability := BinaryQuadraticOpcode.applyWithWork .div head.2 computed.1
        (.ask ⟨weights,head,next,tail,he,
          (by rw [← weights.mass_value,← hMass];
              exact (positive_iff computed.1 (hMass.symm ▸ weights.mass_canonical)).mp hp),
          probability.1,(by
            rw [BinaryQuadraticOpcode.applyWithWork_state .div _ _
              (weights.canonical head (by rw [he]; simp)).1
              (hMass.symm ▸ weights.mass_canonical).1,hMass]
            rfl)⟩,
          computed.2 + guardWork + probability.2 + 4)
      else (.done head.1,computed.2 + guardWork + 3)

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
              have hs := sumWithWork_state (head :: next :: tail) hc
              simp only [hs]
              by_cases hp : positive (WeightList.sumWords (head :: next :: tail)) = true
              · simp only [WeightList.mass,hp,dite_true]
                have he := BinaryQuadraticOpcode.applyWithWork_state .div head.2
                  (WeightList.sumWords (head :: next :: tail)) (hc head (by simp)).1
                  (WeightList.sumWords_canonical _ hc).1
                simp only [he,WeightList.probability,WeightList.mass]
              · simp [WeightList.mass,hp]

 def preparationBound (D length : ℕ) : ℕ :=
  (length + 1) * (11000 * (2 + 2 * binaryWordWidth D)^2 + 2) +
    500 * (2 + 2 * binaryWordWidth D)^2 + 4

 theorem prepareWithWork_bound {α : Type*} (D : ℕ) (hD : 0 < D) (fallback : α)
    (weights : WeightList α) (h : UnitLattice D weights) :
    (prepareWithWork fallback weights).2 ≤ preparationBound D weights.items.length := by
  have hSum := sumWithWork_bound D hD weights h
  have hMass := mass_width D hD weights h
  have hZero : width zero ≤ 1 + 2 * binaryWordWidth D := by change 1 ≤ _; omega
  have hGuard := (BinaryRationalArithmetic.lessEqualWork_bound weights.mass zero).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by
      unfold BinaryRationalArithmetic.pairWidth
      omega : BinaryRationalArithmetic.pairWidth weights.mass zero + 1 ≤ 2 + 2 * binaryWordWidth D) 2))
  unfold prepareWithWork
  split
  · unfold preparationBound; omega
  · unfold preparationBound; omega
  · rename_i head next tail he
    dsimp only
    have hItem := item_width D hD weights h head (by rw [he]; simp)
    have hPair : BinaryRationalArithmetic.pairWidth head.2 weights.mass + 1 ≤ 2 + 2 * binaryWordWidth D := by
      unfold BinaryRationalArithmetic.pairWidth
      omega
    have hDiv := (BinaryQuadraticOpcode.applyWithWork_bound .div head.2 weights.mass).trans
      (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hPair 2))
    simp only [sumWithWork_state _ weights.canonical]
    change BinaryRationalArithmetic.lessEqualWork (WeightList.sumWords weights.items) zero ≤ _ at hGuard
    change (BinaryQuadraticOpcode.applyWithWork .div head.2 (WeightList.sumWords weights.items)).2 ≤ _ at hDiv
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

end Blotto.BinaryPRGWordControllerPreparation
