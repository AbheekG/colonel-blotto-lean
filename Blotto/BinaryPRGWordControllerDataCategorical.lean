import Blotto.BinaryPRGWordControllerCategorical
import Blotto.BinaryPRGWordControllerDataCoin
import Blotto.BinaryQuadraticData

/-! The categorical data path executes structural list control, explicit
quadratic Boolean arithmetic and the data-only shared Boolean-PC coin. Work
annotations and numerical seed-position/length observers are absent. Universal
erasure gives the exact derived operational trace and aggregate component bound;
source-list construction and pointer/array/global-machine joins are separate. -/

namespace Blotto.BinaryPRGWordControllerDataCategorical
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryCategoricalPreparation BinaryCategoricalRun

abbrev Result (α : Type*) (store : Store) := Option α × FixedBinaryWord store.width

def sumWords {α : Type*} : List (α × SignedWord) → SignedWord
  | [] => BinaryRationalOpcode.zero
  | item :: rest => BinaryQuadraticData.apply .add item.2 (sumWords rest)

theorem sum_erasure {α : Type*} (items : List (α × SignedWord)) :
    (BinaryPRGWordControllerPreparation.sumWithWork items).1 = sumWords items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [BinaryPRGWordControllerPreparation.sumWithWork,sumWords]
      rw [ih,BinaryQuadraticData.apply_erasure]

def prepare {α : Type*} (fallback : α) (weights : WeightList α) : Preparation α :=
  match he : weights.items with
  | [] => .done fallback
  | [head] => .done head.1
  | head :: next :: tail =>
      let mass := sumWords weights.items
      have hMass : mass = weights.mass :=
        (sum_erasure weights.items).symm.trans
          (BinaryPRGWordControllerPreparation.sumWithWork_state weights.items weights.canonical)
      if hp : positive mass = true then
        let probability := BinaryQuadraticData.apply .div head.2 mass
        .ask ⟨weights,head,next,tail,he,
          (by rw [← weights.mass_value,← hMass];
              exact (positive_iff mass (hMass.symm ▸ weights.mass_canonical)).mp hp),
          probability,(by
            change BinaryQuadraticData.apply .div head.2 mass = weights.probability head
            rw [← BinaryQuadraticData.apply_erasure,BinaryQuadraticOpcode.applyWithWork_state .div _ _
              (weights.canonical head (by rw [he]; simp)).1 (hMass.symm ▸ weights.mass_canonical).1,hMass]
            rfl)⟩
      else .done head.1

theorem prepare_erasure {α : Type*} (fallback : α) (weights : WeightList α) :
    (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 = prepare fallback weights := by
  cases weights with
  | mk items hc hn =>
      cases items with
      | nil => rfl
      | cons head rest =>
          cases rest with
          | nil => rfl
          | cons next tail =>
              unfold BinaryPRGWordControllerPreparation.prepareWithWork prepare
              dsimp only
              simp only [sum_erasure]
              by_cases hp : positive (sumWords (head :: next :: tail)) = true
              · simp only [hp,dite_true,BinaryQuadraticData.apply_erasure]
              · simp only [hp,Bool.false_eq_true,dite_false]

theorem prepared_choice_weights {α : Type*} (fallback : α) (weights : WeightList α) (choice : Choice α)
    (h : prepare fallback weights = .ask choice) : choice.weights = weights :=
  BinaryPRGWordControllerPreparation.prepared_choice_weights fallback weights choice
    ((prepare_erasure fallback weights).trans h)

def run {α : Type*} (store : Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result α store :=
  match _hs : prepare fallback weights with
  | .done selected => (some selected,pc)
  | .ask choice =>
      let coin := BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp
      match coin.1 with
      | none => (none,coin.2)
      | some true => (some choice.head.1,coin.2)
      | some false => run store fallback choice.rest coin.2
          (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
termination_by weights.items.length
decreasing_by
  have hw := prepared_choice_weights fallback weights choice _hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem run_erasure {α : Type*} (store : Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerCategorical.run store fallback weights pc hp).1 = run store fallback weights pc hp := by
  conv_lhs => unfold BinaryPRGWordControllerCategorical.run
  conv_rhs => unfold run
  dsimp only
  rw [prepare_erasure]
  cases hs : prepare fallback weights with
  | done selected => rfl
  | ask choice =>
      dsimp only
      simp only [BinaryPRGWordControllerDataCoin.sample_erasure]
      cases hc : (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          cases branch
          · exact run_erasure store fallback choice.rest
              (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).2
              (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
          · rfl
termination_by weights.items.length
decreasing_by
  have hw := prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem run_contract {α : Type*} (D : ℕ) (hD : 0 < D) (store : Store) (fallback : α)
    (weights : WeightList α) (hUnit : BinaryCategoricalUnitLattice.UnitLattice D weights)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((run store fallback weights pc hp).1,(run store fallback weights pc hp).2.value) =
      BinaryCategoricalRun.runIndexed fallback store.cap.value (BinaryWordIndexCoinController.reader store)
        (.remaining weights) pc.value hp ∧
      ∃ work trace,
        BinaryPRGWordControllerCategorical.Execution store fallback weights pc hp
          (run store fallback weights pc hp,work) trace ∧
        work ≤ BinaryPRGWordControllerCategorical.bound D weights.items.length store.width
          ((run store fallback weights pc hp).2.value - pc.value) := by
  constructor
  · rw [← run_erasure]
    exact BinaryPRGWordControllerCategorical.run_state store fallback weights pc hp
  · obtain ⟨trace,hTrace⟩ := BinaryPRGWordControllerCategorical.run_has_execution store fallback weights pc hp
    refine ⟨(BinaryPRGWordControllerCategorical.run store fallback weights pc hp).2,trace,?_,?_⟩
    · rw [← run_erasure]
      exact hTrace
    · rw [← run_erasure]
      exact BinaryPRGWordControllerCategorical.run_bound D hD store fallback weights hUnit pc hp

theorem run_prepared_seed {α : Type*} (seed : List Bool) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord (BinarySeedLookupTree.prepare seed).width)
    (hp : pc.value ≤ (BinarySeedLookupTree.prepare seed).cap.value) :
    ((run (BinarySeedLookupTree.prepare seed) fallback weights pc hp).1,
      (run (BinarySeedLookupTree.prepare seed) fallback weights pc hp).2.value) =
      BinaryCategoricalRun.runIndexed fallback seed.length (fun index => seed.getD index.val false)
        (.remaining weights) pc.value (by simpa only [cap_value] using hp) := by
  rw [← run_erasure]
  exact BinaryPRGWordControllerCategorical.run_prepared_seed seed fallback weights pc hp

end Blotto.BinaryPRGWordControllerDataCategorical
