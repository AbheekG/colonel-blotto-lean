import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryQuadraticExpressionMeasured
import Blotto.BinaryQuadraticCategoricalLifetime

/-! Categorical preparation consumes the actual measured mass additions,
mass/zero comparison and reached probability division. The full preceding
preparation record/trace is preserved; unit-lattice inputs derive all widths
and source work. Native observers/references/allocator costs are separate. -/

namespace Blotto.BinaryQuadraticCategoricalMeasured
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalUnitLattice
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 3500000

def sumWithExtras {α : Type*} : List (α × SignedWord) → ((SignedWord × Trace) × ℕ) × ℕ
  | [] => (((zero,[.frames 1,.arrayAllocation 8]),4),0)
  | item::rest =>
      let produced := sumWithExtras rest
      let later := produced.1
      let added := BinaryNormalizedCoordinate.opcode .add item.2 later.1.1
      (((added.1.1.1,[.frames 1,.arrayAllocation 8]++under 1 later.1.2++under 1 added.1.1.2),
        later.2+added.1.2+8),produced.2+added.2)

def sum {α : Type*} : List (α × SignedWord) → (SignedWord × Trace) × ℕ :=
  fun items => (sumWithExtras items).1

theorem sumWithExtras_compat {α : Type*} (items : List (α × SignedWord)) :
    (sumWithExtras items).1 = sum items := rfl

theorem sum_nil {α : Type*} : sum ([] : List (α × SignedWord)) = ((zero,[.frames 1,.arrayAllocation 8]),4) := rfl

theorem sum_cons {α : Type*} (item : α × SignedWord) (rest : List (α × SignedWord)) :
    sum (item::rest) =
      let later := sum rest
      let added := BinaryPlannedQuadratic.apply .add item.2 later.1.1
      ((added.1.1,[.frames 1,.arrayAllocation 8]++under 1 later.1.2++under 1 added.1.2),later.2+added.2+8) := by
  simp only [sum,sumWithExtras,BinaryNormalizedCoordinate.opcode_record]


theorem sum_erases {α : Type*} (items : List (α × SignedWord)) :
    (sum items).1 = BinaryQuadraticCategoricalLifetime.sumWithTrace items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sum_nil,sum_cons,BinaryQuadraticCategoricalLifetime.sumWithTrace,ih,BinaryQuadraticMeasured.apply_erases]

theorem sum_data {α : Type*} (items : List (α × SignedWord)) (hc : ∀ item ∈ items,CanonicalWord item.2) :
    (sum items).1.1 = WeightList.sumWords items := by
  rw [sum_erases,BinaryQuadraticCategoricalLifetime.sumWithTrace_erases items hc]

def operandWidth (D : ℕ) : ℕ := 1+2*binaryWordWidth D
def sumStepPrice (D : ℕ) : ℕ := 11000*(operandWidth D+1)^2+8

theorem sum_work {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α) (h : UnitLattice D weights) :
    (sum weights.items).2 ≤ weights.items.length*sumStepPrice D+4 := by
  cases weights with
  | mk items hc hn =>
      induction items with
      | nil => simp [sum_nil,sum_cons]
      | cons item rest ih =>
          let weights : WeightList α := ⟨item::rest,hc,hn⟩
          let tail := weights.tail item rest rfl
          have ht := tail_unit D weights h item rest rfl
          have hRest := ih tail.canonical tail.nonnegative ht
          have hItem := item_width D hD weights h item (by simp [weights])
          have hMass := mass_width D hD tail ht
          have hTail : (sum rest).1.1 = tail.mass := sum_data rest tail.canonical
          have hOp := BinaryQuadraticMeasured.apply_bound .add item.2 tail.mass
          have hWidth : BinaryRationalArithmetic.pairWidth item.2 tail.mass+1 ≤ operandWidth D+1 := by
            unfold BinaryRationalArithmetic.pairWidth operandWidth
            omega
          have hPower := Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hWidth 2)
          dsimp only at hRest
          simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sum_nil,sum_cons,List.length_cons,hTail]
          unfold sumStepPrice at hRest ⊢
          nlinarith only [hRest,hOp,hPower]

set_option cleanup.letToHave false in
def prepareWithExtras {α : Type*} (fallback : α) (weights : WeightList α) : ((Preparation α × Trace) × ℕ) × ℕ :=
  match he : weights.items with
  | [] => (((.done fallback,[.frames 1,.arrayAllocation 8]),4),0)
  | [head] => (((.done head.1,[.frames 1,.arrayAllocation 8]),4),0)
  | head::next::tail =>
      let produced := sumWithExtras weights.items
      let computed := produced.1
      have hMass : computed.1.1 = weights.mass := sum_data weights.items weights.canonical
      let guard := BinaryQuadraticExpressionMeasured.compare computed.1.1 zero
      let common := [.frames 2,.arrayAllocation 16]++under 2 computed.1.2++under 2 guard.1.2
      if hp : (!guard.1.1) = true then
        let probability := BinaryNormalizedCoordinate.opcode .div head.2 computed.1.1
        (((.ask ⟨weights,head,next,tail,he,
          (by
            rw [← weights.mass_value,← hMass]
            apply (positive_iff computed.1.1 (hMass.symm ▸ weights.mass_canonical)).mp
            simpa only [guard,positive,BinaryQuadraticExpressionMeasured.compare_data] using hp),
          probability.1.1.1,(by
            dsimp only [probability]
            rw [BinaryNormalizedCoordinate.opcode_record,BinaryPlannedQuadratic.apply_previous,BinaryQuadraticMeasured.apply_erases,
              BinaryQuadraticLifetime.applyWithTrace_state .div _ _ (weights.canonical head (by rw [he]; simp)).1
                (hMass.symm ▸ weights.mass_canonical).1,hMass]
            rfl)⟩,common++under 2 probability.1.1.2),computed.2+guard.2+probability.1.2+12),produced.2+probability.2)
      else (((.done head.1,common),computed.2+guard.2+8),produced.2)

def prepare {α : Type*} (fallback : α) (weights : WeightList α) : (Preparation α × Trace) × ℕ :=
  (prepareWithExtras fallback weights).1

theorem prepareWithExtras_compat {α : Type*} (fallback : α) (weights : WeightList α) : (prepareWithExtras fallback weights).1 = prepare fallback weights := rfl

theorem prepare_record {α : Type*} (fallback : α) (weights : WeightList α) : prepare fallback weights =
  match he : weights.items with
  | [] => ((.done fallback,[.frames 1,.arrayAllocation 8]),4)
  | [head] => ((.done head.1,[.frames 1,.arrayAllocation 8]),4)
  | head::next::tail =>
      let computed := sum weights.items
      have hMass : computed.1.1 = weights.mass := sum_data weights.items weights.canonical
      let guard := BinaryQuadraticExpressionMeasured.compare computed.1.1 zero
      let common := [.frames 2,.arrayAllocation 16]++under 2 computed.1.2++under 2 guard.1.2
      if hp : (!guard.1.1) = true then
        let probability := BinaryPlannedQuadratic.apply .div head.2 computed.1.1
        ((.ask ⟨weights,head,next,tail,he,
          (by
            rw [← weights.mass_value,← hMass]
            apply (positive_iff computed.1.1 (hMass.symm ▸ weights.mass_canonical)).mp
            simpa only [guard,positive,BinaryQuadraticExpressionMeasured.compare_data] using hp),
          probability.1.1,(by
            dsimp only [probability]
            rw [BinaryPlannedQuadratic.apply_previous,BinaryQuadraticMeasured.apply_erases,
              BinaryQuadraticLifetime.applyWithTrace_state .div _ _ (weights.canonical head (by rw [he]; simp)).1
                (hMass.symm ▸ weights.mass_canonical).1,hMass]
            rfl)⟩,common++under 2 probability.1.2),computed.2+guard.2+probability.2+12)
      else ((.done head.1,common),computed.2+guard.2+8) := by
  cases weights with
  | mk items hc hn => cases items with
    | nil => rfl
    | cons head rest => cases rest with
      | nil => rfl
      | cons next tail =>
          dsimp only [prepare,prepareWithExtras,sum]
          split <;> simp only [BinaryNormalizedCoordinate.opcode_record]

theorem prepare_erases {α : Type*} (fallback : α) (weights : WeightList α) :
    (prepare fallback weights).1 = BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights := by
  cases weights with
  | mk items hc hn => cases items with
    | nil => rfl
    | cons head rest => cases rest with
      | nil => rfl
      | cons next tail =>
          rw [prepare_record]
          unfold BinaryQuadraticCategoricalLifetime.prepareWithTrace
          dsimp only
          simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sum_erases,BinaryQuadraticExpressionMeasured.compare_erases,BinaryQuadraticMeasured.apply_erases]
          split <;> rfl

def preparationPrice (D M : ℕ) : ℕ :=
  (M+1)*sumStepPrice D+BinaryQuadraticExpression.uniformPrice (binaryWordWidth D)+32

theorem prepare_work {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α) (weights : WeightList α)
    (h : UnitLattice D weights) (hM : weights.items.length ≤ M) :
    (prepare fallback weights).2 ≤ preparationPrice D M := by
  have hSum := sum_work D hD weights h
  have hMass := mass_width D hD weights h
  have hCompare : (BinaryQuadraticExpressionMeasured.compare weights.mass zero).2 ≤
      BinaryQuadraticExpression.uniformPrice (binaryWordWidth D) := by
    rw [BinaryQuadraticExpressionMeasured.compare_work]
    exact BinaryQuadraticExpression.comparePrice_bound _ _ _ hMass (by change 1 ≤ _; omega)
  have hTop := Nat.mul_le_mul_right (sumStepPrice D) hM
  rw [prepare_record]
  split
  · change 4 ≤ _
    unfold preparationPrice
    omega
  · change 4 ≤ _
    unfold preparationPrice
    omega
  · rename_i head next tail he
    dsimp only
    have hHead := item_width D hD weights h head (by rw [he]; simp)
    have hDiv := BinaryQuadraticMeasured.apply_bound .div head.2 weights.mass
    have hWidth : BinaryRationalArithmetic.pairWidth head.2 weights.mass+1 ≤ operandWidth D+1 := by
      unfold BinaryRationalArithmetic.pairWidth operandWidth
      omega
    have hPower := Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hWidth 2)
    simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,WeightList.mass] at hCompare hDiv hPower
    simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sum_data weights.items weights.canonical]
    split <;> unfold preparationPrice <;> rw [Nat.add_mul,Nat.one_mul] <;>
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sumStepPrice] at * <;> omega

theorem prepared_choice_weights {α : Type*} (fallback : α) (weights : WeightList α) (choice : Choice α)
    (h : (prepare fallback weights).1.1 = .ask choice) : choice.weights = weights := by
  have he : (BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).1 = .ask choice := by
    rw [← prepare_erases]
    exact h
  exact BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice he

end Blotto.BinaryQuadraticCategoricalMeasured
