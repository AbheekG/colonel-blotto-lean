import Blotto.BinaryStoredOverlapEnvironment
import Blotto.BinaryResourceChoice
import Blotto.RationalCategoricalLaw

/-! Stored Boolean categorical weights compute remaining mass and head/total
probability through verified opcodes. Numeric weight lists and coin extraction
exist only in the proof view; runtime shares the unselected suffix list. -/

namespace Blotto.BinaryCategoricalPreparation
open BinaryRationalNormalization BinaryRationalEncoding

structure WeightList (α : Type*) where
  items : List (α×SignedWord)
  canonical : ∀ item∈items,CanonicalWord item.2
  nonnegative : ∀ item∈items,0≤value item.2

namespace WeightList

noncomputable def reference {α : Type*} (weights : WeightList α) : RationalWeightList α where
  items:=weights.items.map (fun item=>(item.1,value item.2))
  nonnegative:=by
    intro item hi
    obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hi
    exact weights.nonnegative source hs

def sumWords {α : Type*} : List (α×SignedWord)→SignedWord
  | []=>BinaryRationalOpcode.zero
  | item::rest=>BinaryRationalOpcode.apply .add item.2 (sumWords rest)

theorem sumWords_canonical {α : Type*} (items : List (α×SignedWord))
    (h : ∀ item∈items,CanonicalWord item.2) : CanonicalWord (sumWords items) := by
  induction items with
  | nil=>exact zero_canonical
  | cons item rest ih=>
      exact BinaryReflectedFourSetup.opcode_canonical .add _ _ (h item (by simp))
        (ih (fun next hn=>h next (by simp [hn])))

theorem sumWords_value {α : Type*} (items : List (α×SignedWord))
    (h : ∀ item∈items,CanonicalWord item.2) : value (sumWords items)=(items.map (fun item=>value item.2)).sum := by
  induction items with
  | nil=>exact BinaryRationalOpcode.zero_value
  | cons item rest ih=>
      have hr : ∀ next∈rest,CanonicalWord next.2:=fun next hn=>h next (by simp [hn])
      rw [sumWords,BinaryRationalOpcode.apply_value .add _ _ (h item (by simp)).1 (sumWords_canonical rest hr).1,
        ih hr]
      rfl

def mass {α : Type*} (weights : WeightList α) : SignedWord:=sumWords weights.items
theorem mass_canonical {α : Type*} (weights : WeightList α) : CanonicalWord weights.mass:=sumWords_canonical _ weights.canonical
theorem mass_value {α : Type*} (weights : WeightList α) : value weights.mass=weights.reference.mass:=by
  rw [mass,sumWords_value _ weights.canonical]
  simp only [reference,RationalWeightList.mass,List.map_map,Function.comp_def]

def tail {α : Type*} (head : α×SignedWord) (rest : List (α×SignedWord)) (weights : WeightList α)
    (h : weights.items=head::rest) : WeightList α :=
  ⟨rest,fun item hi=>weights.canonical item (by rw [h]; simp [hi]),
    fun item hi=>weights.nonnegative item (by rw [h]; simp [hi])⟩

def probability {α : Type*} (weights : WeightList α) (head : α×SignedWord) : SignedWord:=
  BinaryRationalOpcode.apply .div head.2 weights.mass

theorem probability_canonical {α : Type*} (weights : WeightList α) (head : α×SignedWord) (hh : head∈weights.items) :
    CanonicalWord (weights.probability head):=
  BinaryReflectedFourSetup.opcode_canonical .div _ _ (weights.canonical head hh) weights.mass_canonical

theorem probability_value {α : Type*} (weights : WeightList α) (head : α×SignedWord) (hh : head∈weights.items) :
    value (weights.probability head)=value head.2/weights.reference.mass:=by
  rw [probability,BinaryRationalOpcode.apply_value .div _ _ (weights.canonical head hh).1 weights.mass_canonical.1,mass_value]
  rfl

theorem probability_coprime {α : Type*} (weights : WeightList α) (head : α×SignedWord) (hh : head∈weights.items) :
    Nat.Coprime (BinaryBigEndian.littleValue (weights.probability head).numerator)
      (BinaryBigEndian.littleValue (weights.probability head).denominator):=
  BinaryRationalOpcode.canonicalize_coprime _ (BinaryRationalOpcode.rawApply_valid .div _ _
    (weights.canonical head hh).1 weights.mass_canonical.1)

theorem head_le_mass {α : Type*} (weights : WeightList α) (head : α×SignedWord) (rest : List (α×SignedWord))
    (h : weights.items=head::rest) : value head.2≤weights.reference.mass:=by
  rw [←weights.mass_value,mass,sumWords_value _ weights.canonical,h,List.map_cons,List.sum_cons]
  have ht : 0≤(rest.map (fun item=>value item.2)).sum:=by
    apply List.sum_nonneg
    intro q hq
    obtain ⟨item,hi,rfl⟩:=List.mem_map.mp hq
    exact weights.nonnegative item (by rw [h]; simp [hi])
  linarith

theorem probability_unit {α : Type*} (weights : WeightList α) (head : α×SignedWord) (rest : List (α×SignedWord))
    (h : weights.items=head::rest) (hm : 0<weights.reference.mass) :
    0≤value (weights.probability head) ∧ value (weights.probability head)≤1:=by
  rw [probability_value _ _ (by rw [h]; simp)]
  exact ⟨div_nonneg (weights.nonnegative head (by rw [h]; simp)) hm.le,(div_le_one hm).mpr (head_le_mass _ _ _ h)⟩

theorem probability_numbers {α : Type*} (weights : WeightList α) (head : α×SignedWord) (rest : List (α×SignedWord))
    (h : weights.items=head::rest) (hm : 0<weights.reference.mass) :
    let p:=ProbabilityWords.ofRat (value head.2/weights.reference.mass)
      ⟨div_nonneg (weights.nonnegative head (by rw [h]; simp)) hm.le,(div_le_one hm).mpr (head_le_mass _ _ _ h)⟩
    BinaryBigEndian.littleValue (weights.probability head).numerator=p.numerator ∧
      BinaryBigEndian.littleValue (weights.probability head).denominator=p.denominator:=by
  have hh : head∈weights.items:=by rw [h]; simp
  have hn:=BinaryRationalOpcode.value_num_den_of_coprime _ (weights.probability_canonical head hh).1
    (weights.probability_coprime head hh)
  rw [probability_value] at hn
  · constructor
    · change _=(value head.2/weights.reference.mass).num.toNat
      rw [←hn.1]
      exact ProbabilityWords.nonnegative_abs_eq_toNat _ (div_nonneg (weights.nonnegative head hh) hm.le)
    · exact hn.2.symm
  · exact hh

end WeightList

def positive (word : SignedWord) : Bool:=!BinaryRationalArithmetic.lessEqual word BinaryRationalOpcode.zero
theorem positive_iff (word : SignedWord) (h : CanonicalWord word) : positive word=true ↔ 0<value word:=by
  unfold positive
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  have he:=BinaryRationalArithmetic.lessEqual_iff word BinaryRationalOpcode.zero h.1 BinaryRationalOpcode.zero_valid
  rw [BinaryRationalOpcode.zero_value] at he
  exact (not_congr he).trans not_le

end Blotto.BinaryCategoricalPreparation
