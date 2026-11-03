import Blotto.BinaryReflectedFourSetup
import Blotto.RationalActiveResources

/-! Three-resource Boolean states scan actual signed-word comparisons and
perform only the selected pair's two array writes. Their interpreted allocation
and active list match the retained rational initialization/update exactly.
This is the data/control stage; coin and terminal continuation execution are
separate stages of the small-branch sampler. -/

namespace Blotto.BinaryThreeResourceState
open BinaryRationalNormalization BinaryRationalEncoding

structure State where
  resource : FixedArrayTable 3 SignedWord
  active : List (Fin 3)

def fractional (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) : Bool :=
  (!BinaryRationalArithmetic.lessEqual (resource.read j) BinaryRationalOpcode.zero) &&
    (!BinaryRationalArithmetic.lessEqual (capacity.read j) (resource.read j))

theorem fractional_iff (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) (j : Fin 3) :
    fractional capacity resource j = true ↔ 0 < value (resource.read j) ∧ value (resource.read j) < value (capacity.read j) := by
  have h0 := BinaryRationalArithmetic.lessEqual_iff (resource.read j) BinaryRationalOpcode.zero (hR j).1 BinaryRationalOpcode.zero_valid
  have hc := BinaryRationalArithmetic.lessEqual_iff (capacity.read j) (resource.read j) (hC j).1 (hR j).1
  rw [BinaryRationalOpcode.zero_value] at h0
  unfold fractional
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    constructor
    · exact lt_of_not_ge (fun hp => by have he:=h0.mpr hp; rw [he] at h; simp at h)
    · exact lt_of_not_ge (fun hp => by have he:=hc.mpr hp; rw [he] at h; simp at h)
  · intro h
    constructor
    · cases he : BinaryRationalArithmetic.lessEqual (resource.read j) BinaryRationalOpcode.zero
      · rfl
      · exact False.elim (not_le.mpr h.1 (h0.mp he))
    · cases he : BinaryRationalArithmetic.lessEqual (capacity.read j) (resource.read j)
      · rfl
      · exact False.elim (not_le.mpr h.2 (hc.mp he))

def initial (capacity resource : FixedArrayTable 3 SignedWord) : State :=
  ⟨resource,(List.finRange 3).filter (fractional capacity resource)⟩

noncomputable def allocation (state : State) : Fin 3 → ℚ := fun j => value (state.resource.read j)

theorem initial_active (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) :
    (initial capacity resource).active =
      (RationalActiveResources.initial (fun j=>value (capacity.read j)) (fun j=>value (resource.read j))).active := by
  unfold initial RationalActiveResources.initial
  dsimp only
  apply congrArg (List.filter · (List.finRange 3))
  funext j
  have he := fractional_iff capacity resource hC hR j
  rw [RationalResourceArray.allocation_ofAllocation]
  apply Bool.eq_iff_iff.mpr
  simpa only [rationalFractionalAt_function,decide_eq_true_eq] using he

def update (capacity : FixedArrayTable 3 SignedWord) (state : State) (a b : Fin 3)
    (tail : List (Fin 3)) (chosen : SignedWord) : State :=
  let total := BinaryRationalOpcode.apply .add (state.resource.read a) (state.resource.read b)
  let second := BinaryRationalOpcode.apply .sub total chosen
  let next := (state.resource.write a chosen).write b second
  ⟨next,[a,b].filter (fractional capacity next) ++ tail⟩

theorem update_canonical (capacity : FixedArrayTable 3 SignedWord) (state : State) (a b : Fin 3)
    (tail : List (Fin 3)) (chosen : SignedWord)
    (hR : ∀ j, CanonicalWord (state.resource.read j)) (hChosen : CanonicalWord chosen) :
    ∀ j, CanonicalWord ((update capacity state a b tail chosen).resource.read j) := by
  have ht := BinaryReflectedFourSetup.opcode_canonical .add _ _ (hR a) (hR b)
  have hs := BinaryReflectedFourSetup.opcode_canonical .sub _ _ ht hChosen
  intro j
  unfold update
  dsimp only
  rw [FixedArrayTable.read_write,FixedArrayTable.read_write]
  split
  · exact hs
  · split
    · exact hChosen
    · exact hR j

theorem update_allocation (capacity : FixedArrayTable 3 SignedWord) (state : State) (a b : Fin 3)
    (tail : List (Fin 3)) (chosen : SignedWord)
    (hR : ∀ j, CanonicalWord (state.resource.read j)) (hChosen : CanonicalWord chosen) :
    allocation (update capacity state a b tail chosen) = Function.update (Function.update (allocation state) a (value chosen)) b
      (allocation state a+allocation state b-value chosen) := by
  have ht := BinaryRationalOpcode.apply_valid .add _ _ (hR a).1 (hR b).1
  funext j
  unfold allocation update
  dsimp only
  rw [FixedArrayTable.read_write,FixedArrayTable.read_write]
  simp only [Function.update_apply]
  split_ifs
  all_goals try rfl
  rw [BinaryRationalOpcode.apply_value .sub _ _ ht hChosen.1,
    BinaryRationalOpcode.apply_value .add _ _ (hR a).1 (hR b).1]
  rfl

theorem update_active (capacity : FixedArrayTable 3 SignedWord) (state : State) (a b : Fin 3)
    (tail : List (Fin 3)) (chosen : SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (state.resource.read j))
    (hChosen : CanonicalWord chosen) :
    (update capacity state a b tail chosen).active = [a,b].filter
      (fun j => decide (0 < allocation (update capacity state a b tail chosen) j ∧
        allocation (update capacity state a b tail chosen) j < value (capacity.read j))) ++ tail := by
  change ([a,b].filter (fractional capacity (update capacity state a b tail chosen).resource)) ++ tail = _
  apply congrArg (· ++ tail)
  apply congrArg (List.filter · [a,b])
  funext j
  apply Bool.eq_iff_iff.mpr
  change fractional capacity (update capacity state a b tail chosen).resource j=true ↔
    decide (0<value ((update capacity state a b tail chosen).resource.read j) ∧
      value ((update capacity state a b tail chosen).resource.read j)<value (capacity.read j))=true
  rw [decide_eq_true_eq]
  exact fractional_iff capacity _ hC (update_canonical capacity state a b tail chosen hR hChosen) j

end Blotto.BinaryThreeResourceState
