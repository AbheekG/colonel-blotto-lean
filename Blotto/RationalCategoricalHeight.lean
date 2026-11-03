import Blotto.RationalHeightSum
import Blotto.WordMachineWordHeight
import Blotto.WordMachineRunHeight
import Blotto.WordMachineIndexedHeight
import Blotto.RationalCategoricalLaw
import Blotto.RationalSegmentProgram
import Blotto.RationalLotteryHeight

/-! Complete categorical request-word bounds for the actual remaining-list
controller. Every branch and zero-mass state is covered; no positive lower
bound on a remaining weight or tail mass is imposed. -/

namespace Blotto

namespace RationalWeightList

def Bounded {α : Type*} (l : RationalWeightList α) (k s : ℕ) : Prop :=
  l.items.length ≤ k ∧ ∀ item ∈ l.items, RationalHeight item.2 s

theorem Bounded.mass_height {α : Type*} {l : RationalWeightList α} {k s : ℕ}
    (h : l.Bounded k s) : RationalHeight l.mass ((s + 1) * k + 1) := by
  have hSum := RationalHeight.list_sum (l := l.items.map Prod.snd) (s := s) (by
    intro q hq
    rcases List.mem_map.mp hq with ⟨item, hi, rfl⟩
    exact h.2 item hi)
  have hm : (s + 1) * (l.items.map Prod.snd).length + 1 ≤ (s + 1) * k + 1 := by
    rw [List.length_map]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left (s + 1) h.1) 1
  exact hSum.mono hm

end RationalWeightList

namespace CategoricalState

def Bounded {α : Type*} : CategoricalState α → ℕ → ℕ → Prop
  | .selected _, _, _ => True
  | .remaining l, k, s => l.Bounded k s

end CategoricalState

theorem categoricalTransition_bounded {α : Type*} (fallback : α) (k s : ℕ)
    (cursor : CategoricalState α) (hI : cursor.Bounded k s) :
    (categoricalTransition fallback cursor).Postcondition (fun c => c.Bounded k s) (fun _ => True) := by
  cases cursor with
  | selected value => trivial
  | remaining l =>
    cases l with
    | mk items hn =>
      cases items with
      | nil => trivial
      | cons head rest =>
        cases rest with
        | nil => trivial
        | cons next tail =>
          unfold categoricalTransition
          dsimp only
          split_ifs
          · change True ∧ ((next :: tail).length ≤ k ∧ ∀ item ∈ next :: tail, RationalHeight item.2 s)
            refine ⟨trivial, ?_, ?_⟩
            · have hLen := hI.1
              simp only [List.length_cons] at hLen ⊢
              omega
            · intro item hi
              exact hI.2 item (by simp [hi])
          · trivial

theorem categoricalTransition_wordsHeight {α : Type*} (fallback : α) (k s : ℕ)
    (cursor : CategoricalState α) (hI : cursor.Bounded k s) :
    (categoricalTransition fallback cursor).WordsHeight ((s + 1) * (k + 1)) := by
  cases cursor with
  | selected value => trivial
  | remaining l =>
    cases l with
    | mk items hn =>
      cases items with
      | nil => trivial
      | cons head rest =>
        cases rest with
        | nil => trivial
        | cons next tail =>
          have hHead : RationalHeight head.2 s := hI.2 head (by simp)
          have hMass := RationalWeightList.Bounded.mass_height (l := ⟨head :: next :: tail, hn⟩) hI
          have hRatio : RationalHeight (head.2 / (RationalWeightList.mk (head :: next :: tail) hn).mass)
              ((s + 1) * (k + 1)) := by
            have hDiv := hHead.div hMass
            convert hDiv using 1
            ring
          unfold categoricalTransition
          dsimp only
          split_ifs
          · apply ProbabilityWords.ofRat_height
            exact hRatio
          · trivial

theorem rationalWeightList_bounded {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (s : ℕ) (hHeight : ∀ j, RationalHeight (weight j) s) :
    (rationalWeightList weight hw).Bounded k s := by
  constructor
  · simp [rationalWeightList]
  · intro item hi
    rcases List.mem_ofFn.mp hi with ⟨j, rfl⟩
    exact hHeight j

theorem rationalCategorical_wordsHeight {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (s : ℕ) (hHeight : ∀ j, RationalHeight (weight j) s) (fallback : Fin k) :
    ((categoricalMachine fallback).specification (.remaining (rationalWeightList weight hw))).WordsHeight
      ((s + 1) * (k + 1)) := by
  exact (categoricalMachine fallback).specification_wordsHeight (fun c => c.Bounded k s) _
    (categoricalTransition_wordsHeight fallback k s) (categoricalTransition_bounded fallback k s)
    _ (rationalWeightList_bounded weight hw s hHeight)

theorem rationalCategorical_runWordsBounded {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (s : ℕ) (hHeight : ∀ j, RationalHeight (weight j) s) (fallback : Fin k) (R : ℕ) (bits : Fin R → Bool) :
    (categoricalMachine fallback).RunWordsBounded (fun c => c.Bounded k s) ((s + 1) * (k + 1)) R
      (.state (.remaining (rationalWeightList weight hw))) bits := by
  exact (categoricalMachine fallback).runCursor_wordsBounded (fun c => c.Bounded k s) _
    (categoricalTransition_wordsHeight fallback k s) (categoricalTransition_bounded fallback k s)
    R _ bits (rationalWeightList_bounded weight hw s hHeight)

theorem rationalCategorical_indexedWordsBounded {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (s : ℕ) (hHeight : ∀ j, RationalHeight (weight j) s) (fallback : Fin k) (R : ℕ) (bits : Fin R → Bool) :
    (categoricalMachine fallback).IndexedWordsBounded (fun c => c.Bounded k s) ((s + 1) * (k + 1)) R bits
      (.state (.remaining (rationalWeightList weight hw))) 0 (Nat.zero_le R) := by
  exact (categoricalMachine fallback).runCursorIndexed_wordsBounded (fun c => c.Bounded k s) _
    (categoricalTransition_wordsHeight fallback k s) (categoricalTransition_bounded fallback k s)
    R bits _ 0 (Nat.zero_le R) (rationalWeightList_bounded weight hw s hHeight)

namespace RationalSegmentLottery

theorem HeightAt.choice_wordsHeight {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (fallback : Fin k) :
    ((categoricalMachine fallback).specification l.start).WordsHeight ((s + 1) * (k + 1)) :=
  rationalCategorical_wordsHeight l.weight l.nonnegative s h.1 fallback

theorem HeightAt.choice_runWordsBounded {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (fallback : Fin k) (R : ℕ) (bits : Fin R → Bool) :
    (categoricalMachine fallback).RunWordsBounded (fun c => c.Bounded k s) ((s + 1) * (k + 1)) R
      (.state l.start) bits := rationalCategorical_runWordsBounded l.weight l.nonnegative s h.1 fallback R bits

theorem HeightAt.choice_indexedWordsBounded {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (fallback : Fin k) (R : ℕ) (bits : Fin R → Bool) :
    (categoricalMachine fallback).IndexedWordsBounded (fun c => c.Bounded k s) ((s + 1) * (k + 1)) R bits
      (.state l.start) 0 (Nat.zero_le R) :=
  rationalCategorical_indexedWordsBounded l.weight l.nonnegative s h.1 fallback R bits

end RationalSegmentLottery
end Blotto
