import Blotto.PreparedSegmentDescriptorHeight
import Blotto.RationalArrayConstructionWork
import Blotto.IndexedLoopMetadataWork

/-! Eager descriptor construction prices index/capacity control and permits
full old-prefix payload copies for weights, endpoint rows and outer tables.
All slots, including zero-weight endpoints, are counted. Formula production,
factory frequency and physical address/record/ownership/space are separate. -/

namespace Blotto.PreparedSegmentDescriptor
open scoped BigOperators

def preparationMetadataBitWork {n k : ℕ} (primitive : ℕ → ℕ) (l : RationalSegmentLottery n k) : ℕ :=
  rationalArrayCopyWork (List.ofFn l.weight) 0 +
    (∑ slot : Fin k, (rationalArrayCopyWork (List.ofFn (l.P slot)) 0 + rationalArrayCopyWork (List.ofFn (l.Q slot)) 0)) +
      2 * k * (∑ slot : Fin k, ∑ j : Fin n, (rationalWordWidth (l.P slot j) + rationalWordWidth (l.Q slot j))) +
        3 * indexedLoopMetadataBitWork primitive 0 k + 2 * k * indexedLoopMetadataBitWork primitive 0 n

def preparationMetadataBound (c n k s : ℕ) : ℕ :=
  2 * k * (k * (1 + 2 * s)) + 4 * k * n * (n * (1 + 2 * s)) + 4 * k * k * (n * (1 + 2 * s)) +
    3 * indexedLoopMetadataBound c k + 2 * k * indexedLoopMetadataBound c n

theorem preparationMetadataBound_mono (c : ℕ) {n N k H s t : ℕ} (hn : n ≤ N) (hk : k ≤ H) (hs : s ≤ t) :
    preparationMetadataBound c n k s ≤ preparationMetadataBound c N H t := by
  have hRows := indexedLoopMetadataBound_mono c hn
  have hSlots := indexedLoopMetadataBound_mono c hk
  unfold preparationMetadataBound
  gcongr

theorem preparationMetadataBitWork_bound {n k : ℕ} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (l : RationalSegmentLottery n k) (s : ℕ) (h : l.HeightAt s) :
    preparationMetadataBitWork primitive l ≤ preparationMetadataBound c n k s := by
  let W := 1 + 2 * s
  have hArray : ∀ row : Fin n → ℚ, (∀ j, rationalWordWidth (row j) ≤ W) →
      rationalArrayCopyWork (List.ofFn row) 0 ≤ 2 * n * (n * W) := by
    intro row hRow
    have hc := rationalArrayCopyWork_bound (List.ofFn row) 0
    have hw := rationalWordWidth_sum_bound (List.ofFn row) W
      (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact hRow j)
    simp only [List.length_ofFn, Nat.zero_add] at hc hw
    exact hc.trans (Nat.mul_le_mul_left (2 * n) hw)
  have hWeights := rationalArrayCopyWork_bound (List.ofFn l.weight) 0
  have hWeightWords := rationalWordWidth_sum_bound (List.ofFn l.weight) W
    (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨slot, rfl⟩; exact rationalWordWidth_of_height (h.1 slot))
  simp only [List.length_ofFn, Nat.zero_add] at hWeights hWeightWords
  have hWeightCopy := hWeights.trans (Nat.mul_le_mul_left (2 * k) hWeightWords)
  have hRows : (∑ slot : Fin k, (rationalArrayCopyWork (List.ofFn (l.P slot)) 0 + rationalArrayCopyWork (List.ofFn (l.Q slot)) 0)) ≤
      4 * k * n * (n * W) := by
    calc
      _ ≤ ∑ _slot : Fin k, (4 * n * (n * W)) := Finset.sum_le_sum (fun slot _ => by
        have hp := hArray (l.P slot) (fun j => rationalWordWidth_of_height (h.2 slot j).1)
        have hq := hArray (l.Q slot) (fun j => rationalWordWidth_of_height (h.2 slot j).2)
        calc
          _ ≤ 2 * n * (n * W) + 2 * n * (n * W) := Nat.add_le_add hp hq
          _ = _ := by ring)
      _ = _ := by simp; ring
  have hOuter : (∑ slot : Fin k, ∑ j : Fin n, (rationalWordWidth (l.P slot j) + rationalWordWidth (l.Q slot j))) ≤ 2 * k * n * W := by
    calc
      _ ≤ ∑ _slot : Fin k, ∑ _j : Fin n, (2 * W) := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => by
        have hp := rationalWordWidth_of_height (h.2 slot j).1
        have hq := rationalWordWidth_of_height (h.2 slot j).2
        change rationalWordWidth (l.P slot j) + rationalWordWidth (l.Q slot j) ≤ 2 * W
        omega))
      _ = _ := by simp; ring
  have hOuterCopy : 2 * k * (∑ slot : Fin k, ∑ j : Fin n, (rationalWordWidth (l.P slot j) + rationalWordWidth (l.Q slot j))) ≤
      4 * k * k * (n * W) := by
    have hp := Nat.mul_le_mul_left (2 * k) hOuter
    nlinarith
  have hSlotLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive k
  have hRowLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive n
  have hSlotPrice := Nat.mul_le_mul_left 3 hSlotLoop
  have hRowPrice := Nat.mul_le_mul_left (2 * k) hRowLoop
  change preparationMetadataBitWork primitive l ≤
    2 * k * (k * W) + 4 * k * n * (n * W) + 4 * k * k * (n * W) +
      3 * indexedLoopMetadataBound c k + 2 * k * indexedLoopMetadataBound c n
  unfold preparationMetadataBitWork
  omega

end Blotto.PreparedSegmentDescriptor
