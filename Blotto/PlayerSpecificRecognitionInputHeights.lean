import Blotto.PlayerSpecificRationalCellHeights

/-! All sweep sizes are derived from the actual encoded rational input,
with polynomial cell heights and no supplied coefficient-width promise. -/
namespace Blotto.PlayerSpecificRecognitionInputHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalSweepHeights
open PlayerSpecificRationalCellHeights PlayerSpecificSweep PlayerSpecificSweepBounds PlayerSpecificRationalCells
set_option autoImplicit false
set_option maxHeartbeats 2500000

def row {n : ℕ} (i : RationalPlayerSpecificInput n) : Data :=
  i.budget::(List.ofFn i.valuesA.weight++List.ofFn i.valuesB.weight)
def inputHeight {n : ℕ} (i : RationalPlayerSpecificInput n) : ℕ := PlayerSpecificRationalMagnitude.inputHeight (row i)
def cellHeight (n H : ℕ) : ℕ := 10*(n+1)*(H+1)

theorem input_positive {n : ℕ} (i : RationalPlayerSpecificInput n) : 1 ≤ inputHeight i := by
  unfold inputHeight PlayerSpecificRationalMagnitude.inputHeight
  omega

theorem original_fields {n : ℕ} (i : RationalPlayerSpecificInput n) :
    RationalHeight i.budget (inputHeight i) ∧
      (∀ j,RationalHeight (i.valuesA.weight j) (inputHeight i)) ∧
      ∀ j,RationalHeight (i.valuesB.weight j) (inputHeight i) := by
  have h:=PlayerSpecificRationalMagnitude.member_height (row i)
  refine ⟨h i.budget List.mem_cons_self,?_,?_⟩
  · intro j
    exact h _ (List.mem_cons_of_mem i.budget (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩)))
  · intro j
    exact h _ (List.mem_cons_of_mem i.budget (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)))

theorem sorted_fields {n : ℕ} (i : RationalPlayerSpecificInput n) :
    FieldsHeight (PlayerSpecificRationalIntervals.fields i) (inputHeight i) := by
  intro x hx
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hx
  exact ⟨(original_fields i).2.1 j,(original_fields i).2.2 j⟩

theorem profile (n H : ℕ) : initialBound n H+(3*H+1)*(n+1)≤cellHeight n H := by
  unfold initialBound cellHeight
  nlinarith

theorem cells {n : ℕ} (i : RationalPlayerSpecificInput n) :
    ∀ c∈PlayerSpecificRationalIntervals.run i,CellHeight c (cellHeight n (inputHeight i)) := by
  have hi:=initial_height (PlayerSpecificRationalIntervals.fields i) (inputHeight i) (sorted_fields i) (input_positive i)
  have hs:=suffix_height (PlayerSpecificRationalIntervals.fields i) (inputHeight i) (sorted_fields i) (input_positive i)
  have hlen : (suffixes (PlayerSpecificRationalIntervals.fields i)).2.1.length=n := by
    have h:=congrArg List.length (suffixes_fields (PlayerSpecificRationalIntervals.fields i))
    simpa only [List.length_map,PlayerSpecificRationalIntervals.fields_length] using h
  rw [PlayerSpecificRationalIntervals.fields_length] at hi
  have hb:=build_height (initial (PlayerSpecificRationalIntervals.fields i)) 0
    (suffixes (PlayerSpecificRationalIntervals.fields i)).2.1 (initialBound n (inputHeight i)) (inputHeight i) hi
    (zero_height.mono (by unfold initialBound; omega)) hs
  rw [hlen] at hb
  intro c hc
  exact mono c _ _ (hb c hc) (profile n (inputHeight i))

end Blotto.PlayerSpecificRecognitionInputHeights
