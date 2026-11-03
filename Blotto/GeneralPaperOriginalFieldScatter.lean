import Blotto.GeneralPaperIndexedScatter

/-! Native original-field scatter from the retained heavy/light arrays.
A single branch reads the original key and the appropriate rational bid.
No inverse permutation, ordered metadata oracle or per-field search is run. -/
namespace Blotto.GeneralPaperOriginalFieldScatter
open GeneralPaperLightFieldScan GeneralPaperLightFieldOrder GeneralPaperLightFieldIndexEquiv
set_option autoImplicit false
set_option maxHeartbeats 2000000

def entry {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (j : Fin (state.heavy.size+state.light.size)) : (Fin n×ℚ)×ℕ :=
  let compare := GeneralPaperIntegerWordPrice.compare indexCost j.val state.heavy.size
  Fin.addCases (fun i => ((index state.heavy i,kept.read i),compare+64*A))
    (fun i => ((index state.light i,light.read i),compare+
      GeneralPaperNaturalPrimitivePrice.binary indexCost (fun a b => a-b) j.val state.heavy.size+64*A)) j

theorem entry_key {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (j : Fin (state.heavy.size+state.light.size)) : (entry indexCost A state kept light j).1.1=mapping state j := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [entry,Fin.addCases_left,mapping]
  · intro i
    simp only [entry,Fin.addCases_right,mapping]

theorem entry_value {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (j : Fin (state.heavy.size+state.light.size)) :
    (entry indexCost A state kept light j).1.2=Fin.addCases kept.read light.read j := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [entry,Fin.addCases_left]
  · intro i
    simp only [entry,Fin.addCases_right]

def run {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ) : FixedArrayTable n ℚ × ℕ :=
  GeneralPaperIndexedScatter.run indexCost A 0 (entry indexCost A state kept light)

theorem read_at {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hInjective : Function.Injective (mapping state)) (j : Fin (state.heavy.size+state.light.size)) :
    (run indexCost A state kept light).1.read (mapping state j)=Fin.addCases kept.read light.read j := by
  have hKey : (fun i => (entry indexCost A state kept light i).1.1)=mapping state := funext (entry_key indexCost A state kept light)
  have hInj : Function.Injective (fun i => (entry indexCost A state kept light i).1.1) := by rw [hKey];exact hInjective
  have h := GeneralPaperIndexedScatter.read_at indexCost A (0:ℚ) (entry indexCost A state kept light) hInj j
  rw [entry_key,entry_value] at h
  exact h

theorem entry_work {n : ℕ} (indexCost : ℕ → ℕ) (hMono : Monotone indexCost) (A : ℕ) (state : State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hControl : indexCost (1+binaryWordWidth (state.heavy.size+state.light.size))≤A)
    (j : Fin (state.heavy.size+state.light.size)) : (entry indexCost A state kept light j).2≤67*A := by
  let m := state.heavy.size+state.light.size
  have hCmp := GeneralPaperIntegerWordPrice.compare_le indexCost hMono j.val state.heavy.size (1+binaryWordWidth m)
    (Nat.add_le_add_left (binaryWordWidth_mono j.isLt.le) 1)
    (Nat.add_le_add_left (binaryWordWidth_mono (by dsimp only [m];omega)) 1)
  have hSub := GeneralPaperNaturalPrimitivePrice.binary_le indexCost hMono (fun a b => a-b) j.val state.heavy.size m
    j.isLt.le (by dsimp only [m];omega) (by omega)
  change indexCost (1+binaryWordWidth m)≤A at hControl
  have hCmp' := hCmp.trans hControl
  have hSub' := hSub.trans (Nat.mul_le_mul_left 2 hControl)
  revert hCmp' hSub'
  refine Fin.addCases ?_ ?_ j
  · intro i hCmp' hSub'
    simp only [entry,Fin.addCases_left]
    have h := hCmp'
    omega
  · intro i hCmp' hSub'
    simp only [entry,Fin.addCases_right]
    have h := hCmp'
    have hs := hSub'
    omega

theorem work {n : ℕ} (indexCost : ℕ → ℕ) (hMono : Monotone indexCost) (A : ℕ) (hA : 1≤A) (state : State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hControl : indexCost (1+binaryWordWidth (state.heavy.size+state.light.size))≤A)
    (hIndex : ∀ i≤n+state.heavy.size+state.light.size,indexCost (binaryWordWidth (i+1))≤A) :
    (run indexCost A state kept light).2≤(state.heavy.size+state.light.size)*(67*A)+
      192*(n+state.heavy.size+state.light.size+1)*A := by
  have h := GeneralPaperIndexedScatter.work indexCost A (67*A) hA (0:ℚ) (entry indexCost A state kept light)
    (entry_work indexCost hMono A state kept light hControl) (fun i hi => hIndex i (by omega))
  simpa only [run,Nat.add_assoc] using h

end Blotto.GeneralPaperOriginalFieldScatter
