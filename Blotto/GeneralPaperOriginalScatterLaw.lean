import Blotto.GeneralPaperOriginalFieldScatter

/-! The native selected-entry writes restore the exact original named
allocation and its hard at-most budget. The inverse equivalence below is
only an erased equality observer; the native routine never computes it. -/
namespace Blotto.GeneralPaperOriginalScatterLaw
open GeneralPaperOriginalFieldScatter GeneralPaperLightFieldIndexEquiv
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem cast_addCases {h g : ℕ} (kept : FixedArrayTable h ℚ) (light : FixedArrayTable g ℚ) (j : Fin (h+g)) :
    ((Fin.addCases kept.read light.read j:ℚ):ℝ)=Fin.addCases (fun i => (kept.read i:ℝ)) (fun i => (light.read i:ℝ)) j := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [Fin.addCases_left]
  · intro i
    simp only [Fin.addCases_right]

theorem data {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hBijective : Function.Bijective (mapping state)) :
    let e := Equiv.ofBijective (mapping state) hBijective
    (fun j => ((run indexCost A state kept light).1.read j:ℝ))=
      GeneralPaperFieldRelabel.allocation e.symm (Fin.addCases (fun i => (kept.read i:ℝ)) (fun i => (light.read i:ℝ))) := by
  let e := Equiv.ofBijective (mapping state) hBijective
  funext j
  have h := read_at indexCost A state kept light hBijective.1 (e.symm j)
  have he : mapping state (e.symm j)=j := e.apply_symm_apply j
  rw [he] at h
  change ((run indexCost A state kept light).1.read j:ℝ)=_
  rw [h,cast_addCases]
  rfl

theorem feasible {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hBijective : Function.Bijective (mapping state)) (B : ℝ)
    (h : Feasible B (Fin.addCases (fun i => (kept.read i:ℝ)) (fun i => (light.read i:ℝ)))) :
    Feasible B (fun j => ((run indexCost A state kept light).1.read j:ℝ)) := by
  rw [data indexCost A state kept light hBijective]
  exact (GeneralPaperFieldRelabel.feasible_iff (Equiv.ofBijective (mapping state) hBijective).symm B _).mpr h

theorem original_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k A : ℕ) (input : FixedArrayTable n ℚ)
    (kept : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size ℚ)
    (light : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.light.size ℚ) :
    (fun j => ((run (GeneralPaperSourceRowsExecution.index bits) A
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified kept light).1.read j:ℝ))=
      GeneralPaperFieldRelabel.allocation (originalEquiv bits model W k input).symm
        (Fin.addCases (fun i => (kept.read i:ℝ)) (fun i => (light.read i:ℝ))) :=
  data _ A _ kept light (original_bijective bits model W k input)

theorem models_data {n : ℕ} (indexCost indexCost' : ℕ → ℕ) (A A' : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ) :
    (run indexCost A state kept light).1=(run indexCost' A' state kept light).1 := by
  apply GeneralPaperIndexedScatter.data_congr
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [entry,Fin.addCases_left]
  · intro i
    simp only [entry,Fin.addCases_right]

theorem size {n : ℕ} (state : GeneralPaperLightFieldScan.State n)
    (hBijective : Function.Bijective (mapping state)) : state.heavy.size+state.light.size=n := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective (mapping state) hBijective)

theorem height {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hBijective : Function.Bijective (mapping state)) (H : ℕ)
    (hKept : ∀ i,RationalHeight (kept.read i) H) (hLight : ∀ i,RationalHeight (light.read i) H)
    (j : Fin n) : RationalHeight ((run indexCost A state kept light).1.read j) H := by
  obtain ⟨i,hi⟩ := hBijective.2 j
  rw [← hi,read_at indexCost A state kept light hBijective.1]
  refine Fin.addCases ?_ ?_ i
  · intro a
    simpa only [Fin.addCases_left] using hKept a
  · intro a
    simpa only [Fin.addCases_right] using hLight a

end Blotto.GeneralPaperOriginalScatterLaw
