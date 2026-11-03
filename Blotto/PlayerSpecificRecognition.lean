import Blotto.PlayerSpecificRootSearch

/-! Soundness and completeness of the full interval/breakpoint search on
sorted field identifiers. The concrete rational sorting/preparation join is
separate; no finite-bit root-isolation claim is made by this real-RAM search. -/
namespace Blotto.PlayerSpecificRecognition
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificSweepBounds
open PlayerSpecificCells PlayerSpecificCellCandidates
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def ValidParameters {n : ℕ} (v w : Values n) (b gamma scale : ℝ) : Prop :=
  0<gamma ∧ 0<scale ∧
  (∑ j,PlayerSpecificMarginals.probA (v.weight j) (w.weight j) gamma*
    PlayerSpecificMarginals.length (v.weight j) (w.weight j) gamma scale)=2 ∧
  (∑ j,PlayerSpecificMarginals.probB (v.weight j) (w.weight j) gamma*
    PlayerSpecificMarginals.length (v.weight j) (w.weight j) gamma scale)=2*b ∧
  ∀ j,PlayerSpecificMarginals.length (v.weight j) (w.weight j) gamma scale≤b

noncomputable def toInput {n : ℕ} (v w : Values n) (b gamma scale : ℝ) (hb : 0<b) (hb1 : b≤1)
    (h : ValidParameters v w b gamma scale) : PlayerSpecificInput n where
  valuesA := v
  valuesB := w
  budget := b
  gamma := gamma
  scale := scale
  budget_pos := hb
  budget_le := hb1
  gamma_pos := h.1
  scale_pos := h.2.1
  meanA := h.2.2.1
  meanB := h.2.2.2.1
  endpoint := h.2.2.2.2

noncomputable def intervals {n : ℕ} (v w : Values n) (ids : List (Fin n)) : List Cell :=
  let fields := ids.map (fun j => (v.weight j,w.weight j))
  (build (initial fields) 0 (suffixes fields).2.1).1

theorem intervals_fit {n : ℕ} (v w : Values n) (ids : List (Fin n))
    (hp : ids.Perm (List.finRange n))
    (hs : ids.Pairwise (fun j k => v.weight j/w.weight j≤v.weight k/w.weight k)) :
    ∀ c∈intervals v w ids,∃ low high,(low++high).Perm (List.finRange n) ∧ Fits v.weight w.weight low high c := by
  apply fits_all v.weight w.weight [] ids (initial (ids.map (fun j => (v.weight j,w.weight j)))) 0
  · simpa only [List.nil_append] using hp
  · exact initial_full _
  · simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  · intro j _
    exact (div_pos (v.positive j) (w.positive j)).le
  · exact hs

theorem cell_nonzero {n : ℕ} (v w : Values n) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (c : Cell) (hf : Fits v.weight w.weight low high c) (b : ℝ) :
    PlayerSpecificPolynomial.polynomial c.state.coefficients b≠0 := by
  rw [PlayerSpecificSweepIndexed.coefficients_eq v.weight w.weight c.state low high hp hf.1.1]
  exact PlayerSpecificPolynomial.nonzero v.weight w.weight _ b
    (PlayerSpecificAcceptance.count_positive v) v.positive w.positive

theorem cell_sound {n : ℕ} (v w : Values n) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (c : Cell) (hf : Fits v.weight w.weight low high c)
    (b gamma : ℝ) (hb : 0<b) (hm : gamma∈candidates c b) (hpass : Passes c b gamma) :
    ValidParameters v w b gamma (candidateScale c.state.coefficients b gamma) := by
  have hroot := PlayerSpecificCellCandidates.sound c b gamma (cell_nonzero v w low high hp c hf b) hm
  have hcoeff := PlayerSpecificSweepIndexed.coefficients_eq v.weight w.weight c.state low high hp hf.1.1
  have hresp := fits_respects v.weight w.weight low high hp c hf gamma hroot.1 w.positive
  have hscale := PlayerSpecificCandidate.scale_positive v.weight w.weight (PlayerSpecificSweepIndexed.highMask high)
    b gamma (PlayerSpecificAcceptance.count_positive v) v.positive w.positive hb hroot.1.1
  have hmeans := PlayerSpecificCandidate.candidate_means v.weight w.weight (PlayerSpecificSweepIndexed.highMask high)
    b gamma (PlayerSpecificAcceptance.count_positive v) v.positive w.positive hb hroot.1.1 hresp
    (by rw [← hcoeff]; exact hroot.2)
  rw [← hcoeff] at hscale hmeans
  exact ⟨hroot.1.1,hscale,hmeans.1,hmeans.2,(gate_iff v w low high hp c hf b gamma hb hroot.1).mp hpass⟩

theorem sound {n : ℕ} (v w : Values n) (ids : List (Fin n))
    (hp : ids.Perm (List.finRange n))
    (hs : ids.Pairwise (fun j k => v.weight j/w.weight j≤v.weight k/w.weight k))
    (b gamma : ℝ) (hb : 0<b) (c : Cell)
    (h : (PlayerSpecificRootSearch.run b (intervals v w ids)).1=some (c,gamma)) :
    ValidParameters v w b gamma (candidateScale c.state.coefficients b gamma) := by
  have hrun := PlayerSpecificRootSearch.sound b (intervals v w ids) c gamma h
  rcases intervals_fit v w ids hp hs c hrun.1 with ⟨low,high,hperm,hfit⟩
  exact cell_sound v w low high hperm c hfit b gamma hb hrun.2.1 hrun.2.2

theorem complete_input {n : ℕ} (i : PlayerSpecificInput n) (ids : List (Fin n))
    (hp : ids.Perm (List.finRange n))
    (hs : ids.Pairwise (fun j k => i.valuesA.weight j/i.valuesB.weight j ≤ i.valuesA.weight k/i.valuesB.weight k)) :
    ∃ chosen,(PlayerSpecificRootSearch.run i.budget (intervals i.valuesA i.valuesB ids)).1=some chosen := by
  rcases covers (initial (ids.map (fun j => (i.valuesA.weight j,i.valuesB.weight j))))
      0 i.gamma (ids.map (fun j => (i.valuesA.weight j,i.valuesB.weight j))) i.gamma_pos i.gamma_pos with
    ⟨c,hcell,hr,hl⟩
  change c∈intervals i.valuesA i.valuesB ids at hcell
  rcases intervals_fit i.valuesA i.valuesB ids hp hs c hcell with ⟨low,high,hperm,hfit⟩
  have hcoeff := PlayerSpecificSweepIndexed.coefficients_eq i.valuesA.weight i.valuesB.weight c.state low high hperm hfit.1.1
  have hresp := fits_respects i.valuesA.weight i.valuesB.weight low high hperm c hfit i.gamma hr i.valuesB.positive
  have hroot := (PlayerSpecificCandidate.root_iff_means i.valuesA.weight i.valuesB.weight
    (PlayerSpecificSweepIndexed.highMask high) i.budget i.gamma i.scale i.valuesA.positive i.valuesB.positive
    i.budget_pos i.gamma_pos i.scale_pos hresp).mp ⟨i.meanA,i.meanB⟩
  rw [← hcoeff] at hroot
  have hmem := PlayerSpecificCellCandidates.complete c i.budget i.gamma
    (cell_nonzero i.valuesA i.valuesB low high hperm c hfit i.budget) hr hl hroot.1
  have hpass : Passes c i.budget i.gamma := by
    apply (gate_iff i.valuesA i.valuesB low high hperm c hfit i.budget i.gamma i.budget_pos hr).mpr
    rw [← hroot.2]
    exact i.endpoint
  exact PlayerSpecificRootSearch.complete i.budget (intervals i.valuesA i.valuesB ids) c i.gamma hcell hmem hpass

theorem complete {n : ℕ} (v w : Values n) (ids : List (Fin n))
    (hp : ids.Perm (List.finRange n))
    (hs : ids.Pairwise (fun j k => v.weight j/w.weight j≤v.weight k/w.weight k))
    (b gamma scale : ℝ) (hb : 0<b) (hb1 : b≤1) (h : ValidParameters v w b gamma scale) :
    ∃ chosen,(PlayerSpecificRootSearch.run b (intervals v w ids)).1=some chosen :=
  complete_input (toInput v w b gamma scale hb hb1 h) ids hp hs

theorem rejection_iff {n : ℕ} (v w : Values n) (ids : List (Fin n))
    (hp : ids.Perm (List.finRange n))
    (hs : ids.Pairwise (fun j k => v.weight j/w.weight j≤v.weight k/w.weight k))
    (b : ℝ) (hb : 0<b) (hb1 : b≤1) :
    (PlayerSpecificRootSearch.run b (intervals v w ids)).1=none ↔
      ¬∃ gamma scale,ValidParameters v w b gamma scale := by
  constructor
  · intro hn ⟨gamma,scale,hp'⟩
    rcases complete v w ids hp hs b gamma scale hb hb1 hp' with ⟨chosen,hchosen⟩
    rw [hn] at hchosen
    cases hchosen
  · intro hn
    cases he : (PlayerSpecificRootSearch.run b (intervals v w ids)).1 with
    | none => rfl
    | some chosen =>
      exact False.elim (hn ⟨chosen.2,candidateScale chosen.1.state.coefficients b chosen.2,
        sound v w ids hp hs b chosen.2 hb chosen.1 he⟩)

end Blotto.PlayerSpecificRecognition
