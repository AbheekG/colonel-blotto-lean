import Blotto.GeneralPaperCommonLatticeDPBits

/-! Complete-score DP followed by the actual strict high-score minimum scan.
The selected data and all deterministic cost ties are unchanged. Shared
lattice bounds price every candidate, selected cell and minimum comparison.
-/
namespace Blotto.GeneralPaperCommonLatticeMinimumBits
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreBitPrimitive
open GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {K : ℕ} (model : RationalCostModel) (W S h : ℕ) (fields : List (Field K)) :
    Option (Selection K) × ℕ :=
  let table := GeneralPaperScoreDPBits.runWithBits model W S fields
  let selected := scanRun model W
    (fun s => (GeneralPaperRayHighMinimum.candidate table.1 h s,12*W)) (List.finRange (S+1))
  (selected.1,table.2+selected.2+4*(S+1)*W+8*W)

theorem data {K : ℕ} (model : RationalCostModel) (W S h : ℕ) (fields : List (Field K)) :
    (run model W S h fields).1=
      scan (GeneralPaperRayHighMinimum.candidate (GeneralPaperExactScoreDP.run S fields) h)
        (List.finRange (S+1)) := by
  simp only [run,scan_data,GeneralPaperScoreDPBits.run_data]

theorem native_data {m K : ℕ} (model : RationalCostModel) (W S h : ℕ)
    (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ) :
    (run model W S h (fields scores costs)).1=GeneralPaperRayHighMinimum.minimum scores costs S h :=
  data model W S h _

theorem candidate_width {K : ℕ} (D M m S h : ℕ) (hD : 0<D) (fields : List (Field K))
    (hf : ∀ f∈fields,∀ l,Bounded D M (f.read l).2) (hLen : fields.length≤m) (s : Fin (S+1)) :
    Width (GeneralPaperRayHighMinimum.candidate (GeneralPaperExactScoreDP.run S fields) h s)
      (GeneralPaperCommonLatticeDPBits.width D M m) := by
  unfold GeneralPaperRayHighMinimum.candidate
  split
  · exact GeneralPaperCommonLatticeDPBits.run_width D M m S hD fields hf hLen s
  · intro chosen hc
    cases hc

theorem width {K : ℕ} (model : RationalCostModel) (W D M m S h : ℕ) (hD : 0<D)
    (fields : List (Field K)) (hf : ∀ f∈fields,∀ l,Bounded D M (f.read l).2) (hLen : fields.length≤m) :
    Width (run model W S h fields).1 (GeneralPaperCommonLatticeDPBits.width D M m) := by
  change Width (scanRun model W
    (fun s => (GeneralPaperRayHighMinimum.candidate
      (GeneralPaperScoreDPBits.runWithBits model W S fields).1 h s,12*W))
        (List.finRange (S+1))).1 _
  apply scan_width
  intro s _
  rw [GeneralPaperScoreDPBits.run_data]
  exact candidate_width D M m S h hD fields hf hLen s

def profile (r K S W P : ℕ) : ℕ :=
  GeneralPaperScoreDPBits.profile r K S W P+(S+1)*(28*W+P)+10*W

theorem work {K : ℕ} (model : RationalCostModel) (W D M m S h : ℕ) (hD : 0<D)
    (fields : List (Field K)) (hf : ∀ f∈fields,∀ l,Bounded D M (f.read l).2)
    (hLen : fields.length≤m) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (run model W S h fields).2≤
      profile fields.length K S W (model.rat (GeneralPaperCommonLatticeDPBits.width D M m)) := by
  have hd := GeneralPaperCommonLatticeDPBits.run_work model W D M m S hD fields hf hLen hW hIndex
  have hs := scan_work model W (GeneralPaperCommonLatticeDPBits.width D M m) (12*W)
    (fun s => (GeneralPaperRayHighMinimum.candidate
      (GeneralPaperScoreDPBits.runWithBits model W S fields).1 h s,12*W))
    (List.finRange (S+1))
    (by
      intro s _
      rw [GeneralPaperScoreDPBits.run_data]
      exact candidate_width D M m S h hD fields hf hLen s)
    (fun _ _ => le_rfl)
  simp only [List.length_finRange] at hs
  change (GeneralPaperScoreDPBits.runWithBits model W S fields).2+_+4*(S+1)*W+8*W≤_
  unfold profile
  nlinarith only [hd,hs]

end Blotto.GeneralPaperCommonLatticeMinimumBits
