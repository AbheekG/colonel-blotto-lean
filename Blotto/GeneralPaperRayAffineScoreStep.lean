import Blotto.GeneralPaperRayStableMinimum

/-! The actual parametric exact-score recurrence stores affine sums and
shared predecessors. One field gives at most K candidates per score. On
a bracket excluding its computed pair crossings, the selected stored layer
evaluates exactly to the ordinary complete DP layer at every interior point.
-/
namespace Blotto.GeneralPaperRayAffineScoreStep
open GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayStableMinimum
set_option autoImplicit false
set_option maxHeartbeats 3500000

abbrev Field (K : ℕ) := FixedArrayTable K (ℕ × Affine)
abbrev Table (S K : ℕ) := FixedArrayTable (S+1) (Option (Choice K))

def add (a b : Affine) : Affine := ⟨a.intercept+b.intercept,a.slope+b.slope⟩

theorem add_value (a b : Affine) (t : ℚ) : (add a b).value t=a.value t+b.value t := by
  dsimp only [add,Affine.value]
  ring

def extend {K : ℕ} (label : Fin K) (cost : Affine) (tail : Choice K) : Choice K :=
  ⟨add cost tail.expression,label::tail.labels⟩

theorem extend_data {K : ℕ} (label : Fin K) (cost : Affine) (tail : Choice K) (t : ℚ) :
    (extend label cost tail).atPoint t=GeneralPaperMinimum.extend label (cost.value t) (tail.atPoint t) := by
  change GeneralPaperMinimum.Selection.mk ((add cost tail.expression).value t) (label::tail.labels)=_
  rw [add_value]
  rfl

def fieldAt {K : ℕ} (field : Field K) (t : ℚ) : GeneralPaperExactScoreDP.Field K :=
  FixedArrayTable.ofFn (fun l => ((field.read l).1,(field.read l).2.value t))

def tableAt {S K : ℕ} (previous : Table S K) (t : ℚ) : FixedArrayTable (S+1) (Option (GeneralPaperMinimum.Selection K)) :=
  FixedArrayTable.ofFn (fun s => (previous.read s).map (fun c => c.atPoint t))

def candidate {S K : ℕ} (field : Field K) (previous : Table S K) (s : Fin (S+1)) (label : Fin K) : Option (Choice K) :=
  let data := field.read label
  if h : data.1≤s.val then
    (previous.read ⟨s.val-data.1,by omega⟩).map (extend label data.2)
  else none

def step {S K : ℕ} (sample : ℚ) (field : Field K) (previous : Table S K) : Table S K :=
  FixedArrayTable.ofFn (fun s => scan sample (candidate field previous s) (List.finRange K))

def crossings {S K : ℕ} (field : Field K) (previous : Table S K) : List ℚ :=
  GeneralPaperRayCrossingPairs.batch (expressions (candidate field previous))

theorem crossings_length {S K : ℕ} (field : Field K) (previous : Table S K) :
    (crossings field previous).length≤(S+1)*(K*K) := GeneralPaperRayCrossingPairs.batch_length _

theorem candidate_data {S K : ℕ} (field : Field K) (previous : Table S K) (t : ℚ) (s : Fin (S+1)) (label : Fin K) :
    (candidate field previous s label).map (fun c => c.atPoint t)=
      GeneralPaperExactScoreDP.candidate (fieldAt field t) (tableAt previous t) s label := by
  simp only [candidate,GeneralPaperExactScoreDP.candidate,fieldAt,tableAt,FixedArrayTable.read_ofFn]
  split
  · simp only [Option.map_map,Function.comp_def,extend_data]
  · rfl

theorem step_data {S K : ℕ} (field : Field K) (previous : Table S K) (lo hi sample t : ℚ)
    (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : ∀ c∈crossings field previous,¬(lo<c ∧ c<hi)) (s : Fin (S+1)) :
    ((step sample field previous).read s).map (fun c => c.atPoint t)=
      (GeneralPaperExactScoreDP.step (fieldAt field t) (tableAt previous t)).read s := by
  rw [step,FixedArrayTable.read_ofFn,batch_stable (candidate field previous) lo hi sample t hSample ht hNoCross s,scan_data]
  simp only [GeneralPaperExactScoreDP.step,FixedArrayTable.read_ofFn,candidate_data]

end Blotto.GeneralPaperRayAffineScoreStep
