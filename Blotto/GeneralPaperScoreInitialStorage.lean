import Blotto.GeneralPaperThresholdScanStorage

/-! Native score-DP initial table: every reserved prefix, actual recursive
constructor frames and native work metadata. The zero-score empty witness
and all absent cells are included, before any nonempty DP layer executes. -/
namespace Blotto.GeneralPaperScoreInitialStorage
open GeneralPaperMinimum GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open GeneralPaperScoreSelectionStorage GeneralPaperScoreTableStorage GeneralPaperScoreConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def callback (W K S : ℕ) (s : Fin (S+1)) : Option (Selection K)×ℕ :=
  (if s.val=0 then some ⟨0,[]⟩ else none,2*W+3)

def window (model : RationalCostModel) (W K S count : ℕ) (hc : count≤S+1) : ℕ :=
  reservedFootprint W (S+1) (optionFootprint W)
      (PaperIndexedArrayConstruction.fill (fun w => w) W (callback W K S) count hc).1+
    constructorFrames (fun w => w) W W (callback W K S) count hc+
    fields W [S,K,count,(GeneralPaperScoreDPBits.initialRun model W K S).2]+128*W

def profile (W K S : ℕ) : ℕ :=
  tableProfile W K S 0 3+constructorProfile W (S+1) (GeneralPaperScoreDPBits.initialProfile S W)+
    4*(natBits (S+K+1+GeneralPaperScoreDPBits.initialProfile S W)+W)+32*W+128*W

theorem bounded (model : RationalCostModel) (W K S : ℕ) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (count : ℕ) (hc : count≤S+1) : window model W K S count hc≤profile W K S := by
  have hPrefix := initial_prefix model W K S count hc
  have hWork := GeneralPaperScoreDPBits.initial_work model W K S hW hIndex
  have hFrames := constructor_bound (fun w => w) W W (GeneralPaperScoreDPBits.initialProfile S W)
    (callback W K S) hWork count hc
  have hf := fields_bound W (natBits (S+K+1+GeneralPaperScoreDPBits.initialProfile S W))
    [S,K,count,(GeneralPaperScoreDPBits.initialRun model W K S).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (S+K+1+GeneralPaperScoreDPBits.initialProfile S W)+W)+32*W at hf
  have hAll := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hPrefix hFrames) hf) (128*W)
  exact hAll.trans_eq (by unfold profile; ring)

@[fun_prop]
theorem scaling (K S : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile W K S) := by
  unfold profile GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperScoreDPBits.initialProfile
  fun_prop

end Blotto.GeneralPaperScoreInitialStorage
