import Blotto.GeneralPaperIndexedMinimumStorage
import Blotto.GeneralPaperScoreLifetimeStorage

/-! Native strict high-score minimum scan with its full returned DP table
resident. Score-cell indices and witness labels have independent arities.
All suspended witnesses, selected output, loop list, primitive scratch and
native wrapper counters are included. DP construction is a prior phase. -/
namespace Blotto.GeneralPaperHighMinimumStorage
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreSelectionStorage GeneralPaperScoreTableStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

theorem candidate_bounded {K S r P : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K)))
    (ht : ∀ s,Bounded r P (table.read s)) (h : ℕ) (s : Fin (S+1)) :
    Bounded r P (GeneralPaperRayHighMinimum.candidate table h s) := by
  unfold GeneralPaperRayHighMinimum.candidate
  split_ifs
  · exact ht s
  · intro a ha
    cases ha

def evaluate {K S : ℕ} (W : ℕ) (table : FixedArrayTable (S+1) (Option (Selection K))) (h : ℕ)
    (s : Fin (S+1)) : Option (Selection K)×ℕ := (GeneralPaperRayHighMinimum.candidate table h s,12*W)

def workCap (model : RationalCostModel) (W K S A r : ℕ) : ℕ :=
  GeneralPaperScoreLifetimeStorage.workCap model W K S A r+
    (S+1)*(28*W+model.rat (GeneralPaperScoreBitPrimitive.resourceWidth A r))+10*W

def metadataCap (model : RationalCostModel) (W K S A r : ℕ) : ℕ := S+1+workCap model W K S A r

def window {K : ℕ} (model : RationalCostModel) (W S h : ℕ) (inputs : List (Field K)) : ℕ :=
  let table := GeneralPaperScoreDPBits.runWithBits model W S inputs
  let selected := GeneralPaperScoreBitPrimitive.scanRun model W (evaluate W table.1 h) (List.finRange (S+1))
  let result := GeneralPaperCommonLatticeMinimumBits.run model W S h inputs
  tableFootprint W table.1+
    GeneralPaperIndexedMinimumStorage.trace model W (evaluate W table.1 h) (List.finRange (S+1))+
    GeneralPaperIndexedMinimumStorage.primitivePeak model W (evaluate W table.1 h) (List.finRange (S+1))+
    listFootprint W labelBits (List.finRange (S+1))+optionFootprint W result.1+
    fields W [h,S,table.2,selected.2,result.2,table.2+selected.2,table.2+selected.2+4*(S+1)*W]+256*W

def profile (model : RationalCostModel) (W K S A r : ℕ) : ℕ :=
  let P := GeneralPaperScoreBitPrimitive.resourceWidth A r
  tableProfile W K S r P+GeneralPaperIndexedMinimumStorage.profile W (S+1) K r P (12*W) (model.rat P)+
    (S+1)*(1+binaryWordWidth (S+1)+2*W)+32*W+optionProfile W K r P+
    7*(natBits (metadataCap model W K S A r)+W)+32*W+256*W

theorem bounded {K : ℕ} (model : RationalCostModel) (W S h A r : ℕ) (inputs : List (Field K))
    (hFields : CostHeight inputs A) (hLen : inputs.length≤r) (hh : h≤S)
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    window model W S h inputs≤profile model W K S A r := by
  let table := GeneralPaperScoreDPBits.runWithBits model W S inputs
  let e := evaluate W table.1 h
  let selected := GeneralPaperScoreBitPrimitive.scanRun model W e (List.finRange (S+1))
  have ht : ∀ s,Bounded r (GeneralPaperScoreBitPrimitive.resourceWidth A r) (table.1.read s) := by
    intro s
    dsimp only [table]
    rw [GeneralPaperScoreDPBits.run_data]
    exact run_bounded S A r inputs hFields hLen s
  have he : ∀ s,Bounded r (GeneralPaperScoreBitPrimitive.resourceWidth A r) (e s).1 :=
    fun s => candidate_bounded table.1 ht h s
  have hTable := table_bound W r _ table.1 ht
  have hScan := GeneralPaperIndexedMinimumStorage.complete_bound model W (12*W) e (List.finRange (S+1))
    (by rw [List.length_finRange]) (fun s _ => he s) (fun _ _ => le_rfl)
  have hLabels := list_bound W (1+binaryWordWidth (S+1)) labelBits (List.finRange (S+1)) (fun l _ => label_bound l)
  simp only [List.length_finRange] at hLabels
  have hOutput := native_scan_bounded model W e (List.finRange (S+1)) (fun s _ => he s)
  have hOutputBits := option_bound W r _ selected.1 hOutput
  have hDP := GeneralPaperScoreLifetimeStorage.run_work_bound model W S A r inputs hFields hLen hW hIndex
  have hScanWork := GeneralPaperScoreBitPrimitive.scan_work model W (GeneralPaperScoreBitPrimitive.resourceWidth A r) (12*W) e
    (List.finRange (S+1)) (fun s _ => GeneralPaperIndexedMinimumStorage.width_of_bounded (he s)) (fun _ _ => le_rfl)
  simp only [List.length_finRange] at hScanWork
  have hFull : table.2+selected.2+4*(S+1)*W+8*W≤workCap model W K S A r := by
    unfold workCap
    dsimp only [table,selected] at *
    nlinarith only [hDP,hScanWork]
  have hf := fields_bound W (natBits (metadataCap model W K S A r))
    [h,S,table.2,selected.2,table.2+selected.2+4*(S+1)*W+8*W,table.2+selected.2,table.2+selected.2+4*(S+1)*W] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap model W K S A r)+W)+32*W at hf
  change tableFootprint W table.1+GeneralPaperIndexedMinimumStorage.trace model W e (List.finRange (S+1))+
    GeneralPaperIndexedMinimumStorage.primitivePeak model W e (List.finRange (S+1))+
    listFootprint W labelBits (List.finRange (S+1))+optionFootprint W selected.1+
    fields W [h,S,table.2,selected.2,table.2+selected.2+4*(S+1)*W+8*W,
      table.2+selected.2,table.2+selected.2+4*(S+1)*W]+256*W≤_
  dsimp only [profile]
  omega

end Blotto.GeneralPaperHighMinimumStorage
