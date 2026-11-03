import Blotto.GeneralPaperScoreStorageRates

/-! Native strict-threshold scan storage. The complete DP table remains
resident once; recursive scan frames retain only integer results/counters.
Rational comparison scratch is a separate maximum of one accepted-score
call. All actual work metadata is encoded through word lengths. -/
namespace Blotto.GeneralPaperThresholdScanStorage
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage
open GeneralPaperScoreSelectionStorage GeneralPaperScoreTableStorage GeneralPaperScoreConstructionStorage
open GeneralPaperThresholdScanBits
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

theorem accepted_bound {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (s : Fin (S+1)) :
    (acceptedRun model W table budget s).1≤S := by
  unfold acceptedRun
  cases table.read s with
  | none => exact Nat.zero_le _
  | some a =>
    change (if a.cost<budget then s.val else 0)≤S
    split_ifs <;> have hs := s.isLt <;> omega

theorem value_bound {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (xs : List (Fin (S+1))) :
    (scanRun model W table budget xs).1≤S := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons s rest ih => exact max_le (accepted_bound model W table budget s) ih

def cap (model : RationalCostModel) (W S H : ℕ) : ℕ :=
  S+1+(24*W+model.rat H)*(S+1)+2*W+(16*W+model.rat H)+4*(S+1)*W+4*W

theorem scan_work_cap {K S : ℕ} (model : RationalCostModel) (W H : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (xs : List (Fin (S+1)))
    (hLen : xs.length≤S+1) (ht : ∀ s,GeneralPaperScoreBitPrimitive.Width (table.read s) H)
    (hb : rationalWordWidth budget≤H) : (scanRun model W table budget xs).2≤cap model W S H := by
  have hw := scan_work model W H table budget xs ht hb
  have hm := Nat.mul_le_mul_left (24*W+model.rat H) hLen
  unfold cap
  omega

def trace {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) : List (Fin (S+1)) → ℕ
  | [] => fields W [0,2*W]+128*W
  | s::rest =>
    let current := acceptedRun model W table budget s
    let later := scanRun model W table budget rest
    let result := scanRun model W table budget (s::rest)
    fields W [(s::rest).length,s.val,current.1,current.2,later.1,later.2,result.1,result.2]+256*W+
      trace model W table budget rest

def frameProfile (model : RationalCostModel) (W S H : ℕ) : ℕ := 8*(natBits (cap model W S H)+W)+288*W

theorem trace_bound {K S : ℕ} (model : RationalCostModel) (W H : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (xs : List (Fin (S+1)))
    (hLen : xs.length≤S+1) (ht : ∀ s,GeneralPaperScoreBitPrimitive.Width (table.read s) H)
    (hb : rationalWordWidth budget≤H) : trace model W table budget xs≤(xs.length+1)*frameProfile model W S H := by
  induction xs with
  | nil =>
    have hf := two_fields_bound W (cap model W S H) 0 (2*W) (Nat.zero_le _) (by unfold cap; omega)
    change fields W [0,2*W]+128*W≤1*frameProfile model W S H
    unfold frameProfile
    omega
  | cons s rest ih =>
    have hl : rest.length≤S+1 := by simp only [List.length_cons] at hLen; omega
    have hRec := ih hl
    have hCurrent := accepted_bound model W table budget s
    have hCurrentWork := accepted_work model W H table budget s (ht s) hb
    have hLater := value_bound model W table budget rest
    have hResult := value_bound model W table budget (s::rest)
    have hLaterWork := scan_work_cap model W H table budget rest hl ht hb
    have hResultWork := scan_work_cap model W H table budget (s::rest) hLen ht hb
    have hf := fields_bound W (natBits (cap model W S H))
      [(s::rest).length,s.val,(acceptedRun model W table budget s).1,(acceptedRun model W table budget s).2,
        (scanRun model W table budget rest).1,(scanRun model W table budget rest).2,
        (scanRun model W table budget (s::rest)).1,(scanRun model W table budget (s::rest)).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · unfold cap; omega
      · have hs := s.isLt; unfold cap; omega
      · unfold cap; omega
      · unfold cap; omega
      · unfold cap; omega
      · exact hLaterWork
      · unfold cap; omega
      · exact hResultWork)
    change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (cap model W S H)+W)+32*W at hf
    have hFrame : fields W [(s::rest).length,s.val,(acceptedRun model W table budget s).1,
        (acceptedRun model W table budget s).2,(scanRun model W table budget rest).1,
        (scanRun model W table budget rest).2,(scanRun model W table budget (s::rest)).1,
        (scanRun model W table budget (s::rest)).2]+256*W≤frameProfile model W S H := by
      unfold frameProfile
      omega
    exact (Nat.add_le_add hFrame hRec).trans_eq (by rw [List.length_cons]; ring)

def primitivePeak {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) : List (Fin (S+1)) → ℕ
  | [] => 0
  | s::rest => max (acceptedRun model W table budget s).2 (primitivePeak model W table budget rest)

theorem primitive_bound {K S : ℕ} (model : RationalCostModel) (W H : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (xs : List (Fin (S+1)))
    (ht : ∀ s,GeneralPaperScoreBitPrimitive.Width (table.read s) H) (hb : rationalWordWidth budget≤H) :
    primitivePeak model W table budget xs≤16*W+model.rat H := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons s rest ih => exact max_le (accepted_work model W H table budget s (ht s) hb) ih

theorem return_work_cap {K S : ℕ} (model : RationalCostModel) (W H : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ)
    (ht : ∀ s,GeneralPaperScoreBitPrimitive.Width (table.read s) H) (hb : rationalWordWidth budget≤H) :
    (runWithBits model W table budget).2≤cap model W S H := by
  have hs := scan_work model W H table budget (List.finRange (S+1)) ht hb
  simp only [List.length_finRange] at hs
  change (scanRun model W table budget (List.finRange (S+1))).2+4*(S+1)*W+4*W≤_
  unfold cap
  nlinarith only [hs,Nat.zero_le S,Nat.zero_le (model.rat H)]

def window {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) : ℕ :=
  tableFootprint W table+rationalWordWidth budget+trace model W table budget (List.finRange (S+1))+
    primitivePeak model W table budget (List.finRange (S+1))+
    listFootprint W labelBits (List.finRange (S+1))+
    fields W [(runWithBits model W table budget).1,(runWithBits model W table budget).2]+64*W

def profile (model : RationalCostModel) (W K S r P H : ℕ) : ℕ :=
  tableProfile W K S r P+H+(S+2)*frameProfile model W S H+(16*W+model.rat H)+
    (S+1)*(1+binaryWordWidth (S+1)+2*W)+32*W+2*(natBits (cap model W S H)+W)+32*W+64*W

theorem bounded {K S : ℕ} (model : RationalCostModel) (W r P H : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ)
    (ht : ∀ s,Bounded r P (table.read s)) (hPH : P≤H) (hb : rationalWordWidth budget≤H) :
    window model W table budget≤profile model W K S r P H := by
  have hT := table_bound W r P table ht
  have hWidth : ∀ s,GeneralPaperScoreBitPrimitive.Width (table.read s) H :=
    fun s a ha => (ht s a ha).2.trans hPH
  have hTrace := trace_bound model W H table budget (List.finRange (S+1)) (by rw [List.length_finRange]) hWidth hb
  simp only [List.length_finRange,Nat.add_assoc,Nat.reduceAdd] at hTrace
  have hPrimitive := primitive_bound model W H table budget (List.finRange (S+1)) hWidth hb
  have hLabels := list_bound W (1+binaryWordWidth (S+1)) labelBits (List.finRange (S+1)) (fun l _ => label_bound l)
  simp only [List.length_finRange] at hLabels
  have hValue : (runWithBits model W table budget).1≤S := value_bound model W table budget _
  have hWork := return_work_cap model W H table budget hWidth hb
  have hFields := two_fields_bound W (cap model W S H) (runWithBits model W table budget).1
    (runWithBits model W table budget).2 (by unfold cap; omega) hWork
  unfold window profile
  omega

end Blotto.GeneralPaperThresholdScanStorage
