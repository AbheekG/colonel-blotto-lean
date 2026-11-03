import Blotto.GeneralPaperStorageCursorPacking

/-! Actual field-constructor counters embed into the closed frontier with
their values unchanged. Returned native partition sizes derive dynamic
cell/rank limits. Inclusive final counts and every native prefix index are
covered; no phase-width or partition-cap oracle is introduced. -/
namespace Blotto.GeneralPaperFieldPhaseCursorCoverage
open GeneralPaperCodeAlphabet GeneralPaperFiniteStorageWindows GeneralPaperStorageCursorPacking
open GeneralPaperFieldFamilyActiveStorage
open GeneralPaperCellPlanConstructionStorage (unsignedPart signedPart)
open GeneralPaperFieldPreparationPhaseStorage (children peak progressCap Progress)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem unsigned_count {k : ℕ} (model : RationalCostModel) (W U : ℕ)
    (cdfSummary tailSummary : GeneralPaperUnsignedCellConstancy.Summary k)
    (bids : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ) :
    (unsignedPart model W k U cdfSummary tailSummary bids).count≤GeneralPaperBatchCounterPrice.limit k := by
  have h := GeneralPaperUnsignedCellPartitionPrice.count_bound true (fun w => w) model.rat W U cdfSummary tailSummary bids
  change (unsignedPart model W k U cdfSummary tailSummary bids).count≤_ at h
  unfold GeneralPaperBatchCounterPrice.limit
  omega

theorem signed_count {k : ℕ} (model : RationalCostModel) (W U : ℕ)
    (summary : GeneralPaperUnsignedCellConstancy.Summary k)
    (bids : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ) :
    (signedPart model W k U summary bids).count≤GeneralPaperBatchCounterPrice.limit k := by
  have h := GeneralPaperSignedCellPartitionPrice.count_bound true (fun w => w) model.rat W U summary bids
  change (signedPart model W k U summary bids).count≤_ at h
  unfold GeneralPaperBatchCounterPrice.limit
  omega

theorem count_word_cap (k : ℕ) : GeneralPaperBatchCounterPrice.limit k+1≤progressCap k := by
  unfold GeneralPaperBatchCounterPrice.limit progressCap
  omega

theorem native_array_sizes (k : ℕ) :
    let S := (GeneralPaperSourceParameters.prepare k).summarySize
    S+(S+2)≤GeneralPaperBatchCounterPrice.limit k+1 ∧
      2*S≤GeneralPaperBatchCounterPrice.limit k+1 ∧
      2*(S+2)+1≤GeneralPaperBatchCounterPrice.limit k+1 ∧
      (2*S+(S+(S+2))+2)≤GeneralPaperBatchCounterPrice.limit k+1 ∧
      (2*(2*S)+(2*(S+2)+1)+2)≤GeneralPaperBatchCounterPrice.limit k+1 := by
  dsimp only
  unfold GeneralPaperBatchCounterPrice.limit
  omega

theorem visit_covered {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m) (progress : Progress k) :
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
      children model W a arrays candidate response mode j progress≤peak model W a arrays candidate response :=
  observed_le_maximum (GeneralPaperFieldPreparationPhaseStorage.visit model W a arrays candidate response)
    (counter m count hc,mode,j,progress)

theorem child_covered {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m) (progress : Progress k) (child : ℕ)
    (hchild : child≤children model W a arrays candidate response mode j progress) :
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+child≤
        peak model W a arrays candidate response :=
  (Nat.add_le_add_left hchild _).trans (visit_covered model W a arrays candidate response count hc mode j progress)

def lossAt {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (mode : Bool) (j : Fin m) (p : Progress k) : ℕ :=
  let S := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperQueryLossConstructionStorage.window model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j) (own arrays mode j)
    (min (p 0).val S) (min (p 1).val (S+1)) (Nat.min_le_right ..) (Nat.min_le_right ..)
    ⟨min (p 2).val S,Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

def incrementAt {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (mode : Bool) (j : Fin m) (p : Progress k) : ℕ :=
  GeneralPaperSignedUpdateConstructionStorage.window model W k (8*a.C) (own arrays mode j) (signed arrays mode j)
    (min (p 3).val (GeneralPaperSourceParameters.prepare k).summarySize) (Nat.min_le_right ..)

theorem loss_le_children {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (mode : Bool) (j : Fin m) (p : Progress k) : lossAt model W a arrays mode j p≤children model W a arrays candidate response mode j p := by
  dsimp only [lossAt,children]
  omega

theorem increment_le_children {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (mode : Bool) (j : Fin m) (p : Progress k) : incrementAt model W a arrays mode j p≤children model W a arrays candidate response mode j p := by
  dsimp only [incrementAt,children]
  omega

def unsignedAt {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (mode : Bool) (j : Fin m) (p : Progress k) : ℕ :=
  let S := (GeneralPaperSourceParameters.prepare k).summarySize
  let u := unsignedPart model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)
  GeneralPaperCellPlanConstructionStorage.unsignedWindow model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
    (options candidate response mode j) (min (p 0).val (S+(S+2))) (p 1).val (p 2).val (p 3).val
    (min (p 4).val u.count) (min (p 5).val u.count) (min (p 6).val u.count) (min (p 7).val (u.count+1))
    (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..)
    ⟨min (p 12).val u.count,Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

def signedAt {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (mode : Bool) (j : Fin m) (p : Progress k) : ℕ :=
  let S := (GeneralPaperSourceParameters.prepare k).summarySize
  let t := signedPart model W k (8*a.C) (own arrays mode j) (options candidate response mode j)
  GeneralPaperCellPlanConstructionStorage.signedWindow model W k (8*a.C) (own arrays mode j) (options candidate response mode j)
    (min (p 8).val (2*S)) (min (p 9).val (2*(S+2)+1)) (p 1).val (p 2).val (p 3).val
    (min (p 10).val t.count) (min (p 11).val t.count) (min (p 12).val t.count)
    (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..)

theorem unsigned_le_children {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (mode : Bool) (j : Fin m) (p : Progress k) :
    unsignedAt model W a arrays candidate response mode j p≤children model W a arrays candidate response mode j p := by
  dsimp only [unsignedAt,children]
  omega

theorem signed_le_children {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (mode : Bool) (j : Fin m) (p : Progress k) :
    signedAt model W a arrays candidate response mode j p≤children model W a arrays candidate response mode j p := by
  dsimp only [signedAt,children]
  omega

theorem unsigned_occurrence {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m) (cdfCount tailCount : ℕ)
    (hCDF : cdfCount≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (ht : tailCount≤(GeneralPaperSourceParameters.prepare k).summarySize+1)
    (q : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) :
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
      GeneralPaperQueryLossConstructionStorage.window model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
        (own arrays mode j) cdfCount tailCount hCDF ht q≤peak model W a arrays candidate response := by
  let values : Fin 13 → ℕ := fun i => if i.val=0 then cdfCount else if i.val=1 then tailCount else if i.val=2 then q.val else 0
  have hv : ∀ i,values i≤progressCap k := by
    intro i
    have hq := q.isLt
    dsimp only [values]
    split_ifs <;> unfold progressCap <;> omega
  let p : Progress k := vector (progressCap k) values hv
  apply child_covered model W a arrays candidate response count hc mode j p
  have h := loss_le_children model W a arrays candidate response mode j p
  have heq : lossAt model W a arrays mode j p=
      GeneralPaperQueryLossConstructionStorage.window model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
        (own arrays mode j) cdfCount tailCount hCDF ht q := by
    dsimp only [lossAt]
    congr 1
    · exact Nat.min_eq_left hCDF
    · exact Nat.min_eq_left ht
    · apply Fin.ext
      exact Nat.min_eq_left (Nat.le_of_lt_succ q.isLt)
  exact heq ▸ h

theorem signed_occurrence {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m) (signedCount : ℕ)
    (hs : signedCount≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
      GeneralPaperSignedUpdateConstructionStorage.window model W k (8*a.C) (own arrays mode j) (signed arrays mode j)
        signedCount hs≤peak model W a arrays candidate response := by
  let values : Fin 13 → ℕ := fun i => if i.val=3 then signedCount else 0
  have hv : ∀ i,values i≤progressCap k := by
    intro i
    dsimp only [values]
    split_ifs <;> unfold progressCap <;> omega
  let p : Progress k := vector (progressCap k) values hv
  apply child_covered model W a arrays candidate response count hc mode j p
  have h := increment_le_children model W a arrays candidate response mode j p
  have heq : incrementAt model W a arrays mode j p=
      GeneralPaperSignedUpdateConstructionStorage.window model W k (8*a.C) (own arrays mode j) (signed arrays mode j) signedCount hs := by
    dsimp only [incrementAt]
    congr 1
    exact Nat.min_eq_left hs
  exact heq ▸ h

theorem unsigned_cell {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m) (inputCount : ℕ)
    (usedP usedE copied : Fin (GeneralPaperBatchCounterPrice.limit k+2))
    (cellCount repCount cdfCount tailCount : ℕ)
    (hi : inputCount≤(GeneralPaperSourceParameters.prepare k).summarySize+((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hcu : cellCount≤(unsignedPart model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)).count)
    (hru : repCount≤(unsignedPart model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)).count)
    (hCDF : cdfCount≤(unsignedPart model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)).count)
    (ht : tailCount≤(unsignedPart model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)).count+1)
    (q : Fin ((unsignedPart model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)).count+1)) :
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
      GeneralPaperCellPlanConstructionStorage.unsignedWindow model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
        (options candidate response mode j) inputCount usedP.val usedE.val copied.val cellCount repCount cdfCount tailCount hi hcu hru hCDF ht q≤
      peak model W a arrays candidate response := by
  let values : Fin 13 → ℕ := fun i =>
    if i.val=0 then inputCount else if i.val=1 then usedP.val else if i.val=2 then usedE.val else if i.val=3 then copied.val
    else if i.val=4 then cellCount else if i.val=5 then repCount else if i.val=6 then cdfCount else if i.val=7 then tailCount
    else if i.val=12 then q.val else 0
  have hp := unsigned_count model W (8*a.C) (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)
  have hcap := count_word_cap k
  have hinput := hi.trans (native_array_sizes k).1
  have husedP := usedP.isLt
  have husedE := usedE.isLt
  have hcopied := copied.isLt
  have hq := q.isLt
  have hv : ∀ i,values i≤progressCap k := by
    intro i
    dsimp only [values]
    split_ifs <;> omega
  let p : Progress k := vector (progressCap k) values hv
  apply child_covered model W a arrays candidate response count hc mode j p
  have h := unsigned_le_children model W a arrays candidate response mode j p
  have heq : unsignedAt model W a arrays candidate response mode j p=
      GeneralPaperCellPlanConstructionStorage.unsignedWindow model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
        (options candidate response mode j) inputCount usedP.val usedE.val copied.val cellCount repCount cdfCount tailCount hi hcu hru hCDF ht q := by
    dsimp only [unsignedAt]
    congr 1
    · exact Nat.min_eq_left hi
    · exact Nat.min_eq_left hcu
    · exact Nat.min_eq_left hru
    · exact Nat.min_eq_left hCDF
    · exact Nat.min_eq_left ht
    · apply Fin.ext
      exact Nat.min_eq_left (Nat.le_of_lt_succ q.isLt)
  exact heq ▸ h

theorem signed_cell {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m) (positionCount extraCount : ℕ)
    (usedP usedE copied : Fin (GeneralPaperBatchCounterPrice.limit k+2)) (cellCount repCount rankCount : ℕ)
    (hp : positionCount≤2*(GeneralPaperSourceParameters.prepare k).summarySize)
    (he : extraCount≤2*((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (hcs : cellCount≤(signedPart model W k (8*a.C) (own arrays mode j) (options candidate response mode j)).count)
    (hrs : repCount≤(signedPart model W k (8*a.C) (own arrays mode j) (options candidate response mode j)).count)
    (hq : rankCount≤(signedPart model W k (8*a.C) (own arrays mode j) (options candidate response mode j)).count) :
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
      GeneralPaperCellPlanConstructionStorage.signedWindow model W k (8*a.C) (own arrays mode j) (options candidate response mode j)
        positionCount extraCount usedP.val usedE.val copied.val cellCount repCount rankCount hp he hcs hrs hq≤peak model W a arrays candidate response := by
  let values : Fin 13 → ℕ := fun i => if i.val=1 then usedP.val else if i.val=2 then usedE.val else if i.val=3 then copied.val
    else if i.val=8 then positionCount else if i.val=9 then extraCount else if i.val=10 then cellCount
    else if i.val=11 then repCount else if i.val=12 then rankCount else 0
  have hpart := signed_count model W (8*a.C) (own arrays mode j) (options candidate response mode j)
  have hcap := count_word_cap k
  have hposition := hp.trans (native_array_sizes k).2.1
  have hextra := he.trans (native_array_sizes k).2.2.1
  have husedP := usedP.isLt
  have husedE := usedE.isLt
  have hcopied := copied.isLt
  have hv : ∀ i,values i≤progressCap k := by
    intro i
    dsimp only [values]
    split_ifs <;> omega
  let p : Progress k := vector (progressCap k) values hv
  apply child_covered model W a arrays candidate response count hc mode j p
  have h := signed_le_children model W a arrays candidate response mode j p
  have heq : signedAt model W a arrays candidate response mode j p=
      GeneralPaperCellPlanConstructionStorage.signedWindow model W k (8*a.C) (own arrays mode j) (options candidate response mode j)
        positionCount extraCount usedP.val usedE.val copied.val cellCount repCount rankCount hp he hcs hrs hq := by
    dsimp only [signedAt]
    congr 1
    · exact Nat.min_eq_left hp
    · exact Nat.min_eq_left he
    · exact Nat.min_eq_left hcs
    · exact Nat.min_eq_left hrs
    · exact Nat.min_eq_left hq
  exact heq ▸ h

end Blotto.GeneralPaperFieldPhaseCursorCoverage
