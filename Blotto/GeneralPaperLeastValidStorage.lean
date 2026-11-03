import Blotto.GeneralPaperCodeScanStorage

/-! Five-candidate least-valid lookup and half-open-cell wrapper. The one
starting split derives the actual five-code list and every decoder cap.
Empty cells stop before child execution; no valid-code or space oracle enters. -/
namespace Blotto.GeneralPaperLeastValidStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def pointWindow (model : RationalCostModel) (W bucket : ℕ) : ℕ :=
  listFootprint W natBits (GeneralPaperLeastValidPointsPrice.run model.rat W bucket).1+
    fields W [4,bucket,4*bucket,4*bucket+1,4*bucket+2,4*bucket+3,4*bucket+4]+
    (GeneralPaperLeastValidPointsPrice.run model.rat W bucket).2+128*W

def pointProfile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  12*operandWidth a.lambda+416*W+10*model.rat (operandWidth a.lambda)

theorem point_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (bucket : ℕ) (hb : bucket≤a.C) :
    pointWindow model W bucket≤pointProfile model W a := by
  have hl := list_bound W (operandWidth a.lambda) natBits (GeneralPaperLeastValidPointsPrice.run model.rat W bucket).1
    (fun code hc => code_word a code (GeneralPaperLeastValidPointsPrice.point_bound model.rat W a bucket hb code hc))
  rw [GeneralPaperLeastValidPointsPrice.length] at hl
  have hC := a.scalePositive
  have hf := fields_bound W (operandWidth a.lambda) [4,bucket,4*bucket,4*bucket+1,4*bucket+2,4*bucket+3,4*bucket+4] (by
    intro x hx
    apply code_word a x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change _≤7*(operandWidth a.lambda+W)+32*W at hf
  have hp := GeneralPaperLeastValidPointsPrice.bit_work model W a bucket hb
  unfold pointWindow pointProfile
  omega

theorem returned (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperCodeRecordStorage.scanRecord W (GeneralPaperLeastValidExecution.run true model W a response lo hi).1≤
      4*operandWidth a.lambda+112*W+1 := by
  apply GeneralPaperCodeRecordStorage.scan_record W a response
  · intro e he
    have hb := GeneralPaperLeastValidExecution.best true model W a response lo hi
    rw [he] at hb
    exact hb.1.2.2
  · have h := GeneralPaperLeastValidPrice.native_work true model W a response lo hi
    unfold metadataCap
    omega

def childWindow (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) : ℕ :=
  let split := (GeneralPaperCodeSplitExecution.run true model W lo a.lambda).1
  let points := (GeneralPaperLeastValidPointsPrice.run model.rat W split.bucket).1
  let found := (GeneralPaperCodeScanExecution.scan true model W a response lo hi points).1
  GeneralPaperCodeSplitStorage.window model W a lo+pointWindow model W split.bucket+
    GeneralPaperCodeScanStorage.window model W a response lo hi points+GeneralPaperCodeRecordStorage.scanRecord W found+
      fields W [split.work,found.work,split.work+found.work,split.work+found.work+32]+128*W

def childProfile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCodeSplitStorage.profile model W a+pointProfile model W a+GeneralPaperCodeScanStorage.profile model W a 5+
    (4*operandWidth a.lambda+112*W+1)+4*(operandWidth a.lambda+W)+32*W+128*W

theorem child_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hlo : lo≤4*a.C) (hhi : hi≤8*a.C) : childWindow model W a response lo hi≤childProfile model W a := by
  let split := (GeneralPaperCodeSplitExecution.run true model W lo a.lambda).1
  let points := (GeneralPaperLeastValidPointsPrice.run model.rat W split.bucket).1
  let found := (GeneralPaperCodeScanExecution.scan true model W a response lo hi points).1
  have hs := GeneralPaperCodeSplitStorage.bounded model W a lo hlo
  have hb := GeneralPaperCodeSplitPrice.bucket_bound true model W a lo hlo
  have hp := point_bound model W a split.bucket hb
  have hlen : points.length=5 := GeneralPaperLeastValidPointsPrice.length model.rat W split.bucket
  have hpoints : ∀ code∈points,code≤8*a.C := GeneralPaperLeastValidPointsPrice.point_bound model.rat W a split.bucket hb
  have hscan := GeneralPaperCodeScanStorage.bounded model W a response lo hi (by omega) hhi points hlen.le hpoints
  rw [hlen] at hscan
  have hr := GeneralPaperCodeScanStorage.scan_record model W a response lo hi points hlen.le
  have hsw : split.work≤14*a.lambda+42 := by
    dsimp only [split]
    rw [GeneralPaperCodeSplitExecution.data]
    exact GeneralPaperCodeSplit.run_work lo a.lambda
  have hfw := GeneralPaperCodeScanOperands.scan_native_work true model W a response lo hi points
  rw [hlen] at hfw
  change found.work≤5*(184*a.lambda+524)+8 at hfw
  have h0 := metadata_word a.lambda split.work (by unfold metadataCap; omega)
  have h1 := metadata_word a.lambda found.work (by unfold metadataCap; omega)
  have h2 := metadata_word a.lambda (split.work+found.work) (by unfold metadataCap; omega)
  have h3 := metadata_word a.lambda (split.work+found.work+32) (by unfold metadataCap; omega)
  have hf := fields_bound W (operandWidth a.lambda) [split.work,found.work,split.work+found.work,split.work+found.work+32] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3)
  change _≤4*(operandWidth a.lambda+W)+32*W at hf
  unfold childWindow childProfile
  change GeneralPaperCodeSplitStorage.window model W a lo+pointWindow model W split.bucket+
    GeneralPaperCodeScanStorage.window model W a response lo hi points+GeneralPaperCodeRecordStorage.scanRecord W found+
      fields W [split.work,found.work,split.work+found.work,split.work+found.work+32]+128*W≤_
  change GeneralPaperCodeRecordStorage.scanRecord W found≤_ at hr
  omega

def window (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) : ℕ :=
  (if lo≤4*a.C then childWindow model W a response lo hi else 0)+
    GeneralPaperCodeRecordStorage.scanRecord W (GeneralPaperLeastValidExecution.run true model W a response lo hi).1+
      fields W [lo,hi,4*a.C]+(GeneralPaperLeastValidExecution.run true model W a response lo hi).2+256*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  childProfile model W a+(4*operandWidth a.lambda+112*W+1)+3*(operandWidth a.lambda+W)+32*W+
    67108864*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))+256*W

theorem bounded (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hlo : lo≤8*a.C) (hhi : hi≤8*a.C) : window model W a response lo hi≤profile model W a := by
  have hchild : (if lo≤4*a.C then childWindow model W a response lo hi else 0)≤childProfile model W a := by
    split
    · rename_i h
      exact child_bound model W a response lo hi h hhi
    · exact Nat.zero_le _
  have hr := returned model W a response lo hi
  have hp := GeneralPaperLeastValidPrice.bit_work model W a response lo hi hlo hhi
  have h0 := code_word a lo hlo
  have h1 := code_word a hi hhi
  have h2 := code_word a (4*a.C) (by omega)
  have hf := fields_bound W (operandWidth a.lambda) [lo,hi,4*a.C] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2)
  change _≤3*(operandWidth a.lambda+W)+32*W at hf
  unfold window profile
  omega

theorem cell_returned (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperCodeRecordStorage.scanRecord W (GeneralPaperLeastValidCellExecution.run true model W a response lo hi).1≤
      4*operandWidth a.lambda+112*W+1 := by
  apply GeneralPaperCodeRecordStorage.scan_record W a response
  · intro e he
    have hb := GeneralPaperLeastValidCellExecution.best true model W a response lo hi
    rw [he] at hb
    exact hb.1.2.2
  · have h := GeneralPaperLeastValidCellPrice.native_work true model W a response lo hi
    unfold metadataCap
    omega

def cellWindow (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) : ℕ :=
  let r := GeneralPaperLeastValidCellExecution.run true model W a response lo hi
  (if lo<hi then window model W a response lo (hi-1) else 0)+GeneralPaperCodeRecordStorage.scanRecord W r.1+
    fields W [lo,hi,hi-1,r.1.work]+r.2+256*W

def cellProfile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  profile model W a+(4*operandWidth a.lambda+112*W+1)+4*(operandWidth a.lambda+W)+32*W+
    134217728*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))+256*W

theorem cell_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hlo : lo≤8*a.C) (hhi : hi≤8*a.C) : cellWindow model W a response lo hi≤cellProfile model W a := by
  have hchild : (if lo<hi then window model W a response lo (hi-1) else 0)≤profile model W a := by
    split
    · exact bounded model W a response lo (hi-1) hlo (by omega)
    · exact Nat.zero_le _
  have hr := cell_returned model W a response lo hi
  have hp := GeneralPaperLeastValidCellPrice.bit_work model W a response lo hi hlo hhi
  have hw := GeneralPaperLeastValidCellPrice.native_work true model W a response lo hi
  have h0 := code_word a lo hlo
  have h1 := code_word a hi hhi
  have h2 := code_word a (hi-1) (by omega)
  have h3 := metadata_word a.lambda (GeneralPaperLeastValidCellExecution.run true model W a response lo hi).1.work
    (by unfold metadataCap; omega)
  have hf := fields_bound W (operandWidth a.lambda)
    [lo,hi,hi-1,(GeneralPaperLeastValidCellExecution.run true model W a response lo hi).1.work] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3)
  change _≤4*(operandWidth a.lambda+W)+32*W at hf
  unfold cellWindow cellProfile
  dsimp only
  omega

theorem cell_profile_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) : cellProfile model W a≤
    1073741824*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  let F := controlWord W a.lambda+model.rat (operandWidth a.lambda)
  have hWF : W≤F := by dsimp [F,controlWord]; omega
  have hLF : operandWidth a.lambda≤F := (model.word_le _).trans (Nat.le_add_left _ _)
  have hPF : model.rat (operandWidth a.lambda)≤F := Nat.le_add_left _ _
  have hOne : 1≤F := (show 1≤operandWidth a.lambda by unfold operandWidth; omega).trans hLF
  unfold cellProfile profile childProfile pointProfile GeneralPaperCodeSplitStorage.profile
    GeneralPaperCodeScanStorage.profile GeneralPaperCodeScanStorage.coefficient GeneralPaperCodeScanStorage.evaluateProfile
    GeneralPaperCodeScanPrice.profile GeneralPaperCodeScanPrice.stepProfile GeneralPaperCodeEvaluatePrice.profile
  dsimp only [F] at *
  nlinarith only [hWF,hLF,hPF,hOne,Nat.zero_le
    (a.lambda*(controlWord W a.lambda+model.rat (operandWidth a.lambda)))]

end Blotto.GeneralPaperLeastValidStorage
