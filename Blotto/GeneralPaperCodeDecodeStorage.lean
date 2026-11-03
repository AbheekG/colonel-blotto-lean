import Blotto.GeneralPaperDecodeBucketStorage

/-! Native complete code decoder: reject tail codes before child execution;
otherwise retain the streamed split and selected bucket query/choice, native
annotation sums and the whole returned record. Original code caps are derived
by actual catalogue/candidate callers. -/
namespace Blotto.GeneralPaperCodeDecodeStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def childWindow (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) : ℕ :=
  let split := (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1
  let found := (GeneralPaperDecodeBucketExecution.run true model W a response split.bucket split.slot).1
  GeneralPaperCodeSplitStorage.window model W a code+
    GeneralPaperDecodeBucketStorage.window model W a response split.bucket split.slot+
      fields W [split.work+found.work,split.work+found.work+16]+128*W

def childProfile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  33554432*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))

theorem child_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ)
    (hc : code≤4*a.C) : childWindow model W a response code≤childProfile model W a := by
  let split := (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1
  let found := (GeneralPaperDecodeBucketExecution.run true model W a response split.bucket split.slot).1
  let F := controlWord W a.lambda+model.rat (operandWidth a.lambda)
  have hspec := GeneralPaperCodeSplitPrice.specification true model W a code hc
  have hb := GeneralPaperCodeSplitPrice.bucket_bound true model W a code hc
  have hsplit := GeneralPaperCodeSplitStorage.bounded model W a code hc
  have hbucket := GeneralPaperDecodeBucketStorage.bounded model W a response split.bucket split.slot hb hspec.2
  have hs : split.work≤14*a.lambda+42 := by
    dsimp only [split]
    rw [GeneralPaperCodeSplitExecution.data]
    exact GeneralPaperCodeSplit.run_work code a.lambda
  have hf : found.work≤170*a.lambda+418 := GeneralPaperDecodeBucketPrice.native_work true model W a response split.bucket split.slot
  have h0 := metadata_word a.lambda (split.work+found.work) (by unfold metadataCap; omega)
  have h1 := metadata_word a.lambda (split.work+found.work+16) (by unfold metadataCap; omega)
  have ha := fields_bound W (operandWidth a.lambda) [split.work+found.work,split.work+found.work+16] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact h0
    · exact h1)
  change _≤2*(operandWidth a.lambda+W)+32*W at ha
  have hWF : W≤F := by dsimp [F,controlWord]; omega
  have hLF : operandWidth a.lambda≤F := (model.word_le _).trans (Nat.le_add_left _ _)
  change GeneralPaperCodeSplitStorage.window model W a code≤8192*(a.lambda+3)*F at hsplit
  change GeneralPaperDecodeBucketStorage.window model W a response split.bucket split.slot≤16777216*(a.lambda+3)*F at hbucket
  unfold childWindow childProfile
  change GeneralPaperCodeSplitStorage.window model W a code+
    GeneralPaperDecodeBucketStorage.window model W a response split.bucket split.slot+
      fields W [split.work+found.work,split.work+found.work+16]+128*W≤33554432*(a.lambda+3)*F
  nlinarith only [hsplit,hbucket,ha,hWF,hLF,Nat.zero_le (a.lambda*F)]

def window (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) : ℕ :=
  (if code≤4*a.C then childWindow model W a response code else 0)+
    GeneralPaperCodeRecordStorage.decodeRecord W (GeneralPaperCodeDecodeExecution.run true model W a response code).1+
    fields W [code,4*a.C,a.lambda,a.C]+(GeneralPaperCodeDecodeExecution.run true model W a response code).2+256*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  67108864*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))

theorem bounded (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) (hc : code≤8*a.C) :
    window model W a response code≤profile model W a := by
  let F := controlWord W a.lambda+model.rat (operandWidth a.lambda)
  have hchild : (if code≤4*a.C then childWindow model W a response code else 0)≤childProfile model W a := by
    split
    · rename_i h
      exact child_bound model W a response code h
    · exact Nat.zero_le _
  have hr := GeneralPaperCodeRecordStorage.native_decode model W a response code
  have hp := GeneralPaperCodeDecodePrice.bit_work model W a response code hc
  have h0 := code_word a code hc
  have h1 := code_word a (4*a.C) (by omega)
  have h2 := metadata_word a.lambda a.lambda (by unfold metadataCap; omega)
  have h3 := code_word a a.C (by omega)
  have hf := fields_bound W (operandWidth a.lambda) [code,4*a.C,a.lambda,a.C] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3)
  change _≤4*(operandWidth a.lambda+W)+32*W at hf
  have hWF : W≤F := by dsimp [F,controlWord]; omega
  have hLF : operandWidth a.lambda≤F := (model.word_le _).trans (Nat.le_add_left _ _)
  have hOne : 1≤F := (show 1≤operandWidth a.lambda by unfold operandWidth; omega).trans hLF
  change (if code≤4*a.C then childWindow model W a response code else 0)≤33554432*(a.lambda+3)*F at hchild
  change (GeneralPaperCodeDecodeExecution.run true model W a response code).2≤8388608*(a.lambda+3)*F at hp
  unfold window profile
  change _≤67108864*(a.lambda+3)*F
  nlinarith only [hchild,hr,hp,hf,hWF,hLF,hOne,Nat.zero_le (a.lambda*F)]

end Blotto.GeneralPaperCodeDecodeStorage
