import Blotto.GeneralPaperDecoderMidpointStorage

/-! Bucket decoder storage follows the selected midpoint branch and retains
the complete returned choice/work record plus caller scalars. Grid/open and
rejected branches include zero and the closed one endpoint. -/
namespace Blotto.GeneralPaperDecodeBucketStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem choice_bounds (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (bucket slot : ℕ) (c : Choice)
    (hc : (GeneralPaperDecodeBucketExecution.run true model W a response bucket slot).1.choice=some c) :
    c.threshold.num≤a.C ∧ c.threshold.den≤a.C := by
  rw [GeneralPaperDecodeBucketExecution.data] at hc
  have hs := GeneralPaperCodeDecodeSound.bucket_sound a response bucket slot c hc
  obtain ⟨other,hd,hv,_⟩ := GeneralPaperCodeDecodeComplete.denotes_complete a response (4*bucket+slot)
    c.threshold.value c.opened hs.1
  have hu := GeneralPaperCodeOrder.decoded_threshold_le_one a response (4*bucket+slot) other hd
  rw [hv] at hu
  exact ⟨(Farey.num_le_den c.threshold hu).trans hs.2,hs.2⟩

theorem returned (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ) :
    GeneralPaperCodeRecordStorage.decodeRecord W (GeneralPaperDecodeBucketExecution.run true model W a response bucket slot).1≤
      3*operandWidth a.lambda+112*W+1 := by
  apply GeneralPaperCodeRecordStorage.decoded_record W a
  · exact choice_bounds model W a response bucket slot
  · have h := GeneralPaperDecodeBucketPrice.native_work true model W a response bucket slot
    unfold metadataCap
    omega

def selectedPhase (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ) : ℕ :=
  if bucket<a.C ∧ (slot=2 ∨ (slot=3 ∧ response=true)) then
    GeneralPaperDecoderMidpointStorage.window model W false a bucket else 0

theorem selected_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ) :
    selectedPhase model W a response bucket slot≤GeneralPaperDecoderMidpointStorage.profile model W a := by
  unfold selectedPhase
  split
  · rename_i h
    exact GeneralPaperDecoderMidpointStorage.bounded model W false a bucket h.1
  · exact Nat.zero_le _

def window (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ) : ℕ :=
  let r := GeneralPaperDecodeBucketExecution.run true model W a response bucket slot
  selectedPhase model W a response bucket slot+GeneralPaperCodeRecordStorage.decodeRecord W r.1+
    fields W [bucket,slot,a.C,r.1.work]+r.2+128*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  16777216*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))

theorem bounded (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ)
    (hb : bucket≤a.C) (hs : slot<4) : window model W a response bucket slot≤profile model W a := by
  let F := controlWord W a.lambda+model.rat (operandWidth a.lambda)
  have hp := selected_bound model W a response bucket slot
  have hr := returned model W a response bucket slot
  have hwork := GeneralPaperDecodeBucketPrice.bit_work model W a response bucket slot hb hs
  have hn := GeneralPaperDecodeBucketPrice.native_work true model W a response bucket slot
  have hC := a.scalePositive
  have h0 := code_word a bucket (by omega)
  have h1 := code_word a slot (by omega)
  have h2 := code_word a a.C (by omega)
  have h3 := metadata_word a.lambda (GeneralPaperDecodeBucketExecution.run true model W a response bucket slot).1.work
    (by unfold metadataCap; omega)
  have hf := fields_bound W (operandWidth a.lambda)
    [bucket,slot,a.C,(GeneralPaperDecodeBucketExecution.run true model W a response bucket slot).1.work] (by
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
  change selectedPhase model W a response bucket slot≤4194304*(a.lambda+3)*F at hp
  change (GeneralPaperDecodeBucketExecution.run true model W a response bucket slot).2≤4194304*(a.lambda+3)*F at hwork
  unfold window profile
  dsimp only
  change _≤16777216*(a.lambda+3)*F
  nlinarith only [hp,hr,hwork,hf,hWF,hLF,hOne,Nat.zero_le (a.lambda*F)]

end Blotto.GeneralPaperDecodeBucketStorage
