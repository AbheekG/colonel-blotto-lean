import Blotto.GeneralPaperCodeRecordStorage

/-! Actual streamed code split: register reservation, complete native division
return, split bucket/slot/work, caller controls and primitive scratch. The
control word is derived from the retained alphabet Lambda and global W. -/
namespace Blotto.GeneralPaperCodeSplitStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def record (W : ℕ) (r : GeneralPaperCodeSplit.Result) : ℕ := fields W [r.bucket,r.slot,r.work]

theorem record_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hc : code≤4*a.C) :
    record W (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1≤3*(operandWidth a.lambda+W)+32*W := by
  have hspec := GeneralPaperCodeSplitPrice.specification true model W a code hc
  have hb := GeneralPaperCodeSplitPrice.bucket_bound true model W a code hc
  have hw : (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1.work≤14*a.lambda+42 := by
    rw [GeneralPaperCodeSplitExecution.data]
    exact GeneralPaperCodeSplit.run_work code a.lambda
  have hp := a.scalePositive
  have h0 := code_word a (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1.bucket (by omega)
  have h1 := code_word a (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1.slot (by omega)
  have h2 := metadata_word a.lambda (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1.work
    (by unfold metadataCap; omega)
  apply fields_bound W (operandWidth a.lambda)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2

theorem division_control (W lambda : ℕ) :
    GeneralPaperQuotientRegisterSpace.counterWord (lambda+1)≤controlWord W lambda := by
  have h := binaryWordWidth_mono (show lambda+2≤lambda+3 by omega)
  change 32+binaryWordWidth (lambda+2)≤controlWord W lambda
  unfold controlWord
  omega

def divisionWindow (model : RationalCostModel) (W code lambda : ℕ) : ℕ :=
  let A := controlWord W lambda
  GeneralPaperQuotientPhaseSpace.reservation model A code 4+
    GeneralPaperStreamingNatDivision.footprint A (GeneralPaperStreamingNatDivision.run code 4 (lambda+1))+16*A

theorem division_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hc : code≤4*a.C) :
    divisionWindow model W code a.lambda≤256*(controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  have h := GeneralPaperStreamingNatDivision.reservation model (controlWord W a.lambda) code 4 (a.lambda+1)
    (by decide) (division_control W a.lambda)
  have hp := model.monotone (GeneralPaperCodeSplitPrice.division_width a code hc)
  exact h.trans (Nat.mul_le_mul_left 256 (Nat.add_le_add_left hp _))

def window (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) : ℕ :=
  divisionWindow model W code a.lambda+record W (GeneralPaperCodeSplitExecution.run true model W code a.lambda).1+
    fields W [code,4,a.lambda,a.lambda+1]+(GeneralPaperCodeSplitExecution.run true model W code a.lambda).2+128*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  8192*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))

theorem bounded (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hc : code≤4*a.C) :
    window model W a code≤profile model W a := by
  let F := controlWord W a.lambda+model.rat (operandWidth a.lambda)
  have hd := division_bound model W a code hc
  have hr := record_bound model W a code hc
  have hp := GeneralPaperCodeSplitPrice.bit_work model W a code hc
  have hC := a.scalePositive
  have h0 := code_word a code (by omega)
  have h1 := code_word a 4 (by omega)
  have h2 := metadata_word a.lambda a.lambda (by unfold metadataCap; omega)
  have h3 := metadata_word a.lambda (a.lambda+1) (by unfold metadataCap; omega)
  have hf := fields_bound W (operandWidth a.lambda) [code,4,a.lambda,a.lambda+1] (by
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
  unfold window profile
  change _≤8192*(a.lambda+3)*F
  change divisionWindow model W code a.lambda≤256*F at hd
  change (GeneralPaperCodeSplitExecution.run true model W code a.lambda).2≤4096*(a.lambda+3)*F at hp
  nlinarith only [hd,hr,hf,hp,hWF,hLF,Nat.zero_le (a.lambda*F)]

end Blotto.GeneralPaperCodeSplitStorage
