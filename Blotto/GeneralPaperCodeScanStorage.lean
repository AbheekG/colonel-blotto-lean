import Blotto.GeneralPaperCodeDecodeStorage

/-! Native fixed-candidate evaluation and scan. Selected frames retain
tested/later/chosen records and annotation sums, while only the active
decoder window is reserved. The actual caller derives the five-code cap. -/
namespace Blotto.GeneralPaperCodeScanStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem evaluate_record (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ) :
    GeneralPaperCodeRecordStorage.scanRecord W (GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1≤
      4*operandWidth a.lambda+112*W+1 := by
  apply GeneralPaperCodeRecordStorage.scan_record W a response
  · intro e he
    rw [GeneralPaperCodeScanExecution.evaluate_data] at he
    exact ((GeneralPaperCodeMinimumScan.evaluate_iff a response lo hi code e).mp he).2.2.2
  · have h := GeneralPaperCodeScanOperands.evaluate_native_work true model W a response lo hi code
    unfold metadataCap
    omega

theorem scan_record (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (codes : List ℕ) (hn : codes.length≤5) :
    GeneralPaperCodeRecordStorage.scanRecord W (GeneralPaperCodeScanExecution.scan true model W a response lo hi codes).1≤
      4*operandWidth a.lambda+112*W+1 := by
  apply GeneralPaperCodeRecordStorage.scan_record W a response
  · intro e he
    rw [GeneralPaperCodeScanExecution.scan_data] at he
    have hb := GeneralPaperCodeMinimumScan.scan_best a response lo hi codes
    rw [he] at hb
    exact (GeneralPaperCodeMinimumScan.listed_possible a response lo hi codes e hb.1).2.2
  · have h := GeneralPaperCodeScanOperands.scan_native_work true model W a response lo hi codes
    have hm := Nat.mul_le_mul_right (184*a.lambda+524) hn
    unfold metadataCap
    omega

def evaluateWindow (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ) : ℕ :=
  let tested := GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code
  (if lo≤code ∧ code≤hi then GeneralPaperCodeDecodeStorage.window model W a response code else 0)+
    GeneralPaperCodeRecordStorage.scanRecord W tested.1+fields W [lo,hi,code,tested.1.work]+tested.2+128*W

def evaluateProfile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  134217728*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))

theorem evaluate_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ)
    (hlo : lo≤8*a.C) (hhi : hi≤8*a.C) (hc : code≤8*a.C) :
    evaluateWindow model W a response lo hi code≤evaluateProfile model W a := by
  let F := controlWord W a.lambda+model.rat (operandWidth a.lambda)
  have hd : (if lo≤code ∧ code≤hi then GeneralPaperCodeDecodeStorage.window model W a response code else 0)≤
      GeneralPaperCodeDecodeStorage.profile model W a := by
    split
    · exact GeneralPaperCodeDecodeStorage.bounded model W a response code hc
    · exact Nat.zero_le _
  have hr := evaluate_record model W a response lo hi code
  have hp := GeneralPaperCodeEvaluatePrice.bit_work model W a response lo hi code hlo hhi hc
  have hm := GeneralPaperCodeScanOperands.evaluate_native_work true model W a response lo hi code
  have h0 := code_word a lo hlo
  have h1 := code_word a hi hhi
  have h2 := code_word a code hc
  have h3 := metadata_word a.lambda (GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1.work
    (by unfold metadataCap; omega)
  have hf := fields_bound W (operandWidth a.lambda)
    [lo,hi,code,(GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1.work] (by
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
  have hPF : model.rat (operandWidth a.lambda)≤F := Nat.le_add_left _ _
  have hOne : 1≤F := (show 1≤operandWidth a.lambda by unfold operandWidth; omega).trans hLF
  unfold GeneralPaperCodeEvaluatePrice.profile at hp
  change _≤8388608*(a.lambda+3)*F+4*model.rat (operandWidth a.lambda)+128*W at hp
  change (if lo≤code ∧ code≤hi then GeneralPaperCodeDecodeStorage.window model W a response code else 0)≤67108864*(a.lambda+3)*F at hd
  unfold evaluateWindow evaluateProfile
  dsimp only
  change _≤134217728*(a.lambda+3)*F
  nlinarith only [hd,hr,hp,hf,hWF,hLF,hPF,hOne,Nat.zero_le (a.lambda*F)]

def frame (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ) (rest : List ℕ) : ℕ :=
  let tested := (GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1
  let later := (GeneralPaperCodeScanExecution.scan true model W a response lo hi rest).1
  let whole := (GeneralPaperCodeScanExecution.scan true model W a response lo hi (code::rest)).1
  GeneralPaperCodeRecordStorage.scanRecord W tested+GeneralPaperCodeRecordStorage.scanRecord W later+
    GeneralPaperCodeRecordStorage.scanRecord W whole+
    fields W [lo,hi,code,tested.work+later.work,tested.work+later.work+24]+256*W

def coefficient (W lambda : ℕ) : ℕ := 32*operandWidth lambda+1024*W+32

theorem frame_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ) (rest : List ℕ)
    (hlo : lo≤8*a.C) (hhi : hi≤8*a.C) (hc : code≤8*a.C) (hn : (code::rest).length≤5) :
    frame model W a response lo hi code rest≤coefficient W a.lambda := by
  have hlen : rest.length≤4 := by simp only [List.length_cons] at hn; omega
  have ht := evaluate_record model W a response lo hi code
  have hl := scan_record model W a response lo hi rest (by omega)
  have hw := scan_record model W a response lo hi (code::rest) hn
  have htw := GeneralPaperCodeScanOperands.evaluate_native_work true model W a response lo hi code
  have hlw := GeneralPaperCodeScanOperands.scan_native_work true model W a response lo hi rest
  have hmul := Nat.mul_le_mul_right (184*a.lambda+524) hlen
  have h0 := code_word a lo hlo
  have h1 := code_word a hi hhi
  have h2 := code_word a code hc
  have h3 := metadata_word a.lambda
    ((GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1.work+
      (GeneralPaperCodeScanExecution.scan true model W a response lo hi rest).1.work) (by unfold metadataCap; omega)
  have h4 := metadata_word a.lambda
    ((GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1.work+
      (GeneralPaperCodeScanExecution.scan true model W a response lo hi rest).1.work+24) (by unfold metadataCap; omega)
  have hf := fields_bound W (operandWidth a.lambda)
    [lo,hi,code,(GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1.work+
      (GeneralPaperCodeScanExecution.scan true model W a response lo hi rest).1.work,
      (GeneralPaperCodeScanExecution.evaluate true model W a response lo hi code).1.work+
        (GeneralPaperCodeScanExecution.scan true model W a response lo hi rest).1.work+24] (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4)
  change _≤5*(operandWidth a.lambda+W)+32*W at hf
  unfold frame coefficient
  dsimp only
  omega

def peak (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) : List ℕ → ℕ
  | [] => GeneralPaperCodeRecordStorage.scanRecord W (GeneralPaperCodeScanExecution.scan true model W a response lo hi []).1+64*W
  | code::rest => frame model W a response lo hi code rest+
      max (evaluateWindow model W a response lo hi code) (peak model W a response lo hi rest)

theorem peak_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hlo : lo≤8*a.C) (hhi : hi≤8*a.C) (codes : List ℕ) (hn : codes.length≤5) (hc : ∀ code∈codes,code≤8*a.C) :
    peak model W a response lo hi codes≤(codes.length+1)*coefficient W a.lambda+evaluateProfile model W a := by
  revert hn hc
  induction codes with
  | nil =>
    intro _ _
    have h := scan_record model W a response lo hi [] (by simp)
    unfold peak coefficient
    simp only [List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons code rest ih =>
    intro hn hc
    have hf := frame_bound model W a response lo hi code rest hlo hhi (hc code (List.mem_cons_self ..)) hn
    have he := evaluate_bound model W a response lo hi code hlo hhi (hc code (List.mem_cons_self ..))
    have hTail := ih (by simp only [List.length_cons] at hn; omega) (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    have he' : evaluateWindow model W a response lo hi code≤
        (rest.length+1)*coefficient W a.lambda+evaluateProfile model W a := he.trans (Nat.le_add_left _ _)
    have hm := max_le he' hTail
    rw [peak,List.length_cons]
    nlinarith only [hf,hm]

def window (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) (codes : List ℕ) : ℕ :=
  listFootprint W natBits codes+peak model W a response lo hi codes+
    (GeneralPaperCodeScanExecution.scan true model W a response lo hi codes).2+128*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) (n : ℕ) : ℕ :=
  n*(operandWidth a.lambda+2*W)+32*W+(n+1)*coefficient W a.lambda+evaluateProfile model W a+
    GeneralPaperCodeScanPrice.profile model W a n+128*W

theorem bounded (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hlo : lo≤8*a.C) (hhi : hi≤8*a.C) (codes : List ℕ) (hn : codes.length≤5) (hc : ∀ code∈codes,code≤8*a.C) :
    window model W a response lo hi codes≤profile model W a codes.length := by
  have hl := list_bound W (operandWidth a.lambda) natBits codes (fun code h => code_word a code (hc code h))
  have hp := peak_bound model W a response lo hi hlo hhi codes hn hc
  have hs := GeneralPaperCodeScanPrice.bit_work model W a response lo hi hlo hhi codes hn hc
  unfold window profile
  omega

end Blotto.GeneralPaperCodeScanStorage
