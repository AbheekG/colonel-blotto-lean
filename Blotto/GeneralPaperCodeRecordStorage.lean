import Blotto.GeneralPaperActualPartitionStorage

/-! Native decoder/lookup records retain full integer fractions, open bits,
optional selections and native work. Payload bounds come from the executed
decoder's unit/denominator guarantees, not from a short mantissa word. -/
namespace Blotto.GeneralPaperCodeRecordStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def choiceBits (W : ℕ) (c : Choice) : ℕ := GeneralPaperEncodedCatalogueStorage.fractionBits W c.threshold+1+32*W
def optionalChoice (W : ℕ) : Option Choice → ℕ
  | none => 32*W
  | some c => choiceBits W c+32*W
def decodeRecord (W : ℕ) (r : GeneralPaperCodeDecode.Result) : ℕ := optionalChoice W r.choice+natBits r.work+32*W
def optionalEntry (W : ℕ) : Option GeneralPaperCodeMinimumScan.Entry → ℕ
  | none => 32*W
  | some e => GeneralPaperEncodedCatalogueStorage.entryBits W e+32*W
def scanRecord (W : ℕ) (r : GeneralPaperCodeMinimumScan.Result) : ℕ := optionalEntry W r.selected+natBits r.work+32*W

theorem fraction (W : ℕ) (a : Alphabet) (f : Farey.Fraction) (hn : f.num≤a.C) (hd : f.den≤a.C) :
    GeneralPaperEncodedCatalogueStorage.fractionBits W f≤2*operandWidth a.lambda+16*W := by
  have h0 := code_word a f.num (by omega)
  have h1 := code_word a f.den (by omega)
  unfold GeneralPaperEncodedCatalogueStorage.fractionBits GeneralPaperEncodedCatalogueStorage.codeBits
  omega

theorem decoded_bounds (a : Alphabet) (response : Bool) (code : ℕ) (c : Choice)
    (hc : (GeneralPaperCodeDecode.decode a response code).choice=some c) : c.threshold.num≤a.C ∧ c.threshold.den≤a.C := by
  have hd := (GeneralPaperCodeDecodeSound.decode_sound a response code c hc).2
  have hu := GeneralPaperCodeOrder.decoded_threshold_le_one a response code c hc
  exact ⟨(Farey.num_le_den c.threshold hu).trans hd,hd⟩

theorem choice (W : ℕ) (a : Alphabet) (c : Choice) (hn : c.threshold.num≤a.C) (hd : c.threshold.den≤a.C) :
    choiceBits W c≤2*operandWidth a.lambda+48*W+1 := by
  have hf := fraction W a c.threshold hn hd
  unfold choiceBits
  omega

theorem optional_choice (W : ℕ) (a : Alphabet) (value : Option Choice)
    (hc : ∀ c,value=some c → c.threshold.num≤a.C ∧ c.threshold.den≤a.C) :
    optionalChoice W value≤2*operandWidth a.lambda+80*W+1 := by
  cases he : value with
  | none => change 32*W≤_; omega
  | some c =>
    have h := hc c he
    have hs := choice W a c h.1 h.2
    change choiceBits W c+32*W≤_
    omega

theorem decoded_record (W : ℕ) (a : Alphabet) (r : GeneralPaperCodeDecode.Result)
    (hc : ∀ c,r.choice=some c → c.threshold.num≤a.C ∧ c.threshold.den≤a.C)
    (hw : r.work≤metadataCap a.lambda) : decodeRecord W r≤3*operandWidth a.lambda+112*W+1 := by
  have h := optional_choice W a r.choice hc
  have hm := metadata_word a.lambda r.work hw
  unfold decodeRecord natBits
  omega

theorem native_decode (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) :
    decodeRecord W (GeneralPaperCodeDecodeExecution.run true model W a response code).1≤
      3*operandWidth a.lambda+112*W+1 := by
  apply decoded_record W a
  · intro c hc
    rw [GeneralPaperCodeDecodeExecution.data] at hc
    exact decoded_bounds a response code c hc
  · have h := GeneralPaperCodeDecodePrice.native_work true model W a response code
    unfold metadataCap
    omega

theorem entry (W : ℕ) (a : Alphabet) (response : Bool) (e : GeneralPaperCodeMinimumScan.Entry)
    (he : (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor) :
    GeneralPaperEncodedCatalogueStorage.entryBits W e≤3*operandWidth a.lambda+48*W+1 := by
  have hf := decoded_bounds a response e.cost e.predecessor he
  have hc := valid_in_alphabet a response e.cost (GeneralPaperCodeDecodeSound.decode_valid a response e.cost e.predecessor he)
  have hw := code_word a e.cost hc.le
  have hp := fraction W a e.predecessor.threshold hf.1 hf.2
  unfold GeneralPaperEncodedCatalogueStorage.entryBits GeneralPaperEncodedCatalogueStorage.codeBits
  omega

theorem optional_entry (W : ℕ) (a : Alphabet) (response : Bool) (value : Option GeneralPaperCodeMinimumScan.Entry)
    (he : ∀ e,value=some e → (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor) :
    optionalEntry W value≤3*operandWidth a.lambda+80*W+1 := by
  cases hs : value with
  | none => change 32*W≤_; omega
  | some e =>
    have h := entry W a response e (he e hs)
    change GeneralPaperEncodedCatalogueStorage.entryBits W e+32*W≤_
    omega

theorem scan_record (W : ℕ) (a : Alphabet) (response : Bool) (r : GeneralPaperCodeMinimumScan.Result)
    (he : ∀ e,r.selected=some e → (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor)
    (hw : r.work≤metadataCap a.lambda) : scanRecord W r≤4*operandWidth a.lambda+112*W+1 := by
  have h := optional_entry W a response r.selected he
  have hm := metadata_word a.lambda r.work hw
  unfold scanRecord natBits
  omega

end Blotto.GeneralPaperCodeRecordStorage
