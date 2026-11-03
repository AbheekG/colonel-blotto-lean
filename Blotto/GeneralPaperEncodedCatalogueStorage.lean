import Blotto.GeneralPaperEncodedFieldPlanStorage

/-! All four catalogue array families are retained explicitly. Entries,
codes, raw Farey numerator/denominator pairs and open bits use the full code
word. Projection proofs and fraction-positivity proofs occupy no payload. -/
namespace Blotto.GeneralPaperEncodedCatalogueStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def codeBits (code : ℕ) : ℕ := 1+binaryWordWidth code
def fractionBits (W : ℕ) (f : Farey.Fraction) : ℕ := codeBits f.num+codeBits f.den+16*W
def entryBits (W : ℕ) (e : GeneralPaperCodeMinimumScan.Entry) : ℕ := codeBits e.cost+fractionBits W e.predecessor.threshold+1+32*W

theorem fraction_words {m k : ℕ} (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    codeBits ((ready.data.thresholds.read j).read i).num≤GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda ∧
    codeBits ((ready.data.thresholds.read j).read i).den≤GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda := by
  have h := GeneralPaperCatalogueTagValue.native_bounds ready.alphabet ready.response k ready.summaries ready.data ready.data_spec j i
  have hc := (GeneralPaperEpochCacheCodeWords.alphabet_scalars ready.alphabet).2.1
  exact ⟨(Nat.add_le_add_left (binaryWordWidth_mono h.1) 1).trans hc,
    (Nat.add_le_add_left (binaryWordWidth_mono h.2) 1).trans hc⟩

theorem fraction_bound {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    fractionBits W ((ready.data.thresholds.read j).read i)≤2*GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda+16*W := by
  have h := fraction_words ready j i
  unfold fractionBits
  omega

theorem entry_bound {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    entryBits W ((ready.data.entries.read j).read i)≤3*GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda+48*W+1 := by
  have hc : codeBits ((ready.data.entries.read j).read i).cost≤GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda := by
    rw [←GeneralPaperCatalogueArrays.codes_read]
    exact GeneralPaperEpochCacheCodeWords.option_word ready j i
  have hf := fraction_bound W ready j i
  rw [GeneralPaperCatalogueArrays.thresholds_read] at hf
  unfold entryBits
  omega

def innerProfile (W K L : ℕ) : ℕ := K*(4*L+65*W+4)+32*W

def footprint {m K : ℕ} (W : ℕ) (data : GeneralPaperCatalogueArrays.Arrays m K) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (entryBits W)) data.entries+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W codeBits) data.codes+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (fractionBits W)) data.thresholds+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (fun _ : Bool => 1)) data.opened+128*W

def profile (W m K L : ℕ) : ℕ := 4*(m*(innerProfile W K L+W)+32*W)+128*W

theorem ready_data {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k) :
    footprint W ready.data≤profile W m ((GeneralPaperSourceParameters.prepare k).summarySize+2)
      (GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda) := by
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  let L := GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda
  let I := innerProfile W K L
  have he (j : Fin m) : GeneralPaperEncodedFixedVector.footprint W (entryBits W) (ready.data.entries.read j)≤I := by
    have h := GeneralPaperEncodedFixedVector.bounded W (4*L+64*W+4) (entryBits W) (ready.data.entries.read j) (by
      intro i
      have h := entry_bound W ready j i
      change entryBits W ((ready.data.entries.read j).read i)≤3*L+48*W+1 at h
      omega)
    exact h.trans_eq (by dsimp only [I,innerProfile]; ring)
  have hc (j : Fin m) : GeneralPaperEncodedFixedVector.footprint W codeBits (ready.data.codes.read j)≤I := by
    have h := GeneralPaperEncodedFixedVector.bounded W (4*L+64*W+4) codeBits (ready.data.codes.read j) (by
      intro i
      have h := GeneralPaperEpochCacheCodeWords.option_word ready j i
      change codeBits ((ready.data.codes.read j).read i)≤L at h
      omega)
    exact h.trans_eq (by dsimp only [I,innerProfile]; ring)
  have hf (j : Fin m) : GeneralPaperEncodedFixedVector.footprint W (fractionBits W) (ready.data.thresholds.read j)≤I := by
    have h := GeneralPaperEncodedFixedVector.bounded W (4*L+64*W+4) (fractionBits W) (ready.data.thresholds.read j) (by
      intro i
      have h := fraction_bound W ready j i
      change fractionBits W ((ready.data.thresholds.read j).read i)≤2*L+16*W at h
      omega)
    exact h.trans_eq (by dsimp only [I,innerProfile]; ring)
  have ho (j : Fin m) : GeneralPaperEncodedFixedVector.footprint W (fun _ : Bool => 1) (ready.data.opened.read j)≤I := by
    have h := GeneralPaperEncodedFixedVector.bounded W (4*L+64*W+4) (fun _ : Bool => 1) (ready.data.opened.read j)
      (fun _ => by omega)
    exact h.trans_eq (by dsimp only [I,innerProfile]; ring)
  have a := GeneralPaperEncodedFixedVector.bounded W I _ ready.data.entries he
  have b := GeneralPaperEncodedFixedVector.bounded W I _ ready.data.codes hc
  have c := GeneralPaperEncodedFixedVector.bounded W I _ ready.data.thresholds hf
  have d := GeneralPaperEncodedFixedVector.bounded W I _ ready.data.opened ho
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) d) (128*W)
  exact h.trans_eq (by unfold profile; change _=4*(m*(I+W)+32*W)+128*W; ring)

end Blotto.GeneralPaperEncodedCatalogueStorage
