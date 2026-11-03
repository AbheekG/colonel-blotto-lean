import Blotto.GeneralPaperNaturalOrderConstructionStorage

/-! Native fixed-grid generation: shared index/height ranges, current
factor and band, retained band suffixes, append buffers and structural map/
flatMap frames. Empty bands and width zero are covered. Primitive scratch
uses the existing complete point-generation operation allowance. -/
namespace Blotto.GeneralPaperGridPointConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperProfitGridPoints
open GeneralPaperProfitPointPrice (width)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem bounded_word (w B x : ℕ) (hx : x≤2*denominator w B) : natBits x≤width w B := by
  have hn := binaryWordWidth_mono hx
  have hp := GeneralPaperNatPowerOperands.power_width 2 B
  have hd := binaryWordWidth_mul (2^B) w
  have he := binaryWordWidth_mul 2 (denominator w B)
  have hw := binaryWordWidth_mono (Nat.le_add_right w 1)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp he
  change binaryWordWidth (denominator w B)≤_ at hd
  unfold natBits width
  omega

theorem point_word (w B x : ℕ) (hx : x∈points w B) : natBits x≤width w B :=
  bounded_word w B x (points_bound w B x hx)

theorem point_list (W w B : ℕ) : listFootprint W natBits (points w B)≤
    (B+1)*w*(width w B+2*W)+32*W := by
  have h := list_bound W (width w B) natBits (points w B) (point_word w B)
  rw [points_length] at h
  exact h

theorem band_list (W w B h : ℕ) (hh : h≤B) : listFootprint W natBits (band w h)≤w*(width w B+2*W)+32*W := by
  have hp : ∀ x∈band w h,natBits x≤width w B := by
    intro x hx
    apply point_word w B x
    change x∈(List.range (B+1)).flatMap (band w)
    exact List.mem_flatMap.mpr ⟨h,List.mem_range.mpr (by omega),hx⟩
  have hBound := list_bound W (width w B) natBits (band w h) hp
  rw [band_length] at hBound
  exact hBound

theorem factor_record (W w B h : ℕ) (hh : h≤B) :
    GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperScoreScaleParameters.powerRun h)≤
      3*(width w B+W)+32*W := by
  have hp := GeneralPaperParameterOperandBounds.dyadic_word h
  have hd := GeneralPaperScoreScaleParameters.power_data h
  have he := GeneralPaperInitializerControlCounters.word_le_self h
  have hw := GeneralPaperInitializerControlCounters.word_le_self (8*h+2)
  unfold GeneralPaperPreparationCacheStorage.powerFootprint
  apply fields_bound W (width w B)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> unfold natBits width
  · omega
  · rw [hd.2.1]; omega
  · rw [hd.2.2]; omega

theorem factor_peak (W w B h : ℕ) (hh : h≤B) :
    GeneralPaperDyadicConstructionStorage.peak W h≤(h+1)*(4*width w B+192*W) := by
  induction h with
  | zero =>
    have hr := factor_record W w B 0 hh
    have h2 : natBits 0=2 := by decide
    simp only [GeneralPaperDyadicConstructionStorage.peak,h2,Nat.zero_add,one_mul]
    unfold width at *
    omega
  | succ h ih =>
    have hr := factor_record W w B (h+1) hh
    have hw := GeneralPaperInitializerControlCounters.word_le_self (h+1)
    have hWord : natBits (h+1)≤width w B := by unfold natBits width; omega
    have hi := ih (by omega)
    rw [GeneralPaperDyadicConstructionStorage.peak]
    nlinarith only [hr,hWord,hi]

theorem range_list (W P n : ℕ) (hw : natBits n≤P) :
    listFootprint W natBits (List.range n)≤n*(P+2*W)+32*W := by
  have h := list_bound W P natBits (List.range n) (by
    intro x hx
    exact (Nat.add_le_add_left (binaryWordWidth_mono (List.mem_range.mp hx).le) 1).trans hw)
  rw [List.length_range] at h
  exact h

def frames (W P n : ℕ) : ℕ := (n+1)*(4*P+128*W)

def window (model : RationalCostModel) (W w B h copied : ℕ) : ℕ :=
  listFootprint W natBits (List.range w)+listFootprint W natBits (List.range (B+1))+
    2*listFootprint W natBits (points w B)+listFootprint W natBits ((points w B).drop copied)+
    listFootprint W natBits (band w h)+GeneralPaperDyadicConstructionStorage.peak W h+
    2*frames W (width w B) w+frames W (width w B) (B+1)+
    (GeneralPaperProfitPointPrice.run model.rat W w B).2+256*W

def profile (model : RationalCostModel) (W w B : ℕ) : ℕ :=
  let P := width w B
  (w*(P+2*W)+32*W)+((B+1)*(P+2*W)+32*W)+3*((B+1)*w*(P+2*W)+32*W)+
    (w*(P+2*W)+32*W)+(B+1)*(4*P+192*W)+2*frames W P w+frames W P (B+1)+
    GeneralPaperProfitPointPrice.profile model.rat W w B+256*W

theorem bounded (model : RationalCostModel) (W w B h copied : ℕ) (hh : h≤B) :
    window model W w B h copied≤profile model W w B := by
  have hw := binaryWordWidth_mono (Nat.le_add_right w 1)
  have hb := GeneralPaperInitializerControlCounters.word_le_self (B+1)
  have hW : natBits w≤width w B := by unfold natBits width; omega
  have hB : natBits (B+1)≤width w B := by unfold natBits width; omega
  have a := range_list W (width w B) w hW
  have b := range_list W (width w B) (B+1) hB
  have c := point_list W w B
  have hd := list_bound W (width w B) natBits ((points w B).drop copied) (fun x hx =>
    point_word w B x (List.mem_of_mem_drop hx))
  have hn : ((points w B).drop copied).length≤(B+1)*w := by rw [List.length_drop,points_length]; omega
  have d := hd.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (width w B+2*W) hn) _)
  have e := band_list W w B h hh
  have f := (factor_peak W w B h hh).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hh 1))
  have hs := GeneralPaperProfitPointPrice.work model.rat model.monotone W w B
  have hSum := Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) (Nat.mul_le_mul_left 2 c)) d) e) f)
      (2*frames W (width w B) w)) (frames W (width w B) (B+1))) hs) (256*W)
  exact hSum.trans_eq (by unfold profile; ring)

end Blotto.GeneralPaperGridPointConstructionStorage
