import Blotto.GeneralPaperGridPointConstructionStorage

/-! Native fixed-grid ordering joins point generation, the exact endpoint
dyadic/denominator records and complete natural ordering. Generated points
and the ordered list may coexist. No source parameter, band or sorter is
replayed by these erased observations. -/
namespace Blotto.GeneralPaperProfitOrderConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem ordered_list (W w B : ℕ) :
    listFootprint W natBits (GeneralPaperProfitGridPrepare.ordered w B)≤
      ((B+1)*w+2)*(GeneralPaperProfitPointPrice.width w B+2*W)+32*W := by
  have h := list_bound W (GeneralPaperProfitPointPrice.width w B) natBits (GeneralPaperProfitGridPrepare.ordered w B)
    (fun x hx => GeneralPaperGridPointConstructionStorage.bounded_word w B x (GeneralPaperSortedBreakpoints.ordered_bound _ _ x hx))
  have hn := GeneralPaperSortedBreakpoints.ordered_length (2*denominator w B) (points w B)
  rw [points_length] at hn
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)

theorem scalar_records (W w B : ℕ) :
    fields W [2^B,denominator w B,2*denominator w B]≤3*(GeneralPaperProfitPointPrice.width w B+W)+32*W := by
  have hDen := GeneralPaperGridPointConstructionStorage.bounded_word w B (denominator w B) (by omega)
  have hEnd := GeneralPaperGridPointConstructionStorage.bounded_word w B (2*denominator w B) (Nat.le_refl _)
  have hp := GeneralPaperNatPowerOperands.power_width 2 B
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  apply fields_bound W _
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · unfold natBits GeneralPaperProfitPointPrice.width; omega
  · exact hDen
  · exact hEnd

def window (model : RationalCostModel) (W w B h copied : ℕ) : ℕ :=
  GeneralPaperGridPointConstructionStorage.window model W w B h copied+
    GeneralPaperNaturalOrderConstructionStorage.window model W (2*denominator w B) (points w B)+
    GeneralPaperDyadicConstructionStorage.peak W B+
    listFootprint W natBits (GeneralPaperProfitGridPrepare.ordered w B)+
    fields W [2^B,denominator w B,2*denominator w B]+(GeneralPaperProfitOrderConstruction.run model.rat W w B).2+128*W

def profile (model : RationalCostModel) (W w B : ℕ) : ℕ :=
  let P := GeneralPaperProfitPointPrice.width w B
  GeneralPaperGridPointConstructionStorage.profile model W w B+
    GeneralPaperNaturalOrderConstructionStorage.profile model W (2*denominator w B) ((B+1)*w)+
    (B+1)*(4*P+192*W)+(((B+1)*w+2)*(P+2*W)+32*W)+
    (3*(P+W)+32*W)+GeneralPaperProfitOrderConstruction.profile model.rat W w B+128*W

theorem bounded (model : RationalCostModel) (W w B h copied : ℕ) (hh : h≤B) :
    window model W w B h copied≤profile model W w B := by
  have a := GeneralPaperGridPointConstructionStorage.bounded model W w B h copied hh
  have b := GeneralPaperNaturalOrderConstructionStorage.bounded model W (2*denominator w B) (points w B) (points_bound w B)
  rw [points_length] at b
  have c := GeneralPaperGridPointConstructionStorage.factor_peak W w B B (Nat.le_refl _)
  have d := ordered_list W w B
  have e := scalar_records W w B
  have hs := GeneralPaperProfitOrderConstruction.work model.rat model.monotone W w B
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) d) e) hs) _

end Blotto.GeneralPaperProfitOrderConstructionStorage
