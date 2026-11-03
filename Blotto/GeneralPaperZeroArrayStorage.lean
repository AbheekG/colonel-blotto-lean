import Blotto.GeneralPaperSelectedRowConstructionStorage

/-! Native zero fills count reserved buffers, full returns, frames, literal
writes and one guarded primitive scratch window. Empty/finished prefixes
select no callback; no previous level array is copied. -/
namespace Blotto.GeneralPaperZeroArrayStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def callback (model : RationalCostModel) (W n : ℕ) (_ : Fin n) : ℕ × ℕ := (0,model.rat 1+16*W)

theorem native_data (model : RationalCostModel) (W n : ℕ) :
    (PaperIndexedArrayConstruction.run (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W n) (callback model W n)).1=
      (GeneralPaperEpochZeroArrayPrice.run true (fun w => w) model.rat W n).1 := rfl

def active (model : RationalCostModel) (W n count : ℕ) : ℕ :=
  if count<n then model.rat 1+natBits 0+64*W else 0

def window (model : RationalCostModel) (W n count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperNativeNatFillStorage.window W (callback model W n) count hc+active model W n count+256*W

def profile (model : RationalCostModel) (W n : ℕ) : ℕ :=
  GeneralPaperNativeNatFillStorage.profile W n 0+model.rat 1+natBits 0+320*W

theorem bounded (model : RationalCostModel) (W n count : ℕ) (hc : count≤n) :
    window model W n count hc≤profile model W n := by
  have hf := GeneralPaperNativeNatFillStorage.bounded W 0 (callback model W n) (fun _ => Nat.le_refl _) count hc
  have ha : active model W n count≤model.rat 1+natBits 0+64*W := by
    unfold active
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  unfold window profile
  omega

theorem profile_mono (model : RationalCostModel) (W n N : ℕ) (hn : n≤N) : profile model W n≤profile model W N := by
  have hf := GeneralPaperRankStorageMonotonicity.native_array W 0 n N hn
  unfold profile
  omega

end Blotto.GeneralPaperZeroArrayStorage
