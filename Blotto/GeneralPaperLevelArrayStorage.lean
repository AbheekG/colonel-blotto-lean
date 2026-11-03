import Blotto.GeneralPaperDeltaArrayStorage

/-! Native level-array addition retains both borrowed input reads, the
unreduced sum, index controls, full reserved buffers/returns/frames and one
guarded primitive callback. No updated-state bound is assumed for sums. -/
namespace Blotto.GeneralPaperLevelArrayStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def elementWindow {n : ℕ} (model : RationalCostModel) (W : ℕ) (current delta : FixedArrayTable n ℕ) (r : Fin n) : ℕ :=
  fields W [current.read r,delta.read r,(GeneralPaperEpochLevelPrice.element model.rat W current delta r).1]+
    fields W [n,r.val]+(GeneralPaperEpochLevelPrice.element model.rat W current delta r).2+256*W

def elementProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  (3*(H+W)+32*W)+(2*(natBits (n+1)+W)+32*W)+2*model.rat H+32*W+256*W

theorem element_bounded {n : ℕ} (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (current delta : FixedArrayTable n ℕ) (r : Fin n)
    (hc : current.read r≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hd : delta.read r≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    elementWindow model W current delta r≤elementProfile model W m lambda k Qv n := by
  let V := GeneralPaperPowerPrecision.levelBound lambda k+8*(GeneralPaperSourceParameters.prepare k).meshDenominator
  have hw : natBits V≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := GeneralPaperEpochLevelPrice.operand_word m lambda k Qv
  have hf := fields_bound W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)
    [current.read r,delta.read r,(GeneralPaperEpochLevelPrice.element model.rat W current delta r).1] (by
      intro x hx
      apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤V from ?_)) 1).trans hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl
      · exact hc.trans (Nat.le_add_right _ _)
      · exact hd.trans (Nat.le_add_left _ _)
      · exact Nat.add_le_add hc hd)
  have hi := GeneralPaperMeshPairStorage.index_fields W n [n,r.val] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · omega
    · exact r.isLt.le.trans (by omega))
  have hp := GeneralPaperEpochLevelPrice.element_work model.rat model.monotone W m lambda k Qv current delta r hc hd
  simp only [List.length_cons,List.length_nil] at hf hi
  dsimp only [elementWindow,elementProfile]
  omega

def active {n : ℕ} (model : RationalCostModel) (W : ℕ) (current delta : FixedArrayTable n ℕ) (count : ℕ) : ℕ :=
  if h : count<n then elementWindow model W current delta ⟨count,h⟩ else 0

def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (current delta : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperNativeNatFillStorage.window W (GeneralPaperEpochLevelPrice.element model.rat W current delta) count hc+
    active model W current delta count+256*W

def profile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  GeneralPaperNativeNatFillStorage.profile W n
      (GeneralPaperPowerPrecision.levelBound lambda k+8*(GeneralPaperSourceParameters.prepare k).meshDenominator)+
    elementProfile model W m lambda k Qv n+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (current delta : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n)
    (hcurrent : ∀ r,current.read r≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hdelta : ∀ r,delta.read r≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    window model W current delta count hc≤profile model W m lambda k Qv n := by
  have hv : ∀ r,(GeneralPaperEpochLevelPrice.element model.rat W current delta r).1≤
      GeneralPaperPowerPrecision.levelBound lambda k+8*(GeneralPaperSourceParameters.prepare k).meshDenominator :=
    fun r => Nat.add_le_add (hcurrent r) (hdelta r)
  have hf := GeneralPaperNativeNatFillStorage.bounded W _ _ hv count hc
  have ha : active model W current delta count≤elementProfile model W m lambda k Qv n := by
    unfold active
    split
    · exact element_bounded model W m lambda k Qv current delta _ (hcurrent _) (hdelta _)
    · exact Nat.zero_le _
  exact Nat.add_le_add_right (Nat.add_le_add hf ha) _

theorem profile_mono (model : RationalCostModel) (W m lambda k Qv n N : ℕ) (hn : n≤N) :
    profile model W m lambda k Qv n≤profile model W m lambda k Qv N := by
  have hf := GeneralPaperRankStorageMonotonicity.native_array W
    (GeneralPaperPowerPrecision.levelBound lambda k+8*(GeneralPaperSourceParameters.prepare k).meshDenominator) n N hn
  have hw := GeneralPaperRankStorageMonotonicity.nat_word (n+1) (N+1) (Nat.add_le_add_right hn 1)
  unfold profile elementProfile
  dsimp only
  gcongr

end Blotto.GeneralPaperLevelArrayStorage
