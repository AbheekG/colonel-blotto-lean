import Blotto.GeneralPaperDyadicConstructionStorage

/-! Native doubling-until-target frames, including zero targets. Every
reached current power is at most twice target+1; native return metadata
comes from the same loop. The word is derived from the constructed target,
and is never supplied to or inspected by the executable loop. -/
namespace Blotto.GeneralPaperCeilingConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPowerCeiling
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def word (target : ℕ) : ℕ := 128+16*binaryWordWidth (target+1)

def frame (W target p : ℕ) (hp : 0<p) : ℕ :=
  let r := loop target p hp
  fields W [target,p,r.power,r.doublings,r.work]+128*W

theorem frame_bound (W target p : ℕ) (hp : 0<p) (hc : p≤2*(target+1)) :
    frame W target p hp≤5*word target+192*W := by
  let r := loop target p hp
  have hs := loop_spec target p hp
  have hd := loop_depth target p hp
  have hPower : r.power≤2*(target+1) := by
    by_cases hz : r.doublings=0
    · have h := hs.2.2.1 hz
      dsimp only [r] at hz
      change r.power=p at h
      omega
    · exact (hs.2.2.2.1 (by dsimp only [r] at hz; omega)).le.trans (by omega)
  have h2 : binaryWordWidth 2=2 := by decide
  have hm := binaryWordWidth_mul 2 (target+1)
  have ht := binaryWordWidth_mono (Nat.le_add_right target 1)
  have hpW := binaryWordWidth_mono hc
  have hP := binaryWordWidth_mono hPower
  have hD := GeneralPaperInitializerControlCounters.word_le_self r.doublings
  have hW := GeneralPaperInitializerControlCounters.word_le_self r.work
  change r.doublings≤binaryWordWidth target at hd
  have hWork : r.work=12*r.doublings+2 := hs.2.2.2.2
  have hFields := fields_bound W (word target) [target,p,r.power,r.doublings,r.work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|hx|hx|hx|hx <;> rw [hx] <;> unfold natBits word <;> omega)
  change fields W [target,p,r.power,r.doublings,r.work]+128*W≤_
  dsimp only [List.length_cons,List.length_nil] at hFields
  omega

def peak (W target p : ℕ) (hp : 0<p) : ℕ :=
  frame W target p hp+if target≤p then 0 else peak W target (2*p) (by omega)
termination_by target-p
decreasing_by omega

theorem bounded (W target p : ℕ) (hp : 0<p) (hc : p≤2*(target+1)) :
    peak W target p hp≤((loop target p hp).doublings+1)*(5*word target+192*W) := by
  have hf := frame_bound W target p hp hc
  rw [peak]
  split
  · rename_i hStop
    rw [loop,ite_eq_left hStop]
    dsimp only
    omega
  · rename_i hContinue
    have hi := bounded W target (2*p) (by omega) (by omega)
    rw [loop,ite_eq_right hContinue]
    dsimp only
    exact (Nat.add_le_add hf hi).trans_eq (by ring)
termination_by target-p
decreasing_by omega

theorem source_word (m lambda k Qv target : ℕ)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m lambda k Qv target) :
    word target≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have h := GeneralPaperSourcePreparationControls.target_word m lambda k Qv target ht
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add target 1
  have h1 : binaryWordWidth 1=1 := by decide
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold word GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem record (W target : ℕ) :
    GeneralPaperPreparationCacheStorage.powerFootprint W (ceiling target)≤5*word target+192*W := by
  have hf := frame_bound W target 1 (by decide) (by omega)
  have hSub : GeneralPaperPreparationCacheStorage.powerFootprint W (ceiling target)≤frame W target 1 (by decide) := by
    unfold GeneralPaperPreparationCacheStorage.powerFootprint frame ceiling fields
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  exact hSub.trans hf

theorem source_record (W m lambda k Qv target : ℕ)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m lambda k Qv target) :
    GeneralPaperPreparationCacheStorage.powerFootprint W (ceiling target)≤
      5*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+192*W :=
  (record W target).trans (by have h := source_word m lambda k Qv target ht; omega)

def window (model : RationalCostModel) (W target : ℕ) : ℕ :=
  peak W target 1 (by decide)+(GeneralPaperPowerCeilingBits.run model.rat W target).2

theorem source (model : RationalCostModel) (W m lambda k Qv target : ℕ)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m lambda k Qv target) :
    window model W target≤
      (128*GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
        (5*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+192*W)+
      64*(128*GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
        (W+model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have hw := source_word m lambda k Qv target ht
  have htW := GeneralPaperSourcePreparationControls.target_word m lambda k Qv target ht
  have hd := loop_depth target 1 (by decide)
  have hp := bounded W target 1 (by decide) (by omega)
  have hs := GeneralPaperPowerCeilingBits.work model.rat model.monotone W target
  have hPower := binaryWordWidth_mul 2 (target+1)
  have h2 : binaryWordWidth 2=2 := by decide
  have hOperand : 1+binaryWordWidth (2*(target+1))≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    unfold word at hw
    omega
  have hStack := hp.trans (Nat.mul_le_mul (Nat.add_le_add_right (hd.trans htW) 1) (by omega :
    5*word target+192*W≤5*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+192*W))
  have hScratch := hs.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.add_le_add_right htW 1))
    (Nat.add_le_add_left (model.monotone hOperand) W))
  exact Nat.add_le_add hStack hScratch

end Blotto.GeneralPaperCeilingConstructionStorage
