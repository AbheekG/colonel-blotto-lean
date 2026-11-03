import Blotto.GeneralPaperSourceBasisControllerStorageReachedRates

/-! Literal recursive power-ceiling storage, with all pending/return
frames. Original target/current/returned powers, reached doubled integer,
native depth/work fields and bit-price prefixes are retained. Only local
comparison/doubling charges bound scratch; whole loop work sizes metadata. -/
namespace Blotto.GeneralPaperPowerCeilingStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W R : ℕ) : ℕ := 64*(R+1)*(W+model.rat R)
def metadataCap (model : RationalCostModel) (W R : ℕ) : ℕ := 32*R+price model W R+64*W+32
def controls (model : RationalCostModel) (W target p : ℕ) (hp : 0<p) : List ℕ :=
  let result := GeneralPaperPowerCeilingBits.loop model.rat W target p hp
  let test := GeneralPaperIntegerWordPrice.compare model.rat target p
  [result.1.doublings,result.1.work,result.2,test,16*W,GeneralPaperFinalStaticLoopStorage.bit (decide (target≤p))]++
    if target≤p then [] else
      let later := GeneralPaperPowerCeilingBits.loop model.rat W target (2*p) (by omega)
      let doubled := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 p
      [later.1.doublings,later.1.work,later.2,doubled,32*W,later.1.doublings+1,later.1.work+12,
        later.2+32*W,later.2+32*W+test]
def frame (model : RationalCostModel) (W target p : ℕ) (hp : 0<p) : ℕ :=
  let result := GeneralPaperPowerCeilingBits.loop model.rat W target p hp
  let test := GeneralPaperIntegerWordPrice.compare model.rat target p
  natBits target+natBits p+natBits result.1.power+test+
    (if target≤p then 0 else
      let later := GeneralPaperPowerCeilingBits.loop model.rat W target (2*p) (by omega)
      natBits 2+natBits (2*p)+natBits later.1.power+
        GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 p)+
    fields W (controls model W target p hp)+256*W
def frameProfile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  6*R+3*model.rat R+15*(natBits (metadataCap model W R)+W)+288*W
def window (model : RationalCostModel) (W target p : ℕ) (hp : 0<p) : ℕ :=
  frame model W target p hp+
    if target≤p then 0 else window model W target (2*p) (by omega)
termination_by target-p
decreasing_by omega
def profile (model : RationalCostModel) (W R : ℕ) : ℕ := (R+1)*frameProfile model W R

theorem result_bounds (model : RationalCostModel) (W target p M R : ℕ) (hp : 0<p)
    (hTarget : target≤M) (hP : p≤2*M) (hR : 1+binaryWordWidth (2*M)≤R) :
    let result := GeneralPaperPowerCeilingBits.loop model.rat W target p hp
    result.1.power≤2*M ∧ result.1.doublings≤R ∧ result.1.work≤12*R+2 := by
  dsimp only
  rw [GeneralPaperPowerCeilingBits.loop_data]
  have hs := GeneralPaperPowerCeiling.loop_spec target p hp
  have hd := GeneralPaperPowerCeiling.loop_depth target p hp
  have hw := binaryWordWidth_mono (show target≤2*M by omega)
  refine ⟨?_,by omega,by omega⟩
  by_cases hz : (GeneralPaperPowerCeiling.loop target p hp).doublings=0
  · exact (hs.2.2.1 hz).le.trans hP
  · exact (hs.2.2.2.1 (by omega)).le.trans (Nat.mul_le_mul_left 2 hTarget)

theorem work_bound (model : RationalCostModel) (W target p M R : ℕ) (hp : 0<p) (hM : 0<M)
    (hTarget : target≤M) (hP : p≤2*M) (hR : 1+binaryWordWidth (2*M)≤R) :
    (GeneralPaperPowerCeilingBits.loop model.rat W target p hp).2≤price model W R := by
  have h := GeneralPaperPowerCeilingBits.loop_work model.rat model.monotone W target p M hp hM hTarget hP
  have hd := (result_bounds model W target p M R hp hTarget hP hR).2.1
  exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hd 1))
    (Nat.add_le_add_left (model.monotone hR) W))

theorem frame_bound (model : RationalCostModel) (W target p M R : ℕ) (hp : 0<p) (hM : 0<M)
    (hTarget : target≤M) (hP : p≤2*M) (hR : 1+binaryWordWidth (2*M)≤R) :
    frame model W target p hp≤frameProfile model W R := by
  let result := GeneralPaperPowerCeilingBits.loop model.rat W target p hp
  let test := GeneralPaperIntegerWordPrice.compare model.rat target p
  have hResult := result_bounds model W target p M R hp hTarget hP hR
  have hWork := work_bound model W target p M R hp hM hTarget hP hR
  change result.1.power≤2*M ∧ result.1.doublings≤R ∧ result.1.work≤12*R+2 at hResult
  change result.2≤price model W R at hWork
  have word (n : ℕ) (hn : n≤2*M) : natBits n≤R := (Nat.add_le_add_left (binaryWordWidth_mono hn) 1).trans hR
  have ht := word target (by omega)
  have hpw := word p hP
  have ho := word result.1.power hResult.1
  have hTest : test≤model.rat R := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone target p R ht hpw
  have hBit := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (target≤p))
  have hCount : (controls model W target p hp).length≤15 := by
    unfold controls
    dsimp only
    split <;> norm_num only [List.length_append,List.length_cons,List.length_nil]
  by_cases hStop : target≤p
  · have hFields := fields_bound W (natBits (metadataCap model W R)) (controls model W target p hp) (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,ite_eq_left hStop,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      change z=result.1.doublings ∨ z=result.1.work ∨ z=result.2 ∨ z=test ∨ z=16*W ∨ z=GeneralPaperFinalStaticLoopStorage.bit (decide (target≤p)) at hz
      unfold metadataCap
      have hPrice : model.rat R≤price model W R := by unfold price; nlinarith only [Nat.zero_le (R*model.rat R),Nat.zero_le (R*W),Nat.zero_le W]
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    have hf := hFields.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCount) _)
    unfold frame frameProfile
    rw [ite_eq_left hStop]
    dsimp only
    dsimp only [result,test] at ht hpw ho hTest hf
    omega
  · have hNext : 2*p≤2*M := by omega
    let later := GeneralPaperPowerCeilingBits.loop model.rat W target (2*p) (by omega)
    let doubled := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 p
    have hLater := result_bounds model W target (2*p) M R (by omega) hTarget hNext hR
    change later.1.power≤2*M ∧ later.1.doublings≤R ∧ later.1.work≤12*R+2 at hLater
    have hLaterWork := work_bound model W target (2*p) M R (by omega) hM hTarget hNext hR
    change later.2≤price model W R at hLaterWork
    have hTwo := word 2 (by omega)
    have hDoubleWord := word (2*p) hNext
    have hLaterPower := word later.1.power hLater.1
    have hDouble : doubled≤2*model.rat R := (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b)
      2 p (2*M) (by omega) hP hNext).trans (Nat.mul_le_mul_left 2 (model.monotone hR))
    have hShape : result.2=later.2+32*W+test+doubled := by
      dsimp only [result]
      rw [GeneralPaperPowerCeilingBits.loop,ite_eq_right hStop]
    have hFields := fields_bound W (natBits (metadataCap model W R)) (controls model W target p hp) (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      change z∈[result.1.doublings,result.1.work,result.2,test,16*W,GeneralPaperFinalStaticLoopStorage.bit (decide (target≤p))]++
        (if target≤p then [] else [later.1.doublings,later.1.work,later.2,doubled,32*W,later.1.doublings+1,later.1.work+12,
          later.2+32*W,later.2+32*W+test]) at hz
      rw [ite_eq_right hStop] at hz
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold metadataCap
      rcases hz with (rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega)
    have hf := hFields.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCount) _)
    unfold frame frameProfile
    rw [ite_eq_right hStop]
    dsimp only
    dsimp only [result,test,later,doubled] at ht hpw ho hTest hf hDouble hTwo hDoubleWord hLaterPower
    omega

theorem window_bound (model : RationalCostModel) (W target p M R : ℕ) (hp : 0<p) (hM : 0<M)
    (hTarget : target≤M) (hP : p≤2*M) (hR : 1+binaryWordWidth (2*M)≤R) :
    window model W target p hp≤((GeneralPaperPowerCeilingBits.loop model.rat W target p hp).1.doublings+1)*frameProfile model W R := by
  have hf := frame_bound model W target p M R hp hM hTarget hP hR
  rw [window]
  by_cases hStop : target≤p
  · rw [ite_eq_left hStop,GeneralPaperPowerCeilingBits.loop,ite_eq_left hStop]
    simpa only [Nat.zero_add,Nat.one_mul,Nat.add_zero] using hf
  · have hi := window_bound model W target (2*p) M R (by omega) hM hTarget (by omega) hR
    rw [ite_eq_right hStop,GeneralPaperPowerCeilingBits.loop,ite_eq_right hStop]
    dsimp only
    exact (Nat.add_le_add hf hi).trans_eq (by ring)
termination_by target-p
decreasing_by omega

theorem bounded (model : RationalCostModel) (W target R : ℕ) (hR : 1+binaryWordWidth (2*(target+1))≤R) :
    window model W target 1 (by decide)≤profile model W R := by
  have h := window_bound model W target 1 (target+1) R (by decide) (by omega) (by omega) (by omega) hR
  have hd := (result_bounds model W target 1 (target+1) R (by decide) (by omega) (by omega) hR).2.1
  exact h.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hd 1))

end Blotto.GeneralPaperPowerCeilingStorage
