import Blotto.GeneralPaperIntegerWordPrice

/-! Price every comparison/doubling/return of the existing constructed
power ceiling. Exact native power, depth and work annotations are retained.
The logarithm occurs only in the proved bound; the program doubles until
the target is reached. No input-encoding query or ceiling oracle is used.
-/
namespace Blotto.GeneralPaperPowerCeilingBits
open GeneralPaperIntegerWordPrice
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def loop (primitive : ℕ → ℕ) (W target p : ℕ) (hp : 0<p) : GeneralPaperPowerCeiling.Result × ℕ :=
  let test := compare primitive target p
  if target≤p then (⟨p,0,2⟩,16*W+test) else
    let later := loop primitive W target (2*p) (by omega)
    (⟨later.1.power,later.1.doublings+1,later.1.work+12⟩,
      later.2+32*W+test+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 p)
termination_by target-p
decreasing_by omega

theorem loop_data (primitive : ℕ → ℕ) (W target p : ℕ) (hp : 0<p) :
    (loop primitive W target p hp).1=GeneralPaperPowerCeiling.loop target p hp := by
  rw [loop,GeneralPaperPowerCeiling.loop]
  split
  · rfl
  · dsimp only
    rw [loop_data primitive W target (2*p) (by omega)]
termination_by target-p
decreasing_by omega

theorem loop_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W target p M : ℕ) (hp : 0<p)
    (hM : 0<M) (hTarget : target≤M) (hP : p≤2*M) :
    (loop primitive W target p hp).2≤64*((loop primitive W target p hp).1.doublings+1)*
      (W+primitive (1+binaryWordWidth (2*M))) := by
  let L := 1+binaryWordWidth (2*M)
  let P := primitive L
  have ht := compare_le primitive hMono target p L
    (Nat.add_le_add_left (binaryWordWidth_mono (by omega : target≤2*M)) 1)
    (Nat.add_le_add_left (binaryWordWidth_mono hP) 1)
  generalize hr : loop primitive W target p hp=result
  rw [loop] at hr
  split at hr
  · subst result
    dsimp only
    change 16*W+compare primitive target p≤64*(0+1)*(W+P)
    change compare primitive target p≤P at ht
    omega
  · rename_i hContinue
    have hNext : 2*p≤2*M := by omega
    have hi := loop_work primitive hMono W target (2*p) M (by omega) hM hTarget hNext
    have hd := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b) 2 p (2*M)
      (by omega) hP (by simpa only [Nat.mul_comm] using hNext)
    subst result
    dsimp only
    change (loop primitive W target (2*p) (by omega)).2+32*W+compare primitive target p+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 p≤
        64*((loop primitive W target (2*p) (by omega)).1.doublings+1+1)*(W+P)
    change (loop primitive W target (2*p) (by omega)).2≤64*((loop primitive W target (2*p) (by omega)).1.doublings+1)*(W+P) at hi
    change compare primitive target p≤P at ht
    change GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 p≤2*P at hd
    nlinarith only [hi,ht,hd]
termination_by target-p
decreasing_by omega

def run (primitive : ℕ → ℕ) (W target : ℕ) : GeneralPaperPowerCeiling.Result × ℕ :=
  loop primitive W target 1 (by decide)

theorem data (primitive : ℕ → ℕ) (W target : ℕ) : (run primitive W target).1=GeneralPaperPowerCeiling.ceiling target :=
  loop_data primitive W target 1 (by decide)

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W target : ℕ) :
    (run primitive W target).2≤64*(binaryWordWidth target+1)*(W+primitive (1+binaryWordWidth (2*(target+1)))) := by
  have hh := loop_work primitive hMono W target 1 (target+1) (by decide) (by omega) (by omega) (by omega)
  rw [loop_data] at hh
  have hd := GeneralPaperPowerCeiling.loop_depth target 1 (by decide)
  have he := Nat.mul_le_mul_right (W+primitive (1+binaryWordWidth (2*(target+1))))
    (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hd 1))
  exact hh.trans he

end Blotto.GeneralPaperPowerCeilingBits
