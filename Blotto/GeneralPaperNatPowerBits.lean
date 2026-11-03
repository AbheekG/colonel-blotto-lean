import Blotto.GeneralPaperNatPowerOperands

/-! Bit-priced execution of the native repeated-squaring constructor.
Zero/parity tests, quotient/remainder, both raw multiplications and all
control/return writes are charged. The full native record is preserved.
-/
namespace Blotto.GeneralPaperNatPowerBits
open GeneralPaperIntegerWordPrice
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W base exponent : ℕ) : GeneralPaperNatPower.Result × ℕ :=
  let test := compare primitive exponent 0
  if exponent=0 then (⟨1,0,2⟩,16*W+test) else
    let earlier := run primitive W base (exponent/2)
    let square := earlier.1.power*earlier.1.power
    let value := if exponent%2=0 then square else square*base
    let extra := if exponent%2=0 then 0 else
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) square base
    (⟨value,earlier.1.steps+1,earlier.1.work+12⟩,
      earlier.2+48*W+test+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a/b) exponent 2+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a%b) exponent 2+
        compare primitive (exponent%2) 0+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) earlier.1.power earlier.1.power+extra)
termination_by exponent
decreasing_by omega

theorem data (primitive : ℕ → ℕ) (W base exponent : ℕ) :
    (run primitive W base exponent).1=GeneralPaperNatPower.run base exponent := by
  rw [run,GeneralPaperNatPower.run]
  split
  · rfl
  · dsimp only
    rw [data primitive W base (exponent/2)]
termination_by exponent
decreasing_by omega

theorem bounded_work (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W base exponent M : ℕ) (hb : 0<base) (h2 : 2≤M)
    (hBase : base≤M) (hExp : exponent≤M) (hPower : base^exponent≤M) :
    (run primitive W base exponent).2≤64*((run primitive W base exponent).1.steps+1)*
      (W+primitive (1+binaryWordWidth M)) := by
  let L := 1+binaryWordWidth M
  let P := primitive L
  have bound (n : ℕ) (hn : n≤M) : 1+binaryWordWidth n≤L :=
    Nat.add_le_add_left (binaryWordWidth_mono hn) 1
  have ht := compare_le primitive hMono exponent 0 L (bound exponent hExp) (bound 0 (by omega))
  generalize hr : run primitive W base exponent=result
  rw [run] at hr
  split at hr
  · subst result
    dsimp only
    change 16*W+compare primitive exponent 0≤64*(0+1)*(W+P)
    change compare primitive exponent 0≤P at ht
    omega
  · rename_i hn
    have hh := GeneralPaperNatPowerOperands.half_power base exponent hb
    have hHalf : base^(exponent/2)≤M := by
      rw [←(GeneralPaperNatPower.data base (exponent/2)).1]
      exact hh.1.trans hPower
    have hi := bounded_work primitive hMono W base (exponent/2) M hb h2 hBase (by omega) hHalf
    have hdiv := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a/b) exponent 2 M hExp h2 (by omega)
    have hmod := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a%b) exponent 2 M hExp h2 (by omega)
    have hp := compare_le primitive hMono (exponent%2) 0 L (bound _ (by omega)) (bound 0 (by omega))
    have hsq := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b)
      (run primitive W base (exponent/2)).1.power (run primitive W base (exponent/2)).1.power M
      (by rw [data]; exact hh.1.trans hPower) (by rw [data]; exact hh.1.trans hPower)
      (by rw [data]; exact hh.2.trans hPower)
    have he : (if exponent%2=0 then 0 else
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b)
          ((run primitive W base (exponent/2)).1.power*(run primitive W base (exponent/2)).1.power) base)≤2*P := by
      split
      · exact Nat.zero_le _
      · rename_i ho
        have hn : exponent=exponent/2+exponent/2+1 := by
          have hm := Nat.mod_add_div exponent 2
          have hr := Nat.mod_lt exponent (by decide : 0<2)
          omega
        apply GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b) _ base M
          (by rw [data]; exact hh.2.trans hPower) hBase
        rw [data,(GeneralPaperNatPower.data base (exponent/2)).1,←pow_add,←pow_succ,←hn]
        exact hPower
    subst result
    dsimp only
    change (run primitive W base (exponent/2)).2+48*W+compare primitive exponent 0+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a/b) exponent 2+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a%b) exponent 2+
      compare primitive (exponent%2) 0+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b)
        (run primitive W base (exponent/2)).1.power (run primitive W base (exponent/2)).1.power+
      (if exponent%2=0 then 0 else GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b)
        ((run primitive W base (exponent/2)).1.power*(run primitive W base (exponent/2)).1.power) base)≤
      64*((run primitive W base (exponent/2)).1.steps+1+1)*(W+P)
    change (run primitive W base (exponent/2)).2≤64*((run primitive W base (exponent/2)).1.steps+1)*(W+P) at hi
    change compare primitive exponent 0≤P at ht
    change compare primitive (exponent%2) 0≤P at hp
    change _≤2*P at hdiv hmod hsq
    nlinarith only [hi,ht,hdiv,hmod,hp,hsq,he]
termination_by exponent
decreasing_by omega

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W base exponent : ℕ) (hb : 0<base) :
    (run primitive W base exponent).2≤64*(binaryWordWidth exponent+1)*
      (W+primitive (GeneralPaperNatPowerOperands.width base exponent)) := by
  let M := GeneralPaperNatPowerOperands.magnitude base exponent
  have hh := bounded_work primitive hMono W base exponent M hb (by dsimp [M,GeneralPaperNatPowerOperands.magnitude]; omega)
    (by dsimp [M,GeneralPaperNatPowerOperands.magnitude]; omega)
    (by dsimp [M,GeneralPaperNatPowerOperands.magnitude]; omega)
    (by dsimp [M,GeneralPaperNatPowerOperands.magnitude]; omega)
  rw [data] at hh
  have hs := GeneralPaperNatPower.steps_le base exponent (binaryWordWidth exponent) (lt_pow_binaryWordWidth exponent)
  have hp := hMono (GeneralPaperNatPowerOperands.magnitude_width base exponent)
  exact hh.trans (Nat.mul_le_mul
    (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hs 1)) (Nat.add_le_add_left hp W))

end Blotto.GeneralPaperNatPowerBits
