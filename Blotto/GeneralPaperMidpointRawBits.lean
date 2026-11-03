import Blotto.GeneralPaperCFRunBits

/-! Construct the midpoint pair and execute the full native CF loop once.
All initial arithmetic is charged. The actual amortized native work yields
a linear-in-Lambda number of primitive prices, including the rejected step.
-/
namespace Blotto.GeneralPaperMidpointRawBits
open GeneralPaperRegularCFLoop GeneralPaperCFOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000

def initialWork (primitive : ℕ → ℕ) (C t : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 t+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (2*t) 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 C

theorem initial_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (D C t lambda : ℕ)
    (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    initialWork primitive C t≤6*primitive (GeneralPaperCFOperandPrice.width lambda D) := by
  let L := GeneralPaperCFOperandPrice.width lambda D
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hN : 2*t+1<2^lambda := hp.1
  have hM : 2*C<2^lambda := hp.2
  have bound (x : ℕ) (hx : x<2^lambda) : 1+binaryWordWidth x≤L := by
    have hh := GeneralPaperCFOperandPrice.small_word lambda x hx
    dsimp [L,GeneralPaperCFOperandPrice.width]
    omega
  have htW := bound t (by omega)
  have hCW := bound C (by omega)
  have hDouble := bound (2*t) (by omega)
  have hNum := bound (2*t+1) hN
  have hDen := bound (2*C) hM
  have h1 : 1+binaryWordWidth 1≤L := by
    have hh : binaryWordWidth 1=1 := by decide
    dsimp [L,GeneralPaperCFOperandPrice.width]
    rw [hh]
    omega
  have h2 : 1+binaryWordWidth 2≤L := by
    have hh : binaryWordWidth 2=2 := by decide
    dsimp [L,GeneralPaperCFOperandPrice.width]
    rw [hh]
    omega
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 t L h2 htW hDouble
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (2*t) 1 L hDouble h1 hNum
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 2 C L h2 hCW hDen
  change initialWork primitive C t≤6*primitive L
  unfold initialWork
  omega

def run (primitive : ℕ → ℕ) (W D C t lambda : ℕ) : State × ℕ :=
  let finished := GeneralPaperCFRunBits.run primitive W D (lambda+2) (2*lambda+4) (initial C t)
  (finished.1,finished.2+initialWork primitive C t+96*W)

theorem data (primitive : ℕ → ℕ) (W D C t lambda : ℕ) :
    (run primitive W D C t lambda).1=GeneralPaperMidpointQuery.raw D C t lambda :=
  GeneralPaperCFRunBits.data primitive W D (lambda+2) (2*lambda+4) (initial C t)

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D C t lambda : ℕ)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (run primitive W D C t lambda).2≤1048576*(lambda+3)*
      (W+primitive (GeneralPaperCFOperandPrice.width lambda D)) := by
  let P := primitive (GeneralPaperCFOperandPrice.width lambda D)
  let F := W+P
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hN : 2*t+1<2^lambda := hp.1
  have hM : 2*C<2^lambda := hp.2
  have hc := GeneralPaperCFRunBits.work primitive hMono W D lambda (2*lambda+4) (2*t+1) (2*C)
    (initial C t) (initial_valid C t lambda hC ht hPower) hN hM
  have hi := initial_work primitive hMono D C t lambda hC ht hPower
  have hw := GeneralPaperMidpointRealWork.lookup_real_work D C t lambda hD hC ht hPower
  change (GeneralPaperMidpointQuery.raw D C t lambda).work+32≤170*lambda+370 at hw
  have hb : (GeneralPaperMidpointQuery.raw D C t lambda).work+1≤170*lambda+339 := by omega
  have hm := Nat.mul_le_mul_right F (Nat.mul_le_mul_left 4096 hb)
  change (GeneralPaperCFRunBits.run primitive W D (lambda+2) (2*lambda+4) (initial C t)).2+
    4096*0*F≤4096*((GeneralPaperMidpointQuery.raw D C t lambda).work+1)*F at hc
  change initialWork primitive C t≤6*P at hi
  change (GeneralPaperCFRunBits.run primitive W D (lambda+2) (2*lambda+4) (initial C t)).2+
    initialWork primitive C t+96*W≤1048576*(lambda+3)*F
  have hWF : W≤F := Nat.le_add_right _ _
  have hPF : P≤F := Nat.le_add_left _ _
  nlinarith only [hc,hi,hm,hWF,hPF,Nat.zero_le (lambda*F)]

theorem valid (primitive : ℕ → ℕ) (W D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    Valid lambda (2*t+1) (2*C) (run primitive W D C t lambda).1 := by
  rw [data]
  exact midpoint_all_prefixes D C t lambda (2*lambda+4) hC ht hPower

end Blotto.GeneralPaperMidpointRawBits
