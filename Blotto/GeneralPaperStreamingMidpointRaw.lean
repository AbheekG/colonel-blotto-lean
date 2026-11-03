import Blotto.GeneralPaperStreamingCFRun

/-! Construct the midpoint pair and execute the full native CF loop once.
All initial arithmetic is charged. The actual amortized native work yields
a linear-in-Lambda number of model.rat prices, including the rejected step.
-/
namespace Blotto.GeneralPaperStreamingMidpointRaw
open GeneralPaperRegularCFLoop GeneralPaperCFOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000

def initialWork (model : RationalCostModel) (C t : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 t+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (2*t) 1+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 C

theorem initial_work (model : RationalCostModel) (D C t lambda : ℕ)
    (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    initialWork model C t≤6*model.rat (GeneralPaperCFOperandPrice.width lambda D) := by
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
  have ha := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 2 t L h2 htW hDouble
  have hb := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) (2*t) 1 L hDouble h1 hNum
  have hc := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 2 C L h2 hCW hDen
  change initialWork model C t≤6*model.rat L
  unfold initialWork
  omega

def run (model : RationalCostModel) (W D C t lambda : ℕ) : State × ℕ :=
  let finished := GeneralPaperStreamingCFRun.run model W D (lambda+2) (2*lambda+4) (initial C t)
  (finished.1,finished.2+initialWork model C t+96*W)

theorem data (model : RationalCostModel) (W D C t lambda : ℕ) :
    (run model W D C t lambda).1=GeneralPaperMidpointQuery.raw D C t lambda :=
  GeneralPaperStreamingCFRun.data model W D (lambda+2) (2*lambda+4) (initial C t)

theorem work (model : RationalCostModel) (W D C t lambda : ℕ)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (run model W D C t lambda).2≤1048576*(lambda+3)*
      (W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  let P := model.rat (GeneralPaperCFOperandPrice.width lambda D)
  let F := W+P
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hN : 2*t+1<2^lambda := hp.1
  have hM : 2*C<2^lambda := hp.2
  have hc := GeneralPaperStreamingCFRun.work model W D lambda (2*lambda+4) (2*t+1) (2*C)
    (initial C t) (initial_valid C t lambda hC ht hPower) hN hM
  have hi := initial_work model D C t lambda hC ht hPower
  have hw := GeneralPaperMidpointRealWork.lookup_real_work D C t lambda hD hC ht hPower
  change (GeneralPaperMidpointQuery.raw D C t lambda).work+32≤170*lambda+370 at hw
  have hb : (GeneralPaperMidpointQuery.raw D C t lambda).work+1≤170*lambda+339 := by omega
  have hm := Nat.mul_le_mul_right F (Nat.mul_le_mul_left 4096 hb)
  change (GeneralPaperStreamingCFRun.run model W D (lambda+2) (2*lambda+4) (initial C t)).2+
    4096*0*F≤4096*((GeneralPaperMidpointQuery.raw D C t lambda).work+1)*F at hc
  change initialWork model C t≤6*P at hi
  change (GeneralPaperStreamingCFRun.run model W D (lambda+2) (2*lambda+4) (initial C t)).2+
    initialWork model C t+96*W≤1048576*(lambda+3)*F
  have hWF : W≤F := Nat.le_add_right _ _
  have hPF : P≤F := Nat.le_add_left _ _
  nlinarith only [hc,hi,hm,hWF,hPF,Nat.zero_le (lambda*F)]

theorem valid (model : RationalCostModel) (W D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    Valid lambda (2*t+1) (2*C) (run model W D C t lambda).1 := by
  rw [data]
  exact midpoint_all_prefixes D C t lambda (2*lambda+4) hC ht hPower

end Blotto.GeneralPaperStreamingMidpointRaw
