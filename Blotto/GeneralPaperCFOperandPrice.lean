import Blotto.GeneralPaperCFOperandBounds

/-! Uniform literal arithmetic prices at a reached CF step. All pair,
continuant and raw-product widths follow from the original midpoint pair;
the comparison with D includes D's own constructed width explicitly.
-/
namespace Blotto.GeneralPaperCFOperandPrice
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 6000000

def width (lambda D : ℕ) : ℕ := 64+16*lambda+4*binaryWordWidth D

theorem small_word (lambda x : ℕ) (hx : x<2^lambda) : binaryWordWidth x≤lambda+1 :=
  binaryWordWidth_le_of_lt_pow (by omega)
    (hx.trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)))

def rawWork (primitive : ℕ → ℕ) (q : ℕ) (s : State) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) q s.previousNum+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (q*s.previousNum) s.olderNum+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) q s.previousDen+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (q*s.previousDen) s.olderDen

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (D lambda N M : ℕ)
    (s : State) (h : Valid lambda N M s) (hN : N<2^lambda) (hM : M<2^lambda) (hd : 0<s.denominator) :
    rawWork primitive (GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).quotient s≤
      8*primitive (width lambda D) := by
  let q := (GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).quotient
  let L := width lambda D
  obtain ⟨hq,hpN,hpM,hsN,hsM⟩ := raw_products D lambda N M s h hd
  have hPrev := previous lambda N M s h
  have bound (x : ℕ) (hx : x<2^lambda) : 1+binaryWordWidth x≤L := by
    have hh := small_word lambda x hx
    dsimp [L,width]
    omega
  have wq := bound q (hq.trans_lt h.pair.1)
  have wn := bound s.previousNum (hPrev.1.trans_lt hN)
  have wm := bound s.previousDen (hPrev.2.trans_lt hM)
  have won := bound s.olderNum (h.olderNum.trans_lt hN)
  have wom := bound s.olderDen (h.olderDen.trans_lt hM)
  have wpn := bound (q*s.previousNum) (hpN.trans_lt hN)
  have wpm := bound (q*s.previousDen) (hpM.trans_lt hM)
  have wsn := bound (q*s.previousNum+s.olderNum) (hsN.trans_lt hN)
  have wsm := bound (q*s.previousDen+s.olderDen) (hsM.trans_lt hM)
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) q s.previousNum L wq wn wpn
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (q*s.previousNum) s.olderNum L wpn won wsn
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) q s.previousDen L wq wm wpm
  have hd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (q*s.previousDen) s.olderDen L wpm wom wsm
  change rawWork primitive q s≤8*primitive L
  unfold rawWork
  omega

def checks (primitive : ℕ → ℕ) (D den : ℕ) : ℕ :=
  GeneralPaperIntegerWordPrice.compare primitive 0 den+
    if 0<den then GeneralPaperIntegerWordPrice.compare primitive den D else 0

theorem checks_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (lambda D den : ℕ)
    (hDen : den<2^lambda) : checks primitive D den≤2*primitive (width lambda D) := by
  let L := width lambda D
  have hd := small_word lambda den hDen
  have h0 : binaryWordWidth 0=1 := by decide
  have hA := GeneralPaperIntegerWordPrice.compare_le primitive hMono 0 den L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  have hB := GeneralPaperIntegerWordPrice.compare_le primitive hMono den D L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  change checks primitive D den≤2*primitive L
  unfold checks
  split <;> omega

theorem zero_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (lambda D : ℕ) (s : State)
    (hPair : PairBound lambda s) :
    GeneralPaperIntegerWordPrice.compare primitive s.denominator 0≤primitive (width lambda D) := by
  have hd := small_word lambda s.denominator hPair.2
  have h0 : binaryWordWidth 0=1 := by decide
  apply GeneralPaperIntegerWordPrice.compare_le primitive hMono <;> unfold width <;> omega

theorem division_width (lambda D : ℕ) (s : State) (hPair : PairBound lambda s) :
    GeneralPaperGrowingQuotientBits.width s.numerator s.denominator≤width lambda D := by
  have hn := small_word lambda s.numerator hPair.1
  have hd := small_word lambda s.denominator hPair.2
  unfold GeneralPaperGrowingQuotientBits.width width
  omega

end Blotto.GeneralPaperCFOperandPrice
