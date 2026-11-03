import Blotto.GeneralPaperPrecallLoopWords

/-! The constructed power exponents themselves fit the shared control
word. Their produced powers dominate 2^exponent, so the existing measured
target widths bound each index, including every halved recursive exponent.
-/
namespace Blotto.GeneralPaperPrecallIndexWords
open GeneralPaperPrecallControlWord
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem exponent_le_word (e value : ℕ) (h : 2^e≤value) : e≤binaryWordWidth value := by
  have hv : 0<value := (Nat.two_pow_pos e).trans_le h
  have hh := (Nat.le_log2 hv.ne').mpr h
  unfold binaryWordWidth
  omega

theorem root_exponent (m k : ℕ) : (GeneralPaperProxyParameters.prepare m k).d+2≤measure m k := by
  let r := GeneralPaperProxyParameters.prepare m k
  have hPow : 2^(r.d+2)≤r.H := by
    rw [(GeneralPaperProxyParameters.data m k).2.2.2.1]
    exact Nat.pow_le_pow_left (by omega : 2≤m+3) _
  have he := exponent_le_word (r.d+2) r.H hPow
  have hPos := GeneralPaperProxyParameters.H_positive m k
  have hSquare : r.H≤r.H*r.H := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left r.H (show 1≤r.H by exact hPos)
  have hTarget : r.H≤4*r.H*r.H := by nlinarith only [hSquare]
  have hw := binaryWordWidth_mono hTarget
  have ht := (terms m k).2.2.2.1
  change binaryWordWidth (4*r.H*r.H)+1≤measure m k at ht
  change r.d+2≤measure m k
  omega

theorem alphabet_exponent (m k : ℕ) :
    (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J≤measure m k := by
  let r := GeneralPaperProxyParameters.prepare m k
  let a := GeneralPaperComparatorParameters.prepare m k r.qbar
  have hq := GeneralPaperProxyParameters.cap_positive m k
  have hData : a.D=r.qbar*(m+2)^a.J := (GeneralPaperComparatorParameters.data m k r.qbar).2.2.1
  have hPow : 2^a.J≤a.D := by
    rw [hData]
    have hb := Nat.pow_le_pow_left (by omega : 2≤m+2) a.J
    have hq1 : 1≤r.qbar := hq
    have hm := Nat.mul_le_mul_right ((m+2)^a.J) hq1
    exact hb.trans (by simpa only [one_mul] using hm)
  have he := exponent_le_word a.J a.D hPow
  have hPos := GeneralPaperComparatorParameters.denominator_positive m k r.qbar hq
  have hSquare : a.D≤a.D*a.D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a.D (show 1≤a.D by exact hPos)
  have hTarget : a.D≤4*a.D*a.D := by nlinarith only [hSquare]
  have hw := binaryWordWidth_mono hTarget
  have ht := (terms m k).2.2.2.2.2.1
  change binaryWordWidth (4*a.D*a.D)+1≤measure m k at ht
  change a.J≤measure m k
  omega

theorem recursive_indices (m k exponent : ℕ)
    (he : exponent≤(GeneralPaperProxyParameters.prepare m k).d+2 ∨
      exponent≤(GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J) :
    binaryWordWidth exponent≤word m k ∧ binaryWordWidth (exponent/2)≤word m k ∧
      binaryWordWidth (exponent%2)≤word m k := by
  have hE : exponent≤measure m k := he.elim
    (fun h => h.trans (root_exponent m k)) (fun h => h.trans (alphabet_exponent m k))
  have hw := measured m k exponent hE
  have hh := binaryWordWidth_mono (show exponent/2≤exponent by omega)
  have hMod : exponent%2≤cap m k := by have hm:=Nat.mod_lt exponent (by decide : 0<2); unfold cap; omega
  have hm := bounded m k (exponent%2) hMod
  omega

theorem dyadic_indices (m k exponent : ℕ) (he : exponent≤17+k) :
    binaryWordWidth exponent≤word m k ∧ binaryWordWidth (exponent+1)≤word m k := by
  have ht := (terms m k).1
  have hw := measured m k (exponent+1) (by omega)
  have hm := binaryWordWidth_mono (show exponent≤exponent+1 by omega)
  omega

end Blotto.GeneralPaperPrecallIndexWords
