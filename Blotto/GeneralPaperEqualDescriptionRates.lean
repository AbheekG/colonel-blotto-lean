import Blotto.GeneralPaperEqualNativeRetainedStorage
import Blotto.GeneralPaperReferenceCapacity

/-! A complete retained-description bound with an internally derived safe
reference width. Original budget length is additive; only its logarithm enters
the reference overhead. This does not assert a preparation lifetime bound. -/
namespace Blotto.GeneralPaperEqualDescriptionRates
open GeneralPaperEqualNativeRetainedStorage GeneralPaperEqualRetainedStorage
open GeneralPaperEncodedBasisStorage (arrayProfile)
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualStoredBitSampler (native)
open GeneralPaperEqualBitDrawRates (log)
set_option autoImplicit false
set_option maxHeartbeats 1500000

def bound (W n k b : ℕ) : ℕ :=
  17179869184 * (n + 1) * short n k * (W + 1) + b + 2 * log n k b + 4

theorem profile_bound (W n k b : ℕ) : profile W n k b ≤ bound W n k b := by
  let q := short n k
  let D := (n + 1) * q * (W + 1)
  have hq : 1 ≤ q := by dsimp [q, short]; omega
  have hk : k ≤ q := by dsimp [q, short]; omega
  have hNQ : n * q ≤ D := by
    dsimp [D]
    exact (Nat.mul_le_mul_right q (Nat.le_succ n)).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((n + 1) * q) (show 1 ≤ W + 1 by omega))
  have hQ : q ≤ D := by
    have h := Nat.le_mul_of_pos_left q (show 0 < n + 1 by omega)
    exact h.trans (by dsimp [D]; simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((n + 1) * q) (show 1 ≤ W + 1 by omega))
  have hQW : q * W ≤ D := by
    dsimp [D]
    calc
      _ ≤ ((n + 1) * q) * W := Nat.mul_le_mul_right W (Nat.le_mul_of_pos_left q (by omega))
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hNW : n * W ≤ D := by
    have hnq : n ≤ n * q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hq
    exact (Nat.mul_le_mul_right W hnq).trans (by
      dsimp [D]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right q (Nat.le_succ n)) (show W ≤ W + 1 by omega))
  have hW : W ≤ D := (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W hq : W ≤ q * W).trans hQW
  have hN : n ≤ D := (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hq : n ≤ n * q).trans hNQ
  have hOne : 1 ≤ D := hq.trans hQ
  have h3 : binaryWordWidth 3 = 2 := by decide
  have h7 : binaryWordWidth 7 = 3 := by decide
  unfold profile preparedProfile segmentProfile cacheProfile wordProfile arrayProfile height bound
  rw [h3, h7]
  dsimp only [D, q] at hNQ hQ hQW hNW hW hN hOne hk
  nlinarith only [hNQ, hQ, hQW, hNW, hW, hN, hOne, hk]

def reference (n k b : ℕ) : ℕ := GeneralPaperReferenceCapacity.referenceWord (bound 1 n k b)

theorem scaling (n k b : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => bound W n k b) := by
  unfold bound
  fun_prop

theorem capacity (n k b : ℕ) : bound (reference n k b) n k b < 2 ^ reference n k b :=
  GeneralPaperReferenceCapacity.profile_capacity _ (scaling n k b)

theorem reference_bound (n k b : ℕ) : reference n k b ≤ 160 * log n k b := by
  let a := n + GeneralPaperEqualBitDrawRates.word n k b + 32
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : n + 1 ≤ a := by dsimp [a]; omega
  have hq : short n k ≤ a := by
    dsimp [a, GeneralPaperEqualBitDrawRates.word, GeneralPaperEqualBitDrawRates.size, short]
    omega
  have hb : b ≤ a := by
    dsimp [a, GeneralPaperEqualBitDrawRates.word, GeneralPaperEqualBitDrawRates.size]
    omega
  have hl : log n k b ≤ a + 2 := by
    have h := Nat.log2_le_self a
    change a.log2 + 2 ≤ a + 2
    omega
  have hprod := Nat.mul_le_mul hn hq
  have haa : a ≤ a * a := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left a ha
  have hC : bound 1 n k b ≤ 68719476736 * a * a := by
    unfold bound
    nlinarith only [hprod, hb, hl, ha, haa]
  have hw := binaryWordWidth_mono hC
  have hp := binaryWordWidth_mul (68719476736 * a) a
  have hpa := binaryWordWidth_mul 68719476736 a
  have hc : binaryWordWidth 68719476736 = 37 := by decide
  rw [hc] at hpa
  change 4 * binaryWordWidth (bound 1 n k b) ≤ 160 * (binaryWordWidth a + 1)
  omega

def paperBound (n k b : ℕ) : ℕ :=
  4398046511104 * (n + 1) * short n k * log n k b + b

theorem bound_at_reference (n k b : ℕ) : bound (reference n k b) n k b ≤ paperBound n k b := by
  have hw := reference_bound n k b
  have hl : 1 ≤ log n k b := by unfold log; omega
  have hq : 1 ≤ short n k := by unfold short; omega
  have he : 1 ≤ (n + 1) * short n k := by nlinarith only [hq]
  have hL : log n k b ≤ (n + 1) * short n k * log n k b := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (log n k b) he
  have hE : 1 ≤ (n + 1) * short n k * log n k b := hl.trans hL
  have hW1 : reference n k b + 1 ≤ 161 * log n k b := by omega
  have hProduct := Nat.mul_le_mul_left (17179869184 * (n + 1) * short n k) hW1
  unfold bound paperBound
  nlinarith only [hProduct, hL, hE]

theorem native_description {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model Wv k values v hv).weight j ≤ 1) (budget : ℚ) :
    let b := rationalWordWidth budget
    let W := reference n k b
    footprint W (native bits model Wv k values v hv small budget) ≤ bound W n k b ∧
      footprint W (native bits model Wv k values v hv small budget) < 2 ^ W := by
  dsimp only
  have h := (native_bound bits model Wv (reference n k (rationalWordWidth budget)) k values v hv small budget).trans
    (profile_bound _ n k (rationalWordWidth budget))
  exact ⟨h, h.trans_lt (capacity n k (rationalWordWidth budget))⟩

theorem paperBound_mono (n : ℕ) {k K b B : ℕ} (hk : k ≤ K) (hb : b ≤ B) :
    paperBound n k b ≤ paperBound n K B := by
  have hq : short n k ≤ short n K := by unfold short; omega
  have hw : GeneralPaperEqualBitDrawRates.word n k b ≤ GeneralPaperEqualBitDrawRates.word n K B := by
    unfold GeneralPaperEqualBitDrawRates.word GeneralPaperEqualBitDrawRates.size
    omega
  have hl : log n k b ≤ log n K B :=
    Nat.add_le_add_right (binaryWordWidth_mono (by omega : n + GeneralPaperEqualBitDrawRates.word n k b + 32 ≤
      n + GeneralPaperEqualBitDrawRates.word n K B + 32)) 1
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left (4398046511104 * (n + 1)) hq) hl) hb

theorem native_paper_description {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model Wv k values v hv).weight j ≤ 1) (budget : ℚ) :
    let b := rationalWordWidth budget
    let W := reference n k b
    footprint W (native bits model Wv k values v hv small budget) ≤ paperBound n k b ∧
      footprint W (native bits model Wv k values v hv small budget) < 2 ^ W := by
  dsimp only
  have h := native_description bits model Wv k values v hv small budget
  exact ⟨h.1.trans (bound_at_reference n k (rationalWordWidth budget)), h.2⟩

theorem accuracy_description {n L0 : ℕ} (bits : Bool) (model : RationalCostModel) (Wv : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ)
    (small : ∀ j, 2 * (rounded bits model Wv (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : RationalHeight budget L0) :
    let k := (GeneralPaperDyadicAccuracy.prepare eps).exponent
    let W := reference n k (rationalWordWidth budget)
    footprint W (native bits model Wv k values v hv small budget) ≤
      paperBound n (binaryWordWidth ⌈eps⁻¹⌉₊) (1 + 2 * L0) ∧
      footprint W (native bits model Wv k values v hv small budget) < 2 ^ W := by
  dsimp only
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by
    have h0 := GeneralPaperDyadicAccuracy.prepare_work eps
    have h1 := GeneralPaperDyadicAccuracy.prepare_work_exact eps
    omega
  have h := native_paper_description bits model Wv (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
  exact ⟨h.1.trans (paperBound_mono n hk (rationalWordWidth_of_height hB)), h.2⟩

end Blotto.GeneralPaperEqualDescriptionRates
