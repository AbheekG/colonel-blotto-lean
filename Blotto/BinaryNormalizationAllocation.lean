import Blotto.BinaryDivisionAllocation
import Blotto.BinaryRationalNormalization

/-! Structural Boolean/list-cell storage for the native Euclidean GCD and
rational normalizer. The observer keeps all allocated cells and every held
input, division result and recursive control frame until return. It therefore
overcounts sharing and lifetime shortening. It is an explicit abstract
no-release storage model, not a physical heap, compiler or GC guarantee.
The original certified `2*(width+1)` Euclidean fuel is preserved. -/

namespace Blotto.BinaryNormalizationAllocation

open BinaryRationalNormalization

def scanWithFrames : List Bool → Bool × ℕ
  | [] => (false, 1)
  | bit :: rest =>
      if bit then (true, 1) else
        let later := scanWithFrames rest
        (later.1, 1 + later.2)

theorem scanWithFrames_state (bits : List Bool) :
    (scanWithFrames bits).1 = BinaryEuclideanGCD.nonzero bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit
      · change (scanWithFrames rest).1 = rest.any id
        exact ih
      · rfl

theorem scanWithFrames_bound (bits : List Bool) :
    (scanWithFrames bits).2 ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [scanWithFrames]
  | cons bit rest ih =>
      cases bit
      · simp only [scanWithFrames, Bool.false_eq_true, ite_false, List.length_cons]
        omega
      · simp [scanWithFrames]

def gcdLoopAllocated : ℕ → List Bool → List Bool → ℕ
  | 0, _first, _second => 1
  | fuel + 1, first, second =>
      (scanWithFrames second).2 + 2 + if BinaryEuclideanGCD.nonzero second then
        (BinaryDivisionAllocation.divideWithAllocation first second).2 +
          gcdLoopAllocated fuel second (BinaryLongDivision.divide first second).2
      else 0

def gcdLoopWithAllocation : ℕ → List Bool → List Bool → List Bool × ℕ
  | 0, first, _second => (first, 1)
  | fuel + 1, first, second =>
      let scan := scanWithFrames second
      if scan.1 then
        let divided := BinaryDivisionAllocation.divideWithAllocation first second
        let later := gcdLoopWithAllocation fuel second divided.1.2
        (later.1, scan.2 + 2 + divided.2 + later.2)
      else (first, scan.2 + 2)

theorem gcdLoopWithAllocation_refines (fuel : ℕ) (first second : List Bool) :
    gcdLoopWithAllocation fuel first second =
      (BinaryEuclideanGCD.loop fuel first second, gcdLoopAllocated fuel first second) := by
  induction fuel generalizing first second with
  | zero => rfl
  | succ fuel ih =>
      simp only [gcdLoopWithAllocation, scanWithFrames_state]
      split
      · rename_i h
        rw [BinaryDivisionAllocation.divideWithAllocation_state, ih]
        simp [BinaryEuclideanGCD.loop, gcdLoopAllocated, h, Nat.add_assoc]
      · rename_i h
        simp [BinaryEuclideanGCD.loop, gcdLoopAllocated, h]

theorem divideAllocated_width (first second : List Bool) (W : ℕ)
    (hA : first.length ≤ W) (hB : second.length ≤ W) :
    (BinaryDivisionAllocation.divideWithAllocation first second).2 ≤ 30 * (W + 2) ^ 2 := by
  have h := BinaryDivisionAllocation.divideWithAllocation_bound first second
  have hMul := Nat.mul_le_mul hA (show 7 * second.length + 14 ≤ 7 * W + 14 by omega)
  nlinarith

theorem gcdLoopAllocated_bound (fuel : ℕ) (first second : List Bool) (W : ℕ)
    (hA : first.length ≤ W) (hB : second.length ≤ W) :
    gcdLoopAllocated fuel first second ≤ 1 + fuel * (40 * (W + 2) ^ 2) := by
  induction fuel generalizing first second with
  | zero => simp [gcdLoopAllocated]
  | succ fuel ih =>
      have hs := scanWithFrames_bound second
      have hd := divideAllocated_width first second W hA hB
      have ht := ih second (BinaryLongDivision.divide first second).2 hB
        ((BinaryLongDivision.divide_lengths first second).2.le.trans hB)
      simp only [gcdLoopAllocated]
      split <;> nlinarith

def gcdLoopHeld : ℕ → List Bool → List Bool → ℕ
  | 0, first, second => first.length + second.length + 1
  | fuel + 1, first, second =>
      first.length + second.length + (scanWithFrames second).2 + 3 +
        if BinaryEuclideanGCD.nonzero second then
          let divided := BinaryLongDivision.divide first second
          -- The quotient is discarded by the GCD but retained by this model.
          divided.1.length + divided.2.length +
            BinaryDivisionAllocation.divideStorage first second +
              gcdLoopHeld fuel second divided.2
        else 0

theorem gcdLoopHeld_bound (fuel : ℕ) (first second : List Bool) (W : ℕ)
    (hA : first.length ≤ W) (hB : second.length ≤ W) :
    gcdLoopHeld fuel first second ≤ (fuel + 1) * (600 * (W + 2) ^ 3) := by
  induction fuel generalizing first second with
  | zero =>
      simp only [gcdLoopHeld, Nat.zero_add, Nat.one_mul]
      have hp : W + 2 ≤ (W + 2) ^ 3 := by
        simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 2) (by omega : 1 ≤ 3))
      omega
  | succ fuel ih =>
      have hs := scanWithFrames_bound second
      have hd := BinaryDivisionAllocation.divideStorage_bound first second W hA hB
      have hq := (BinaryLongDivision.divide_lengths first second).1
      have hr := (BinaryLongDivision.divide_lengths first second).2
      have ht := ih second (BinaryLongDivision.divide first second).2 hB (hr.le.trans hB)
      simp only [gcdLoopHeld]
      have hp : W + 2 ≤ (W + 2) ^ 3 := by
        simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 2) (by omega : 1 ≤ 3))
      split <;> nlinarith

def gcdWithAllocation (first second : List Bool) : List Bool × ℕ :=
  let W := BinaryEuclideanGCD.width first second
  let result := gcdLoopWithAllocation (2 * (W + 1)) first second
  (result.1, first.length + second.length + 4 * (W + 1) + result.2)

theorem gcdWithAllocation_state (first second : List Bool) :
    (gcdWithAllocation first second).1 = BinaryEuclideanGCD.gcd first second := by
  unfold gcdWithAllocation
  dsimp only
  rw [gcdLoopWithAllocation_refines]
  rfl

theorem gcdWithAllocation_bound (first second : List Bool) :
    (gcdWithAllocation first second).2 ≤ 100 * (BinaryEuclideanGCD.width first second + 2) ^ 3 := by
  let W := BinaryEuclideanGCD.width first second
  have hA : first.length ≤ W := Nat.le_max_left _ _
  have hB : second.length ≤ W := Nat.le_max_right _ _
  have h := gcdLoopAllocated_bound (2 * (W + 1)) first second W hA hB
  unfold gcdWithAllocation
  dsimp only
  rw [gcdLoopWithAllocation_refines]
  change first.length + second.length + 4 * (W + 1) +
    gcdLoopAllocated (2 * (W + 1)) first second ≤ 100 * (W + 2) ^ 3
  nlinarith

def gcdStorage (first second : List Bool) : ℕ :=
  let W := BinaryEuclideanGCD.width first second
  first.length + second.length + 4 * (W + 1) +
    gcdLoopHeld (2 * (W + 1)) first second + (gcdWithAllocation first second).2

theorem gcdStorage_bound (first second : List Bool) :
    gcdStorage first second ≤ 2000 * (BinaryEuclideanGCD.width first second + 2) ^ 4 := by
  let W := BinaryEuclideanGCD.width first second
  have hA : first.length ≤ W := Nat.le_max_left _ _
  have hB : second.length ≤ W := Nat.le_max_right _ _
  have hh := gcdLoopHeld_bound (2 * (W + 1)) first second W hA hB
  have ha := gcdWithAllocation_bound first second
  change (gcdWithAllocation first second).2 ≤ 100 * (W + 2) ^ 3 at ha
  unfold gcdStorage
  change first.length + second.length + 4 * (W + 1) +
    gcdLoopHeld (2 * (W + 1)) first second + (gcdWithAllocation first second).2 ≤ 2000 * (W + 2) ^ 4
  have hp : W + 2 ≤ (W + 2) ^ 3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 2) (by omega : 1 ≤ 3))
  have he : (W + 2) ^ 4 = (W + 2) ^ 3 * (W + 2) := by ring
  rw [he]
  nlinarith

theorem gcdWithAllocation_contract (first second : List Bool) :
    BinaryBigEndian.littleValue (gcdWithAllocation first second).1 =
        Nat.gcd (BinaryBigEndian.littleValue first) (BinaryBigEndian.littleValue second) ∧
      (gcdWithAllocation first second).1.length ≤ BinaryEuclideanGCD.width first second ∧
      (gcdWithAllocation first second).2 ≤ 100 * (BinaryEuclideanGCD.width first second + 2) ^ 3 ∧
      gcdStorage first second ≤ 2000 * (BinaryEuclideanGCD.width first second + 2) ^ 4 := by
  rw [gcdWithAllocation_state]
  exact ⟨BinaryEuclideanGCD.gcd_value first second, BinaryEuclideanGCD.gcd_length first second,
    gcdWithAllocation_bound first second, gcdStorage_bound first second⟩

def normalizeWithAllocation (word : SignedWord) : SignedWord × ℕ :=
  let common := gcdWithAllocation word.numerator word.denominator
  let numerator := BinaryDivisionAllocation.divideWithAllocation word.numerator common.1
  let denominator := BinaryDivisionAllocation.divideWithAllocation word.denominator common.1
  let scan := scanWithFrames numerator.1.1
  (⟨word.negative && scan.1, numerator.1.1, denominator.1.1⟩,
    common.2 + numerator.2 + denominator.2 + scan.2 + 4)

theorem gcdWithAllocation_eq_work_state (first second : List Bool) :
    (gcdWithAllocation first second).1 = (BinaryEuclideanGCD.gcdWithWork first second).1 := by
  rw [gcdWithAllocation_state]
  unfold BinaryEuclideanGCD.gcdWithWork
  dsimp only
  rw [BinaryEuclideanGCD.loopWithWork_refines]
  rfl

theorem normalizeWithAllocation_state (word : SignedWord) :
    (normalizeWithAllocation word).1 = BinaryRationalNormalization.normalize word := by
  unfold normalizeWithAllocation BinaryRationalNormalization.normalize normalizeWithWork
  dsimp only
  rw [gcdWithAllocation_eq_work_state, BinaryDivisionAllocation.divideWithAllocation_state,
    BinaryDivisionAllocation.divideWithAllocation_state, scanWithFrames_state,
    BinaryLongDivision.divideWithWork_refines, BinaryLongDivision.divideWithWork_refines]

theorem normalizeWithAllocation_bound (word : SignedWord) :
    (normalizeWithAllocation word).2 ≤ 200 * (width word + 2) ^ 3 := by
  let W := width word
  let common := (gcdWithAllocation word.numerator word.denominator).1
  have hA : word.numerator.length ≤ W := Nat.le_max_left _ _
  have hB : word.denominator.length ≤ W := Nat.le_max_right _ _
  have hc : common.length ≤ W := by
    dsimp only [common]
    rw [gcdWithAllocation_state]
    exact BinaryEuclideanGCD.gcd_length _ _
  have hg := gcdWithAllocation_bound word.numerator word.denominator
  change (gcdWithAllocation word.numerator word.denominator).2 ≤ 100 * (W + 2) ^ 3 at hg
  have hn := divideAllocated_width word.numerator common W hA hc
  have hd := divideAllocated_width word.denominator common W hB hc
  have hs := scanWithFrames_bound (BinaryDivisionAllocation.divideWithAllocation word.numerator common).1.1
  rw [BinaryDivisionAllocation.divideWithAllocation_state,
    (BinaryLongDivision.divide_lengths word.numerator common).1] at hs
  unfold normalizeWithAllocation
  change (gcdWithAllocation word.numerator word.denominator).2 +
    (BinaryDivisionAllocation.divideWithAllocation word.numerator common).2 +
    (BinaryDivisionAllocation.divideWithAllocation word.denominator common).2 +
    (scanWithFrames (BinaryDivisionAllocation.divideWithAllocation word.numerator common).1.1).2 + 4 ≤ 200 * (W + 2) ^ 3
  rw [BinaryDivisionAllocation.divideWithAllocation_state]
  have hp : W + 2 ≤ (W + 2) ^ 2 := by nlinarith
  have hpp : (W + 2) ^ 2 ≤ (W + 2) ^ 3 := by nlinarith
  nlinarith

def normalizeHeld (word : SignedWord) : ℕ :=
  let common := (gcdWithAllocation word.numerator word.denominator).1
  let numerator := (BinaryLongDivision.divide word.numerator common)
  let denominator := (BinaryLongDivision.divide word.denominator common)
  word.numerator.length + word.denominator.length + 1 + common.length +
    numerator.1.length + numerator.2.length + denominator.1.length + denominator.2.length +
      (scanWithFrames numerator.1).2 + 4 + gcdStorage word.numerator word.denominator +
        BinaryDivisionAllocation.divideStorage word.numerator common +
          BinaryDivisionAllocation.divideStorage word.denominator common

def normalizeStorage (word : SignedWord) : ℕ := normalizeHeld word + (normalizeWithAllocation word).2

theorem normalizeStorage_bound (word : SignedWord) :
    normalizeStorage word ≤ 4000 * (width word + 2) ^ 4 := by
  let W := width word
  let common := (gcdWithAllocation word.numerator word.denominator).1
  have hA : word.numerator.length ≤ W := Nat.le_max_left _ _
  have hB : word.denominator.length ≤ W := Nat.le_max_right _ _
  have hc : common.length ≤ W := by
    dsimp only [common]
    rw [gcdWithAllocation_state]
    exact BinaryEuclideanGCD.gcd_length _ _
  have hg := gcdStorage_bound word.numerator word.denominator
  change gcdStorage word.numerator word.denominator ≤ 2000 * (W + 2) ^ 4 at hg
  have hn := BinaryDivisionAllocation.divideStorage_bound word.numerator common W hA hc
  have hd := BinaryDivisionAllocation.divideStorage_bound word.denominator common W hB hc
  have hnl := BinaryLongDivision.divide_lengths word.numerator common
  have hdl := BinaryLongDivision.divide_lengths word.denominator common
  have hs := scanWithFrames_bound (BinaryLongDivision.divide word.numerator common).1
  rw [hnl.1] at hs
  have ha := normalizeWithAllocation_bound word
  change (normalizeWithAllocation word).2 ≤ 200 * (W + 2) ^ 3 at ha
  unfold normalizeStorage normalizeHeld
  change word.numerator.length + word.denominator.length + 1 + common.length +
    (BinaryLongDivision.divide word.numerator common).1.length +
    (BinaryLongDivision.divide word.numerator common).2.length +
    (BinaryLongDivision.divide word.denominator common).1.length +
    (BinaryLongDivision.divide word.denominator common).2.length +
    (scanWithFrames (BinaryLongDivision.divide word.numerator common).1).2 + 4 +
    gcdStorage word.numerator word.denominator +
    BinaryDivisionAllocation.divideStorage word.numerator common +
    BinaryDivisionAllocation.divideStorage word.denominator common + (normalizeWithAllocation word).2 ≤ 4000 * (W + 2) ^ 4
  rw [hnl.1, hnl.2, hdl.1, hdl.2]
  have hp : W + 2 ≤ (W + 2) ^ 3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < W + 2) (by omega : 1 ≤ 3))
  have hpp : (W + 2) ^ 3 ≤ (W + 2) ^ 4 := by nlinarith
  nlinarith

theorem normalizeWithAllocation_contract (word : SignedWord)
    (hD : 0 < BinaryBigEndian.littleValue word.denominator) :
    value (normalizeWithAllocation word).1 = value word ∧
      0 < BinaryBigEndian.littleValue (normalizeWithAllocation word).1.denominator ∧
      Nat.Coprime (BinaryBigEndian.littleValue (normalizeWithAllocation word).1.numerator)
        (BinaryBigEndian.littleValue (normalizeWithAllocation word).1.denominator) ∧
      (BinaryBigEndian.littleValue (normalizeWithAllocation word).1.numerator = 0 →
        (normalizeWithAllocation word).1.negative = false) ∧
      (normalizeWithAllocation word).1.numerator.length = word.numerator.length ∧
      (normalizeWithAllocation word).1.denominator.length = word.denominator.length ∧
      (normalizeWithAllocation word).2 ≤ 200 * (width word + 2) ^ 3 ∧
      normalizeStorage word ≤ 4000 * (width word + 2) ^ 4 := by
  rw [normalizeWithAllocation_state]
  exact ⟨normalize_value word hD, normalize_denominator_positive word hD, normalize_coprime word hD,
    normalize_zero_sign word, (normalize_lengths word).1, (normalize_lengths word).2,
    normalizeWithAllocation_bound word, normalizeStorage_bound word⟩

end Blotto.BinaryNormalizationAllocation
