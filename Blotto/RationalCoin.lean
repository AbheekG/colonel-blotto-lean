import Blotto.FairBitLaw

/-! A concrete digit-by-digit rational Bernoulli comparison. Only fresh input
bits are read. Matching a terminating dyadic expansion returns false without
another bit; exhausting the input returns none with the exact consumed count.
No success-probability or shared-cap claim is assumed by this program. -/

namespace Blotto

def probabilityDigit (p : ℚ) : Bool := decide ((1 / 2 : ℚ) ≤ p)

def coinResidual (p : ℚ) : ℚ := 2 * p - if probabilityDigit p then 1 else 0

def runRationalCoin : (K : ℕ) → ℚ → (Fin K → Bool) → Option Bool × ℕ
  | 0, p, _ => if p ≤ 0 then (some false, 0) else if 1 ≤ p then (some true, 0) else (none, 0)
  | K + 1, p, bits =>
    if p ≤ 0 then (some false, 0) else if 1 ≤ p then (some true, 0) else
      if bits 0 = probabilityDigit p then
        let result := runRationalCoin K (coinResidual p) (Fin.tail bits)
        (result.1, result.2 + 1)
      else (some (!bits 0), 1)

theorem runRationalCoin_zero (K : ℕ) (bits : Fin K → Bool) : runRationalCoin K 0 bits = (some false, 0) := by
  cases K <;> simp [runRationalCoin]

theorem runRationalCoin_one (K : ℕ) (bits : Fin K → Bool) : runRationalCoin K 1 bits = (some true, 0) := by
  cases K <;> norm_num [runRationalCoin]

theorem runRationalCoin_bits_le (K : ℕ) (p : ℚ) (bits : Fin K → Bool) : (runRationalCoin K p bits).2 ≤ K := by
  induction K generalizing p with
  | zero => simp [runRationalCoin]; split_ifs <;> simp
  | succ K ih =>
    unfold runRationalCoin
    split_ifs
    · simp
    · simp
    · exact Nat.succ_le_succ (ih _ _)
    · simp

theorem runRationalCoin_none_bits (K : ℕ) (p : ℚ) (bits : Fin K → Bool)
    (h : (runRationalCoin K p bits).1 = none) : (runRationalCoin K p bits).2 = K := by
  induction K generalizing p with
  | zero => simp [runRationalCoin]; split_ifs <;> simp
  | succ K ih =>
    by_cases hp : p ≤ 0
    · simp [runRationalCoin, hp] at h
    by_cases hp1 : 1 ≤ p
    · simp [runRationalCoin, hp, hp1] at h
    by_cases hd : bits 0 = probabilityDigit p
    · have hr : (runRationalCoin K (coinResidual p) (Fin.tail bits)).1 = none := by
        simpa only [runRationalCoin, hp, hp1, hd, ite_false, ite_true] using h
      simp only [runRationalCoin, hp, hp1, hd, ite_false, ite_true]
      exact congrArg (fun k => k + 1) (ih _ _ hr)
    · simp [runRationalCoin, hp, hp1, hd] at h

theorem runRationalCoin_none_unique (K : ℕ) (p : ℚ) (x y : Fin K → Bool)
    (hx : (runRationalCoin K p x).1 = none) (hy : (runRationalCoin K p y).1 = none) : x = y := by
  induction K generalizing p with
  | zero => funext j; exact Fin.elim0 j
  | succ K ih =>
    have hp : ¬p ≤ 0 := by intro h; simp [runRationalCoin, h] at hx
    have hp1 : ¬1 ≤ p := by intro h; simp [runRationalCoin, hp, h] at hx
    have hxd : x 0 = probabilityDigit p := by
      by_contra h
      simp [runRationalCoin, hp, hp1, h] at hx
    have hyd : y 0 = probabilityDigit p := by
      by_contra h
      simp [runRationalCoin, hp, hp1, h] at hy
    have hxt : (runRationalCoin K (coinResidual p) (Fin.tail x)).1 = none := by
      simpa only [runRationalCoin, hp, hp1, hxd, ite_false, ite_true] using hx
    have hyt : (runRationalCoin K (coinResidual p) (Fin.tail y)).1 = none := by
      simpa only [runRationalCoin, hp, hp1, hyd, ite_false, ite_true] using hy
    have ht := ih _ _ _ hxt hyt
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hxd, hyd, ht]

theorem coinResidual_bounds {p : ℚ} (hp : 0 ≤ p ∧ p ≤ 1) : 0 ≤ coinResidual p ∧ coinResidual p ≤ 1 := by
  unfold coinResidual probabilityDigit
  split_ifs with h
  · simp only [decide_eq_true_eq] at h
    constructor <;> linarith [hp.1, hp.2]
  · simp only [decide_eq_true_eq] at h
    constructor <;> linarith [hp.1, hp.2]

end Blotto
