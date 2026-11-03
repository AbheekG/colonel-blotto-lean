import Blotto.FareyQuotientStep

/-! A native accelerated Stern--Brocot strict predecessor for the retained
bounded-denominator Farey representation. Each recursive step is an exact
quotient jump. Equality is handled by extending the adjacent left endpoint,
so no denominator enumeration or modular-inverse oracle is needed. Correctness
is proved during construction; logarithmic operation/word pricing is separate. -/

namespace Blotto.Farey

structure PredecessorResult (D : ℕ) (cutoff : ℚ) where
  fraction : Fraction
  bounded : fraction.den ≤ D
  strict : fraction.value < cutoff
  greatest : ∀ middle : Fraction, middle.den ≤ D → middle.value < cutoff → middle.value ≤ fraction.value

def terminalResult (D : ℕ) (left right : Fraction) (h : Adjacent left right) (hBound : left.den ≤ D) :
    PredecessorResult D right.value :=
  let cert := terminalPredecessor_contract D left right h hBound
  ⟨terminalPredecessor D left right, cert.1, cert.2.1, cert.2.2⟩

def predecessorFrom (D : ℕ) (cutoff : ℚ) (left right : Fraction)
    (hAdj : Adjacent left right) (hLeftDen : left.den ≤ D) (hRightDen : right.den ≤ D)
    (hLeft : left.value < cutoff) (hRight : cutoff ≤ right.value) : PredecessorResult D cutoff :=
  if hEqual : cutoff = right.value then
    hEqual.symm ▸ terminalResult D left right hAdj hLeftDen
  else if hDone : D < left.den + right.den then
    ⟨left, hLeftDen, hLeft, fun middle hm hv => left_greatest_below D hAdj hDone cutoff hRight middle hm hv⟩
  else
    let middle := mediant left right
    have hSum : left.den + right.den ≤ D := Nat.le_of_not_gt hDone
    if hMiddle : middle.value = cutoff then
      hMiddle ▸ terminalResult D left middle (adjacent_mediant_left hAdj) hLeftDen
    else if hBelow : middle.value < cutoff then
      let k := leftQuotient D left right cutoff
      let next := leftJump left right k
      have cert := leftQuotient_contract D left right cutoff hSum hBelow (lt_of_le_of_ne hRight hEqual)
      have hk : 1 ≤ k := cert.1
      have hnBound : next.den ≤ D := cert.2.1
      have hnVal : next.value ≤ cutoff := cert.2.2
      if hHit : next.value = cutoff then
        let previous := leftJump left right (k - 1)
        have hpBound : previous.den ≤ D := leftJump_den_bound D left right hLeftDen _
          ((Nat.sub_le k 1).trans (min_le_right _ _))
        have hpAdj : Adjacent previous next := by
          have he := consecutive_leftJump hAdj (k - 1)
          have hh : k - 1 + 1 = k := by omega
          simpa only [hh] using he
        hHit ▸ terminalResult D previous next hpAdj hpBound
      else
        predecessorFrom D cutoff next right (leftJump_adjacent hAdj k) hnBound hRightDen
          (lt_of_le_of_ne hnVal hHit) hRight
    else
      have hAbove : cutoff < middle.value := lt_of_le_of_ne (le_of_not_gt hBelow) (Ne.symm hMiddle)
      let k := rightQuotient D left right cutoff
      let next := rightJump left right k
      have cert := rightQuotient_contract D left right cutoff hSum hLeft hAbove
      predecessorFrom D cutoff left next (rightJump_adjacent hAdj k) hLeftDen cert.2.1 hLeft cert.2.2
termination_by D + 1 - left.den - right.den
decreasing_by
  · have hd := right.den_pos
    have _hk : 1 ≤ leftQuotient D left right cutoff := cert.1
    have hp : 1 ≤ leftQuotient D left right cutoff * right.den := by nlinarith
    change D + 1 - (left.den + leftQuotient D left right cutoff * right.den) - right.den <
      D + 1 - left.den - right.den
    omega
  · have hd := left.den_pos
    have _hk : 1 ≤ rightQuotient D left right cutoff := cert.1
    have hp : 1 ≤ rightQuotient D left right cutoff * left.den := by nlinarith
    change D + 1 - left.den - (right.den + rightQuotient D left right cutoff * left.den) <
      D + 1 - left.den - right.den
    omega

def zeroFraction : Fraction := ⟨0, 1, by decide⟩
def oneFraction : Fraction := ⟨1, 1, by decide⟩

def predecessor (D : ℕ) (hD : 0 < D) (cutoff : ℚ) (hCutoff : 0 < cutoff ∧ cutoff ≤ 1) :
    PredecessorResult D cutoff :=
  predecessorFrom D cutoff zeroFraction oneFraction (by rfl) (by change 1 ≤ D; omega)
    (by change 1 ≤ D; omega) (by simpa [zeroFraction, Fraction.value] using hCutoff.1)
    (by simpa [oneFraction, Fraction.value] using hCutoff.2)

theorem predecessor_nonnegative (D : ℕ) (hD : 0 < D) (cutoff : ℚ) (hCutoff : 0 < cutoff ∧ cutoff ≤ 1) :
    0 ≤ (predecessor D hD cutoff hCutoff).fraction.value := value_nonnegative _

theorem predecessor_mono (D : ℕ) (hD : 0 < D) (first second : ℚ)
    (hFirst : 0 < first ∧ first ≤ 1) (hSecond : 0 < second ∧ second ≤ 1) (h : first ≤ second) :
    (predecessor D hD first hFirst).fraction.value ≤ (predecessor D hD second hSecond).fraction.value :=
  (predecessor D hD second hSecond).greatest _ (predecessor D hD first hFirst).bounded
    ((predecessor D hD first hFirst).strict.trans_le h)

theorem predecessor_zero (D : ℕ) (hD : 0 < D) (cutoff : ℚ)
    (hCutoff : 0 < cutoff ∧ cutoff ≤ 1) (hSmall : cutoff ≤ 1 / (D : ℚ)) :
    (predecessor D hD cutoff hCutoff).fraction.value = 0 := by
  let output := (predecessor D hD cutoff hCutoff).fraction
  have hDen := (predecessor D hD cutoff hCutoff).bounded
  have hBelow := (predecessor D hD cutoff hCutoff).strict
  have hn : output.num = 0 := by
    by_contra hn
    have hnPos : 1 ≤ output.num := by omega
    have hd : (0 : ℚ) < output.den := by exact_mod_cast output.den_pos
    have hOrder : (output.den : ℚ) ≤ D := by exact_mod_cast hDen
    have hInv := one_div_le_one_div_of_le hd hOrder
    have hNum : 1 / (output.den : ℚ) ≤ output.value := by
      unfold Fraction.value
      exact div_le_div_of_nonneg_right (by exact_mod_cast hnPos) hd.le
    have hv := hInv.trans hNum
    linarith
  change output.value = 0
  simp [Fraction.value, hn]

end Blotto.Farey
