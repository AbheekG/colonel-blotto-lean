import Blotto.FareyQuotientProgress

/-! Actual native quotient-predecessor execution with a state-visit and
floor/budget-quotient observer. The starting state derives the logarithmic
bound: continuing jumps alternate and double the updated denominator.
The observer is a named arithmetic-path model, not CPU profiling or a claim
that rational normalization/Boolean division has unit bit cost. -/

namespace Blotto.Farey
set_option maxRecDepth 2048

structure CountedPredecessor (D : ℕ) (cutoff : ℚ) (left right : Fraction) where
  result : PredecessorResult D cutoff
  calls : ℕ
  quotientQueries : ℕ

def terminalWork (D : ℕ) (cutoff : ℚ) (left right : Fraction) (_hl : left.den ≤ D) (_hr : right.den ≤ D)
    (result : PredecessorResult D cutoff) (queries : ℕ) (_hq : queries ≤ 3) : CountedPredecessor D cutoff left right where
  result := result
  calls := 1
  quotientQueries := queries

def countedFrom (D : ℕ) (cutoff : ℚ) (left right : Fraction)
    (hAdj : Adjacent left right) (hLeftDen : left.den ≤ D) (hRightDen : right.den ≤ D)
    (hLeft : left.value < cutoff) (hRight : cutoff ≤ right.value) (_hOrder : StepOrdered D cutoff left right) :
    CountedPredecessor D cutoff left right :=
  if hEqual : cutoff = right.value then
    terminalWork D cutoff left right hLeftDen hRightDen
      (hEqual.symm ▸ terminalResult D left right hAdj hLeftDen) 1 (by decide)
  else if hDone : D < left.den + right.den then
    terminalWork D cutoff left right hLeftDen hRightDen
      ⟨left, hLeftDen, hLeft, fun middle hm hv => left_greatest_below D hAdj hDone cutoff hRight middle hm hv⟩ 0 (by decide)
  else
    let middle := mediant left right
    have hSum : left.den + right.den ≤ D := Nat.le_of_not_gt hDone
    if hMiddle : middle.value = cutoff then
      terminalWork D cutoff left right hLeftDen hRightDen
        (hMiddle ▸ terminalResult D left middle (adjacent_mediant_left hAdj) hLeftDen) 1 (by decide)
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
        terminalWork D cutoff left right hLeftDen hRightDen
          (hHit ▸ terminalResult D previous next hpAdj hpBound) 3 (by decide)
      else
        let child := countedFrom D cutoff next right (leftJump_adjacent hAdj k) hnBound hRightDen
          (lt_of_le_of_ne hnVal hHit) hRight
          (leftQuotient_next_ordered D left right cutoff hSum hBelow (lt_of_le_of_ne hRight hEqual))
        { result := child.result
          calls := child.calls + 1
          quotientQueries := child.quotientQueries + 2
          }
    else
      have hAbove : cutoff < middle.value := lt_of_le_of_ne (le_of_not_gt hBelow) (Ne.symm hMiddle)
      let k := rightQuotient D left right cutoff
      let next := rightJump left right k
      have cert := rightQuotient_contract D left right cutoff hSum hLeft hAbove
      let child := countedFrom D cutoff left next (rightJump_adjacent hAdj k) hLeftDen cert.2.1 hLeft cert.2.2
        (rightQuotient_next_ordered D left right cutoff hSum hLeft hAbove)
      { result := child.result
        calls := child.calls + 1
        quotientQueries := child.quotientQueries + 2
        }
termination_by D + 1 - left.den - right.den
decreasing_by
  all_goals first
  | (have hd := right.den_pos
     have _hk : 1 ≤ leftQuotient D left right cutoff := cert.1
     have hp : 1 ≤ leftQuotient D left right cutoff * right.den := by nlinarith
     change D + 1 - (left.den + leftQuotient D left right cutoff * right.den) - right.den <
       D + 1 - left.den - right.den
     omega)
  | (have hd := left.den_pos
     have _hk : 1 ≤ rightQuotient D left right cutoff := cert.1
     have hp : 1 ≤ rightQuotient D left right cutoff * left.den := by nlinarith
     change D + 1 - left.den - (right.den + rightQuotient D left right cutoff * left.den) <
       D + 1 - left.den - right.den
     omega)

def predecessorWithWork (D : ℕ) (hD : 0 < D) (cutoff : ℚ) (hCutoff : 0 < cutoff ∧ cutoff ≤ 1) :
    CountedPredecessor D cutoff zeroFraction oneFraction :=
  countedFrom D cutoff zeroFraction oneFraction (by rfl) (by change 1 ≤ D; omega)
    (by change 1 ≤ D; omega) (by simpa [zeroFraction, Fraction.value] using hCutoff.1)
    (by simpa [oneFraction, Fraction.value] using hCutoff.2) (initial_step_ordered D cutoff)

theorem terminal_calls_bound (D : ℕ) (left right : Fraction) (hl : left.den ≤ D) (hr : right.den ≤ D) :
    1 + binaryWordWidth left.den + binaryWordWidth right.den ≤ 2 * binaryWordWidth D + 1 := by
  have hLeft := binaryWordWidth_mono hl
  have hRight := binaryWordWidth_mono hr
  omega

theorem countedFrom_calls_bound (D : ℕ) (cutoff : ℚ) (left right : Fraction)
    (hAdj : Adjacent left right) (hLeftDen : left.den ≤ D) (hRightDen : right.den ≤ D)
    (hLeft : left.value < cutoff) (hRight : cutoff ≤ right.value) (hOrder : StepOrdered D cutoff left right) :
    (countedFrom D cutoff left right hAdj hLeftDen hRightDen hLeft hRight hOrder).calls +
      binaryWordWidth left.den + binaryWordWidth right.den ≤ 2 * binaryWordWidth D + 1 := by
  fun_induction countedFrom
  all_goals simp only [terminalWork]
  case case5 =>
    rename_i L R hAdj hLD hRD hL hR hOrd hNE hND middle hSum hNM hBelow k next cert hk hnBound hnVal hNH child ih
    have hg := leftJump_width_growth L R k hk ((hOrd hSum).1 hBelow)
    change binaryWordWidth L.den + 1 ≤ binaryWordWidth next.den at hg
    change child.calls + binaryWordWidth next.den + binaryWordWidth R.den ≤ _ at ih
    omega
  case case6 =>
    rename_i L R hAdj hLD hRD hL hR hOrd hNE hND middle hSum hNM hBelow hAbove k next cert child ih
    have hg := rightJump_width_growth L R k cert.1 ((hOrd hSum).2 hAbove)
    change binaryWordWidth R.den + 1 ≤ binaryWordWidth next.den at hg
    change child.calls + binaryWordWidth L.den + binaryWordWidth next.den ≤ _ at ih
    omega
  all_goals exact terminal_calls_bound D _ _ (by assumption) (by assumption)

theorem countedFrom_queries_bound (D : ℕ) (cutoff : ℚ) (left right : Fraction)
    (hAdj : Adjacent left right) (hLeftDen : left.den ≤ D) (hRightDen : right.den ≤ D)
    (hLeft : left.value < cutoff) (hRight : cutoff ≤ right.value) (hOrder : StepOrdered D cutoff left right) :
    (countedFrom D cutoff left right hAdj hLeftDen hRightDen hLeft hRight hOrder).quotientQueries ≤
      3 * (countedFrom D cutoff left right hAdj hLeftDen hRightDen hLeft hRight hOrder).calls := by
  fun_induction countedFrom
  all_goals simp only [terminalWork]
  case case5 =>
    rename_i child ih
    change child.quotientQueries ≤ 3 * child.calls at ih
    omega
  case case6 =>
    rename_i child ih
    change child.quotientQueries ≤ 3 * child.calls at ih
    omega
  all_goals omega

theorem countedFrom_fraction (D : ℕ) (cutoff : ℚ) (left right : Fraction)
    (hAdj : Adjacent left right) (hLeftDen : left.den ≤ D) (hRightDen : right.den ≤ D)
    (hLeft : left.value < cutoff) (hRight : cutoff ≤ right.value) (hOrder : StepOrdered D cutoff left right) :
    (countedFrom D cutoff left right hAdj hLeftDen hRightDen hLeft hRight hOrder).result.fraction =
      (predecessorFrom D cutoff left right hAdj hLeftDen hRightDen hLeft hRight).fraction := by
  fun_induction countedFrom
  all_goals rw [predecessorFrom.eq_def]
  all_goals simp_all (config := { zetaDelta := true }) only [terminalWork, dite_true, dite_false]

theorem predecessorWithWork_value (D : ℕ) (hD : 0 < D) (cutoff : ℚ) (hCutoff : 0 < cutoff ∧ cutoff ≤ 1) :
    (predecessorWithWork D hD cutoff hCutoff).result.fraction.value = (predecessor D hD cutoff hCutoff).fraction.value := by
  apply le_antisymm
  · exact (predecessor D hD cutoff hCutoff).greatest _
      (predecessorWithWork D hD cutoff hCutoff).result.bounded (predecessorWithWork D hD cutoff hCutoff).result.strict
  · exact (predecessorWithWork D hD cutoff hCutoff).result.greatest _
      (predecessor D hD cutoff hCutoff).bounded (predecessor D hD cutoff hCutoff).strict

theorem predecessorWithWork_calls (D : ℕ) (hD : 0 < D) (cutoff : ℚ) (hCutoff : 0 < cutoff ∧ cutoff ≤ 1) :
    (predecessorWithWork D hD cutoff hCutoff).calls + 1 ≤ 2 * binaryWordWidth D := by
  have hb := countedFrom_calls_bound D cutoff zeroFraction oneFraction (by rfl) (by change 1 ≤ D; omega)
    (by change 1 ≤ D; omega) (by simpa [zeroFraction, Fraction.value] using hCutoff.1)
    (by simpa [oneFraction, Fraction.value] using hCutoff.2) (initial_step_ordered D cutoff)
  have hOne : binaryWordWidth 1 = 1 := by decide
  change (predecessorWithWork D hD cutoff hCutoff).calls + binaryWordWidth 1 + binaryWordWidth 1 ≤ _ at hb
  rw [hOne] at hb
  omega

theorem predecessorWithWork_queries (D : ℕ) (hD : 0 < D) (cutoff : ℚ) (hCutoff : 0 < cutoff ∧ cutoff ≤ 1) :
    (predecessorWithWork D hD cutoff hCutoff).quotientQueries ≤ 6 * binaryWordWidth D := by
  have hb := countedFrom_queries_bound D cutoff zeroFraction oneFraction (by rfl) (by change 1 ≤ D; omega)
    (by change 1 ≤ D; omega) (by simpa [zeroFraction, Fraction.value] using hCutoff.1)
    (by simpa [oneFraction, Fraction.value] using hCutoff.2) (initial_step_ordered D cutoff)
  change (predecessorWithWork D hD cutoff hCutoff).quotientQueries ≤ 3 * (predecessorWithWork D hD cutoff hCutoff).calls at hb
  have hc := predecessorWithWork_calls D hD cutoff hCutoff
  omega

end Blotto.Farey
