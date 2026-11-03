import Blotto.GeneralPaperRoundedPowerTable

/-! Shared-table power evaluation by descending binary columns. The code
compares and subtracts constructed natural exponents and multiplies stored
dyadic numbers. It neither reads original input encodings nor computes a
fully expanded rational power. The supplied table is the one actually built
by `GeneralPaperRoundedPowerTable.build` in the final caller theorem.
-/
namespace Blotto.GeneralPaperRoundedPowerQuery
open GeneralPaperDyadicFloat GeneralPaperDyadicMultiply GeneralPaperRoundedPowerTable
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Columns : List Entry → ℕ → Prop
  | [],0 => True
  | entry::rest,width+1 => entry.degree=2^width ∧ Columns rest width
  | _,_ => False

theorem build_columns (unit p width : ℕ) (base : Number) : Columns (build unit p base width).entries width := by
  induction width with
  | zero => trivial
  | succ width ih =>
    change (build unit p base (width+1)).top.degree=2^width ∧ Columns (build unit p base width).entries width
    exact ⟨top_degree unit p width base,ih⟩

structure Result where
  number : Number
  remaining : ℕ
  work : ℕ

def scan (unit p : ℕ) : List Entry → ℕ → Number → Result
  | [],remaining,acc => ⟨acc,remaining,2⟩
  | entry::rest,remaining,acc =>
    if entry.degree≤remaining then
      let product := multiply unit p acc entry.number
      let later := scan unit p rest (remaining-entry.degree) product.number
      ⟨later.number,later.remaining,product.work+later.work+16⟩
    else
      let later := scan unit p rest remaining acc
      ⟨later.number,later.remaining,later.work+8⟩

theorem scan_work (unit p : ℕ) (entries : List Entry) (remaining : ℕ) (acc : Number) :
    (scan unit p entries remaining acc).work≤entries.length*(12*(p+1)+82)+2 := by
  induction entries generalizing remaining acc with
  | nil => simp [scan]
  | cons entry rest ih =>
    unfold scan
    split
    · dsimp only
      have hm := multiply_work unit p acc entry.number
      have hi := ih (remaining-entry.degree) (multiply unit p acc entry.number).number
      simp only [List.length_cons]
      nlinarith
    · dsimp only
      have hi := ih remaining acc
      simp only [List.length_cons]
      nlinarith

theorem scan_zero (unit p : ℕ) (entries : List Entry) (hEntries : ∀ entry∈entries, 0<entry.degree)
    (acc : Number) : (scan unit p entries 0 acc).number=acc := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    have hd := hEntries entry (by simp)
    simp only [scan,show ¬entry.degree≤0 by omega,ite_false]
    exact ih (fun e he => hEntries e (by simp [he]))

theorem chosen_product_bounds (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : ℚ) (hBase : 0<base) (entry : Entry) (hEntry : EntryGood unit base entry)
    (acc : Number) (hAcc : Normal unit acc) :
    retention unit^entry.degree*(value acc*base^entry.degree)≤value (multiply unit p acc entry.number).number ∧
      value (multiply unit p acc entry.number).number≤value acc*base^entry.degree := by
  have hRet := retention_bounds unit hUnit
  have hm := multiply_certificate unit p (by omega) hPower acc entry.number hAcc hEntry.2.1
  have hLow := mul_le_mul_of_nonneg_left hEntry.2.2.2.1 (value_nonnegative acc)
  have hLow' := mul_le_mul_of_nonneg_left hLow hRet.1.le
  have hEq : retention unit*(value acc*(retention unit^(entry.degree-1)*base^entry.degree))=
      retention unit^entry.degree*(value acc*base^entry.degree) := by
    have hd : entry.degree=(entry.degree-1)+1 := by have := hEntry.1; omega
    calc
      _ = (retention unit^(entry.degree-1)*retention unit)*(value acc*base^entry.degree) := by ring
      _ = _ := by rw [← pow_succ,← hd]
  rw [hEq] at hLow'
  exact ⟨hLow'.trans hm.1,hm.2.trans (mul_le_mul_of_nonneg_left hEntry.2.2.2.2 (value_nonnegative acc))⟩

theorem scan_correct (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : ℚ) (hBase : 0<base) (width : ℕ) (entries : List Entry)
    (hColumns : Columns entries width) (hEntries : ∀ entry∈entries, EntryGood unit base entry)
    (remaining : ℕ) (hRemaining : remaining<2^width) (acc : Number)
    (hAcc : Normal unit acc) (hPositive : 0<acc.mantissa) :
    (scan unit p entries remaining acc).remaining=0 ∧
      Normal unit (scan unit p entries remaining acc).number ∧
      0<(scan unit p entries remaining acc).number.mantissa ∧
      retention unit^remaining*(value acc*base^remaining)≤value (scan unit p entries remaining acc).number ∧
      value (scan unit p entries remaining acc).number≤value acc*base^remaining := by
  have hRet := retention_bounds unit hUnit
  induction width generalizing entries remaining acc with
  | zero =>
    cases entries with
    | nil =>
      have hz : remaining=0 := by simp only [pow_zero] at hRemaining; omega
      subst remaining
      exact ⟨rfl,hAcc,hPositive,by simp [scan],by simp [scan]⟩
    | cons e rest => exact False.elim hColumns
  | succ width ih =>
    cases entries with
    | nil => exact False.elim hColumns
    | cons entry rest =>
      have hc : entry.degree=2^width ∧ Columns rest width := hColumns
      have hEntry := hEntries entry (by simp)
      have hRest : ∀ e∈rest, EntryGood unit base e := fun e he => hEntries e (by simp [he])
      unfold scan
      split
      · rename_i hChosen
        have hNextBound : remaining-entry.degree<2^width := by
          rw [pow_succ] at hRemaining
          rw [hc.1] at hChosen ⊢
          omega
        have hNextNormal := multiply_normal unit p (by omega) hPower _ _ hAcc hEntry.2.1
        have hNextPositive := multiply_positive unit p (by omega) hPower _ _ hAcc hEntry.2.1 hPositive hEntry.2.2.1
        have hi := ih rest hc.2 hRest (remaining-entry.degree) hNextBound _ hNextNormal hNextPositive
        have hm := chosen_product_bounds unit p hUnit hPower base hBase entry hEntry acc hAcc
        dsimp only
        refine ⟨hi.1,hi.2.1,hi.2.2.1,?_,?_⟩
        · have hScaled := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hm.1 (pow_nonneg hRet.1.le (remaining-entry.degree)))
            (pow_nonneg hBase.le (remaining-entry.degree))
          have hEq : retention unit^(remaining-entry.degree)*
              (retention unit^entry.degree*(value acc*base^entry.degree))*base^(remaining-entry.degree)=
              retention unit^remaining*(value acc*base^remaining) := by
            calc
              _ = (retention unit^(remaining-entry.degree)*retention unit^entry.degree)*
                  value acc*(base^(remaining-entry.degree)*base^entry.degree) := by ring
              _ = _ := by rw [← pow_add,← pow_add,Nat.sub_add_cancel hChosen]; ring
          rw [hEq] at hScaled
          exact hScaled.trans (by simpa only [mul_assoc] using hi.2.2.2.1)
        · have hScaled := mul_le_mul_of_nonneg_right hm.2 (pow_nonneg hBase.le (remaining-entry.degree))
          have hEq : value acc*base^entry.degree*base^(remaining-entry.degree)=value acc*base^remaining := by
            rw [mul_assoc,← pow_add,Nat.add_sub_of_le hChosen]
          rw [hEq] at hScaled
          exact hi.2.2.2.2.trans hScaled
      · rename_i hSkip
        have hNextBound : remaining<2^width := by rw [hc.1] at hSkip; omega
        exact ih rest hc.2 hRest remaining hNextBound acc hAcc hPositive

def evaluate (unit p : ℕ) (table : List Entry) (exponent : ℕ) : Result :=
  let answer := scan unit p table exponent (one unit p)
  ⟨answer.number,answer.remaining,answer.work+8⟩

theorem evaluate_constructed (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : Number) (hNormal : Normal unit base) (hPositive : 0<base.mantissa)
    (width exponent : ℕ) (hExponent : exponent<2^width) :
    (evaluate unit p (build unit p base width).entries exponent).remaining=0 ∧
      Normal unit (evaluate unit p (build unit p base width).entries exponent).number ∧
      0<(evaluate unit p (build unit p base width).entries exponent).number.mantissa ∧
      retention unit^exponent*value base^exponent≤value (evaluate unit p (build unit p base width).entries exponent).number ∧
      value (evaluate unit p (build unit p base width).entries exponent).number≤value base^exponent := by
  have ht := build_good unit p hUnit hPower base hNormal hPositive width
  have he := scan_correct unit p hUnit hPower _ (value_positive base hPositive) width _
    (build_columns unit p width base) ht.2 exponent hExponent (one unit p)
    (one_normal unit p (by omega)) (show 0<(one unit p).mantissa from by dsimp [one]; omega)
  simpa only [evaluate,one_value unit p hPower,one_mul] using he

theorem evaluate_zero (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : Number) (hNormal : Normal unit base) (hPositive : 0<base.mantissa) (width : ℕ) :
    (evaluate unit p (build unit p base width).entries 0).number=one unit p := by
  exact scan_zero unit p _ (fun entry he => (build_good unit p hUnit hPower base hNormal hPositive width).2 entry he |>.1) _

theorem evaluate_work (unit p width exponent : ℕ) (base : Number) :
    (evaluate unit p (build unit p base width).entries exponent).work≤width*(12*(p+1)+82)+10 := by
  have he := scan_work unit p (build unit p base width).entries exponent (one unit p)
  rw [entries_length] at he
  change (scan unit p (build unit p base width).entries exponent (one unit p)).work+8≤_
  omega

end Blotto.GeneralPaperRoundedPowerQuery
