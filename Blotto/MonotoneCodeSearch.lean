import Blotto.RationalSingleFieldLoss
import Blotto.BinaryWidthPrecision

/-! Executable lower-bound search on a monotone finite code predicate. Every
step halves a bracket; logarithmic fuel follows from the stored code width.
Predicate evaluation costs and the specific Farey decoder remain separate. -/

namespace Blotto.MonotoneCodeSearch

def search : ℕ → (ℕ → Bool) → ℕ → ℕ → ℕ × ℕ
  | 0, _, lo, _hi => (lo, 0)
  | fuel + 1, predicate, lo, hi =>
      if lo < hi then
        let mid := lo + (hi - lo) / 2
        let next := if predicate mid then search fuel predicate lo mid
          else search fuel predicate (mid + 1) hi
        (next.1, next.2 + 1)
      else (lo, 0)

def Bracket (C : ℕ) (predicate : ℕ → Bool) (lo hi : ℕ) : Prop :=
  lo ≤ hi ∧ hi ≤ C + 1 ∧
    (∀ code < lo, predicate code = false) ∧
    (∀ code, hi ≤ code → code ≤ C → predicate code = true)

def IsMonotone (C : ℕ) (predicate : ℕ → Bool) : Prop :=
  ∀ first second, first ≤ second → second ≤ C → predicate first = true → predicate second = true

theorem search_visits (fuel : ℕ) (predicate : ℕ → Bool) (lo hi : ℕ) :
    (search fuel predicate lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [search]
    split
    · split <;> dsimp only <;> exact Nat.add_le_add_right (ih _ _) 1
    · simp

theorem search_contract (fuel C : ℕ) (predicate : ℕ → Bool) (lo hi : ℕ)
    (hm : IsMonotone C predicate) (hb : Bracket C predicate lo hi)
    (hf : hi - lo < 2 ^ fuel) :
    lo ≤ (search fuel predicate lo hi).1 ∧ (search fuel predicate lo hi).1 ≤ hi ∧
      Bracket C predicate (search fuel predicate lo hi).1 (search fuel predicate lo hi).1 := by
  induction fuel generalizing lo hi with
  | zero =>
    have hlo := hb.1
    have he : lo = hi := by norm_num at hf; omega
    simp only [search]
    exact ⟨le_rfl, hb.1, by simpa only [he] using hb⟩
  | succ fuel ih =>
    by_cases hActive : lo < hi
    · rw [search, ite_eq_left hActive]
      let mid := lo + (hi - lo) / 2
      dsimp only
      change lo ≤ (if predicate mid then search fuel predicate lo mid else search fuel predicate (mid + 1) hi).1 ∧
        (if predicate mid then search fuel predicate lo mid else search fuel predicate (mid + 1) hi).1 ≤ hi ∧
        Bracket C predicate
          (if predicate mid then search fuel predicate lo mid else search fuel predicate (mid + 1) hi).1
          (if predicate mid then search fuel predicate lo mid else search fuel predicate (mid + 1) hi).1
      have hhi := hb.2.1
      have hmLo : lo ≤ mid := by dsimp only [mid]; omega
      have hmHi : mid < hi := by dsimp only [mid]; omega
      have hHalf : (hi - lo) / 2 < 2 ^ fuel := by
        rw [pow_succ] at hf
        omega
      by_cases hp : predicate mid = true
      · rw [ite_eq_left hp]
        have hbNext : Bracket C predicate lo mid := by
          refine ⟨hmLo, by omega, hb.2.2.1, ?_⟩
          intro code hmid hC
          exact hm mid code hmid hC hp
        have he := ih lo mid hbNext (by dsimp only [mid]; omega)
        exact ⟨he.1, he.2.1.trans hmHi.le, he.2.2⟩
      · have hpFalse : predicate mid = false := by cases h : predicate mid <;> simp_all
        rw [ite_eq_right hp]
        have hbNext : Bracket C predicate (mid + 1) hi := by
          refine ⟨by omega, hb.2.1, ?_, hb.2.2.2⟩
          intro code hcode
          by_cases hBefore : code < lo
          · exact hb.2.2.1 code hBefore
          · have hmC : mid ≤ C := by omega
            by_cases hc : predicate code = true
            · have ht := hm code mid (by omega) hmC hc
              rw [hpFalse] at ht
              cases ht
            · cases he : predicate code <;> simp_all
        have he := ih (mid + 1) hi hbNext (by dsimp only [mid]; omega)
        exact ⟨hmLo.trans (Nat.le_succ mid) |>.trans he.1, he.2.1, he.2.2⟩
    · rw [search, ite_eq_right hActive]
      have hlo := hb.1
      have he : lo = hi := by omega
      exact ⟨le_rfl, hb.1, by simpa only [he] using hb⟩

def first (C : ℕ) (predicate : ℕ → Bool) : ℕ × ℕ :=
  search (binaryWordWidth (C + 1)) predicate 0 (C + 1)

theorem first_visits (C : ℕ) (predicate : ℕ → Bool) :
    (first C predicate).2 ≤ binaryWordWidth (C + 1) := search_visits _ _ _ _

theorem first_contract (C : ℕ) (predicate : ℕ → Bool) (hm : IsMonotone C predicate) :
    (first C predicate).1 ≤ C + 1 ∧
      (∀ code ≤ C, predicate code = true ↔ (first C predicate).1 ≤ code) := by
  have hf : C + 1 < 2 ^ binaryWordWidth (C + 1) := by
    exact Nat.lt_log2_self (n := C + 1)
  have hb : Bracket C predicate 0 (C + 1) := by
    refine ⟨Nat.zero_le _, le_rfl, ?_, ?_⟩
    · intro code hc; omega
    · intro code hc hC; omega
  have he := search_contract (binaryWordWidth (C + 1)) C predicate 0 (C + 1) hm hb (by simpa using hf)
  change 0 ≤ (first C predicate).1 ∧ (first C predicate).1 ≤ C + 1 ∧
    Bracket C predicate (first C predicate).1 (first C predicate).1 at he
  refine ⟨he.2.1, ?_⟩
  intro code hC
  constructor
  · intro hp
    by_contra hn
    have hfalse := he.2.2.2.2.1 code (by omega)
    rw [hp] at hfalse
    cases hfalse
  · intro hp
    exact he.2.2.2.2.2 code hp hC

end Blotto.MonotoneCodeSearch
