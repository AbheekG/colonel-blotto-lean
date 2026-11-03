import Blotto.GeneralPaperRankMidpoint

/-! Bounded binary rank lookup in an ordered occurrence array. The only
division is the checked arithmetic midpoint routine. A guarded native read
keeps the function total; the valid-state theorem excludes that fallback.
-/
namespace Blotto.GeneralPaperRankSearch
open GeneralPaperRankMidpoint
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result where
  rank : ℕ
  work : ℕ
  probes : ℕ

def run {n : ℕ} (values : FixedArrayTable n ℕ) (cut depth : ℕ) : ℕ → ℕ → ℕ → Result
  | 0,lo,_ => ⟨lo,8,0⟩
  | fuel+1,lo,hi =>
    if lo<hi then
      let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
      if hMid : mid.quotient<n then
        if values.read ⟨mid.quotient,hMid⟩<cut then
          let child := run values cut depth fuel (mid.quotient+1) hi
          ⟨child.rank,child.work+mid.work+32,child.probes+1⟩
        else
          let child := run values cut depth fuel lo mid.quotient
          ⟨child.rank,child.work+mid.work+32,child.probes+1⟩
      else ⟨lo,mid.work+24,0⟩
    else ⟨lo,8,0⟩

def ValidRank {n : ℕ} (values : FixedArrayTable n ℕ) (cut rank : ℕ) : Prop :=
  rank≤n ∧ ∀ i, values.read i<cut ↔ i.val<rank

theorem closed_bracket {n : ℕ} (values : FixedArrayTable n ℕ) (cut lo hi : ℕ)
    (hLo : lo≤hi) (hHi : hi≤n) (hClosed : hi=lo)
    (hLeft : ∀ i : Fin n, i.val<lo → values.read i<cut)
    (hRight : ∀ i : Fin n, hi≤ i.val → cut≤values.read i) : ValidRank values cut lo := by
  refine ⟨hLo.trans hHi,?_⟩
  intro i
  constructor
  · intro h
    by_contra hn
    have hr := hRight i (by omega)
    omega
  · exact hLeft i

theorem run_spec {n : ℕ} (values : FixedArrayTable n ℕ) (cut depth fuel lo hi : ℕ)
    (hMono : Monotone values.read) (hLo : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth)
    (hSpan : hi-lo<2^fuel)
    (hLeft : ∀ i : Fin n, i.val<lo → values.read i<cut)
    (hRight : ∀ i : Fin n, hi≤ i.val → cut≤values.read i) :
    ValidRank values cut (run values cut depth fuel lo hi).rank := by
  induction fuel generalizing lo hi with
  | zero =>
    have hc : hi=lo := by simp only [pow_zero] at hSpan; omega
    exact closed_bracket values cut lo hi hLo hHi hc hLeft hRight
  | succ fuel ih =>
    by_cases hOpen : lo<hi
    · have hm := midpoint_inside n depth lo hi hOpen hHi hSize
      have hMid : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hHi
      have hShrink := midpoint_shrinks n depth lo hi fuel hOpen hHi hSize hSpan
      rw [run,if_pos hOpen,dif_pos hMid]
      split
      · rename_i hBelow
        dsimp only
        apply ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi (by omega) hHi hShrink.2 _ hRight
        intro i hIndex
        have hI : i≤⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩ := by
          change i.val≤(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient
          omega
        exact (hMono hI).trans_lt hBelow
      · rename_i hAbove
        dsimp only
        apply ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient hm.1 (by omega) hShrink.1 hLeft
        intro i hIndex
        have hI : (⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩:Fin n)≤ i := by
          change (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient≤ i.val
          exact hIndex
        exact (le_of_not_gt hAbove).trans (hMono hI)
    · rw [run,if_neg hOpen]
      exact closed_bracket values cut lo hi hLo hHi (by omega) hLeft hRight

theorem run_work {n : ℕ} (values : FixedArrayTable n ℕ) (cut depth fuel lo hi : ℕ) :
    (run values cut depth fuel lo hi).work≤fuel*(12*depth+34)+8 := by
  induction fuel generalizing lo hi with
  | zero => simp only [run,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      split
      · split <;> dsimp only
        · have ht := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi
          rw [midpoint_work]
          nlinarith
        · have ht := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient
          rw [midpoint_work]
          nlinarith
      · dsimp only
        rw [midpoint_work]
        nlinarith
    · dsimp only
      omega

theorem run_probes {n : ℕ} (values : FixedArrayTable n ℕ) (cut depth fuel lo hi : ℕ) :
    (run values cut depth fuel lo hi).probes≤fuel := by
  induction fuel generalizing lo hi with
  | zero => exact le_refl _
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      split
      · split <;> dsimp only
        · have ht := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi; omega
        · have ht := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient; omega
      · dsimp only; omega
    · dsimp only; omega

end Blotto.GeneralPaperRankSearch
