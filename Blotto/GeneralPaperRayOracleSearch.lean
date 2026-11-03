import Blotto.GeneralPaperRayCrossingPairs

/-! On-demand binary search for the first infeasible crossing. Each
iteration executes exactly one feasibility query at its arithmetic midpoint;
it never materializes query results for all crossings. Guarded reads make
the program total and the valid-state proof excludes the fallback.
-/
namespace Blotto.GeneralPaperRayOracleSearch
open GeneralPaperRankMidpoint
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result where
  rank : ℕ
  work : ℕ
  probes : ℕ

def run {n : ℕ} (query : Fin n → Bool × ℕ) (depth : ℕ) : ℕ → ℕ → ℕ → Result
  | 0,lo,_ => ⟨lo,8,0⟩
  | fuel+1,lo,hi =>
    if lo<hi then
      let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
      if hMid : mid.quotient<n then
        let current := query ⟨mid.quotient,hMid⟩
        if current.1=true then
          let child := run query depth fuel (mid.quotient+1) hi
          ⟨child.rank,child.work+mid.work+current.2+32,child.probes+1⟩
        else
          let child := run query depth fuel lo mid.quotient
          ⟨child.rank,child.work+mid.work+current.2+32,child.probes+1⟩
      else ⟨lo,mid.work+24,0⟩
    else ⟨lo,8,0⟩

def Downward {n : ℕ} (query : Fin n → Bool × ℕ) : Prop :=
  ∀ i j,i≤j → (query j).1=true → (query i).1=true

def Valid {n : ℕ} (query : Fin n → Bool × ℕ) (rank : ℕ) : Prop :=
  rank≤n ∧ ∀ i,(query i).1=true ↔ i.val<rank

theorem closed {n : ℕ} (query : Fin n → Bool × ℕ) (lo hi : ℕ)
    (hLo : lo≤hi) (hHi : hi≤n) (hClosed : hi=lo)
    (hLeft : ∀ i : Fin n,i.val<lo → (query i).1=true)
    (hRight : ∀ i : Fin n,hi ≤ i.val → (query i).1≠true) : Valid query lo := by
  refine ⟨hLo.trans hHi,?_⟩
  intro i
  constructor
  · intro h
    by_contra hn
    exact hRight i (by omega) h
  · exact hLeft i

theorem run_spec {n : ℕ} (query : Fin n → Bool × ℕ) (depth fuel lo hi : ℕ)
    (hDown : Downward query) (hLo : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth)
    (hSpan : hi-lo<2^fuel)
    (hLeft : ∀ i : Fin n,i.val<lo → (query i).1=true)
    (hRight : ∀ i : Fin n,hi ≤ i.val → (query i).1≠true) :
    Valid query (run query depth fuel lo hi).rank := by
  induction fuel generalizing lo hi with
  | zero =>
    have hc : hi=lo := by simp only [pow_zero] at hSpan; omega
    exact closed query lo hi hLo hHi hc hLeft hRight
  | succ fuel ih =>
    by_cases hOpen : lo<hi
    · have hm := midpoint_inside n depth lo hi hOpen hHi hSize
      have hMid : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hHi
      have hShrink := midpoint_shrinks n depth lo hi fuel hOpen hHi hSize hSpan
      rw [run,ite_eq_left hOpen,dite_eq_left hMid]
      dsimp only
      split
      · rename_i hTrue
        apply ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi (by omega) hHi hShrink.2 _ hRight
        intro i hIndex
        exact hDown i ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩
          (by change i.val≤(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient; omega) hTrue
      · rename_i hFalse
        apply ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient hm.1 (by omega) hShrink.1 hLeft
        intro i hIndex hTrue
        exact hFalse (hDown ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩ i hIndex hTrue)
    · rw [run,ite_eq_right hOpen]
      exact closed query lo hi hLo hHi (by omega) hLeft hRight

theorem run_work {n : ℕ} (query : Fin n → Bool × ℕ) (depth fuel lo hi E : ℕ)
    (hWork : ∀ i,(query i).2≤E) : (run query depth fuel lo hi).work≤fuel*(12*depth+34+E)+8 := by
  induction fuel generalizing lo hi with
  | zero => simp only [run,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      split
      · rename_i hMid
        have hCost := hWork ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩
        split <;> dsimp only
        · have ht := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi
          rw [midpoint_work]
          nlinarith only [ht,hCost]
        · have ht := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient
          rw [midpoint_work]
          nlinarith only [ht,hCost]
      · dsimp only
        rw [midpoint_work]
        nlinarith
    · dsimp only
      omega

theorem run_probes {n : ℕ} (query : Fin n → Bool × ℕ) (depth fuel lo hi : ℕ) :
    (run query depth fuel lo hi).probes≤fuel := by
  induction fuel generalizing lo hi with
  | zero => exact le_rfl
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

end Blotto.GeneralPaperRayOracleSearch
