import Blotto.GeneralPaperPricedCrossingArray

/-! Price on-demand crossing search with word/control cost W and already
priced feasibility queries. Its rank and probe trace are exactly those of
the selected unweighted search. Each iteration invokes only its one query.
-/
namespace Blotto.GeneralPaperPricedRaySearch
open GeneralPaperRayOracleSearch GeneralPaperRankMidpoint
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {n : ℕ} (query : Fin n → Bool × ℕ) (W depth : ℕ) : ℕ → ℕ → ℕ → Result
  | 0,lo,_ => ⟨lo,8*W,0⟩
  | fuel+1,lo,hi =>
    if lo<hi then
      let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
      if hMid : mid.quotient<n then
        let current := query ⟨mid.quotient,hMid⟩
        if current.1=true then
          let child := run query W depth fuel (mid.quotient+1) hi
          ⟨child.rank,child.work+mid.work*W+current.2+32*W,child.probes+1⟩
        else
          let child := run query W depth fuel lo mid.quotient
          ⟨child.rank,child.work+mid.work*W+current.2+32*W,child.probes+1⟩
      else ⟨lo,(mid.work+24)*W,0⟩
    else ⟨lo,8*W,0⟩

theorem trace {n : ℕ} (query : Fin n → Bool × ℕ) (W depth fuel lo hi : ℕ) :
    (run query W depth fuel lo hi).rank=(GeneralPaperRayOracleSearch.run query depth fuel lo hi).rank ∧
    (run query W depth fuel lo hi).probes=(GeneralPaperRayOracleSearch.run query depth fuel lo hi).probes := by
  induction fuel generalizing lo hi with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    rw [run,GeneralPaperRayOracleSearch.run]
    split
    · dsimp only
      split
      · split
        · dsimp only
          have ht := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi
          exact ⟨ht.1,congrArg (·+1) ht.2⟩
        · dsimp only
          have ht := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient
          exact ⟨ht.1,congrArg (·+1) ht.2⟩
      · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩

theorem work {n : ℕ} (query : Fin n → Bool × ℕ) (W depth fuel lo hi E : ℕ)
    (hWork : ∀ i,(query i).2≤E) :
    (run query W depth fuel lo hi).work≤fuel*((12*depth+34)*W+E)+8*W := by
  induction fuel generalizing lo hi with
  | zero => simp only [run,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      split
      · rename_i hMid
        have hc := hWork ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩
        split
        · dsimp only
          have ht := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi
          rw [midpoint_work]
          nlinarith only [ht,hc]
        · dsimp only
          have ht := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient
          rw [midpoint_work]
          nlinarith only [ht,hc]
      · dsimp only
        rw [midpoint_work]
        have hm := Nat.mul_le_mul_right ((12*depth+34)*W+E)
          (show 1≤fuel+1 by omega)
        simp only [Nat.one_mul] at hm
        nlinarith only [hm]
    · dsimp only
      omega

def selected {n : ℕ} (query : Fin n → Bool × ℕ) (W : ℕ) : Result :=
  let scale := GeneralPaperPowerCeiling.ceiling n
  let result := run query W (scale.doublings+1) (scale.doublings+1) 0 n
  ⟨result.rank,result.work+scale.work*W+16*W,result.probes⟩

theorem selected_rank {n : ℕ} (query : Fin n → Bool × ℕ) (W : ℕ) :
    (selected query W).rank=(GeneralPaperRaySearchControls.selected query).rank :=
  (trace query W _ _ _ _).1

theorem selected_probes {n : ℕ} (query : Fin n → Bool × ℕ) (W : ℕ) :
    (selected query W).probes≤binaryWordWidth n+1 := by
  change (run query W _ _ _ _).probes≤_
  rw [(trace query W _ _ _ _).2]
  exact GeneralPaperRaySearchControls.logarithmic_probes query

theorem selected_work {n : ℕ} (query : Fin n → Bool × ℕ) (W E : ℕ)
    (hWork : ∀ i,(query i).2≤E) :
    (selected query W).work≤
      GeneralPaperRaySearchControls.depth n*((12*GeneralPaperRaySearchControls.depth n+34)*W+E)+
        (12*binaryWordWidth n+26)*W := by
  have hr := work query W (GeneralPaperRaySearchControls.depth n)
    (GeneralPaperRaySearchControls.depth n) 0 n E hWork
  have hc := Nat.mul_le_mul_right W (GeneralPaperPowerCeiling.ceiling_work n)
  change (run query W (GeneralPaperRaySearchControls.depth n)
    (GeneralPaperRaySearchControls.depth n) 0 n).work+
    (GeneralPaperPowerCeiling.ceiling n).work*W+16*W≤_
  nlinarith only [hr,hc]

theorem oracle_rank_congr {n : ℕ} (first second : Fin n → Bool × ℕ)
    (h : ∀ i,(first i).1=(second i).1) (depth fuel lo hi : ℕ) :
    (GeneralPaperRayOracleSearch.run first depth fuel lo hi).rank=
      (GeneralPaperRayOracleSearch.run second depth fuel lo hi).rank := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    rw [GeneralPaperRayOracleSearch.run,GeneralPaperRayOracleSearch.run]
    split
    · dsimp only
      split
      · rename_i hMid
        rw [h ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,hMid⟩]
        split
        · exact ih _ _
        · exact ih _ _
      · rfl
    · rfl

theorem selected_rank_congr {n : ℕ} (first second : Fin n → Bool × ℕ)
    (h : ∀ i,(first i).1=(second i).1) (W : ℕ) :
    (selected first W).rank=(GeneralPaperRaySearchControls.selected second).rank := by
  rw [selected_rank]
  exact oracle_rank_congr first second h _ _ _ _

end Blotto.GeneralPaperPricedRaySearch
