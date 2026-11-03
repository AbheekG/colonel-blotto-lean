import Blotto.GeneralPaperSourceRayStorageRates

/-! Erased exact query traces for the actual indexed binary search. The
trace has the native probe count and every rational read comes from its
actual constructed crossing array. No trace is materialized at runtime. -/
namespace Blotto.GeneralPaperRaySearchProbeTrace
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

def run {n : ℕ} (query : Fin n → Bool×ℕ) (depth : ℕ) : ℕ → ℕ → ℕ → List (Fin n)
  | 0,_,_ => []
  | fuel+1,lo,hi =>
    if lo<hi then
      let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
      if hMid : mid.quotient<n then
        let i : Fin n := ⟨mid.quotient,hMid⟩
        i::if (query i).1=true then run query depth fuel (mid.quotient+1) hi else run query depth fuel lo mid.quotient
      else []
    else []

theorem length {n : ℕ} (query : Fin n → Bool×ℕ) (W depth fuel lo hi : ℕ) :
    (run query depth fuel lo hi).length=(GeneralPaperPricedRaySearch.run query W depth fuel lo hi).probes := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    rw [run,GeneralPaperPricedRaySearch.run]
    split
    · dsimp only
      split
      · split <;> simpa only [List.length_cons] using congrArg (·+1) (ih _ _)
      · rfl
    · rfl

def selected {n : ℕ} (query : Fin n → Bool×ℕ) : List (Fin n) :=
  let scale := GeneralPaperPowerCeiling.ceiling n
  run query (scale.doublings+1) (scale.doublings+1) 0 n

theorem selected_length {n : ℕ} (query : Fin n → Bool×ℕ) (W : ℕ) :
    (selected query).length=(GeneralPaperPricedRaySearch.selected query W).probes := length query W _ _ _ _

def refinement (primitive index : ℕ → ℕ) (W : ℕ) (query : ℚ → Bool×ℕ) (lo hi : ℚ) (points : List ℚ) : List ℚ :=
  let values := (GeneralPaperPricedCrossingArray.run primitive index W lo hi points).1
  (selected (GeneralPaperPricedCrossingRefinement.readQuery query W values)).map values.read

theorem refinement_length (primitive index : ℕ → ℕ) (W : ℕ) (query : ℚ → Bool×ℕ) (lo hi : ℚ) (points : List ℚ) :
    (refinement primitive index W query lo hi points).length=
      (GeneralPaperPricedCrossingRefinement.run primitive index W query lo hi points).probes := by
  simp only [refinement,List.length_map,GeneralPaperPricedCrossingRefinement.run]
  exact selected_length _ W

theorem refinement_mem (primitive index : ℕ → ℕ) (W : ℕ) (query : ℚ → Bool×ℕ) (lo hi : ℚ) (points : List ℚ)
    (t : ℚ) (ht : t∈refinement primitive index W query lo hi points) :
    t∈GeneralPaperRaySortedCrossings.ordered lo hi points := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
  rw [GeneralPaperPricedCrossingArray.data]
  exact GeneralPaperRaySortedCrossings.read_mem lo hi points i

theorem bounded (primitive index : ℕ → ℕ) (W R : ℕ) (query : ℚ → Bool×ℕ) (lo hi : ℚ) (points : List ℚ)
    (hOrder : lo≤hi) (hl : RationalHeight lo R) (hh : RationalHeight hi R)
    (hp : ∀ q∈points,RationalHeight q R) (t : ℚ) (ht : t∈refinement primitive index W query lo hi points) :
    lo≤t ∧ t≤hi ∧ RationalHeight t R := by
  have hm := refinement_mem primitive index W query lo hi points t ht
  have hb := GeneralPaperRaySortedCrossings.ordered_bound lo hi hOrder points t hm
  refine ⟨hb.1,hb.2,?_⟩
  rcases (GeneralPaperRaySortedCrossings.ordered_mem lo hi points t).mp hm with rfl|rfl|⟨hm,_,_⟩
  · exact hl
  · exact hh
  · exact hp t hm

end Blotto.GeneralPaperRaySearchProbeTrace
