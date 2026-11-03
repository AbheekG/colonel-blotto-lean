import Blotto.GeneralPaperConstructedNatDivision

/-! The selected midpoint regular-CF loop. Construct every integer quotient
arithmetically, update the two continuants, and retain the last convergent
whose denominator is within D. The final rejected convergent is charged too.
Coverage by constructed fuel and the regular-convergent/Legendre completeness
join remain required; this module proves the actual loop and local invariants.
-/
namespace Blotto.GeneralPaperRegularCFLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure State where
  numerator : ℕ
  denominator : ℕ
  olderNum : ℕ
  olderDen : ℕ
  previousNum : ℕ
  previousDen : ℕ
  selected : Option Farey.Fraction
  steps : ℕ
  quotientDepth : ℕ
  zeroChecks : ℕ
  work : ℕ

def initial (C t : ℕ) : State := ⟨2*t+1,2*C,0,1,1,0,none,0,0,0,0⟩

def advance (D divisionFuel : ℕ) (state : State) : State × Bool :=
  if state.denominator=0 then ({state with zeroChecks := state.zeroChecks+1,work := state.work+12},false) else
    let divided := GeneralPaperConstructedNatDivision.run state.numerator state.denominator divisionFuel
    let numerator := divided.quotient*state.previousNum+state.olderNum
    let denominator := divided.quotient*state.previousDen+state.olderDen
    let charged : State := ⟨state.denominator,divided.remainder,state.previousNum,state.previousDen,numerator,denominator,
      state.selected,state.steps+1,state.quotientDepth+divided.depth,state.zeroChecks,state.work+divided.work+48⟩
    if hd : 0<denominator then
      if denominator≤D then ({charged with selected := some ⟨numerator,denominator,hd⟩},true)
      else (charged,false)
    else (charged,false)

def run (D divisionFuel : ℕ) : ℕ → State → State
  | 0,state => state
  | fuel+1,state =>
    let next := advance D divisionFuel state
    if next.2 then run D divisionFuel fuel next.1 else next.1

def SelectedBounded (D : ℕ) (state : State) : Prop := ∀ f, state.selected=some f → f.den≤D

theorem advance_selected_bounded (D divisionFuel : ℕ) (state : State) (hBound : SelectedBounded D state) :
    SelectedBounded D (advance D divisionFuel state).1 := by
  dsimp only [advance]
  split
  · exact hBound
  · split
    · split
      · rename_i hDen
        intro f hf
        have he := congrArg Farey.Fraction.den (Option.some.inj hf)
        simpa only [←he] using hDen
      · exact hBound
    · exact hBound

theorem run_selected_bounded (D divisionFuel fuel : ℕ) (state : State) (hBound : SelectedBounded D state) :
    SelectedBounded D (run D divisionFuel fuel state) := by
  induction fuel generalizing state with
  | zero => exact hBound
  | succ fuel ih =>
    dsimp only [run]
    split
    · exact ih _ (advance_selected_bounded D divisionFuel state hBound)
    · exact advance_selected_bounded D divisionFuel state hBound

theorem initial_bounded (D C t : ℕ) : SelectedBounded D (initial C t) := by
  intro f hf
  cases hf

theorem advance_euclidean (D divisionFuel : ℕ) (state : State) (hDen : 0<state.denominator)
    (hCap : state.numerator<state.denominator*2^divisionFuel) :
    (advance D divisionFuel state).1.numerator=state.denominator ∧
      (advance D divisionFuel state).1.denominator=state.numerator%state.denominator := by
  have hs : ¬state.denominator=0 := hDen.ne'
  simp only [advance,ite_eq_right hs]
  split
  · split <;> exact ⟨rfl,GeneralPaperConstructedNatDivision.remainder_eq _ _ _ hDen hCap⟩
  · exact ⟨rfl,GeneralPaperConstructedNatDivision.remainder_eq _ _ _ hDen hCap⟩

theorem advance_zero_stop (D divisionFuel : ℕ) (state : State) (hZero : state.denominator=0) :
    (advance D divisionFuel state).2=false ∧ (advance D divisionFuel state).1.work=state.work+12 := by
  simp only [advance,ite_eq_left hZero,and_self]

theorem advance_counter (D divisionFuel : ℕ) (state : State) :
    (advance D divisionFuel state).1.work+14*state.quotientDepth+64*state.steps+12*state.zeroChecks=
      state.work+14*(advance D divisionFuel state).1.quotientDepth+64*(advance D divisionFuel state).1.steps+
        12*(advance D divisionFuel state).1.zeroChecks := by
  dsimp only [advance]
  split
  · ring
  · split
    · split <;> dsimp only <;> rw [GeneralPaperConstructedNatDivision.work_depth] <;> ring
    · dsimp only
      rw [GeneralPaperConstructedNatDivision.work_depth]
      ring

theorem run_counter (D divisionFuel fuel : ℕ) (state : State) :
    (run D divisionFuel fuel state).work+14*state.quotientDepth+64*state.steps+12*state.zeroChecks=
      state.work+14*(run D divisionFuel fuel state).quotientDepth+64*(run D divisionFuel fuel state).steps+
        12*(run D divisionFuel fuel state).zeroChecks := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    have he := advance_counter D divisionFuel state
    dsimp only [run]
    split
    · have hh := ih (advance D divisionFuel state).1
      omega
    · exact he

theorem run_zero_checks (D divisionFuel fuel : ℕ) (state : State) :
    (run D divisionFuel fuel state).zeroChecks≤state.zeroChecks+1 := by
  induction fuel generalizing state with
  | zero => change state.zeroChecks≤state.zeroChecks+1; omega
  | succ fuel ih =>
    by_cases hd : state.denominator=0
    · simp only [run,advance,ite_eq_left hd,Bool.false_eq_true,ite_false,le_refl]
    · have he : (advance D divisionFuel state).1.zeroChecks=state.zeroChecks := by
        simp only [advance,ite_eq_right hd]
        split
        · split <;> rfl
        · rfl
      dsimp only [run]
      split
      · have hh := ih (advance D divisionFuel state).1
        rw [he] at hh
        exact hh
      · rw [he]
        omega

theorem initial_work (D divisionFuel fuel C t : ℕ) :
    (run D divisionFuel fuel (initial C t)).work≤
      14*(run D divisionFuel fuel (initial C t)).quotientDepth+64*(run D divisionFuel fuel (initial C t)).steps+12 := by
  have he := run_counter D divisionFuel fuel (initial C t)
  have hh := run_zero_checks D divisionFuel fuel (initial C t)
  simp only [initial,Nat.mul_zero,Nat.add_zero,Nat.zero_add] at he hh ⊢
  omega

end Blotto.GeneralPaperRegularCFLoop
