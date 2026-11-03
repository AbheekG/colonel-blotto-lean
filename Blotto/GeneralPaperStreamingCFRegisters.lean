import Blotto.GeneralPaperStreamingMidpointQuery

/-! The CF data program as fixed-register tail traversal. The operation
ledger is an analytical annotation, not retained recursive call frames.
Runs and reachability are erased propositions. Every reached configuration
is an actual native prefix, with the original total fuel partitioned once.
-/
namespace Blotto.GeneralPaperStreamingCFRegisters
open GeneralPaperRegularCFLoop
set_option autoImplicit false
set_option maxHeartbeats 8000000

def advance (D divisionFuel : ℕ) (s : State) : State × Bool :=
  if s.denominator=0 then
    ({s with zeroChecks := s.zeroChecks+1,work := s.work+12},false)
  else GeneralPaperStreamingCFAdvance.finish D s
    (GeneralPaperStreamingNatDivision.run s.numerator s.denominator divisionFuel)

theorem advance_data (D divisionFuel : ℕ) (s : State) :
    advance D divisionFuel s=GeneralPaperRegularCFLoop.advance D divisionFuel s := by
  unfold advance GeneralPaperRegularCFLoop.advance
  split
  · rfl
  · rw [GeneralPaperStreamingNatDivision.data]
    rfl

def value (D divisionFuel : ℕ) : ℕ → State → State
  | 0,s => s
  | fuel+1,s =>
    let next := advance D divisionFuel s
    if next.2 then value D divisionFuel fuel next.1 else next.1

theorem value_data (D divisionFuel fuel : ℕ) (s : State) :
    value D divisionFuel fuel s=GeneralPaperRegularCFLoop.run D divisionFuel fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [value,GeneralPaperRegularCFLoop.run,advance_data]
    split
    · exact ih _
    · rfl

theorem priced_data (model : RationalCostModel) (W D divisionFuel fuel : ℕ) (s : State) :
    (GeneralPaperStreamingCFRun.run model W D divisionFuel fuel s).1=value D divisionFuel fuel s := by
  rw [GeneralPaperStreamingCFRun.data,value_data]

structure Configuration where
  remaining : ℕ
  state : State

def step (D divisionFuel : ℕ) (c : Configuration) : State ⊕ Configuration :=
  match c.remaining with
  | 0 => .inl c.state
  | fuel+1 =>
    let next := advance D divisionFuel c.state
    if next.2 then .inr ⟨fuel,next.1⟩ else .inl next.1

def result (D divisionFuel : ℕ) (c : Configuration) : State :=
  value D divisionFuel c.remaining c.state

theorem step_result (D divisionFuel : ℕ) (c next : Configuration)
    (h : step D divisionFuel c=.inr next) : result D divisionFuel c=result D divisionFuel next := by
  obtain ⟨remaining,s⟩ := c
  cases remaining with
  | zero => cases h
  | succ fuel =>
    dsimp only [step] at h
    split at h
    · rename_i hb
      have he := Sum.inr.inj h
      subst next
      simp only [result,value,ite_eq_left hb]
    · cases h

theorem stop_result (D divisionFuel : ℕ) (c : Configuration) (out : State)
    (h : step D divisionFuel c=.inl out) : result D divisionFuel c=out := by
  obtain ⟨remaining,s⟩ := c
  cases remaining with
  | zero => exact Sum.inl.inj h
  | succ fuel =>
    dsimp only [step] at h
    split at h
    · cases h
    · rename_i hb
      have he := Sum.inl.inj h
      simp only [result,value,ite_eq_right hb]
      exact he

inductive Runs (D divisionFuel : ℕ) : Configuration → State → Prop
  | stop (c : Configuration) (out : State) (h : step D divisionFuel c=.inl out) : Runs D divisionFuel c out
  | more (c next : Configuration) (out : State) (h : step D divisionFuel c=.inr next)
      (later : Runs D divisionFuel next out) : Runs D divisionFuel c out

theorem runs (D divisionFuel : ℕ) (c : Configuration) : Runs D divisionFuel c (result D divisionFuel c) := by
  obtain ⟨remaining,s⟩ := c
  induction remaining generalizing s with
  | zero => exact .stop _ _ rfl
  | succ fuel ih =>
    by_cases hb : (advance D divisionFuel s).2=true
    · have hs : step D divisionFuel ⟨fuel+1,s⟩=.inr ⟨fuel,(advance D divisionFuel s).1⟩ := by
        simp only [step,ite_eq_left hb]
      rw [step_result D divisionFuel _ _ hs]
      exact .more _ _ _ hs (ih _)
    · have hs : step D divisionFuel ⟨fuel+1,s⟩=.inl (advance D divisionFuel s).1 := by
        simp only [step,ite_eq_right hb]
      rw [stop_result D divisionFuel _ _ hs]
      exact .stop _ _ hs

inductive Continues (D divisionFuel : ℕ) (initialState : State) : ℕ → State → Prop
  | start : Continues D divisionFuel initialState 0 initialState
  | more (n : ℕ) (s : State) (old : Continues D divisionFuel initialState n s)
      (h : (advance D divisionFuel s).2=true) :
      Continues D divisionFuel initialState (n+1) (advance D divisionFuel s).1

theorem continuation (D divisionFuel : ℕ) (initialState : State) (n : ℕ) (s : State)
    (h : Continues D divisionFuel initialState n s) (fuel : ℕ) :
    GeneralPaperRegularCFLoop.run D divisionFuel (n+fuel) initialState=
      GeneralPaperRegularCFLoop.run D divisionFuel fuel s := by
  induction h generalizing fuel with
  | start => simp only [Nat.zero_add]
  | more n s _ hb ih =>
    rw [show n+1+fuel=n+(fuel+1) by omega,ih (fuel+1)]
    rw [GeneralPaperRegularCFLoop.run,←advance_data,ite_eq_left hb]

inductive Reach (D divisionFuel total : ℕ) (initialState : State) : Configuration → Prop
  | start : Reach D divisionFuel total initialState ⟨total,initialState⟩
  | more (c next : Configuration) (old : Reach D divisionFuel total initialState c)
      (h : step D divisionFuel c=.inr next) : Reach D divisionFuel total initialState next

theorem reached_prefix (D divisionFuel total : ℕ) (initialState : State) (c : Configuration)
    (h : Reach D divisionFuel total initialState c) :
    ∃ n, n+c.remaining=total ∧ c.state=GeneralPaperRegularCFLoop.run D divisionFuel n initialState := by
  have stronger : ∃ n, n+c.remaining=total ∧ Continues D divisionFuel initialState n c.state := by
    induction h with
    | start => exact ⟨0,Nat.zero_add total,.start⟩
    | more c next _ hs ih =>
      obtain ⟨n,hn,hc⟩ := ih
      obtain ⟨remaining,s⟩ := c
      cases remaining with
      | zero => cases hs
      | succ fuel =>
        dsimp only [step] at hs
        split at hs
        · rename_i hb
          have he := Sum.inr.inj hs
          subst next
          exact ⟨n+1,by dsimp only at hn ⊢; omega,.more n s hc hb⟩
        · cases hs
  obtain ⟨n,hn,hc⟩ := stronger
  refine ⟨n,hn,?_⟩
  have he := continuation D divisionFuel initialState n c.state hc 0
  simpa only [Nat.add_zero,GeneralPaperRegularCFLoop.run] using he.symm

end Blotto.GeneralPaperStreamingCFRegisters
