import Blotto.GeneralPaperQuotientRegisters

/-! Every reachable register configuration has bounded data and counters.
The original division identity bounds the descending quotient/remainder;
the only divisor retained is the current constructed power.
-/
namespace Blotto.GeneralPaperQuotientRegisterBounds
open GeneralPaperQuotientTraversal GeneralPaperQuotientRegisters
set_option autoImplicit false
set_option maxHeartbeats 6000000

def magnitude (n a : ℕ) : ℕ := 2*(n+a+1)

def UpValid (n a fuel : ℕ) (s : UpState) : Prop :=
  0<s.scale ∧ s.scale≤magnitude n a ∧ s.fuel+s.count=fuel

theorem up_initial (n a fuel : ℕ) (ha : 0<a) : UpValid n a fuel ⟨a,fuel,0⟩ := by
  dsimp only [UpValid,magnitude]
  omega

theorem up_next (n a fuel : ℕ) (s next : UpState) (h : UpValid n a fuel s) (hs : upStep n s=some next) :
    UpValid n a fuel next := by
  obtain ⟨scale,remaining,count⟩ := s
  cases remaining with
  | zero => cases hs
  | succ remaining =>
    dsimp only [upStep] at hs
    split at hs
    · cases hs
    · rename_i hn
      have he := Option.some.inj hs
      subst next
      dsimp only [UpValid] at h ⊢
      unfold magnitude at *
      omega

inductive UpReach (n a fuel : ℕ) : UpState → Prop
  | initial : UpReach n a fuel ⟨a,fuel,0⟩
  | next (s next : UpState) (past : UpReach n a fuel s) (step : upStep n s=some next) : UpReach n a fuel next

theorem up_reachable (n a fuel : ℕ) (ha : 0<a) (s : UpState) (h : UpReach n a fuel s) : UpValid n a fuel s := by
  induction h with
  | initial => exact up_initial n a fuel ha
  | next s next past step ih => exact up_next n a fuel s next ih step

theorem up_result (n a fuel : ℕ) (s : UpState) (h : UpValid n a fuel s) :
    0<(upValue n s).scale ∧ (upValue n s).scale≤magnitude n a ∧ (upValue n s).depth≤fuel := by
  obtain ⟨scale,remaining,count⟩ := s
  induction remaining generalizing scale count with
  | zero =>
    change 0<scale ∧ scale≤magnitude n a ∧ count≤fuel
    dsimp only [UpValid] at h
    omega
  | succ remaining ih =>
    by_cases hn : n<scale
    · have hs : upStep n ⟨scale,remaining+1,count⟩=none := by simp only [upStep,ite_eq_left hn]
      rw [up_stop_value _ _ hs]
      change 0<scale ∧ scale≤magnitude n a ∧ count≤fuel
      dsimp only [UpValid] at h
      omega
    · have hs : upStep n ⟨scale,remaining+1,count⟩=some ⟨2*scale,remaining,count+1⟩ := by simp only [upStep,ite_eq_right hn]
      rw [up_step_value _ _ _ hs]
      exact ih _ _ (up_next n a fuel _ _ h hs)

theorem restore_identity (scale q r : ℕ) :
    scale*(restore scale (q,r)).1+(restore scale (q,r)).2=2*scale*q+r := by
  unfold restore
  split
  · rename_i h
    have hs : r-scale+scale=r := by omega
    dsimp only
    nlinarith only [hs]
  · dsimp only
    ring

def DownValid (n a fuel : ℕ) (s : DownState) : Prop :=
  s.scale=a*2^s.remaining ∧ s.remaining≤fuel ∧ n=s.scale*s.quotient+s.remainder ∧
    0<s.scale ∧ s.scale≤magnitude n a

def initialDown (n a fuel : ℕ) : DownState :=
  let top := up n a fuel 0
  ⟨top.scale,top.depth,0,n⟩

theorem down_initial (n a fuel : ℕ) (ha : 0<a) : DownValid n a fuel (initialDown n a fuel) := by
  have ht := up_data n a fuel 0
  simp only [Nat.zero_add] at ht
  have hb := up_result n a fuel ⟨a,fuel,0⟩ (up_initial n a fuel ha)
  change 0<(up n a fuel 0).scale ∧ (up n a fuel 0).scale≤magnitude n a ∧ (up n a fuel 0).depth≤fuel at hb
  dsimp only [initialDown,DownValid]
  refine ⟨?_,hb.2.2,?_,hb.1,hb.2.1⟩
  · rw [ht.1,ht.2]
  · simp only [Nat.mul_zero,Nat.zero_add]

theorem down_next (n a fuel : ℕ) (ha : 0<a) (s next : DownState)
    (h : DownValid n a fuel s) (hs : downStep s=some next) : DownValid n a fuel next := by
  obtain ⟨scale,remaining,q,r⟩ := s
  cases remaining with
  | zero => cases hs
  | succ remaining =>
    dsimp only [downStep] at hs
    have he := Option.some.inj hs
    subst next
    dsimp only [DownValid] at h ⊢
    have hh : scale/2=a*2^remaining := by rw [h.1,halve]
    have hDouble : scale=2*(scale/2) := by rw [hh,h.1,pow_succ]; ring
    refine ⟨hh,by omega,?_,?_,?_⟩
    · calc
        n = 2*(scale/2)*q+r := by rw [←hDouble]; exact h.2.2.1
        _ = (scale/2)*(restore (scale/2) (q,r)).1+(restore (scale/2) (q,r)).2 :=
          (restore_identity (scale/2) q r).symm
    · rw [hh]
      exact Nat.mul_pos ha (Nat.two_pow_pos remaining)
    · exact (show scale/2≤scale by omega).trans h.2.2.2.2

inductive DownReach (n a fuel : ℕ) : DownState → Prop
  | initial : DownReach n a fuel (initialDown n a fuel)
  | next (s next : DownState) (past : DownReach n a fuel s) (step : downStep s=some next) : DownReach n a fuel next

theorem down_reachable (n a fuel : ℕ) (ha : 0<a) (s : DownState) (h : DownReach n a fuel s) : DownValid n a fuel s := by
  induction h with
  | initial => exact down_initial n a fuel ha
  | next s next past step ih => exact down_next n a fuel ha s next ih step

theorem down_payload (n a fuel : ℕ) (s : DownState) (h : DownValid n a fuel s) :
    s.quotient≤n ∧ s.remainder≤n := by
  have hq : s.quotient≤s.scale*s.quotient := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right s.quotient (show 1≤s.scale by exact h.2.2.2.1)
  have he := h.2.2.1
  omega

theorem operational (n a fuel : ℕ) :
    UpRuns n ⟨a,fuel,0⟩ (up n a fuel 0) ∧
      DownRuns (initialDown n a fuel) ((GeneralPaperStreamingQuotient.run n a fuel).quotient,
        (GeneralPaperStreamingQuotient.run n a fuel).remainder) := by
  refine ⟨up_runs n ⟨a,fuel,0⟩,?_⟩
  exact down_runs (initialDown n a fuel)

end Blotto.GeneralPaperQuotientRegisterBounds
