import Blotto.PlayerSpecificSweep

/-! The endpoint gate uses cached prefix/suffix maxima, rather than a new
scan for every root. The suffix construction below visits each field once.
These statements concern the literal data, not a supplied maximum oracle. -/
namespace Blotto.PlayerSpecificSweepBounds
open PlayerSpecificCubic PlayerSpecificSweep
set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂]

def maximum {α : Type*} (f : α → 𝕂) : List α → 𝕂
  | [] => 0
  | x::xs => max (f x) (maximum f xs)

theorem maximum_nonnegative {α : Type*} (f : α → 𝕂) (xs : List α) : 0≤maximum f xs := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

theorem maximum_bound {α : Type*} (f : α → 𝕂) (xs : List α) (bound : 𝕂) :
    maximum f xs≤bound ↔ 0≤bound ∧ ∀ x∈xs,f x≤bound := by
  induction xs with
  | nil => simp only [maximum,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
  | cons x xs ih => simp only [maximum,max_le_iff,ih,List.mem_cons,forall_eq_or_imp]; tauto

theorem maximum_append {α : Type*} (f : α → 𝕂) (xs ys : List α) :
    maximum f (xs++ys)=max (maximum f xs) (maximum f ys) := by
  induction xs with
  | nil => simp only [List.nil_append,maximum,max_eq_right (maximum_nonnegative f ys)]
  | cons x xs ih => simp only [List.cons_append,maximum,ih,max_assoc]

theorem scaled_maximum_bound [IsStrictOrderedRing 𝕂] {α : Type*} (f : α → 𝕂) (xs : List α) (gamma bound : 𝕂)
    (hg : 0<gamma) :
    gamma*maximum f xs≤bound ↔ 0≤bound ∧ ∀ x∈xs,gamma*f x≤bound := by
  rw [← le_div_iff₀' hg,maximum_bound]
  constructor
  · rintro ⟨hb,hx⟩
    exact ⟨by simpa only [mul_zero] using (le_div_iff₀' hg).mp hb,
      fun x hx' => (le_div_iff₀' hg).mp (hx x hx')⟩
  · rintro ⟨hb,hx⟩
    exact ⟨div_nonneg hb hg.le,fun x hx' => (le_div_iff₀' hg).mpr (hx x hx')⟩

theorem endpoint_gate [IsStrictOrderedRing 𝕂] (low high : List (𝕂×𝕂)) (gamma bound : 𝕂) (hg : 0<gamma) :
    max (maximum Prod.fst low) (gamma*maximum Prod.snd high)≤bound ↔
      0≤bound ∧ (∀ x∈low,x.1≤bound) ∧ (∀ x∈high,gamma*x.2≤bound) := by
  rw [max_le_iff,maximum_bound,scaled_maximum_bound _ _ _ _ hg]
  tauto

def FullInvariant (s : State 𝕂) (low high : List (𝕂×𝕂)) : Prop :=
  Invariant s low high ∧ s.prefixMax=maximum Prod.fst low

theorem initial_full (fields : List (𝕂×𝕂)) : FullInvariant (initial fields) [] fields :=
  ⟨initial_invariant fields,rfl⟩

theorem move_full (s : State 𝕂) (low high : List (𝕂×𝕂)) (v w : 𝕂)
    (h : FullInvariant s low ((v,w)::high)) : FullInvariant (move s v w) (low++[(v,w)]) high := by
  refine ⟨move_invariant s low high v w h.1,?_⟩
  change max s.prefixMax v=maximum Prod.fst (low++[(v,w)])
  rw [h.2,maximum_append]
  dsimp only [maximum]
  rw [← max_assoc]
  exact (max_eq_left ((maximum_nonnegative Prod.fst low).trans (le_max_left _ _))).symm

/-- A suffix envelope is stored beside each field. The empty suffix has
maximum zero. Construction is one backwards pass. -/
def suffixes : List (𝕂×𝕂) → 𝕂×List ((𝕂×𝕂)×𝕂)×ℕ
  | [] => (0,[],4)
  | x::xs =>
    let tail := suffixes xs
    let bound := max x.2 tail.1
    (bound,(x,bound)::tail.2.1,tail.2.2+16)

theorem suffixes_maximum (fields : List (𝕂×𝕂)) :
    (suffixes fields).1=maximum Prod.snd fields := by
  induction fields with
  | nil => rfl
  | cons x xs ih => simpa only [suffixes,maximum] using congrArg (max x.2) ih

theorem suffixes_fields (fields : List (𝕂×𝕂)) :
    ((suffixes fields).2.1.map Prod.fst)=fields := by
  induction fields with
  | nil => rfl
  | cons x xs ih => simp only [suffixes,List.map_cons,ih]

theorem suffixes_work (fields : List (𝕂×𝕂)) : (suffixes fields).2.2=16*fields.length+4 := by
  induction fields with
  | nil => rfl
  | cons x xs ih => simp only [suffixes,List.length_cons,ih]; omega

theorem suffixes_cons (x : 𝕂×𝕂) (xs : List (𝕂×𝕂)) :
    (suffixes (x::xs)).2.1=(x,maximum Prod.snd (x::xs))::(suffixes xs).2.1 := by
  rw [← suffixes_maximum]
  rfl

end Blotto.PlayerSpecificSweepBounds
