import Blotto.PlayerSpecificPolynomial

/-! The literal four-scalar update when a field moves from the high-ratio
suffix to the low-ratio prefix. Complete sums are computed once; each move
uses constant arithmetic. A sorted/grouped scanner is a later caller. -/
namespace Blotto.PlayerSpecificSweep
open PlayerSpecificCubic
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure State (𝕂 : Type*) where
  coefficients : Coefficients 𝕂
  prefixMax : 𝕂

def initial {𝕂 : Type*} [Field 𝕂] (fields : List (𝕂 × 𝕂)) : State 𝕂 :=
  ⟨⟨(fields.map Prod.snd).sum,0,(fields.map (fun x => x.2^2/x.1)).sum,0⟩,0⟩

def move {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] (s : State 𝕂) (v w : 𝕂) : State 𝕂 :=
  ⟨⟨s.coefficients.A1-w,s.coefficients.A2+v^2/w,s.coefficients.B1-w^2/v,s.coefficients.B2+v⟩,
    max s.prefixMax v⟩

def advance {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] (s : State 𝕂) : List (𝕂 × 𝕂) → State 𝕂
  | [] => s
  | x::rest => advance (move s x.1 x.2) rest

def Invariant {𝕂 : Type*} [Field 𝕂] (s : State 𝕂) (low high : List (𝕂 × 𝕂)) : Prop :=
  s.coefficients.A1=(high.map Prod.snd).sum ∧
  s.coefficients.A2=(low.map (fun x => x.1^2/x.2)).sum ∧
  s.coefficients.B1=(high.map (fun x => x.2^2/x.1)).sum ∧
  s.coefficients.B2=(low.map Prod.fst).sum

theorem initial_invariant {𝕂 : Type*} [Field 𝕂] (fields : List (𝕂 × 𝕂)) :
    Invariant (initial fields) [] fields := by simp [Invariant,initial]

theorem move_invariant {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂]
    (s : State 𝕂) (low high : List (𝕂 × 𝕂)) (v w : 𝕂)
    (h : Invariant s low ((v,w)::high)) : Invariant (move s v w) (low++[(v,w)]) high := by
  rcases h with ⟨h1,h2,h3,h4⟩
  dsimp only [Invariant,move]
  simp only [List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_nil,List.sum_nil,add_zero] at h1 h3 ⊢
  exact ⟨by linear_combination h1,by rw [h2],by linear_combination h3,by rw [h4]⟩

theorem advance_invariant {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂]
    (s : State 𝕂) (low moved high : List (𝕂 × 𝕂)) (h : Invariant s low (moved++high)) :
    Invariant (advance s moved) (low++moved) high := by
  induction moved generalizing s low with
  | nil => simpa only [advance,List.nil_append,List.append_nil] using h
  | cons x rest ih =>
    have hm := move_invariant s low (rest++high) x.1 x.2 h
    have ht := ih (move s x.1 x.2) (low++[x]) hm
    simpa only [advance,List.append_assoc,List.singleton_append] using ht

theorem finished {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] (fields : List (𝕂 × 𝕂)) :
    (advance (initial fields) fields).coefficients.A1=0 ∧
    (advance (initial fields) fields).coefficients.A2=(fields.map (fun x => x.1^2/x.2)).sum ∧
    (advance (initial fields) fields).coefficients.B1=0 ∧
    (advance (initial fields) fields).coefficients.B2=(fields.map Prod.fst).sum := by
  have h := advance_invariant (initial fields) [] fields [] (by simpa using initial_invariant fields)
  simpa only [Invariant,List.nil_append,List.map_nil,List.sum_nil] using h

theorem prefix_bound {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] (s : State 𝕂) (v w : 𝕂) (bound : 𝕂) :
    (move s v w).prefixMax≤bound ↔ s.prefixMax≤bound ∧ v≤bound := max_le_iff

theorem scale_at_breakpoint {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂]
    (s : State 𝕂) (v w b gamma : 𝕂) (hg : 0<gamma) (h : v=gamma*w) :
    candidateScale (move s v w).coefficients b gamma=candidateScale s.coefficients b gamma := by
  rw [h]
  unfold candidateScale move
  congr 1
  field_simp [hg.ne']
  ring

theorem cubic_at_breakpoint {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂]
    (s : State 𝕂) (v w b gamma : 𝕂) (hg : 0<gamma) (h : v=gamma*w) :
    cubic (move s v w).coefficients b gamma=cubic s.coefficients b gamma := by
  rw [h]
  unfold cubic move
  field_simp [hg.ne']
  ring

end Blotto.PlayerSpecificSweep
