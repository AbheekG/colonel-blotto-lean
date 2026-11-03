import Blotto.PlayerSpecificSweepBounds

/-! Transfer from the actual prefix/suffix sweep to the finite indexed
sums used by the marginal and equilibrium theorems. Field identifiers are
a permutation, so equal value pairs and equal ratios remain distinct. -/
namespace Blotto.PlayerSpecificSweepIndexed
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificSweepBounds
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

def highMask {n : ℕ} (high : List (Fin n)) (j : Fin n) : Bool := decide (j∈high)

theorem low_not_high {n : ℕ} (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (j : Fin n) (hj : j∈low) : j∉high := by
  have hn := List.nodup_append.mp (hp.nodup_iff.mpr (List.nodup_finRange n))
  exact fun hh => hn.2.2 j hj j hh rfl

theorem covered {n : ℕ} (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (j : Fin n) : j∈low ∨ j∈high := by
  have h := hp.mem_iff.mpr (List.mem_finRange j)
  exact List.mem_append.mp h

theorem sum_high {𝕂 : Type*} [Field 𝕂] {n : ℕ} (f : Fin n → 𝕂) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) :
    (∑ j,if highMask high j then f j else 0)=(high.map f).sum := by
  have hlow : low.map (fun j => if highMask high j then f j else 0)=low.map (fun _ => (0 : 𝕂)) := by
    apply List.map_congr_left
    intro j hj
    simp only [highMask,decide_eq_false (low_not_high low high hp j hj),Bool.false_eq_true,ite_false]
  have hhigh : high.map (fun j => if highMask high j then f j else 0)=high.map f := by
    apply List.map_congr_left
    intro j hj
    simp only [highMask,decide_eq_true hj,ite_true]
  have hs := (hp.map (fun j => if highMask high j then f j else 0)).sum_eq
  rw [List.map_append,List.sum_append,hlow,hhigh] at hs
  simpa only [← List.ofFn_eq_map,List.sum_ofFn,List.map_const',List.sum_replicate,nsmul_zero,zero_add] using hs.symm

theorem sum_low {𝕂 : Type*} [Field 𝕂] {n : ℕ} (f : Fin n → 𝕂) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) :
    (∑ j,if highMask high j then 0 else f j)=(low.map f).sum := by
  have hlow : low.map (fun j => if highMask high j then 0 else f j)=low.map f := by
    apply List.map_congr_left
    intro j hj
    simp only [highMask,decide_eq_false (low_not_high low high hp j hj),Bool.false_eq_true,ite_false]
  have hhigh : high.map (fun j => if highMask high j then 0 else f j)=high.map (fun _ => (0 : 𝕂)) := by
    apply List.map_congr_left
    intro j hj
    simp only [highMask,decide_eq_true hj,ite_true]
  have hs := (hp.map (fun j => if highMask high j then 0 else f j)).sum_eq
  rw [List.map_append,List.sum_append,hlow,hhigh] at hs
  simpa only [← List.ofFn_eq_map,List.sum_ofFn,List.map_const',List.sum_replicate,nsmul_zero,add_zero] using hs.symm

theorem coefficients_eq {𝕂 : Type*} [Field 𝕂] {n : ℕ} (v w : Fin n → 𝕂)
    (s : State 𝕂) (low high : List (Fin n)) (hp : (low++high).Perm (List.finRange n))
    (hi : Invariant s (low.map (fun j => (v j,w j))) (high.map (fun j => (v j,w j)))) :
    s.coefficients=coefficients v w (highMask high) := by
  have hc : coefficients v w (highMask high)=
      ⟨(high.map w).sum,(low.map (fun j => (v j)^2/w j)).sum,
        (high.map (fun j => (w j)^2/v j)).sum,(low.map v).sum⟩ := by
    dsimp only [coefficients]
    rw [sum_high w low high hp,sum_low (fun j => (v j)^2/w j) low high hp,
      sum_high (fun j => (w j)^2/v j) low high hp,sum_low v low high hp]
  rw [hc]
  rcases s with ⟨⟨a1,a2,b1,b2⟩,m⟩
  dsimp only [Invariant] at hi
  simp only [List.map_map,Function.comp_def] at hi
  rcases hi with ⟨h1,h2,h3,h4⟩
  change Coefficients.mk a1 a2 b1 b2=_
  rw [h1,h2,h3,h4]

variable {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂]

omit [IsStrictOrderedRing 𝕂] in
theorem respects {n : ℕ} (v w : Fin n → 𝕂) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (gamma : 𝕂)
    (hl : ∀ j∈low,v j≤gamma*w j) (hh : ∀ j∈high,gamma*w j≤v j) :
    Respects v w (highMask high) gamma := by
  intro j
  by_cases hj : j∈high
  · simpa only [highMask,decide_eq_true hj,ite_true] using hh j hj
  · have hjl := (covered low high hp j).resolve_right hj
    simpa only [highMask,decide_eq_false hj,Bool.false_eq_true,ite_false] using hl j hjl

theorem indexed_gate {n : ℕ} (v w : Fin n → 𝕂) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (gamma bound : 𝕂) (hg : 0<gamma) (hb : 0≤bound) :
    max (maximum v low) (gamma*maximum w high)≤bound ↔
      ∀ j,if highMask high j then gamma*w j≤bound else v j≤bound := by
  rw [max_le_iff,maximum_bound,scaled_maximum_bound _ _ _ _ hg]
  constructor
  · rintro ⟨⟨_,hl⟩,⟨_,hh⟩⟩ j
    by_cases hj : j∈high
    · simpa only [highMask,decide_eq_true hj,ite_true] using hh j hj
    · simpa only [highMask,decide_eq_false hj,Bool.false_eq_true,ite_false] using
        hl j ((covered low high hp j).resolve_right hj)
  · intro h
    refine ⟨⟨hb,fun j hj => ?_⟩,⟨hb,fun j hj => ?_⟩⟩
    · simpa only [highMask,decide_eq_false (low_not_high low high hp j hj),Bool.false_eq_true,ite_false] using h j
    · simpa only [highMask,decide_eq_true hj,ite_true] using h j

end Blotto.PlayerSpecificSweepIndexed
