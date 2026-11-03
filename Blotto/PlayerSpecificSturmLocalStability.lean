import Blotto.PlayerSpecificSturmPattern

/-! The evaluated Sturm rules imply the zero-entry pattern, and finite
families of continuous polynomial rows then have locally constant variation
counts. No assumption that every row is nonzero at the point is needed. -/
namespace Blotto.PlayerSpecificSturmLocalStability
open SignType PlayerSpecificSturmPattern PlayerSpecificSturmSignEvents Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 3500000

def RulesFrom (a : ℝ) : List ℝ → Prop
  | [] => a≠0
  | b::tail => (a≠0 ∨ b≠0) ∧ RulesFrom b tail ∧
    match tail with
    | [] => True
    | c::_ => b=0 → a = -c

theorem opposite_sign (x : ℝ) (hx : x≠0) : sign (-x)≠sign x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [sign_pos (neg_pos.mpr hneg),sign_neg hneg]
    decide
  · rw [sign_neg (neg_lt_zero.mpr hpos),sign_pos hpos]
    decide

theorem pattern_bound (fuel : ℕ) (a : ℝ) (rest : List ℝ) (hcap : rest.length+1≤fuel)
    (hr : RulesFrom a rest) (ha : a≠0) : Pattern (a::rest) := by
  induction fuel generalizing a rest with
  | zero => omega
  | succ fuel ih =>
    cases rest with
    | nil => rw [Pattern.eq_def]; exact ha
    | cons b tail =>
      rw [Pattern.eq_def]
      refine ⟨ha,?_⟩
      by_cases hb : b=0
      · rw [ite_eq_left hb]
        cases tail with
        | nil => exact False.elim (hr.2.1 hb)
        | cons c rest =>
          have hc : c≠0 := hr.2.1.1.resolve_left (not_not.mpr hb)
          have hrel : a = -c := hr.2.2 hb
          refine ⟨hc,?_,?_⟩
          · rw [hrel]
            exact opposite_sign c hc
          · exact ih c rest (by simp only [List.length_cons] at hcap; omega) hr.2.1.2.1 hc
      · rw [ite_eq_right hb]
        exact ih b tail (by simp only [List.length_cons] at hcap; omega) hr.2.1 hb

theorem pattern (a : ℝ) (rest : List ℝ) (hr : RulesFrom a rest) (ha : a≠0) : Pattern (a::rest) :=
  pattern_bound (rest.length+1) a rest le_rfl hr ha

theorem agree_near (rows : List (Polynomial ℝ)) (a : ℝ) :
    ∀ᶠ x in 𝓝 a,Agree (rows.map (fun p => p.eval a)) (rows.map (fun p => p.eval x)) := by
  induction rows with
  | nil => exact Filter.Eventually.of_forall (fun _ => List.Forall₂.nil)
  | cons p rows ih =>
    by_cases hp : p.eval a=0
    · filter_upwards [ih] with x hx
      exact List.Forall₂.cons (fun hn => False.elim (hn hp)) hx
    · have hs := polynomial_sign_near p a hp
      filter_upwards [hs,ih] with x hsign hx
      exact List.Forall₂.cons (fun _ => hsign) hx

theorem variations_near (rows : List (Polynomial ℝ)) (a : ℝ)
    (hp : Pattern (rows.map (fun p => p.eval a))) :
    ∀ᶠ x in 𝓝 a,(rows.map (fun p => p.eval x)).signVariations=(rows.map (fun p => p.eval a)).signVariations := by
  exact (agree_near rows a).mono (fun x hx => (stable _ _ hp hx).symm)

end Blotto.PlayerSpecificSturmLocalStability
