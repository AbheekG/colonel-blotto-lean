import Blotto.PlayerSpecificSturmSignEvents

/-! Variation counts are unchanged by arbitrary perturbations of isolated
zero entries whose neighbours have opposite signs, while the nonzero
entries keep their signs. This handles simultaneous internal row zeroes. -/
namespace Blotto.PlayerSpecificSturmPattern
open SignType PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 3500000

variable {α : Type*} [Zero α] [LinearOrder α]

def Pattern : List α → Prop
  | [] => True
  | [a] => a≠0
  | a::b::tail => a≠0 ∧ if b=0 then
      match tail with
      | [] => False
      | c::rest => c≠0 ∧ sign a≠sign c ∧ Pattern (c::rest)
    else Pattern (b::tail)
termination_by xs => xs.length
decreasing_by all_goals simp_wf

def Agree (base changed : List α) : Prop := List.Forall₂ (fun a b => a≠0 → sign b=sign a) base changed

theorem agree_nonzero (a b : α) (ha : a≠0) (h : a≠0 → sign b=sign a) : b≠0 := by
  intro hb
  have hs := h ha
  rw [hb,sign_zero] at hs
  exact ha (sign_eq_zero_iff.mp hs.symm)

theorem stable_bound (fuel : ℕ) (base changed : List α) (hcap : base.length≤fuel)
    (hp : Pattern base) (ha : Agree base changed) : base.signVariations=changed.signVariations := by
  induction fuel generalizing base changed with
  | zero =>
    have hz : base=[] := List.length_eq_zero_iff.mp (by omega)
    subst base
    have hc : changed=[] := List.forall₂_nil_left_iff.mp ha
    subst changed
    rfl
  | succ fuel ih =>
    cases base with
    | nil =>
      have hc : changed=[] := List.forall₂_nil_left_iff.mp ha
      subst changed
      rfl
    | cons a rest =>
      rcases List.forall₂_cons_left_iff.mp ha with ⟨a',rest',haa,hrest,rfl⟩
      cases rest with
      | nil =>
        have hc : rest'=[] := List.forall₂_nil_left_iff.mp hrest
        subst rest'
        simp only [List.signVariations_singleton]
      | cons b tail =>
        rcases List.forall₂_cons_left_iff.mp hrest with ⟨b',tail',hbb,htail,rfl⟩
        rw [Pattern.eq_def] at hp
        have ha' := agree_nonzero a a' hp.1 haa
        by_cases hb : b=0
        · simp only [hb,ite_true] at hp
          cases tail with
          | nil => exact False.elim hp.2
          | cons c rest =>
            rcases List.forall₂_cons_left_iff.mp htail with ⟨c',restC',hcc,hrestC,rfl⟩
            have hc' := agree_nonzero c c' hp.2.1 hcc
            have hac' : sign a'≠sign c' := by rw [haa hp.1,hcc hp.2.1]; exact hp.2.2.1
            have hvar := ih (c::rest) (c'::restC') (by simp only [List.length_cons] at hcap ⊢; omega)
              hp.2.2.2 (List.Forall₂.cons hcc hrestC)
            rw [opposite_middle a b c rest hp.1 hp.2.1 hp.2.2.1,
              opposite_middle a' b' c' restC' ha' hc' hac',hvar]
        · have hpat : Pattern (b::tail) := by simpa only [hb,ite_false] using hp.2
          have hb' := agree_nonzero b b' hb hbb
          have hvar := ih (b::tail) (b'::tail') (by simp only [List.length_cons] at hcap ⊢; omega)
            hpat (List.Forall₂.cons hbb htail)
          rw [List.signVariations_cons_cons_of_ne_zero tail hp.1 hb,
            List.signVariations_cons_cons_of_ne_zero tail' ha' hb',hvar,haa hp.1,hbb hb]

theorem stable (base changed : List α) (hp : Pattern base) (ha : Agree base changed) :
    base.signVariations=changed.signVariations := stable_bound base.length base changed le_rfl hp ha

end Blotto.PlayerSpecificSturmPattern
