import Blotto.GeneralPaperRayActualRefinement

/-! A minimum selector retains an affine expression and shared predecessor
labels, selecting by one interior evaluation. The earlier candidate wins
ties. Absence and candidate provenance are retained in the executed data.
-/
namespace Blotto.GeneralPaperRayAffineMinimum
open GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Choice (K : ℕ) where
  expression : Affine
  labels : List (Fin K)

def Choice.atPoint {K : ℕ} (c : Choice K) (t : ℚ) : GeneralPaperMinimum.Selection K :=
  ⟨c.expression.value t,c.labels⟩

def pick {K : ℕ} (t : ℚ) : Option (Choice K) → Option (Choice K) → Option (Choice K)
  | none,b => b
  | a,none => a
  | some a,some b => if a.expression.value t≤b.expression.value t then some a else some b

def scan {i : Type*} {K : ℕ} (t : ℚ) (options : i → Option (Choice K)) : List i → Option (Choice K)
  | [] => none
  | a::rest => pick t (options a) (scan t options rest)

theorem pick_data {K : ℕ} (t : ℚ) (a b : Option (Choice K)) :
    (pick t a b).map (fun c => c.atPoint t)=
      GeneralPaperMinimum.pick (a.map (fun c => c.atPoint t)) (b.map (fun c => c.atPoint t)) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      change (if a.expression.value t≤b.expression.value t then some a else some b).map _=
        (if a.expression.value t≤b.expression.value t then some (a.atPoint t) else some (b.atPoint t))
      split <;> rfl

theorem scan_data {i : Type*} {K : ℕ} (t : ℚ) (options : i → Option (Choice K)) (xs : List i) :
    (scan t options xs).map (fun c => c.atPoint t)=GeneralPaperMinimum.scan (fun i => (options i).map (fun c => c.atPoint t)) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => rw [scan,pick_data,ih]; rfl

theorem pick_origin {K : ℕ} (t : ℚ) (a b : Option (Choice K)) (chosen : Choice K)
    (hc : pick t a b=some chosen) : a=some chosen ∨ b=some chosen := by
  cases a with
  | none => exact Or.inr hc
  | some a =>
    cases b with
    | none => exact Or.inl hc
    | some b =>
      change (if a.expression.value t≤b.expression.value t then some a else some b)=some chosen at hc
      split at hc
      · exact Or.inl hc
      · exact Or.inr hc

theorem scan_origin {i : Type*} {K : ℕ} (t : ℚ) (options : i → Option (Choice K)) (xs : List i)
    (chosen : Choice K) (hc : scan t options xs=some chosen) : ∃ j∈xs,options j=some chosen := by
  induction xs with
  | nil => contradiction
  | cons a rest ih =>
    rcases pick_origin t (options a) (scan t options rest) chosen hc with h|h
    · exact ⟨a,List.mem_cons_self,h⟩
    · obtain ⟨j,hj,he⟩ := ih h
      exact ⟨j,List.mem_cons_of_mem _ hj,he⟩

theorem option_best {i : Type*} {K : ℕ} (t : ℚ) (options : i → Option (Choice K)) (j : i) :
    GeneralPaperMinimum.Best (fun selected => ∃ c,options j=some c ∧ c.atPoint t=selected)
      ((options j).map (fun c => c.atPoint t)) := by
  cases he : options j with
  | none =>
    intro selected hs
    obtain ⟨c,hc,_⟩ := hs
    contradiction
  | some c =>
    refine ⟨⟨c,rfl,rfl⟩,?_⟩
    intro other hOther
    obtain ⟨d,hd,rfl⟩ := hOther
    have hh : c=d := Option.some.inj hd
    subst d
    exact le_rfl

theorem scan_minimum {i : Type*} {K : ℕ} (t : ℚ) (options : i → Option (Choice K)) (xs : List i)
    (chosen : Choice K) (hc : scan t options xs=some chosen) (j : i) (hj : j∈xs)
    (other : Choice K) (hOther : options j=some other) : chosen.expression.value t≤other.expression.value t := by
  have hb := GeneralPaperMinimum.scan_best (fun i => (options i).map (fun c => c.atPoint t))
    (fun i selected => ∃ c,options i=some c ∧ c.atPoint t=selected) xs (fun i _ => option_best t options i)
  rw [←scan_data,hc] at hb
  exact hb.2 (other.atPoint t) ⟨j,hj,other,hOther,rfl⟩

end Blotto.GeneralPaperRayAffineMinimum
