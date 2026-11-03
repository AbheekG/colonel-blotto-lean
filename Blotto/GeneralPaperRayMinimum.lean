import Blotto.GeneralPaperRayAffine

/-! Streaming static-ray minimum. The accumulator keeps one original
constraint and its exact positive-slope crossing. The earlier constraint
wins ties. Only the supplied STATIC row list is traversed; high-score
tuples will be handled by the separate exact-score feasibility search.
-/
namespace Blotto.GeneralPaperRayMinimum
open GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Choice (i : Type*) where
  blocker : i
  time : ℚ

def pick {i : Type*} : Option (Choice i) → Option (Choice i) → Option (Choice i)
  | none,b => b
  | a,none => a
  | some a,some b => if a.time≤b.time then some a else some b

def candidate {i : Type*} (j : i) (a : Affine) : Option (Choice i) :=
  if 0<a.slope then some ⟨j,a.crossing⟩ else none

def Best {i : Type*} (P : Choice i → Prop) : Option (Choice i) → Prop
  | none => ∀ c,¬P c
  | some c => P c ∧ ∀ other,P other → c.time≤other.time

theorem pick_best {i : Type*} (P Q : Choice i → Prop) (a b : Option (Choice i))
    (ha : Best P a) (hb : Best Q b) : Best (fun c => P c ∨ Q c) (pick a b) := by
  cases a with
  | none =>
    cases b with
    | none => exact fun c hc => hc.elim (ha c) (hb c)
    | some b => exact ⟨Or.inr hb.1,fun c hc => hc.elim (fun h => (ha c h).elim) (hb.2 c)⟩
  | some a =>
    cases b with
    | none => exact ⟨Or.inl ha.1,fun c hc => hc.elim (ha.2 c) (fun h => (hb c h).elim)⟩
    | some b =>
      change Best _ (if a.time≤b.time then some a else some b)
      split
      · rename_i h
        exact ⟨Or.inl ha.1,fun c hc => hc.elim (ha.2 c) (fun hc => h.trans (hb.2 c hc))⟩
      · rename_i h
        exact ⟨Or.inr hb.1,fun c hc => hc.elim (fun hc => (le_of_not_ge h).trans (ha.2 c hc)) (hb.2 c)⟩

def Possible {i : Type*} (j : i) (a : Affine) (c : Choice i) : Prop :=
  c.blocker=j ∧ c.time=a.crossing ∧ 0<a.slope

theorem candidate_best {i : Type*} (j : i) (a : Affine) : Best (Possible j a) (candidate j a) := by
  unfold candidate
  split
  · rename_i hp
    refine ⟨⟨rfl,rfl,hp⟩,?_⟩
    intro c hc
    rw [hc.2.1]
  · rename_i hp
    exact fun c hc => hp hc.2.2

structure Result (i : Type*) where
  choice : Option (Choice i)
  work : ℕ

def loop {i : Type*} (evaluate : i → Affine × ℕ) : List i → Option (Choice i) → ℕ → Result i
  | [],current,spent => ⟨current,spent+2⟩
  | j::rest,current,spent =>
      let a := evaluate j
      loop evaluate rest (pick current (candidate j a.1)) (spent+a.2+32)

def scan {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i) : Result i := loop evaluate rows none 0

theorem loop_best {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i) (P : Choice i → Prop)
    (current : Option (Choice i)) (spent : ℕ) (hc : Best P current) :
    Best (fun c => P c ∨ ∃ j∈rows,Possible j (evaluate j).1 c) (loop evaluate rows current spent).choice := by
  induction rows generalizing P current spent with
  | nil => simpa only [loop,List.not_mem_nil,exists_false,false_and,or_false] using hc
  | cons j rest ih =>
    have hp := pick_best P (Possible j (evaluate j).1) current _ hc (candidate_best j _)
    have hh := ih (fun c => P c ∨ Possible j (evaluate j).1 c) _ (spent+(evaluate j).2+32) hp
    have he : (fun c => (P c ∨ Possible j (evaluate j).1 c) ∨ ∃ k∈rest,Possible k (evaluate k).1 c)=
        (fun c => P c ∨ ∃ k∈j::rest,Possible k (evaluate k).1 c) := by
      funext c
      apply propext
      simp only [List.mem_cons,exists_eq_or_imp,or_assoc]
    rw [he] at hh
    exact hh

theorem scan_best {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i) :
    Best (fun c => ∃ j∈rows,Possible j (evaluate j).1 c) (scan evaluate rows).choice := by
  have hh := loop_best evaluate rows (fun _ => False) none 0 (fun c hc => hc)
  simpa only [scan,false_or] using hh

theorem loop_work {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i) (current : Option (Choice i)) (spent : ℕ) :
    (loop evaluate rows current spent).work=spent+(rows.map (fun j => (evaluate j).2+32)).sum+2 := by
  induction rows generalizing current spent with
  | nil => rfl
  | cons j rest ih =>
    simp only [loop,ih,List.map_cons,List.sum_cons]
    omega

theorem scan_work {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i) :
    (scan evaluate rows).work=(rows.map (fun j => (evaluate j).2+32)).sum+2 := by
  simpa only [scan,Nat.zero_add] using loop_work evaluate rows none 0

end Blotto.GeneralPaperRayMinimum
