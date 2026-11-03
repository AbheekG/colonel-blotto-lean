import Blotto.PlayerSpecificAlgebraicResourceLoop

/-! Ghost families of disjoint, nonrepeating leaves. A reached pair can
merge its leaves into at most one surviving active owner. -/
namespace Blotto.PlayerSpecificLineageFamily
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Valid {N : ℕ} {α : Type} (active : List (Fin N)) (rows : Fin N → List α) : Prop where
  nodup : ∀ i∈active,(rows i).Nodup
  separate : ∀ i∈active,∀ j∈active,i≠j → ∀ a∈rows i,a∉rows j

def merge {N : ℕ} {α : Type} (rows : Fin N → List α) (i j : Fin N) (fresh : List α) : Fin N → List α :=
  fun k => if k=i ∨ k=j then rows i++rows j++fresh else rows k

theorem merge_valid {N : ℕ} {α : Type} (old next : List (Fin N)) (rows : Fin N → List α)
    (i j : Fin N) (fresh : List α) (h : Valid old rows)
    (hi : i∈old) (hj : j∈old) (hij : i≠j) (hsub : ∀ k∈next,k∈old)
    (hone : ∀ k∈next,∀ l∈next,(k=i ∨ k=j) → (l=i ∨ l=j) → k=l)
    (hf : fresh.Nodup) (hnew : ∀ k∈old,∀ a∈fresh,a∉rows k) :
    Valid next (merge rows i j fresh) := by
  have hmerged : (rows i++rows j++fresh).Nodup := by
    apply List.Nodup.append
    · exact (h.nodup i hi).append (h.nodup j hj) (List.disjoint_left.mpr (h.separate i hi j hj hij))
    · exact hf
    · apply List.disjoint_left.mpr
      intro a ha haf
      rcases List.mem_append.mp ha with hai|haj
      · exact hnew i hi a haf hai
      · exact hnew j hj a haf haj
  have hsep : ∀ k∈old,k≠i → k≠j → ∀ a∈rows i++rows j++fresh,a∉rows k := by
    intro k hk hki hkj a ha hak
    simp only [List.mem_append] at ha
    rcases ha with (hai|haj)|haf
    · exact h.separate i hi k hk (Ne.symm hki) a hai hak
    · exact h.separate j hj k hk (Ne.symm hkj) a haj hak
    · exact hnew k hk a haf hak
  constructor
  · intro k hk
    unfold merge
    split
    · exact hmerged
    · exact h.nodup k (hsub k hk)
  · intro k hk l hl hkl a ha hal
    by_cases hks : k=i ∨ k=j
    · have hls : ¬(l=i ∨ l=j) := fun hls => hkl (hone k hk l hl hks hls)
      simp only [merge,ite_eq_left hks,ite_eq_right hls] at ha hal
      exact hsep l (hsub l hl) (fun e => hls (Or.inl e)) (fun e => hls (Or.inr e)) a ha hal
    · by_cases hls : l=i ∨ l=j
      · simp only [merge,ite_eq_right hks,ite_eq_left hls] at ha hal
        exact hsep k (hsub k hk) (fun e => hks (Or.inl e)) (fun e => hks (Or.inr e)) a hal ha
      · simp only [merge,ite_eq_right hks,ite_eq_right hls] at ha hal
        exact h.separate k (hsub k hk) l (hsub l hl) hkl a ha hal

theorem singleton_valid (N : ℕ) (active : List (Fin N)) : Valid active (fun i => [i]) := by
  constructor
  · intro i _; simp
  · intro i _ j _ hij a ha haj
    simp only [List.mem_singleton] at ha haj
    exact hij (ha.symm.trans haj)

theorem empty_valid (N : ℕ) (active : List (Fin N)) : Valid active (fun _ => ([] : List (Fin N))) := by
  constructor
  · intro i _; exact List.nodup_nil
  · intro i _ j _ _ a ha; exact False.elim (List.not_mem_nil ha)

end Blotto.PlayerSpecificLineageFamily
