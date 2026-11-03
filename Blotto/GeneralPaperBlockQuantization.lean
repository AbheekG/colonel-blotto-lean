import Blotto.GeneralPaperQuantileBlocks

/-! The paper's previous-block anchor rule. Every positive-label anchor is
the last occurrence of the preceding block; label zero is exactly zero.
One-block event bounds are proved by an injection, for both CDF conventions.
-/
namespace Blotto.GeneralPaperBlockQuantization
open GeneralPaperQuantileBlocks
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

def predecessor {K B : ℕ} (hB : 0<B) (l : Fin K) : Fin (K*B) :=
  ⟨l.val*B-1,by
    have hs := (position hB l ⟨0,hB⟩).isLt
    change l.val*B+0<K*B at hs
    omega⟩

def anchor {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ) (l : Fin K) : ℚ :=
  if l.val=0 then 0 else x (predecessor hB l)

def rounded {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ) (r : Fin (K*B)) : ℚ :=
  anchor hB x (block hB r)

theorem anchor_zero {K B : ℕ} (hB : 0<B) (hK : 0<K) (x : Fin (K*B) → ℚ) :
    anchor hB x ⟨0,hK⟩=0 := by simp only [anchor,ite_true]

theorem anchor_nonnegative {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ)
    (hNonnegative : ∀ r,0≤x r) (l : Fin K) : 0≤anchor hB x l := by
  unfold anchor
  split
  · exact le_rfl
  · exact hNonnegative _

theorem anchor_mono {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ)
    (hOrder : Monotone x) (hNonnegative : ∀ r,0≤x r) : Monotone (anchor hB x) := by
  intro a b hab
  by_cases ha : a.val=0
  · simp only [anchor,ite_eq_left ha]
    exact anchor_nonnegative hB x hNonnegative b
  · have hb : b.val≠0 := by have hv := hab; change a.val≤b.val at hv; omega
    simp only [anchor,ite_eq_right ha,ite_eq_right hb]
    apply hOrder
    change a.val*B-1 ≤ b.val*B-1
    have h := Nat.mul_le_mul_right B hab
    have hm : a.val*B ≤ b.val*B := by nlinarith only [h]
    omega

theorem predecessor_le_rank {K B : ℕ} (hB : 0<B) (r : Fin (K*B)) :
    predecessor hB (block hB r) ≤ r := by
  have h : r.val/B*B ≤ r.val := Nat.div_mul_le_self _ _
  change r.val/B*B-1 ≤ r.val
  omega

theorem rounded_le {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ)
    (hOrder : Monotone x) (hNonnegative : ∀ r,0≤x r) (r : Fin (K*B)) : rounded hB x r≤x r := by
  unfold rounded anchor
  split
  · exact hNonnegative r
  · exact hOrder (predecessor_le_rank hB r)

def shift {K B : ℕ} (hB : 0<B) (r : Fin (K*B)) : Fin (K*B) ⊕ Fin B :=
  if h : r.val<B then .inr ⟨r.val,h⟩ else .inl ⟨r.val-B,by omega⟩

theorem shift_injective {K B : ℕ} (hB : 0<B) : Function.Injective (shift (K:=K) hB) := by
  intro a b h
  by_cases ha : a.val<B <;> by_cases hb : b.val<B
  · simp only [shift,dite_eq_left ha,dite_eq_left hb,Sum.inr.injEq] at h
    exact Fin.ext (congrArg (fun r : Fin B => r.val) h)
  · simp only [shift,dite_eq_left ha,dite_eq_right hb,Sum.inr_ne_inl] at h
  · simp only [shift,dite_eq_right ha,dite_eq_left hb,Sum.inl_ne_inr] at h
  · simp only [shift,dite_eq_right ha,dite_eq_right hb,Sum.inl.injEq] at h
    apply Fin.ext
    have he := congrArg Fin.val h
    change a.val-B=b.val-B at he
    omega

theorem shifted_value_le {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ) (hOrder : Monotone x)
    (r : Fin (K*B)) (hLarge : ¬r.val<B) :
    x ⟨r.val-B,by omega⟩ ≤ rounded hB x r := by
  have hMod := Nat.mod_add_div r.val B
  have hRemainder := Nat.mod_lt r.val hB
  have hEq : r.val=r.val/B*B+r.val%B := by nlinarith only [hMod]
  have hBlock : (block hB r).val≠0 := by
    change r.val/B≠0
    intro hz
    rw [hz,Nat.zero_mul,Nat.zero_add] at hEq
    omega
  simp only [rounded,anchor,ite_eq_right hBlock]
  apply hOrder
  change r.val-B ≤ r.val/B*B-1
  omega

theorem event_count_upper {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ) (hOrder : Monotone x)
    (P : ℚ → Prop) [DecidablePred P] (hDown : ∀ a b,a≤b → P b → P a) :
    (Finset.univ.filter (fun r => P (rounded hB x r))).card ≤
      (Finset.univ.filter (fun r => P (x r))).card+B := by
  let source := Finset.univ.filter (fun r : Fin (K*B) => P (rounded hB x r))
  let target := (Finset.univ.filter (fun r : Fin (K*B) => P (x r))).disjSum (Finset.univ : Finset (Fin B))
  have hMap : Set.MapsTo (shift (K:=K) hB) (source : Set (Fin (K*B)))
      (target : Set (Fin (K*B) ⊕ Fin B)) := by
    intro r hr
    have hp := (Finset.mem_filter.mp hr).2
    change shift hB r ∈ (Finset.univ.filter (fun r : Fin (K*B) => P (x r))).disjSum
      (Finset.univ : Finset (Fin B))
    by_cases hs : r.val<B
    · simp only [shift,dite_eq_left hs,Finset.inr_mem_disjSum,Finset.mem_univ]
    · simp only [shift,dite_eq_right hs,Finset.inl_mem_disjSum,Finset.mem_filter,Finset.mem_univ,true_and]
      exact hDown _ _ (shifted_value_le hB x hOrder r hs) hp
  have hCard := Finset.card_le_card_of_injOn (shift hB) hMap (shift_injective hB).injOn
  simpa only [source,target,Finset.card_disjSum,Finset.card_fin] using hCard

theorem event_count_lower {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ) (hOrder : Monotone x)
    (hNonnegative : ∀ r,0≤x r) (P : ℚ → Prop) [DecidablePred P]
    (hDown : ∀ a b,a≤b → P b → P a) :
    (Finset.univ.filter (fun r => P (x r))).card ≤
      (Finset.univ.filter (fun r => P (rounded hB x r))).card := by
  apply Finset.card_le_card
  intro r hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hDown _ _ (rounded_le hB x hOrder hNonnegative r) (Finset.mem_filter.mp hr).2⟩

end Blotto.GeneralPaperBlockQuantization
