import Blotto.GeneralPaperCircleActualWeights

/-! Finite uniform-cell CDF count for the reconstruction index. A successful
arc either starts in a successful prefix of bins or wraps across zero. Its
count is at most f*W+L. This is common to strict and weak bid thresholds once
the sorted row's successful prefix rank is identified. -/
namespace Blotto.GeneralPaperCircleCDFCount
open GeneralPaperCircleCell
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem prefix_card (D A : ℕ) : (Finset.univ.filter (fun c:Fin D => c.val<A)).card≤A := by
  let s := Finset.univ.filter (fun c:Fin D => c.val<A)
  let f : s → Fin A := fun c => ⟨c.val.val,(Finset.mem_filter.mp c.property).2⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun i:Fin A => i.val) h
  have h := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,Fintype.card_fin] using h

theorem wrap_card (D L : ℕ) : (Finset.univ.filter (fun c:Fin D => D≤c.val+L)).card≤L := by
  let s := Finset.univ.filter (fun c:Fin D => D≤c.val+L)
  let f : s → Fin L := fun c => ⟨D-1-c.val.val,by
    have hc := c.val.isLt
    have hw := (Finset.mem_filter.mp c.property).2
    omega⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    have hh := congrArg Fin.val h
    change D-1-a.val.val=D-1-b.val.val at hh
    have ha := a.val.isLt
    have hb := b.val.isLt
    omega
  have h := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,Fintype.card_fin] using h

noncomputable def event (R W : ℕ) (hR : 0<R) (hW : 0<W) (L f : ℕ) : Finset (Fin (R*W)) :=
  Finset.univ.filter (fun c => (choice R W hR hW c L).val<f)

theorem event_subset (R W : ℕ) (hR : 0<R) (hW : 0<W) (L f : ℕ) :
    event R W hR hW L f⊆(Finset.univ.filter (fun c:Fin (R*W) => c.val<f*W))∪
      (Finset.univ.filter (fun c:Fin (R*W) => R*W≤c.val+L)) := by
  intro c hc
  have hh := (Finset.mem_filter.mp hc).2
  by_cases hw : R*W≤c.val+L
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩))
  · rw [choice_nonwrapping R W hR hW c L (Nat.lt_of_not_ge hw)] at hh
    have hp : c.val<f*W := (Nat.div_lt_iff_lt_mul hW).mp hh
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩))

theorem event_card (R W : ℕ) (hR : 0<R) (hW : 0<W) (L f : ℕ) :
    (event R W hR hW L f).card≤f*W+L :=
  (Finset.card_le_card (event_subset R W hR hW L f)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (prefix_card (R*W) (f*W)) (wrap_card (R*W) L)))

theorem event_zero (R W : ℕ) (hR : 0<R) (hW : 0<W) (L : ℕ) : event R W hR hW L 0=∅ := by
  simp only [event,Nat.not_lt_zero,Finset.filter_false]

theorem event_full (R W : ℕ) (hR : 0<R) (hW : 0<W) (L f : ℕ) (hf : R≤f) :
    event R W hR hW L f=Finset.univ := by
  apply Finset.filter_true_of_mem
  intro c _
  exact (choice R W hR hW c L).isLt.trans_le hf

theorem probability_bound (R W : ℕ) (hR : 0<R) (hW : 0<W) (w f : ℕ) :
    ((event R W hR hW (R*w) f).card:ℝ)/(R*W:ℕ)≤(f:ℝ)/R+(w:ℝ)/W := by
  have hc : ((event R W hR hW (R*w) f).card:ℝ)≤(f*W+R*w:ℕ) := by
    exact_mod_cast event_card R W hR hW (R*w) f
  have hR' : (0:ℝ)<R := by exact_mod_cast hR
  have hW' : (0:ℝ)<W := by exact_mod_cast hW
  apply (div_le_iff₀ (by exact_mod_cast Nat.mul_pos hR hW : (0:ℝ)<(R*W:ℕ))).mpr
  push_cast at hc ⊢
  field_simp
  nlinarith only [hc]

end Blotto.GeneralPaperCircleCDFCount
