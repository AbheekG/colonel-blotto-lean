import Blotto.GeneralPaperProxyCellPaths

/-! Exact transfer-facing semantics of every executed selection branch.
Unchanged proxies equal the original budget. Modified proxies have reduced
denominator>H, lie on the proper side of the original budget, and have no
small-denominator rational on the OPEN path to their chosen endpoint.
-/
namespace Blotto.GeneralPaperProxySelectionPaths
open GeneralPaperBucketGeometry GeneralPaperProxyCell GeneralPaperProxyCellPaths
open GeneralPaperProxySelection GeneralPaperProxyBranchSpec
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Safe (H : ℕ) (b : ℝ) (s : Selected) : Prop :=
  Unchanged b s ∨
    H<s.proxy.value.den ∧
    (∀ x : ℚ, x.den≤H → ¬Between s.proxy.value s.endpoint x) ∧
    ((s.modify=some .rich ∧ (s.proxy.value:ℝ)<b ∧ b<(s.endpoint:ℝ)) ∨
      (s.modify=some .poor ∧ (s.endpoint:ℝ)<b ∧ b<(s.proxy.value:ℝ)))

theorem select_safe (H Q j : ℕ) (hH : 0<H) (hQ : 0<Q) (hScale : 4*H*H≤Q)
    (b : ℝ) (hCell : (lower Q j:ℝ)≤b ∧ b<(upper Q j:ℝ)) (root : Option Farey.Fraction)
    (hRoot : ∀ f, root=some f → f.den≤H ∧ Closed Q j f.value)
    (hNone : root=none → ∀ f : Farey.Fraction, f.den≤H → ¬Closed Q j f.value) :
    Safe H b (select Q j hQ b root) := by
  have hEnds := endpoints_closed Q j hQ
  have hMid := midpoint_closed Q j hQ
  rcases select_spec Q j hQ b root with hu|hr|hp|her|hep
  · exact Or.inl hu
  · obtain ⟨f,hf,hbf,hne,hm,hv,ht⟩ := hr
    have hfc := hRoot f hf
    have hDifferent : lower Q j≠f.value := by
      intro he
      have he' := congrArg (fun q : ℚ => (q:ℝ)) he
      linarith only [he',hCell.1,hbf]
    refine Or.inr ⟨?_,?_,Or.inl ⟨hm,?_,?_⟩⟩
    · rw [hv]
      exact large_if_distinct H Q j hH hScale _ hEnds.1 f hfc.1 hfc.2 hDifferent
    · intro x hx
      rw [hv,ht]
      exact path_to_unique_root H Q j hH hScale _ hEnds.1 f hfc.1 hfc.2 x hx
    · rw [hv]
      exact lt_of_le_of_ne hCell.1 (Ne.symm hne)
    · rw [ht]
      exact hbf
  · obtain ⟨f,hf,hfb,hm,hv,ht⟩ := hp
    have hfc := hRoot f hf
    have hDifferent : upper Q j≠f.value := by
      intro he
      have he' := congrArg (fun q : ℚ => (q:ℝ)) he
      linarith only [he',hCell.2,hfb]
    refine Or.inr ⟨?_,?_,Or.inr ⟨hm,?_,?_⟩⟩
    · rw [hv]
      exact large_if_distinct H Q j hH hScale _ hEnds.2 f hfc.1 hfc.2 hDifferent
    · intro x hx
      rw [hv,ht]
      exact path_to_unique_root H Q j hH hScale _ hEnds.2 f hfc.1 hfc.2 x hx
    · rw [ht]
      exact hfb
    · rw [hv]
      exact hCell.2
  · obtain ⟨hn,hmb,hm,hv,ht⟩ := her
    have he := hNone hn
    refine Or.inr ⟨?_,?_,Or.inl ⟨hm,?_,?_⟩⟩
    · rw [hv]
      exact empty_large H Q j he _ hMid
    · intro x hx
      rw [hv,ht]
      exact empty_path H Q j he _ _ hMid hEnds.2 x hx
    · rw [hv]
      exact hmb
    · rw [ht]
      exact hCell.2
  · obtain ⟨hn,hbm,hm,hv,ht⟩ := hep
    have he := hNone hn
    have hDifferent : (lower Q j:ℝ)≠b := by
      intro hb
      have hx : b≠(lower Q j:ℝ) := by
        intro hEq
        have hs : (select Q j hQ b root).modify=none := by simp only [select,ite_eq_left hEq]
        rw [hm] at hs
        cases hs
      exact hx hb.symm
    refine Or.inr ⟨?_,?_,Or.inr ⟨hm,?_,?_⟩⟩
    · rw [hv]
      exact empty_large H Q j he _ hMid
    · intro x hx
      rw [hv,ht]
      exact empty_path H Q j he _ _ hMid hEnds.1 x hx
    · rw [ht]
      exact lt_of_le_of_ne hCell.1 hDifferent
    · rw [hv]
      exact hbm

theorem unchanged_eq (H : ℕ) (b : ℝ) (s : Selected) (hs : Safe H b s) (hm : s.modify=none) :
    (s.proxy.value:ℝ)=b := by
  rcases hs with hu|⟨hd,hp,hr|hb⟩
  · exact hu.2
  · rw [hm] at hr; cases hr.1
  · rw [hm] at hb; cases hb.1

theorem modified_denominator (H : ℕ) (b : ℝ) (s : Selected) (hs : Safe H b s) (hm : s.modify≠none) :
    H<s.proxy.value.den := by
  rcases hs with hu|hs
  · exact (hm hu.1).elim
  · exact hs.1

theorem modified_path (H : ℕ) (b : ℝ) (s : Selected) (hs : Safe H b s) (hm : s.modify≠none)
    (x : ℚ) (hx : x.den≤H) : ¬Between s.proxy.value s.endpoint x := by
  rcases hs with hu|hs
  · exact (hm hu.1).elim
  · exact hs.2.1 x hx

end Blotto.GeneralPaperProxySelectionPaths
