import Blotto.GeneralPaperProxyWidths

/-! Exact branch semantics of the executed seven-way proxy selection.
The three unchanged cases share one consequence; each modification records
its actual proxy, side and endpoint. This proof observer adds no execution.
-/
namespace Blotto.GeneralPaperProxyBranchSpec
open GeneralPaperBucketGeometry GeneralPaperProxySelection
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Unchanged (b : ℝ) (s : Selected) : Prop := s.modify=none ∧ (s.proxy.value:ℝ)=b

def RootRich (Q j : ℕ) (b : ℝ) (root : Option Farey.Fraction) (s : Selected) : Prop :=
  ∃ f, root=some f ∧ b<(f.value:ℝ) ∧ b≠(lower Q j:ℝ) ∧
    s.modify=some .rich ∧ s.proxy.value=lower Q j ∧ s.endpoint=f.value

def RootPoor (Q j : ℕ) (b : ℝ) (root : Option Farey.Fraction) (s : Selected) : Prop :=
  ∃ f, root=some f ∧ (f.value:ℝ)<b ∧
    s.modify=some .poor ∧ s.proxy.value=upper Q j ∧ s.endpoint=f.value

def EmptyRich (Q j : ℕ) (b : ℝ) (root : Option Farey.Fraction) (s : Selected) : Prop :=
  root=none ∧ (GeneralPaperBucketGeometry.midpoint Q j:ℝ)<b ∧
    s.modify=some .rich ∧ s.proxy.value=GeneralPaperBucketGeometry.midpoint Q j ∧ s.endpoint=upper Q j

def EmptyPoor (Q j : ℕ) (b : ℝ) (root : Option Farey.Fraction) (s : Selected) : Prop :=
  root=none ∧ b<(GeneralPaperBucketGeometry.midpoint Q j:ℝ) ∧
    s.modify=some .poor ∧ s.proxy.value=GeneralPaperBucketGeometry.midpoint Q j ∧ s.endpoint=lower Q j

theorem select_spec (Q j : ℕ) (hQ : 0<Q) (b : ℝ) (root : Option Farey.Fraction) :
    let s := select Q j hQ b root
    Unchanged b s ∨ RootRich Q j b root s ∨ RootPoor Q j b root s ∨ EmptyRich Q j b root s ∨ EmptyPoor Q j b root s := by
  dsimp only
  by_cases hl : b=(lower Q j:ℝ)
  · left
    exact ⟨by simp only [select,ite_eq_left hl],by simpa only [select,ite_eq_left hl,lower_value Q j hQ] using hl.symm⟩
  · cases hs : root with
    | some f =>
      by_cases he : b=(f.value:ℝ)
      · left
        exact ⟨by simp only [select,ite_eq_right hl,ite_eq_left he],by simpa only [select,ite_eq_right hl,ite_eq_left he] using he.symm⟩
      · by_cases ht : b<(f.value:ℝ)
        · exact Or.inr (Or.inl ⟨f,rfl,ht,hl,by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_left ht],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_left ht,lower_value Q j hQ],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_left ht]⟩)
        · have hfb : (f.value:ℝ)<b := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he)
          exact Or.inr (Or.inr (Or.inl ⟨f,rfl,hfb,
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_right ht],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_right ht,upper_value Q j hQ],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_right ht]⟩))
    | none =>
      by_cases he : b=(GeneralPaperBucketGeometry.midpoint Q j:ℝ)
      · left
        exact ⟨by simp only [select,ite_eq_right hl,ite_eq_left he],by simpa only [select,ite_eq_right hl,ite_eq_left he,midpoint_value Q j hQ] using he.symm⟩
      · by_cases ht : (GeneralPaperBucketGeometry.midpoint Q j:ℝ)<b
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,ht,
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_left ht],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_left ht,midpoint_value Q j hQ],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_left ht]⟩)))
        · have hbm : b<(GeneralPaperBucketGeometry.midpoint Q j:ℝ) := lt_of_le_of_ne (le_of_not_gt ht) he
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,hbm,
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_right ht],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_right ht,midpoint_value Q j hQ],
            by simp only [select,ite_eq_right hl,ite_eq_right he,ite_eq_right ht]⟩)))

end Blotto.GeneralPaperProxyBranchSpec
