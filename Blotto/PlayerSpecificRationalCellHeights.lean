import Blotto.PlayerSpecificRationalSweepHeights

/-! Polynomial coefficient and cached-bound sizes throughout the actual
cell-construction recursion, using additive fresh-field sweep growth. -/
namespace Blotto.PlayerSpecificRationalCellHeights
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificRationalCells PlayerSpecificPolynomialHeights
open PlayerSpecificRationalSweepHeights
set_option autoImplicit false
set_option maxHeartbeats 2500000

def CellHeight (c : Cell) (H : ℕ) : Prop := StateHeight c.state H ∧ RationalHeight c.lower H ∧
  (∀ q∈c.upper,RationalHeight q H) ∧ RationalHeight c.suffixMax H
def bound (T H N : ℕ) : ℕ := T+(3*H+1)*(N+1)

theorem mono (c : Cell) (H J : ℕ) (hh : CellHeight c H) (hHJ : H≤J) : CellHeight c J :=
  ⟨state_mono c.state H J hh.1 hHJ,hh.2.1.mono hHJ,fun q hq => (hh.2.2.1 q hq).mono hHJ,hh.2.2.2.mono hHJ⟩

theorem build_height (s : State ℚ) (lower : ℚ) (xs : List ((ℚ×ℚ)×ℚ)) (T H : ℕ)
    (hs : StateHeight s T) (hl : RationalHeight lower T)
    (hx : ∀ x∈xs,RationalHeight x.1.1 H ∧ RationalHeight x.1.2 H ∧ RationalHeight x.2 H) :
    ∀ c∈build s lower xs,CellHeight c (bound T H xs.length) := by
  induction xs generalizing s lower T with
  | nil =>
    intro c hc
    have he:=List.mem_singleton.mp hc
    subst c
    have hT : T≤bound T H 0 := by unfold bound; omega
    have hlarge : 1≤bound T H 0 := by unfold bound; omega
    refine ⟨state_mono s T _ hs hT,hl.mono hT,?_,zero_height.mono hlarge⟩
    intro q hq
    cases hq
  | cons x xs ih =>
    have hhead:=hx x List.mem_cons_self
    have htail : ∀ y∈xs,RationalHeight y.1.1 H ∧ RationalHeight y.1.2 H ∧ RationalHeight y.2 H :=
      fun y hy => hx y (List.mem_cons_of_mem x hy)
    have hnext:=move_height s x.1.1 x.1.2 T H hs hhead.1 hhead.2.1
    have hratio:=hhead.1.div hhead.2.1
    have hrec:=ih (move s x.1.1 x.1.2) (x.1.1/x.1.2) (stepBound T H) hnext
      (hratio.mono (by unfold stepBound; omega)) htail
    intro c hc
    rcases List.mem_cons.mp hc with he | ht
    · subst c
      have hT : T≤bound T H (x::xs).length := by unfold bound; omega
      have hH : H≤bound T H (x::xs).length := by unfold bound; simp only [List.length_cons]; nlinarith
      have hr : H+H≤bound T H (x::xs).length := by unfold bound; simp only [List.length_cons]; nlinarith
      refine ⟨state_mono s T _ hs hT,hl.mono hT,?_,hhead.2.2.mono hH⟩
      intro q hq
      have hqeq : q=x.1.1/x.1.2 := Option.some.inj (Option.mem_def.mp hq).symm
      rw [hqeq]
      exact hratio.mono hr
    · have hh:=hrec c ht
      have heq : bound (stepBound T H) H xs.length=bound T H (x::xs).length := by
        unfold bound stepBound
        simp only [List.length_cons]
        ring
      rwa [heq] at hh

end Blotto.PlayerSpecificRationalCellHeights
