import Blotto.PlayerSpecificLineageFamily

/-! A reached branch has one frozen selected coordinate. Its other
coordinate is the old sum, optionally minus that frozen endpoint. The
endpoint test is coordinate-specific, including coincident lengths. -/
namespace Blotto.PlayerSpecificAlgebraicResourceShape
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def combined {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (i j : Fin N) (extra : Option (Fin N)) : Data :=
  let total:=PlayerSpecificAlgebraicField.plus p.parameters.root.polynomial (s.data.read i) (s.data.read j)
  match extra with
  | none => total
  | some k => PlayerSpecificAlgebraicField.minus p.parameters.root.polynomial total (p.rows.read k).length

theorem read_first {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (upper : Bool) (hij : f.first≠f.second) :
    (advance model p s f upper).data.read f.first=(if upper then f.pair.upperA else f.pair.lowerA) := by
  simp only [advance,update,FixedArrayTable.read_write,ite_eq_right hij,ite_true]

theorem read_second {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (upper : Bool) :
    (advance model p s f upper).data.read f.second=(if upper then f.pair.upperB else f.pair.lowerB) := by
  simp only [advance,update,FixedArrayTable.read_write,ite_true]

theorem read_other {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (upper : Bool) (k : Fin N) (hki : k≠f.first) (hkj : k≠f.second) :
    (advance model p s f upper).data.read k=s.data.read k := by
  simp only [advance,update,FixedArrayTable.read_write,ite_eq_right hkj,ite_eq_right hki]

theorem branch_shape {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool) (hij : f.first≠f.second) :
    ∃ (dropped : Fin N) (extra : Option (Fin N)),
      (dropped=f.first ∨ dropped=f.second) ∧ (extra=none ∨ extra=some dropped) ∧
      ((advance model p s f upper).data.read dropped=[] ∨
        (advance model p s f upper).data.read dropped=(p.rows.read dropped).length) ∧
      (∀ k,(k=f.first ∨ k=f.second) → k≠dropped →
        (advance model p s f upper).data.read k=combined p s f.first f.second extra) := by
  have hp:=(fields model p s f hf).2
  have ha:=read_first model p s f upper hij
  have hb:=read_second model p s f upper
  rw [hp] at ha hb
  cases upper
  · by_cases hlow : PlayerSpecificAlgebraicPairStep.le model p.parameters.root
        (PlayerSpecificAlgebraicField.plus p.parameters.root.polynomial (s.data.read f.first) (s.data.read f.second))
        (p.rows.read f.second).length=true
    · simp only [Bool.false_eq_true,ite_false,PlayerSpecificAlgebraicPairStep.run,hlow,ite_true] at ha hb
      refine ⟨f.first,none,Or.inl rfl,Or.inl rfl,Or.inl ha,?_⟩
      intro k hk hkd
      rcases hk with rfl|rfl
      · exact False.elim (hkd rfl)
      · exact hb
    · have hfalse : PlayerSpecificAlgebraicPairStep.le model p.parameters.root
          (PlayerSpecificAlgebraicField.plus p.parameters.root.polynomial (s.data.read f.first) (s.data.read f.second))
          (p.rows.read f.second).length=false := Bool.eq_false_iff.mpr hlow
      simp only [Bool.false_eq_true,ite_false,PlayerSpecificAlgebraicPairStep.run,hfalse] at ha hb
      refine ⟨f.second,some f.second,Or.inr rfl,Or.inr rfl,Or.inr hb,?_⟩
      intro k hk hkd
      rcases hk with rfl|rfl
      · exact ha
      · exact False.elim (hkd rfl)
  · by_cases hlow : PlayerSpecificAlgebraicPairStep.le model p.parameters.root
        (PlayerSpecificAlgebraicField.plus p.parameters.root.polynomial (s.data.read f.first) (s.data.read f.second))
        (p.rows.read f.first).length=true
    · simp only [ite_true,PlayerSpecificAlgebraicPairStep.run,hlow] at ha hb
      refine ⟨f.second,none,Or.inr rfl,Or.inl rfl,Or.inl hb,?_⟩
      intro k hk hkd
      rcases hk with rfl|rfl
      · exact ha
      · exact False.elim (hkd rfl)
    · have hfalse : PlayerSpecificAlgebraicPairStep.le model p.parameters.root
          (PlayerSpecificAlgebraicField.plus p.parameters.root.polynomial (s.data.read f.first) (s.data.read f.second))
          (p.rows.read f.first).length=false := Bool.eq_false_iff.mpr hlow
      simp only [ite_true,PlayerSpecificAlgebraicPairStep.run,hfalse,Bool.false_eq_true,ite_false] at ha hb
      refine ⟨f.first,some f.first,Or.inl rfl,Or.inr rfl,Or.inr ha,?_⟩
      intro k hk hkd
      rcases hk with rfl|rfl
      · exact False.elim (hkd rfl)
      · exact hb

theorem frozen_inactive {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ)
    (s : State N) (hs : Valid p x s) (k : Fin N)
    (hk : s.data.read k=[] ∨ s.data.read k=(p.rows.read k).length) : k∉s.active := by
  intro h
  have hfrac:= (hs.membership k).mp h
  change 0<realEvaluate (s.data.read k) x ∧ realEvaluate (s.data.read k) x<realEvaluate (p.rows.read k).length x at hfrac
  rcases hk with hz|he
  · rw [hz] at hfrac
    exact (lt_irrefl (0 : ℝ)) (by simpa only [realEvaluate,List.foldr] using hfrac.1)
  · rw [he] at hfrac
    exact (lt_irrefl _) hfrac.2

end Blotto.PlayerSpecificAlgebraicResourceShape
