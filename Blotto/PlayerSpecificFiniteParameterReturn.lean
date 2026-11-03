import Blotto.PlayerSpecificFiniteRecognitionComplete

/-! The executing finite-bit recognizer retains the selected irreducible
root and an actual reduced field representation of its positive scale.
Global original-input recognition costs remain a separate obligation. -/
namespace Blotto.PlayerSpecificFiniteParameterReturn
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificRationalCells PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  cell : Cell
  root : Candidate
  scale : Data

def scale (c : Cell) (b : ℚ) (m : Data) : Data :=
  PlayerSpecificModularHorner.run m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1]
def run {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) : Option Result :=
  match PlayerSpecificFiniteRecognition.run model i with
  | none => none
  | some (c,r) => some ⟨c,r,scale c i.budget r.polynomial⟩

theorem scale_value (c : Cell) (b : ℚ) (m : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (scale c b m) x=PlayerSpecificCubic.candidateScale (castCell c).state.coefficients (b:ℝ) x := by
  rw [scale,PlayerSpecificModularHorner.real_value m _ _ x hx]
  dsimp only [realEvaluate,List.foldr_cons,List.foldr_nil,PlayerSpecificCubic.candidateScale,castCell,castState,castCoefficients]
  push_cast
  ring

theorem rejection_iff {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) :
    run model i=none ↔ ¬∃ gamma sigma,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma := by
  rw [←PlayerSpecificFiniteRecognitionComplete.rejection_iff model i]
  rw [run]
  cases PlayerSpecificFiniteRecognition.run model i <;> simp

theorem sound {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) (r : Result)
    (hr : run model i=some r) :
    Normalized r.root.polynomial ∧ Irreducible (semantics r.root.polynomial) ∧ r.root.polynomial.length≤4 ∧
      Reduced r.root.polynomial r.scale ∧
      ∃! x : ℝ,realEvaluate r.root.polynomial x=0 ∧ r.root.interval.Contains x ∧
        PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) x (realEvaluate r.scale x) := by
  cases hchosen : PlayerSpecificFiniteRecognition.run model i with
  | none => rw [run,hchosen] at hr; cases hr
  | some chosen =>
    rw [run,hchosen] at hr
    have he:=Option.some.inj hr
    subst r
    have hs:=PlayerSpecificFiniteRecognition.sound model i chosen.1 chosen.2 hchosen
    have hgood:=hs.1
    have hm0 : chosen.2.polynomial≠[] := by intro hz; exact hgood.2.1.ne_zero (by rw [hz]; rfl)
    have hred:=PlayerSpecificModularHorner.reduced chosen.2.polynomial [1/(2*i.budget)]
      [chosen.1.state.coefficients.B2,0,chosen.1.state.coefficients.B1] hgood.1 hm0
    obtain ⟨x,hx,hunique⟩:=hgood.2.2.2.1
    refine ⟨hgood.1,hgood.2.1,hgood.2.2.1,hred,⟨x,⟨hx.1,hx.2,?_⟩,?_⟩⟩
    · rw [scale_value chosen.1 i.budget chosen.2.polynomial x hx.1]
      exact hs.2 x hx.1 hx.2
    · intro y hy
      exact hunique y ⟨hy.1,hy.2.1⟩

end Blotto.PlayerSpecificFiniteParameterReturn
