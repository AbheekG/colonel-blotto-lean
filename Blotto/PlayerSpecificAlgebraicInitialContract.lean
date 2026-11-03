import Blotto.PlayerSpecificAlgebraicInitialVector

/-! Actual algebraic sampler input satisfies both hard-budget coupling
systems: positive common lengths, exact endpoint cap, boxed mixture values
and exact sums twice each player's budget. No marginal or inverse oracle
is supplied; the accepted root and cached inverse are actually computed. -/
namespace Blotto.PlayerSpecificAlgebraicInitialContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicInitialVector
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem accepted_point {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    Normalized r.root.polynomial ∧ Irreducible (semantics r.root.polynomial) ∧ r.root.polynomial.length≤4 ∧
      Reduced r.root.polynomial r.scale ∧
      ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
        PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) x (realEvaluate r.scale x) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  obtain ⟨x,hx,_⟩:=hs.2.2.2.2
  obtain ⟨y,hy,hunique⟩:=accepted_unique i r hr
  refine ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,x,?_,hx.2.2⟩
  exact ⟨hx.1,hx.2.1,fun z hz hzin => (hunique z ⟨hz,hzin⟩).trans (hunique x ⟨hx.1,hx.2.1⟩).symm⟩

theorem mixture_box (v w x scale : ℝ) (hv : 0<v) (hw : 0<w) (hg : 0<x) (hs : 0<scale) :
    0<PlayerSpecificMarginals.length v w x scale ∧
      (0≤PlayerSpecificMarginals.probA v w x*PlayerSpecificMarginals.length v w x scale ∧
        PlayerSpecificMarginals.probA v w x*PlayerSpecificMarginals.length v w x scale≤PlayerSpecificMarginals.length v w x scale) ∧
      (0≤PlayerSpecificMarginals.probB v w x*PlayerSpecificMarginals.length v w x scale ∧
        PlayerSpecificMarginals.probB v w x*PlayerSpecificMarginals.length v w x scale≤PlayerSpecificMarginals.length v w x scale) := by
  have hl:=PlayerSpecificMarginals.length_pos hv hw hg hs
  have ha:=PlayerSpecificMarginals.probA_pos hv hw hg
  have hb:=PlayerSpecificMarginals.probB_pos hv hw hg
  have ha1:=mul_le_mul_of_nonneg_right (PlayerSpecificMarginals.probA_le_one v w x) hl.le
  have hb1:=mul_le_mul_of_nonneg_right (PlayerSpecificMarginals.probB_le_one v w x) hl.le
  exact ⟨hl,⟨mul_nonneg ha.le hl.le,by simpa only [one_mul] using ha1⟩,
    ⟨mul_nonneg hb.le hl.le,by simpa only [one_mul] using hb1⟩⟩

theorem actual_coupling_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      Reduced r.root.polynomial (prepare RationalCostModel.schoolbook i r).inverseScale ∧
      (∀ j,Reduced r.root.polynomial ((prepare RationalCostModel.schoolbook i r).rows.read j).length ∧
        Reduced r.root.polynomial ((prepare RationalCostModel.schoolbook i r).rows.read j).initialA ∧
        Reduced r.root.polynomial ((prepare RationalCostModel.schoolbook i r).rows.read j).initialB) ∧
      (∀ j,(0<realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).length x ∧
          realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).length x≤(i.budget:ℝ)) ∧
        (0≤realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).initialA x ∧
          realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).initialA x≤realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).length x) ∧
        (0≤realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).initialB x ∧
          realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).initialB x≤realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).length x)) ∧
      (∑ j,realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).initialA x)=2 ∧
      (∑ j,realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).initialB x)=2*(i.budget:ℝ) := by
  obtain ⟨hm,hirr,_,hscale,x,hx,hvalid⟩:=accepted_point i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hred:=reduced_rows RationalCostModel.schoolbook i r hm hm0
  have hvals:=values RationalCostModel.schoolbook i r hm hirr hscale x hx hvalid.1
  refine ⟨x,hx,hred.1,hred.2,?_,?_,?_⟩
  · intro j
    have hb:=mixture_box (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x (realEvaluate r.scale x)
      (by exact_mod_cast i.valuesA.positive j) (by exact_mod_cast i.valuesB.positive j) hvalid.1 hvalid.2.1
    have hj:=hvals j
    rw [hj.1,hj.2.1,hj.2.2]
    exact ⟨⟨hb.1,hvalid.2.2.2.2 j⟩,hb.2.1,hb.2.2⟩
  · calc
      _ = ∑ j,PlayerSpecificMarginals.probA (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x*
          PlayerSpecificMarginals.length (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x (realEvaluate r.scale x) :=
        Finset.sum_congr rfl (fun j _ => (hvals j).2.1)
      _ = 2 := hvalid.2.2.1
  · calc
      _ = ∑ j,PlayerSpecificMarginals.probB (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x*
          PlayerSpecificMarginals.length (i.valuesA.weight j:ℝ) (i.valuesB.weight j:ℝ) x (realEvaluate r.scale x) :=
        Finset.sum_congr rfl (fun j _ => (hvals j).2.2)
      _ = 2*(i.budget:ℝ) := hvalid.2.2.2.1

end Blotto.PlayerSpecificAlgebraicInitialContract
