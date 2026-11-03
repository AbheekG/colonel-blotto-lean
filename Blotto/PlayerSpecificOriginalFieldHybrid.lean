import Blotto.PlayerSpecificFiniteFieldHybrid

/-! Original accepted inputs have a complete H-independent exact-choice
midpoint hybrid. The actual whole-event/total-variation error is bounded
by (N+1000)*2^-H, and its remaining CDF error is only the scalar error. -/
namespace Blotto.PlayerSpecificOriginalFieldHybrid
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ accepted : PlayerSpecificInput N,
      accepted.valuesA=i.valuesA.values ∧ accepted.valuesB=i.valuesB.values ∧ accepted.budget=(i.budget:ℝ) ∧
      PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval accepted.gamma ∧
      regret i.valuesA.values 1 accepted.lawA accepted.lawB=0 ∧
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 ∧
      ∀ (player : Bool) (K : ℕ),∃ hybrid : Mixed N,
        (∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificFiniteFieldCDF.law p i.budget player H K accepted.gamma) hybrid
          (((N+1000:ℕ):ℝ)/(2:ℝ)^H)) ∧
        (∀ H,PlayerSpecificEventDistance.distance (PlayerSpecificFiniteFieldCDF.law p i.budget player H K accepted.gamma) hybrid ≤
          ((N+1000:ℕ):ℝ)/(2:ℝ)^H) ∧
        CDFClose hybrid (if player then accepted.lawA else accepted.lawB) (3/(2*(2:ℝ)^K)) := by
  let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  obtain ⟨accepted,hA,hB,hbudget,hgamma,hregA,hregB,hCDF⟩ := PlayerSpecificOriginalFieldCDF.original_input i r hr
  obtain ⟨x,hx,_,hred,hinit,_,_⟩ := PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  have hex : x=accepted.gamma := hgamma.2.2 x hx.1 hx.2.1
  subst x
  obtain ⟨z,hz,hpaths⟩ := PlayerSpecificOriginalIdealResourceLeaves.original_input i r hr
  have hez : z=accepted.gamma := hgamma.2.2 z hz.1 hz.2.1
  subst z
  have hs := PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hroot0 := (PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr).1
  have hsize0 := (PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2
  let L := PlayerSpecificInitialPositivePrecision.inputSize i
  let T := PlayerSpecificAlgebraicFiniteDrawContract.base N L
  have hFT : PlayerSpecificFiniteParameterSizes.height N L ≤ T := by dsimp [T,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hIT : PlayerSpecificAlgebraicInitialInputSizes.height N L ≤ T := by dsimp [T,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hRT : PlayerSpecificAlgebraicPathContract.height N L ≤ T := by dsimp [T,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hLT : L ≤ T := by dsimp [T,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hT : 1 ≤ T := by dsimp [T,PlayerSpecificAlgebraicFiniteDrawContract.base]; omega
  have hc : PlayerSpecificAlgebraicResourceLoop.Context p accepted.gamma := by
    refine ⟨hs.1,hs.2.1,?_,hgamma,fun j => (hred j).1⟩
    have hv : (r.root.interval.lo:ℝ) < r.root.interval.hi := lt_of_lt_of_le hgamma.2.1.1 hgamma.2.1.2
    exact_mod_cast hv
  have hroot : HasHeight p.parameters.root.polynomial T := mono hroot0 hFT
  have hsize : ∀ j,HasHeight (p.rows.read j).length T := fun j => mono (hsize0 j).1 hIT
  refine ⟨accepted,hA,hB,hbudget,hgamma,hregA,hregB,?_⟩
  intro player K
  let b : ℚ := if player then 1 else i.budget
  have hpos : 0 < b := by cases player; exact i.budget_pos; exact zero_lt_one
  have hBH : RationalHeight b T := by
    cases player
    · exact (PlayerSpecificRecognitionInputHeights.original_fields i).1.mono hLT
    · exact one_height.mono hT
  have hL : ∀ j,0 < lengths p accepted.gamma j ∧ lengths p accepted.gamma j ≤ (b:ℝ) := by
    intro j
    refine ⟨(hinit j).1.1,?_⟩
    cases player
    · exact (hinit j).1.2
    · exact (hinit j).1.2.trans (by exact_mod_cast i.budget_le)
  have hstart := start_valid RationalCostModel.schoolbook p player hc.normalized hc.irreducible hc.interval accepted.gamma hc.root
    (fun j => by cases player; exact (hred j).2.2; exact (hred j).2.1)
  have hleaves : PlayerSpecificResourceIdealLeaves.ForLeaves RationalCostModel.schoolbook p
      (fun s => Valid p accepted.gamma s ∧ InBox (lengths p accepted.gamma) (eval s accepted.gamma) ∧
        (∑ j,eval s accepted.gamma j)=2*(b:ℝ) ∧ s.active.length ≤ 1 ∧ ∀ j,HasHeight (s.data.read j) T)
        (N-1) (start RationalCostModel.schoolbook p player) := by
    apply PlayerSpecificResourceIdealLeaves.mono RationalCostModel.schoolbook p _ _ (N-1)
      (start RationalCostModel.schoolbook p player) (hpaths player)
    intro s hstate
    have hmass : (∑ j,eval s accepted.gamma j)=2*(b:ℝ) := by
      cases player
      · exact hstate.2.2.1
      · simpa [b] using hstate.2.2.1
    exact ⟨hstate.1,hstate.2.1,hmass,hstate.2.2.2.1,fun j => mono (hstate.2.2.2.2 j) hRT⟩
  obtain ⟨hybrid,hevent⟩ := PlayerSpecificFiniteFieldHybrid.prepared p i.budget player accepted.gamma hc hstart hpos hL
    T hroot hs.2.2.1 hBH hsize hleaves K
  have hbound : ∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificFiniteFieldCDF.law p i.budget player H K accepted.gamma) hybrid
      (((N+1000:ℕ):ℝ)/(2:ℝ)^H) := by
    intro H
    have hn : ((N-1+80:ℕ):ℝ) ≤ ((N+1000:ℕ):ℝ) := by exact_mod_cast (show N-1+80 ≤ N+1000 by omega)
    exact PlayerSpecificEventDistance.mono _ _ _ _ (hevent H) (div_le_div_of_nonneg_right hn (by positivity))
  refine ⟨hybrid,hbound,fun H => PlayerSpecificEventDistance.distance_le _ _ _ (hbound H),?_⟩
  exact PlayerSpecificHybridLimit.CDF_error (fun H => PlayerSpecificFiniteFieldCDF.law p i.budget player H K accepted.gamma)
    hybrid (if player then accepted.lawA else accepted.lawB) ((N+1000:ℕ):ℝ) ((N+1000:ℕ):ℝ) (3/(2*(2:ℝ)^K))
      hbound (fun H => hCDF player H K)

end Blotto.PlayerSpecificOriginalFieldHybrid
