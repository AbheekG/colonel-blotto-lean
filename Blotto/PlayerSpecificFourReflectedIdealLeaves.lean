import Blotto.PlayerSpecificResourceContinuationCDF
import Blotto.PlayerSpecificNestedTerminalDrawLaw

/-! Every leaf of the reflected branch's exact-probability semantics
has native validity, the real terminal constraints and the computed row
sizes needed by the actual terminal sampler. No leaf or size oracle is used. -/
namespace Blotto.PlayerSpecificFourReflectedIdealLeaves
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem leaves (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) :
    let p := PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a
    PlayerSpecificResourceIdealLeaves.ForLeaves RationalCostModel.schoolbook p.resources
      (fun s => Valid p.resources x s ∧ (i.reflectedResourceSystem hcase).Valid (eval s x) ∧
        PlayerSpecificAlgebraicNestedTerminalSizes.Fits r.root (PlayerSpecificAlgebraicFourReflectedTerminal.input p s) (iterate 16 T))
      2 (start RationalCostModel.schoolbook p.resources true) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let model := RationalCostModel.schoolbook
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare model r a
  let sys := i.reflectedResourceSystem hcase
  have hp := PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a T hfit hm hm0 hml hmT hT
  have hmeans : ∀ j,Reduced p.resources.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p.resources true j) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p.resources true j) (iterate 15 T) := fun j => (hp.2.2.1 j).2
  have hlengths : ∀ j,Reduced p.resources.parameters.root.polynomial (p.resources.rows.read j).length ∧
      HasHeight (p.resources.rows.read j).length (iterate 15 T) := fun j => (hp.2.2.1 j).1
  have hc : Context p.resources x := ⟨hm,hirr,hv,hx,fun j => (hlengths j).1⟩
  have hs := start_valid model p.resources true hm hirr hv x hx (fun j => (hmeans j).1)
  have hstart := PlayerSpecificAlgebraicFourReflectedPath.start_values model r a i hm hirr hv x hx ha T hfit hcase
  have hbox : InBox (lengths p.resources x) (eval (start model p.resources true) x) := by
    rw [hstart.1,hstart.2]
    exact sys.initial_box
  apply PlayerSpecificResourceIdealLeaves.of_paths
  intro choices
  let s := (run model p.resources 2 (start model p.resources true) choices).1
  have ht := complete_path model p.resources x hc true choices (fun j => (hmeans j).1) hbox
  have hvalid : sys.Valid (eval s x) := by
    refine ⟨?_,?_,?_⟩
    · rw [←hstart.1]
      exact ht.2.1
    · rw [←hstart.1]
      change (fractionalSet (lengths p.resources x) (eval s x)).card ≤ 1
      rw [←length_eq_card p.resources x s ht.1]
      exact ht.2.2.2.2
    · have he := sys.initial_mean
      rw [Finset.sum_sub_distrib] at he ⊢
      rw [ht.2.2.1,hstart.2]
      exact he
  have hh := PlayerSpecificAlgebraicLoopHeights.run_heights model p.resources true x hc 2
    (start model p.resources true) choices hs (PlayerSpecificAlgebraicResourceLineage.start_certificate model p.resources true)
    (iterate 15 T) hmeans hlengths (by
      intro j
      rw [start_read]
      apply mono (hmeans j).2
      have hl := PlayerSpecificAlgebraicLoopHeights.leaf_le_active 3 (iterate 15 T) (by omega)
      unfold PlayerSpecificAlgebraicLoopHeights.storedHeight PlayerSpecificAlgebraicPairHeights.resourceHeight
      omega)
  have hh' : ∀ j,HasHeight (s.data.read j) (iterate 16 T) := fun j =>
    mono (hh j) (PlayerSpecificAlgebraicFourReflectedSizes.stored_height_le (iterate 15 T))
  have hi := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15 ≤ 16)
  refine ⟨ht.1,hvalid,?_,⟩
  refine ⟨⟨hp.2.2.2.1,mono hp.2.2.2.2 hi⟩,fun j => ⟨(hp.1 j).1,mono (hp.1 j).2 hi⟩,
    fun j => ⟨(hp.2.1 j).1,mono (hp.2.1 j).2 hi⟩,?_,fun j => ⟨ht.1.reduced j,hh' j⟩⟩
  intro j
  simp only [PlayerSpecificAlgebraicFourReflectedTerminal.input,FixedArrayTable.read_ofFn]
  exact ⟨(hp.2.2.1 j).1.1,mono (hp.2.2.1 j).1.2 hi⟩

end Blotto.PlayerSpecificFourReflectedIdealLeaves
