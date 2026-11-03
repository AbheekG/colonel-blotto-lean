import Blotto.PlayerSpecificAlgebraicFourReflectedSizes

/-! Actual finite-bit reflected-resource paths use the existing two-step
engine on computed capacities. They end at a valid nested terminal input. -/
namespace Blotto.PlayerSpecificAlgebraicFourReflectedPath
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
open PlayerSpecificAlgebraicFourReflectedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ) (bits : Fin (2*H) → Bool) : State 3 × ℕ :=
  let p := prepare RationalCostModel.schoolbook r a
  PlayerSpecificFiniteResourceLoop.draw p.resources true H bits

theorem start_values (model : RationalCostModel) (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hcase : i.w < (1-i.p)*i.ell) :
    lengths (prepare model r a).resources x=(i.reflectedResourceSystem hcase).capacity ∧
      eval (start model (prepare model r a).resources true) x=(i.reflectedResourceSystem hcase).initial := by
  have hp := PlayerSpecificAlgebraicFourReflectedInput.values model r a i hm hirr hv x hx ha T hfit hcase
  constructor
  · funext j; exact hp.2.2.1 j
  · funext j
    simp only [eval,start_read,PlayerSpecificInitialLineageBound.means,ite_true]
    exact hp.2.2.2.1 j

theorem contract (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H : ℕ) (bits : Fin (2*H) → Bool) :
    Valid (prepare RationalCostModel.schoolbook r a).resources x (draw r a H bits).1 ∧
      (i.reflectedResourceSystem hcase).Valid (eval (draw r a H bits).1 x) ∧ (draw r a H bits).2 ≤ 2 := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let p := (prepare RationalCostModel.schoolbook r a).resources
  let sys := i.reflectedResourceSystem hcase
  have hb := PlayerSpecificAlgebraicFourReflectedSizes.bounds RationalCostModel.schoolbook r a T hfit hm hm0 hml hmT hT
  have hmeans : ∀ j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p true j) :=
    fun j => (hb.2.2.1 j).2.1
  have hc : Context p x := ⟨hm,hirr,hv,hx,fun j => (hb.2.2.1 j).1.1⟩
  have hstart := start_values RationalCostModel.schoolbook r a i hm hirr hv x hx ha T hfit hcase
  have hbox : InBox (lengths p x) (eval (start RationalCostModel.schoolbook p true) x) := by
    rw [hstart.1,hstart.2]
    exact sys.initial_box
  obtain ⟨choices,_,heq⟩ := PlayerSpecificFiniteResourceLoop.draw_refinement p true H bits
  have ht := complete_path RationalCostModel.schoolbook p x hc true choices hmeans hbox
  change Valid p x (PlayerSpecificAlgebraicPathContract.drawPath p true choices).1 ∧
    InBox (lengths p x) (eval (PlayerSpecificAlgebraicPathContract.drawPath p true choices).1 x) ∧
    (∑ j,eval (PlayerSpecificAlgebraicPathContract.drawPath p true choices).1 x j)=
      (∑ j,eval (start RationalCostModel.schoolbook p true) x j) ∧
    (PlayerSpecificAlgebraicPathContract.drawPath p true choices).2 ≤ 2 ∧
    (PlayerSpecificAlgebraicPathContract.drawPath p true choices).1.active.length ≤ 1 at ht
  change PlayerSpecificFiniteResourceLoop.draw p true H bits=PlayerSpecificAlgebraicPathContract.drawPath p true choices at heq
  change Valid p x (PlayerSpecificFiniteResourceLoop.draw p true H bits).1 ∧
    sys.Valid (eval (PlayerSpecificFiniteResourceLoop.draw p true H bits).1 x) ∧
      (PlayerSpecificFiniteResourceLoop.draw p true H bits).2 ≤ 2
  rw [heq]
  refine ⟨ht.1,⟨?_,?_,?_⟩,ht.2.2.2.1⟩
  · rw [← hstart.1]
    exact ht.2.1
  · rw [← hstart.1]
    change (fractionalSet (lengths p x) (eval (PlayerSpecificAlgebraicPathContract.drawPath p true choices).1 x)).card ≤ 1
    rw [← length_eq_card p x _ ht.1]
    exact ht.2.2.2.2
  · have hmixed := sys.initial_mean
    rw [Finset.sum_sub_distrib] at hmixed ⊢
    rw [ht.2.2.1,hstart.2]
    exact hmixed

theorem heights (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (T : ℕ) (hfit : Fits r.root a T) (hml : r.root.polynomial.length ≤ 4)
    (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (H : ℕ) (bits : Fin (2*H) → Bool) :
    ∀ j,HasHeight (((draw r a H bits).1.data).read j) (iterate 16 T) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let p := (prepare RationalCostModel.schoolbook r a).resources
  have hb := PlayerSpecificAlgebraicFourReflectedSizes.bounds RationalCostModel.schoolbook r a T hfit hm hm0 hml hmT hT
  have hmeans : ∀ j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p true j) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p true j) (iterate 15 T) := fun j => (hb.2.2.1 j).2
  have hlengths : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧
      HasHeight (p.rows.read j).length (iterate 15 T) := fun j => (hb.2.2.1 j).1
  have hc : Context p x := ⟨hm,hirr,hv,hx,fun j => (hlengths j).1⟩
  have hs := start_valid RationalCostModel.schoolbook p true hm hirr hv x hx (fun j => (hmeans j).1)
  obtain ⟨choices,_,heq⟩ := PlayerSpecificFiniteResourceLoop.draw_refinement p true H bits
  have hh := PlayerSpecificAlgebraicLoopHeights.run_heights RationalCostModel.schoolbook p true x hc 2
    (start RationalCostModel.schoolbook p true) choices hs
    (PlayerSpecificAlgebraicResourceLineage.start_certificate RationalCostModel.schoolbook p true)
    (iterate 15 T) hmeans hlengths (by
      intro j
      rw [start_read]
      apply mono (hmeans j).2
      have hl := PlayerSpecificAlgebraicLoopHeights.leaf_le_active 3 (iterate 15 T) (by omega)
      unfold PlayerSpecificAlgebraicLoopHeights.storedHeight PlayerSpecificAlgebraicPairHeights.resourceHeight
      omega)
  change ∀ j,HasHeight ((PlayerSpecificAlgebraicPathContract.drawPath p true choices).1.data.read j)
    (PlayerSpecificAlgebraicLoopHeights.storedHeight 3 (iterate 15 T)) at hh
  change ∀ j,HasHeight ((PlayerSpecificFiniteResourceLoop.draw p true H bits).1.data.read j) (iterate 16 T)
  rw [heq]
  intro j
  exact mono (hh j) (PlayerSpecificAlgebraicFourReflectedSizes.stored_height_le (iterate 15 T))

end Blotto.PlayerSpecificAlgebraicFourReflectedPath
