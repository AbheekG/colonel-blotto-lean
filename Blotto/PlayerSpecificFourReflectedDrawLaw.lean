import Blotto.PlayerSpecificFourReflectedIdealLeaves
import Blotto.PlayerSpecificNestedAffineCDF
import Blotto.PlayerSpecificAlgebraicFourReflectedDraw
import Blotto.FourDyadicTransport

/-! The complete executing reflected branch includes two resource coins,
the reached nested terminal sampler and the final reflection. All reached
terminal hypotheses and sizes come from its actual prepared input. -/
namespace Blotto.PlayerSpecificFourReflectedDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def terminalDraw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (s : State 3) (bits : Fin ((17*H+K)+K) → Bool) : Allocation 3 :=
  PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicNestedTerminalDraw.draw RationalCostModel.schoolbook r.root
    (PlayerSpecificAlgebraicFourReflectedTerminal.input (PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a) s)
      H K bits) x

noncomputable def unreflectedLaw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 3 :=
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a
  PlayerSpecificResourceContinuationLaw.law RationalCostModel.schoolbook p.resources H 2 ((17*H+K)+K)
    (start RationalCostModel.schoolbook p.resources true) (terminalDraw r a H K x)

noncomputable def law (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw (2*H+((17*H+K)+K))).map (fun bits =>
    PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicFourReflectedDraw.draw r a H K bits) x)

theorem law_eq (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput) (x : ℝ)
    (hx : realEvaluate r.root.polynomial x=0) (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (H K : ℕ) :
    law r a H K x=reflectedLaw i.originalLengths (unreflectedLaw r a H K x) := by
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a
  have hl : PlayerSpecificAlgebraicSegment.values p.long x=i.originalLengths := by
    funext j
    exact PlayerSpecificAlgebraicFourReflectedInput.original_value a i x ha j
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits => PlayerSpecificAlgebraicSegment.values
    (PlayerSpecificAlgebraicFourReflectedDraw.draw r a H K bits) x) _=
      Measure.map (reflectAppend i.originalLengths) (Measure.map _
        (fairBitLaw (2*H+((17*H+K)+K)) : Measure (Fin (2*H+((17*H+K)+K)) → Bool)))
  rw [Measure.map_map (measurable_reflectAppend _) (measurable_of_countable _)]
  congr 1
  funext bits
  rw [PlayerSpecificAlgebraicFourReflectedDraw.draw,PlayerSpecificAlgebraicReflectAppend.value _ _ _ x hx]
  rw [hl]
  rfl

theorem unreflected_CDF_error (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) :
    CDFClose (unreflectedLaw r a H K x) (i.reflectedResourceSystem hcase).law
      (19/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let model := RationalCostModel.schoolbook
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare model r a
  let sys := i.reflectedResourceSystem hcase
  have hp := PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a T hfit hm hm0 hml hmT hT
  have hc : Context p.resources x := ⟨hm,hirr,hv,hx,fun j => (hp.2.2.1 j).1.1⟩
  have hs := start_valid model p.resources true hm hirr hv x hx (fun j => (hp.2.2.1 j).2.1)
  have hstart := PlayerSpecificAlgebraicFourReflectedPath.start_values model r a i hm hirr hv x hx ha T hfit hcase
  have hleaves := PlayerSpecificFourReflectedIdealLeaves.leaves r a i hm hirr hv x hx ha T hfit hml hmT hT hcase
  have ht : ∀ j z,closedCDF sys.law j z=PlayerSpecificNestedAffineCDF.base sys j z+
      PlayerSpecificNestedAffineCDF.slope sys j z*eval (start model p.resources true) x j := by
    intro j z
    rw [hstart.2]
    exact PlayerSpecificNestedAffineCDF.initial sys j z
  have hl : ∀ j z,PlayerSpecificResourceIdealLeaves.ForLeaves model p.resources
      (fun s => |closedCDF ((fairBitLaw ((17*H+K)+K)).map (terminalDraw r a H K x s)) j z-
        (PlayerSpecificNestedAffineCDF.base sys j z+PlayerSpecificNestedAffineCDF.slope sys j z*eval s x j)|
          ≤ 17/(2:ℝ)^H+3/(2*(2:ℝ)^K)) 2 (start model p.resources true) := by
    intro j z
    apply PlayerSpecificResourceIdealLeaves.mono model p.resources _ _ 2 (start model p.resources true) hleaves
    intro s hstate
    have hval := PlayerSpecificAlgebraicFourReflectedTerminal.values r a i hm hirr hv x hx ha T hfit hcase s hstate.2.1
    have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 16 T
    have h := PlayerSpecificNestedTerminalDrawLaw.CDF_error model r.root _ (sys.terminal (eval s x) hstate.2.1)
      hm hirr hv x hx hval (iterate 16 T) hstate.2.2 hml (mono hmT hi) (hT.trans hi) H K
    have he := h j z
    rw [PlayerSpecificNestedAffineCDF.terminal sys (eval s x) hstate.2.1 j z] at he
    exact he
  have h := PlayerSpecificResourceContinuationCDF.CDF_error model p.resources x hc H 2 ((17*H+K)+K)
    (start model p.resources true) hs (terminalDraw r a H K x) sys.law
      (PlayerSpecificNestedAffineCDF.base sys) (PlayerSpecificNestedAffineCDF.slope sys)
      (17/(2:ℝ)^H+3/(2*(2:ℝ)^K)) ht hl
  have he : (2:ℝ)/(2:ℝ)^H+(17/(2:ℝ)^H+3/(2*(2:ℝ)^K))=19/(2:ℝ)^H+3/(2*(2:ℝ)^K) := by ring
  norm_num only [Nat.cast_ofNat] at h
  rw [he] at h
  exact h

theorem CDF_error (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) :
    CDFClose (law r a H K x) (i.reflectedZeroLaw hcase) (19/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
  rw [law_eq r a i x hx.1 ha H K]
  exact reflectedLaw_CDFClose _ (unreflected_CDF_error r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H K)

end Blotto.PlayerSpecificFourReflectedDrawLaw
