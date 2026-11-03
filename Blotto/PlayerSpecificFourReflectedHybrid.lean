import Blotto.PlayerSpecificFourMergedHybrid

/-! The reflected branch has one H-independent exact-choice midpoint
hybrid. Its whole-event discrepancy includes both resource coins and
every reached nested choice; only finite scalar draws are discretized. -/
namespace Blotto.PlayerSpecificFourReflectedHybrid
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicResourceState
open PlayerSpecificAlgebraicResourceLoop
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem exists_hybrid (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (K : ℕ) :
    ∃ hybrid : Mixed 4,
      (∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificFourReflectedDrawLaw.law r a H K x) hybrid (19/(2:ℝ)^H)) ∧
      CDFClose hybrid (i.reflectedZeroLaw hcase) (3/(2*(2:ℝ)^K)) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let model := RationalCostModel.schoolbook
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare model r a
  let sys := i.reflectedResourceSystem hcase
  let initial := start model p.resources true
  have hp := PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a T hfit hm hm0 hml hmT hT
  have hc : Context p.resources x := ⟨hm,hirr,hv,hx,fun j => (hp.2.2.1 j).1.1⟩
  have hs : Valid p.resources x initial := start_valid model p.resources true hm hirr hv x hx (fun j => (hp.2.2.1 j).2.1)
  have hstart := PlayerSpecificAlgebraicFourReflectedPath.start_values model r a i hm hirr hv x hx ha T hfit hcase
  have hleaves := PlayerSpecificFourReflectedIdealLeaves.leaves r a i hm hirr hv x hx ha T hfit hml hmT hT hcase
  let leaf := fun s : State 3 => sys.dyadicLeafLaw K (eval s x)
  let hn := PlayerSpecificResourceIdealMean.of_valid model p.resources x hc 2 initial hs
  let hybrid := PlayerSpecificResourceIdealLaw.law model p.resources x leaf 2 initial hn
  have hleaf : ∀ H,PlayerSpecificResourceIdealLeaves.ForLeaves model p.resources
      (fun s => PlayerSpecificEventDistance.Bound
        ((fairBitLaw ((17*H+K)+K)).map (PlayerSpecificFourReflectedDrawLaw.terminalDraw r a H K x s)) (leaf s) (17/(2:ℝ)^H))
        2 initial := by
    intro H
    apply PlayerSpecificResourceIdealLeaves.mono model p.resources _ _ 2 initial hleaves
    intro s hstate A hA
    have hval := PlayerSpecificAlgebraicFourReflectedTerminal.values r a i hm hirr hv x hx ha T hfit hcase s hstate.2.1
    have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 16 T
    have h := PlayerSpecificNestedTerminalDrawLaw.event_error model r.root _ (sys.terminal (eval s x) hstate.2.1)
      hm hirr hv x hx hval (iterate 16 T) hstate.2.2 hml (PlayerSpecificPolynomialHeights.mono hmT hi) (hT.trans hi) H K A hA
    change |((fairBitLaw ((17*H+K)+K)).map (PlayerSpecificFourReflectedDrawLaw.terminalDraw r a H K x s) : Measure (Allocation 3)).real A-
      (sys.dyadicLeafLaw K (eval s x) : Measure (Allocation 3)).real A| ≤ _
    rw [NestedResourceSystem.dyadicLeafLaw,dite_eq_left hstate.2.1]
    exact h
  have hevent := PlayerSpecificResourceHybrid.event_bound model p.resources x hc 2 initial hs
    (fun H => (17*H+K)+K) (fun H => PlayerSpecificFourReflectedDrawLaw.terminalDraw r a H K x) leaf 17 hleaf
  have htarget : ∀ j z,closedCDF sys.law j z=PlayerSpecificNestedAffineCDF.base sys j z+
      PlayerSpecificNestedAffineCDF.slope sys j z*eval initial x j := by
    intro j z
    rw [hstart.2]
    exact PlayerSpecificNestedAffineCDF.initial sys j z
  have hmidpoint : ∀ j z,PlayerSpecificResourceIdealLeaves.ForLeaves model p.resources
      (fun s => |closedCDF (leaf s) j z-(PlayerSpecificNestedAffineCDF.base sys j z+
        PlayerSpecificNestedAffineCDF.slope sys j z*eval s x j)| ≤ 3/(2*(2:ℝ)^K)) 2 initial := by
    intro j z
    apply PlayerSpecificResourceIdealLeaves.mono model p.resources _ _ 2 initial hleaves
    intro s hstate
    have h := (sys.dyadicLeafLaw_CDF_error K (eval s x) hstate.2.1) j z
    have he : sys.leafLaw (eval s x)=(sys.terminal (eval s x) hstate.2.1).law := by
      rw [NestedResourceSystem.leafLaw,dite_eq_left hstate.2.1]
    rw [he,PlayerSpecificNestedAffineCDF.terminal sys (eval s x) hstate.2.1 j z] at h
    exact h
  have hCDF : CDFClose hybrid sys.law (3/(2*(2:ℝ)^K)) :=
    PlayerSpecificResourceContinuationCDF.ideal_error model p.resources x hc 2 initial hs leaf sys.law
      (PlayerSpecificNestedAffineCDF.base sys) (PlayerSpecificNestedAffineCDF.slope sys) _ htarget hmidpoint
  refine ⟨reflectedLaw i.originalLengths hybrid,?_,?_⟩
  · intro H
    rw [PlayerSpecificFourReflectedDrawLaw.law_eq r a i x hx.1 ha H K]
    have h : PlayerSpecificEventDistance.Bound (PlayerSpecificFourReflectedDrawLaw.unreflectedLaw r a H K x) hybrid (19/(2:ℝ)^H) :=
      hevent H
    exact PlayerSpecificEventDistance.map _ _ _ h (reflectAppend i.originalLengths) (measurable_reflectAppend _)
  · exact reflectedLaw_CDFClose _ hCDF

end Blotto.PlayerSpecificFourReflectedHybrid
