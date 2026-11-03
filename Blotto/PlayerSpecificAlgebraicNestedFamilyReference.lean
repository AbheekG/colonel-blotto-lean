import Blotto.PlayerSpecificAlgebraicNestedFamily

/-! Actual family profiles refine the preserved fixed-mean conditional
law at the reached outer midpoint. Every reference endpoint remains feasible. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFamilyReference
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificAlgebraicNestedFamily
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def reference (i : NestedInput) (short : ℝ) (hshort : 0<short) (hxv : short≤ i.v)
    (K : ℕ) (outer : Fin K → Bool) : SegmentLottery 3 9 :=
  let f:=i.atLength short hshort (by linarith [i.lengths.2.2.1])
  let s:=f.location (dyadicMidpointSample K outer)
  PlayerSpecificAlgebraicNestedFirstTable.reference f hxv s
    (f.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)

theorem table_reference_congr (i : NestedInput) (htv : i.t≤ i.v) (s t : ℝ)
    (hs : 0≤s ∧ s≤ i.t) (ht : 0≤t ∧ t≤ i.t) (he : s=t) :
    PlayerSpecificAlgebraicNestedFirstTable.reference i htv s hs=
      PlayerSpecificAlgebraicNestedFirstTable.reference i htv t ht := by
  cases he
  rfl

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (short : Data) (T : ℕ) (hfit : Fits root a T)
    (hshort : Reduced root.polynomial short ∧ HasHeight short T) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) (hx0 : 0<realEvaluate short x) (hxv : realEvaluate short x≤ i.v)
    (K : ℕ) (outer : Fin K → Bool) :
    Refines (profile model root a short K outer) x (reference i (realEvaluate short x) hx0 hxv K outer) := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hxuv : realEvaluate short x< i.u+i.v := by linarith [i.lengths.2.2.1]
  let f:=i.atLength (realEvaluate short x) hx0 hxuv
  let raw:=family model root a short
  let s:=PlayerSpecificAlgebraicNestedFirstDraw.location model root raw K outer
  have henv:=PlayerSpecificAlgebraicNestedInputTools.environment_reduced root a short T hfit hshort.1
  have hf:=PlayerSpecificAlgebraicNestedFamily.value model root a i hm hirr hv x hx ha short henv hx0 hxuv
  have hfits:=PlayerSpecificAlgebraicNestedFamily.fits model root a short T hfit hshort hm hm0 hml hmT hT
  have hl:=PlayerSpecificAlgebraicNestedFirstDraw.location_value model root raw f hm hirr hv x hx hf (iterate 9 T) hfits K outer
  have hs : 0≤realEvaluate s x ∧ realEvaluate s x≤ f.t := by
    rw [hl]
    exact f.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩
  have hsred:=PlayerSpecificAlgebraicNestedFirstDraw.location_reduced model root raw hm hm0 (iterate 9 T) hfits K outer
  have henv2:=PlayerSpecificAlgebraicNestedInputTools.environment_reduced root raw s (iterate 9 T) hfits hsred
  have hr:=PlayerSpecificAlgebraicNestedFirstTable.refines model root raw f hm hirr hv x hx hf s henv2 hxv hs
  have ht:=f.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩
  have hsame:=table_reference_congr f hxv (realEvaluate s x) (f.location (dyadicMidpointSample K outer)) hs ht hl
  change Refines (PlayerSpecificAlgebraicNestedFirstTable.prepare model root raw s) x
    (PlayerSpecificAlgebraicNestedFirstTable.reference f hxv (f.location (dyadicMidpointSample K outer)) ht)
  exact hsame ▸ hr

theorem endpoints_budget (i : NestedInput) (short : ℝ) (hshort : 0<short) (hxv : short≤ i.v)
    (K : ℕ) (outer : Fin K → Bool) :
    (∀ slot,FullBudget i.M ((reference i short hshort hxv K outer).P slot)) ∧
      (∀ slot,FullBudget i.M ((reference i short hshort hxv K outer).Q slot)) := by
  let f:=i.atLength short hshort (by linarith [i.lengths.2.2.1])
  exact PlayerSpecificAlgebraicNestedFirstReference.endpoints_budget f hxv
    (f.location (dyadicMidpointSample K outer))
    (f.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)

theorem endpoints_box (i : NestedInput) (short : ℝ) (hshort : 0<short) (hxv : short≤ i.v)
    (K : ℕ) (outer : Fin K → Bool) :
    (∀ slot,InBox ![i.a,i.d,i.c] ((reference i short hshort hxv K outer).P slot)) ∧
      (∀ slot,InBox ![i.a,i.d,i.c] ((reference i short hshort hxv K outer).Q slot)) := by
  let f:=i.atLength short hshort (by linarith [i.lengths.2.2.1])
  exact PlayerSpecificAlgebraicNestedFirstReference.endpoints_box f hxv
    (f.location (dyadicMidpointSample K outer))
    (f.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)

end Blotto.PlayerSpecificAlgebraicNestedFamilyReference
