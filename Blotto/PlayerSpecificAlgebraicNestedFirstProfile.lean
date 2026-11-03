import Blotto.PlayerSpecificAlgebraicNestedRemainingSizes

/-! The first interior case uses the same eighteen-slot interface as
the other cases, with a reached outer midpoint and feasible padding. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFirstProfile
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18 :=
  let s := PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer
  PlayerSpecificAlgebraicDescriptorPad.pad (PlayerSpecificAlgebraicNestedFirstTable.prepare model root a s) 9 0

noncomputable def reference (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) (outer : Fin K → Bool) : SegmentLottery 3 18 :=
  PlayerSpecificSegmentAssemblyReference.pad
    (PlayerSpecificAlgebraicNestedFirstTable.reference i htv (i.location (dyadicMidpointSample K outer))
      (i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)) 9 0

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (htv : i.t ≤ i.v) (K : ℕ) (outer : Fin K → Bool) :
    Refines (prepare model root a K outer) x (reference i htv K outer) := by
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let s := PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer
  have hl := PlayerSpecificAlgebraicNestedFirstDraw.location_value model root a i hm hirr hv x hx ha T hfit K outer
  have hs : 0 ≤ realEvaluate s x ∧ realEvaluate s x ≤ i.t := by
    rw [hl]
    exact i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩
  have he := PlayerSpecificAlgebraicNestedInputTools.environment_reduced root a s T hfit
    (PlayerSpecificAlgebraicNestedFirstDraw.location_reduced model root a hm hm0 T hfit K outer)
  have hr := PlayerSpecificAlgebraicNestedFirstTable.refines model root a i hm hirr hv x hx ha s he htv hs
  have ht := i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩
  have hsame := PlayerSpecificAlgebraicNestedFamilyReference.table_reference_congr i htv (realEvaluate s x)
    (i.location (dyadicMidpointSample K outer)) hs ht hl
  have hr' := hsame ▸ hr
  exact PlayerSpecificAlgebraicDescriptorPad.refines (PlayerSpecificAlgebraicNestedFirstTable.prepare model root a s) 9 0 x _ hr'

theorem property (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) (outer : Fin K → Bool) (P : Allocation 3 → Prop)
    (h : ∀ slot,P ((PlayerSpecificAlgebraicNestedFirstTable.reference i htv (i.location (dyadicMidpointSample K outer))
      (i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)).P slot) ∧
      P ((PlayerSpecificAlgebraicNestedFirstTable.reference i htv (i.location (dyadicMidpointSample K outer))
        (i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)).Q slot)) :
    ∀ slot,P ((reference i htv K outer).P slot) ∧ P ((reference i htv K outer).Q slot) :=
  PlayerSpecificSegmentAssemblyProperties.pad_property _ 9 0 P h

theorem budget (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,FullBudget i.M ((reference i htv K outer).P slot) ∧ FullBudget i.M ((reference i htv K outer).Q slot) := by
  have h := PlayerSpecificAlgebraicNestedFirstReference.endpoints_budget i htv (i.location (dyadicMidpointSample K outer))
    (i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)
  exact property i htv K outer (FullBudget i.M) (fun slot => ⟨h.1 slot,h.2 slot⟩)

theorem box (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,InBox ![i.a,i.d,i.c] ((reference i htv K outer).P slot) ∧ InBox ![i.a,i.d,i.c] ((reference i htv K outer).Q slot) := by
  have h := PlayerSpecificAlgebraicNestedFirstReference.endpoints_box i htv (i.location (dyadicMidpointSample K outer))
    (i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩)
  exact property i htv K outer (InBox ![i.a,i.d,i.c]) (fun slot => ⟨h.1 slot,h.2 slot⟩)

end Blotto.PlayerSpecificAlgebraicNestedFirstProfile
