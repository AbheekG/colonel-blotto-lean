import Blotto.PlayerSpecificAlgebraicNestedInputTools

/-! Actual first-case nested sampling: one outer K-bit midpoint enters
the algebraic location formula, followed by the reached conditional table
and its fresh bounded coin/midpoint blocks. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFirstDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def location (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Data :=
  scalar model root a (PlayerSpecificAlgebraicField.constant root.polynomial (dyadicMidpointSample K outer)) 0

def draw (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin ((8*H+K)+K) → Bool) : FixedArrayTable 3 Data :=
  let outer:=secondBitBlock (8*H+K) K bits
  let s:=location model root a K outer
  let table:=PlayerSpecificAlgebraicNestedFirstTable.prepare model root a s
  PlayerSpecificAlgebraicSegmentSample.sample model root table 8 H K (firstBitBlock (8*H+K) K bits)

theorem location_value (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (K : ℕ) (outer : Fin K → Bool) :
    realEvaluate (location model root a K outer) x=i.location (dyadicMidpointSample K outer) := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hq:=PlayerSpecificAlgebraicField.constant_reduced root.polynomial (dyadicMidpointSample K outer) hm hm0
  have henv:=PlayerSpecificAlgebraicNestedInputTools.environment_reduced root a _ T hfit hq
  have he:=scalar_value model root a i hm hirr hv x hx ha _ henv 0
  simpa only [location,RealNestedParametersCode.scalarValues,Matrix.cons_val_zero,
    PlayerSpecificAlgebraicField.constant_value _ _ x hx.1] using he

theorem location_reduced (model : RationalCostModel) (root : Candidate) (a : Input)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (T : ℕ) (hfit : Fits root a T)
    (K : ℕ) (outer : Fin K → Bool) : Reduced root.polynomial (location model root a K outer) := by
  have hq:=PlayerSpecificAlgebraicField.constant_reduced root.polynomial (dyadicMidpointSample K outer) hm hm0
  exact PlayerSpecificAlgebraicExpression.reduced model root _ _ hm hm0
    (PlayerSpecificAlgebraicNestedInputTools.environment_reduced root a _ T hfit hq)

theorem every_path (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (htv : i.t≤ i.v) (H K : ℕ) (bits : Fin ((8*H+K)+K) → Bool) :
    FullBudget i.M (values (draw model root a H K bits) x) ∧ InBox ![i.a,i.d,i.c] (values (draw model root a H K bits) x) := by
  let outer:=secondBitBlock (8*H+K) K bits
  let s:=location model root a K outer
  let table:=PlayerSpecificAlgebraicNestedFirstTable.prepare model root a s
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hloc:=location_value model root a i hm hirr hv x hx ha T hfit K outer
  have hs : 0≤realEvaluate s x ∧ realEvaluate s x≤ i.t := by
    rw [hloc]
    exact i.location_bounds ⟨(dyadicMidpointSample_bounds K outer).1.le,(dyadicMidpointSample_bounds K outer).2.le⟩
  have henv:=PlayerSpecificAlgebraicNestedInputTools.environment_reduced root a s T hfit
    (location_reduced model root a hm hm0 T hfit K outer)
  have href:=PlayerSpecificAlgebraicNestedFirstTable.refines model root a i hm hirr hv x hx ha s henv htv hs
  have hbudget:=PlayerSpecificAlgebraicNestedFirstReference.endpoints_budget i htv (realEvaluate s x) hs
  have hbox:=PlayerSpecificAlgebraicNestedFirstReference.endpoints_box i htv (realEvaluate s x) hs
  exact ⟨PlayerSpecificAlgebraicDescriptorReference.sample_budget model root table 8 H K (firstBitBlock (8*H+K) K bits) x i.M
      _ href hx.1 hbudget.1 hbudget.2,
    PlayerSpecificAlgebraicDescriptorReference.sample_box model root table 8 H K (firstBitBlock (8*H+K) K bits) x ![i.a,i.d,i.c]
      _ href hx.1 hbox.1 hbox.2⟩

theorem random_bit_budget (N H K : ℕ) : (8*H+K)+K≤(N+1000)*H+2*K := by
  have h:=Nat.mul_le_mul_right H (show 8≤N+1000 by omega)
  omega

end Blotto.PlayerSpecificAlgebraicNestedFirstDraw
