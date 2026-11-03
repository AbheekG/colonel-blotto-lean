import Blotto.PlayerSpecificAlgebraicPathContract
import Blotto.DyadicMidpointLaw
import Blotto.DyadicMidpointHeight

/-! An actual bounded fair-bit block chooses a branch by an exact
retained-root sign comparison. Equality at a midpoint chooses false. -/
namespace Blotto.PlayerSpecificAlgebraicMidpointCoin
open MeasureTheory Set
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ) (bits : Fin H → Bool) : Bool :=
  !PlayerSpecificAlgebraicPairStep.le model root probability [dyadicMidpointSample H bits]

theorem correct (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ) (bits : Fin H → Bool)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    run model root probability H bits=true ↔ (dyadicMidpointSample H bits:ℝ)<realEvaluate probability x := by
  simp only [run,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
    PlayerSpecificAlgebraicPairStep.le_correct model root probability _ hm hirr hv x hx,not_le]
  simp only [realEvaluate,List.foldr_cons,List.foldr_nil,mul_zero,add_zero]

noncomputable def success (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ) : ℝ :=
  (fairBitLaw H : Measure (Fin H → Bool)).real {bits | run model root probability H bits=true}

theorem success_eq (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    success model root probability H=(dyadicMidpointLaw H : Measure ℝ).real (Iio (realEvaluate probability x)) := by
  have he : {bits | run model root probability H bits=true}=
      (fun bits => (dyadicMidpointSample H bits:ℝ)) ⁻¹' Iio (realEvaluate probability x) := by
    ext bits
    exact correct model root probability H bits hm hirr hv x hx
  unfold success
  rw [he]
  exact (map_measureReal_apply (measurable_of_countable _) measurableSet_Iio).symm

theorem discrepancy (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hp : 0≤realEvaluate probability x ∧ realEvaluate probability x≤1) :
    |success model root probability H-realEvaluate probability x|≤1/(2*(2:ℝ)^H) := by
  rw [success_eq model root probability H hm hirr hv x hx]
  have h:=(dyadicMidpointLaw_CDF_error H).strict (realEvaluate probability x)
  simpa only [unitUniform_strictCDF,min_eq_left hp.2,max_eq_left hp.1] using h

theorem paper_discrepancy (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hp : 0≤realEvaluate probability x ∧ realEvaluate probability x≤1) :
    |success model root probability H-realEvaluate probability x|≤1/(2:ℝ)^H := by
  apply (discrepancy model root probability H hm hirr hv x hx hp).trans
  apply one_div_le_one_div_of_le
  · positivity
  · have h : 0≤(2:ℝ)^H := by positivity
    linarith

end Blotto.PlayerSpecificAlgebraicMidpointCoin
