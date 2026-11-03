import Blotto.PlayerSpecificAlgebraicInitialCopyCost

/-! The actual one-field initial-data source price joins every numerical
caller and retained copy. Fixed-depth size bounds discharge all stage
height hypotheses from original operands. -/
namespace Blotto.PlayerSpecificAlgebraicInitialCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicInitialStages PlayerSpecificAlgebraicInitialPrimitiveCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

def workCoefficient : ℕ := 33*PlayerSpecificPolynomialSignCost.workCoefficient+11000001000

theorem price_eq (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) :
    (PlayerSpecificAlgebraicInitialExecution.run model root inverseScale v w).2=
      price model (scalar .multiply (-1) w).2+
      (PlayerSpecificPolynomialSignExecution.run model root.polynomial [v,-w] root.interval).2+
      price model (PlayerSpecificFieldCombinationContract.constant root.polynomial v).2+
      price model (PlayerSpecificDivisionExecution.run [0,w] root.polynomial).2+
      price model (PlayerSpecificFieldCombinationContract.constant root.polynomial 1).2+
      (if PlayerSpecificAlgebraicInitial.low model root v w then
        PlayerSpecificFieldDivisionExecution.run model root.polynomial (PlayerSpecificAlgebraicField.constant root.polynomial v) (PlayerSpecificAlgebraicInitial.weighted root w) else
        PlayerSpecificFieldDivisionExecution.run model root.polynomial (PlayerSpecificAlgebraicInitial.weighted root w) (PlayerSpecificAlgebraicField.constant root.polynomial v)).2+
      (PlayerSpecificModularExecution.run model root.polynomial inverseScale (PlayerSpecificAlgebraicInitial.numerator model root v w)).2+
      (PlayerSpecificModularExecution.run model root.polynomial (PlayerSpecificAlgebraicInitial.run model root inverseScale v w).length
        (PlayerSpecificAlgebraicInitial.probabilityA model root v w)).2+
      (PlayerSpecificModularExecution.run model root.polynomial (PlayerSpecificAlgebraicInitial.run model root inverseScale v w).length
        (PlayerSpecificAlgebraicInitial.probabilityB model root v w)).2+
      price model (PlayerSpecificAlgebraicInitialExecution.frame root inverseScale v w
        (PlayerSpecificAlgebraicField.constant root.polynomial v) (PlayerSpecificAlgebraicInitial.weighted root w)
        (PlayerSpecificAlgebraicField.constant root.polynomial 1) (quotient model root v w)
        (PlayerSpecificAlgebraicInitial.run model root inverseScale v w)) := by
  simp only [PlayerSpecificAlgebraicInitialExecution.run,scalar_value,Arithmetic.apply,neg_one_mul,
    PlayerSpecificFieldCombinationContract.constant_value,PlayerSpecificDivisionExecution.value,PlayerSpecificModularExecution.value,
    PlayerSpecificAlgebraicInitial.run,PlayerSpecificAlgebraicInitial.low,PlayerSpecificAlgebraicInitial.weighted,
    PlayerSpecificAlgebraicInitial.numerator,PlayerSpecificAlgebraicInitial.probabilityA,PlayerSpecificAlgebraicInitial.probabilityB,
    quotient,PlayerSpecificAlgebraicField.times,PlayerSpecificAlgebraicReduction.reduce]
  split <;> simp_all only [PlayerSpecificFieldDivisionExecution.value,Bool.false_eq_true,ite_true,ite_false]

theorem source_cost (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) (G : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmG : HasHeight root.polynomial G) (he : HasHeight [root.interval.lo,root.interval.hi] G)
    (hv : RationalHeight v G) (hw : RationalHeight w G) (hG : 1≤G) (hnode : root.interval.lo<root.interval.hi)
    (hi : Bounded root.polynomial G inverseScale) (hs : Bounds model root inverseScale v w G) :
    (PlayerSpecificAlgebraicInitialExecution.run model root inverseScale v w).2≤workCoefficient*(G+1)*model.rat (width G) := by
  have hn:=negative_cost model w G hw hG
  have hsign:=raw_sign_cost model root.polynomial [v,-w] root.interval G hm hm0 hml (by simp) hmG
    (cons_height hv (cons_height hw.neg (nil_height _))) he hnode
  have hf:=constant_cost model root.polynomial v G hm hm0 hml hmG hv hG
  have hsecond:=reduction_cost model root.polynomial [0,w] G hml (by simp) hmG
    (cons_height (zero_height.mono hG) (cons_height hw (nil_height _))) hG
  have hu:=constant_cost model root.polynomial 1 G hm hm0 hml hmG (one_height.mono hG) hG
  have hquotient : (if PlayerSpecificAlgebraicInitial.low model root v w then
      PlayerSpecificFieldDivisionExecution.run model root.polynomial (PlayerSpecificAlgebraicField.constant root.polynomial v) (PlayerSpecificAlgebraicInitial.weighted root w) else
      PlayerSpecificFieldDivisionExecution.run model root.polynomial (PlayerSpecificAlgebraicInitial.weighted root w) (PlayerSpecificAlgebraicField.constant root.polynomial v)).2≤8000000000*model.rat (width G) := by
    split
    · exact division_cost model _ _ _ G hm hm0 hml hs.first.1 hs.second.1 hmG hs.first.2 hs.second.2 hG
    · exact division_cost model _ _ _ G hm hm0 hml hs.second.1 hs.first.1 hmG hs.second.2 hs.first.2 hG
  have hl:=product_cost model root.polynomial inverseScale (PlayerSpecificAlgebraicInitial.numerator model root v w) G
    hm hm0 hml hs.numerator.1 hi.1 hmG hs.numerator.2 hi.2
  have ha:=product_cost model root.polynomial (PlayerSpecificAlgebraicInitial.run model root inverseScale v w).length
    (PlayerSpecificAlgebraicInitial.probabilityA model root v w) G hm hm0 hml hs.probabilityA.1 hs.length.1 hmG hs.probabilityA.2 hs.length.2
  have hb:=product_cost model root.polynomial (PlayerSpecificAlgebraicInitial.run model root inverseScale v w).length
    (PlayerSpecificAlgebraicInitial.probabilityB model root v w) G hm hm0 hml hs.probabilityB.1 hs.length.1 hmG hs.probabilityB.2 hs.length.2
  have hc:=PlayerSpecificAlgebraicInitialCopyCost.frame_cost model root inverseScale v w G hml hmG he hv hw hi hs
  have hunit:=Nat.mul_le_mul_right (model.rat (width G)) (show 1≤G+1 by omega)
  rw [price_eq]
  unfold workCoefficient
  nlinarith only [hn,hsign,hf,hsecond,hu,hquotient,hl,ha,hb,hc,hunit]

theorem fixed_depth_source_cost (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : RationalHeight v H) (hw : RationalHeight w H) (hH : 1≤H) (hnode : root.interval.lo<root.interval.hi)
    (hi : Reduced root.polynomial inverseScale) (hiH : HasHeight inverseScale (PlayerSpecificAlgebraicHeightEnvelope.step H)) :
    (PlayerSpecificAlgebraicInitialExecution.run model root inverseScale v w).2≤
      workCoefficient*(PlayerSpecificAlgebraicInitialHeights.height H+1)*model.rat (width (PlayerSpecificAlgebraicInitialHeights.height H)) := by
  have hbase:=PlayerSpecificInitialPositivePrecision.base_le_height H
  have hstep:=(step_bounds H).1
  exact source_cost model root inverseScale v w _ hm hm0 hml (mono hmH hbase) (mono he hbase)
    (hv.mono hbase) (hw.mono hbase) (by omega) hnode ⟨hi,mono hiH hstep⟩
    (bounds model root inverseScale v w H hm hm0 hml hmH hv hw hH hi hiH)

end Blotto.PlayerSpecificAlgebraicInitialCost
