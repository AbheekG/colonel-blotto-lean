import Blotto.PlayerSpecificAlgebraicFourReflectedTerminal

/-! Actual reflected branch: two fresh resource coin blocks, the reached
nested draw, coordinate restoration, reflection and a literal zero last row. -/
namespace Blotto.PlayerSpecificAlgebraicFourReflectedDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((2*H)+((17*H+K)+K)) → Bool) : FixedArrayTable 4 Data :=
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a
  let resourceBits := firstBitBlock (2*H) ((17*H+K)+K) bits
  let innerBits := secondBitBlock (2*H) ((17*H+K)+K) bits
  let state := PlayerSpecificFiniteResourceLoop.draw p.resources true H resourceBits
  let terminal := PlayerSpecificAlgebraicFourReflectedTerminal.input p state.1
  let y := PlayerSpecificAlgebraicNestedTerminalDraw.draw RationalCostModel.schoolbook r.root terminal H K innerBits
  PlayerSpecificAlgebraicReflectAppend.reflect r.root p.long y

theorem every_path (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) (bits : Fin ((2*H)+((17*H+K)+K)) → Bool) :
    FullBudget i.B (values (draw r a H K bits) x) := by
  let resourceBits := firstBitBlock (2*H) ((17*H+K)+K) bits
  let innerBits := secondBitBlock (2*H) ((17*H+K)+K) bits
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a
  let state := PlayerSpecificAlgebraicFourReflectedPath.draw r a H resourceBits
  let terminal := PlayerSpecificAlgebraicFourReflectedTerminal.input p state.1
  have hr := PlayerSpecificAlgebraicFourReflectedPath.contract r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H resourceBits
  let target := (i.reflectedResourceSystem hcase).terminal (PlayerSpecificAlgebraicResourceState.eval state.1 x) hr.2.1
  have ht := PlayerSpecificAlgebraicFourReflectedTerminal.values r a i hm hirr hv x hx ha T hfit hcase state.1 hr.2.1
  have hf := PlayerSpecificAlgebraicFourReflectedTerminal.fits r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H resourceBits
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 16 T
  let y := PlayerSpecificAlgebraicNestedTerminalDraw.draw RationalCostModel.schoolbook r.root terminal H K innerBits
  have hy := PlayerSpecificAlgebraicNestedTerminalDraw.every_path RationalCostModel.schoolbook r.root terminal target
    hm hirr hv x hx ht (iterate 16 T) hf hml (mono hmT hi) (hT.trans hi) H K innerBits
  have hl : values p.long x=i.originalLengths := by
    funext j
    exact PlayerSpecificAlgebraicFourReflectedInput.original_value a i x ha j
  have hsum : ∑ j,i.originalLengths j=i.B+i.reflectedBudget := by
    rw [i.originalLengths_sum,(i.reflected_budget_bounds hcase).2]
    ring
  change FullBudget i.B (values (PlayerSpecificAlgebraicReflectAppend.reflect r.root p.long y) x)
  rw [PlayerSpecificAlgebraicReflectAppend.value r.root p.long y x hx.1,hl]
  exact reflectAppend_fullBudget hsum hy.1 hy.2

def height (T K : ℕ) : ℕ := step (PlayerSpecificAlgebraicNestedInteriorDraw.height (iterate 17 T) K)
def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)*
  PlayerSpecificAlgebraicNestedInteriorLinear.coefficient*((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^17+1)

theorem inner_profile (A T K S : ℕ) (h : S+1 ≤ A*(T+1)) : S+K+1 ≤ (A+1)*(T+K+1) := by
  have hn := Nat.zero_le (A*K)
  nlinarith only [h,hn,Nat.zero_le T,Nat.zero_le K]

theorem height_linear (T K : ℕ) : height T K+1 ≤ coefficient*(T+K+1) := by
  have hi := inner_profile _ T K _ (iterate_bound 17 T)
  have hn := PlayerSpecificAlgebraicNestedInteriorLinear.height_linear (iterate 17 T) K
  have ho := iterate_bound 1 (PlayerSpecificAlgebraicNestedInteriorDraw.height (iterate 17 T) K)
  have he := hn.trans (Nat.mul_le_mul_left PlayerSpecificAlgebraicNestedInteriorLinear.coefficient hi)
  exact ho.trans (by simpa only [coefficient,mul_assoc,pow_one] using
    Nat.mul_le_mul_left (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1) he)

theorem bounds (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) (bits : Fin ((2*H)+((17*H+K)+K)) → Bool) :
    ∀ j,Reduced r.root.polynomial ((draw r a H K bits).read j) ∧ HasHeight ((draw r a H K bits).read j) (height T K) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let resourceBits := firstBitBlock (2*H) ((17*H+K)+K) bits
  let innerBits := secondBitBlock (2*H) ((17*H+K)+K) bits
  let p := PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a
  let state := PlayerSpecificAlgebraicFourReflectedPath.draw r a H resourceBits
  let terminal := PlayerSpecificAlgebraicFourReflectedTerminal.input p state.1
  let y := PlayerSpecificAlgebraicNestedTerminalDraw.draw RationalCostModel.schoolbook r.root terminal H K innerBits
  have hf := PlayerSpecificAlgebraicFourReflectedTerminal.fits r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H resourceBits
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 16 T
  have hy := PlayerSpecificAlgebraicNestedTerminalDraw.bounds RationalCostModel.schoolbook r.root terminal (iterate 16 T) hf
    hm hm0 hml (mono hmT hi) (hT.trans hi) H K innerBits
  have hp := PlayerSpecificAlgebraicFourReflectedSizes.bounds RationalCostModel.schoolbook r a T hfit hm hm0 hml hmT hT
  have hbase := PlayerSpecificAlgebraicNestedInteriorSizes.input_le (iterate 17 T) K
  have hwide : iterate 17 T ≤ PlayerSpecificAlgebraicNestedInteriorDraw.height (iterate 17 T) K :=
    hbase.trans ((show PlayerSpecificAlgebraicNestedInteriorSizes.height (iterate 17 T) K ≤
      PlayerSpecificAlgebraicNestedInteriorSizes.height (iterate 17 T) K+2*K+6 by omega).trans
      (PlayerSpecificAlgebraicExpressionBudget.initial_le 3 _))
  have hlong := (PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15 ≤ 17)).trans hwide
  exact PlayerSpecificAlgebraicReflectAppend.bounds r.root p.long y _ hm hm0
    (fun j => ⟨(hp.1 j).1,mono (hp.1 j).2 hlong⟩) hy

theorem last_zero (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((2*H)+((17*H+K)+K)) → Bool) : (draw r a H K bits).read 3=[] := by
  simp only [draw,PlayerSpecificAlgebraicReflectAppend.reflect,FixedArrayTable.read_ofFn]
  rfl

theorem random_bit_budget (N H K : ℕ) : (2*H)+((17*H+K)+K) ≤ (N+1000)*H+2*K := by
  have h := Nat.mul_le_mul_right H (show 19 ≤ N+1000 by omega)
  omega

end Blotto.PlayerSpecificAlgebraicFourReflectedDraw
