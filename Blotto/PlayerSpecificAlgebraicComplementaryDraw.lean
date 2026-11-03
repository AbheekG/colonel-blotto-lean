import Blotto.PlayerSpecificAlgebraicFourSpecDraw

/-! The two-uniform-group terminal case uses one midpoint and an exact
complement. Two unused group/mixture coordinates are literal zero rows. -/
namespace Blotto.PlayerSpecificAlgebraicComplementaryDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (root : Candidate) (budget : Data) (K : ℕ) (bits : Fin K → Bool) : FixedArrayTable 4 Data :=
  let q := PlayerSpecificAlgebraicField.constant root.polynomial (dyadicMidpointSample K bits)
  let first := PlayerSpecificAlgebraicField.times root.polynomial budget q
  let second := PlayerSpecificAlgebraicField.minus root.polynomial budget first
  FixedArrayTable.ofFn ![first,second,[],[]]

noncomputable def point (B q : ℝ) : Allocation 4 := ![B*q,B*(1-q),0,0]

theorem value (root : Candidate) (budget : Data) (K : ℕ) (bits : Fin K → Bool) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) :
    values (draw root budget K bits) x=point (realEvaluate budget x) (dyadicMidpointSample K bits) := by
  have hz : realEvaluate [] x=0 := rfl
  funext j
  fin_cases j <;> simp [draw,values,point,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicField.times_value _ _ _ x hx,PlayerSpecificAlgebraicField.minus_value _ _ _ x hx,
    PlayerSpecificAlgebraicField.constant_value _ _ x hx,hz]
  ring

theorem point_budget (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q ∧ q ≤ 1) : FullBudget B (point B q) := by
  constructor
  · intro j
    fin_cases j
    · exact mul_nonneg hB hq.1
    · exact mul_nonneg hB (sub_nonneg.mpr hq.2)
    · exact le_rfl
    · exact le_rfl
  · simp [point,Fin.sum_univ_succ]
    ring

theorem every_path (root : Candidate) (budget : Data) (K : ℕ) (bits : Fin K → Bool) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (hB : 0 ≤ realEvaluate budget x) :
    FullBudget (realEvaluate budget x) (values (draw root budget K bits) x) := by
  rw [value root budget K bits x hx]
  exact point_budget _ _ hB ⟨(dyadicMidpointSample_bounds K bits).1.le,(dyadicMidpointSample_bounds K bits).2.le⟩

def height (T K : ℕ) : ℕ := iterate 3 (T+K+3)

theorem bounds (root : Candidate) (budget : Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hB : Reduced root.polynomial budget ∧ HasHeight budget T)
    (K : ℕ) (bits : Fin K → Bool) :
    ∀ j,Reduced root.polynomial ((draw root budget K bits).read j) ∧ HasHeight ((draw root budget K bits).read j) (height T K) := by
  let G := T+K+3
  let q := PlayerSpecificAlgebraicField.constant root.polynomial (dyadicMidpointSample K bits)
  let first := PlayerSpecificAlgebraicField.times root.polynomial budget q
  have hTG : T ≤ G := by dsimp [G]; omega
  have hroot := mono hmT hTG
  have hq := PlayerSpecificAlgebraicField.constant_reduced root.polynomial (dyadicMidpointSample K bits) hm hm0
  have hqh := constant_height root.polynomial _ G hroot
    ((dyadicMidpointSample_height K bits).mono (by dsimp [G]; omega)) (by dsimp [G]; omega) hml
  have hG1 : G ≤ step G := (Nat.le_succ _).trans (large G)
  have hG2 := PlayerSpecificAlgebraicExpressionBudget.initial_le 2 G
  have hG3 := PlayerSpecificAlgebraicExpressionBudget.initial_le 3 G
  have hfirst := PlayerSpecificAlgebraicField.times_reduced root.polynomial budget q hm hm0
  have hfirsth := times_height root.polynomial budget q (step G) hm hm0 hml hB.1 hq
    (mono hroot hG1) (mono hB.2 (hTG.trans hG1)) hqh
  have hsecond := PlayerSpecificAlgebraicField.minus_reduced root.polynomial budget first hm hm0
  have hsecondh := (PlayerSpecificAlgebraicExpressionBudget.binary_heights RationalCostModel.schoolbook root budget first (iterate 2 G)
    hm hm0 hml hB.1 hfirst (mono hroot hG2) (mono hB.2 (hTG.trans hG2)) hfirsth
    ((show 1 ≤ G by dsimp [G]; omega).trans hG2)).2.1
  intro j
  fin_cases j <;> simp only [draw,FixedArrayTable.read_ofFn]
  · exact ⟨hfirst,mono hfirsth (PlayerSpecificAlgebraicExpressionBudget.fuel_mono G (by omega : 2 ≤ 3))⟩
  · exact ⟨hsecond,hsecondh⟩
  · exact ⟨nil_reduced _ hm0,nil_height _⟩
  · exact ⟨nil_reduced _ hm0,nil_height _⟩

theorem height_linear (T K : ℕ) : height T K+1 ≤ (4*(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3)*(T+K+1) := by
  have h := iterate_bound 3 (T+K+3)
  have he : T+K+3+1 ≤ 4*(T+K+1) := by omega
  exact h.trans (by simpa only [mul_assoc,mul_left_comm] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3) he)

end Blotto.PlayerSpecificAlgebraicComplementaryDraw
