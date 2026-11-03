import Blotto.PlayerSpecificAlgebraicNestedFirstDraw

/-! The actual first nested draw keeps one fixed global coefficient
height linear in raw-input height and scalar midpoint precision. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFirstDrawSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicNestedInputTools
open PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def base (T K : ℕ) : ℕ := T+K+3
def height (T K : ℕ) : ℕ := iterate 3 (iterate 32 (base T K)+2*K+6)
def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3*
  (4*(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^32+10)

theorem linear_profile (A T K S : ℕ) (h : S+1≤A*(T+K+4)) : S+2*K+6+1≤(4*A+10)*(T+K+1) := by
  have hn:=Nat.zero_le (A*(T+K))
  nlinarith only [h,hn,Nat.zero_le T,Nat.zero_le K]

theorem height_linear (T K : ℕ) : height T K+1≤coefficient*(T+K+1) := by
  have hi:=iterate_bound 32 (base T K)
  have ho:=iterate_bound 3 (iterate 32 (base T K)+2*K+6)
  have he:=linear_profile ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^32) T K _ hi
  exact ho.trans (by simpa only [coefficient,mul_assoc] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3) he)

theorem location_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ)
    (hfit : Fits root a T) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) (K : ℕ) (outer : Fin K → Bool) :
    Reduced root.polynomial (PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer) ∧
      HasHeight (PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer) (iterate 10 (base T K)) := by
  let G:=base T K
  have hTG : T≤G := by dsimp [G,base]; omega
  have hroot:=mono hmT hTG
  have hq:=dyadicMidpointSample_height K outer
  have hqG : RationalHeight (dyadicMidpointSample K outer) G := hq.mono (by dsimp [G,base]; omega)
  have hconst:=constant_height root.polynomial _ G hroot hqG (by dsimp [G,base]; omega) hml
  have hred:=PlayerSpecificAlgebraicField.constant_reduced root.polynomial (dyadicMidpointSample K outer) hm hm0
  have hinc : G≤step G := (Nat.le_succ _).trans (large G)
  have hh:=scalar_bounds model root a (PlayerSpecificAlgebraicField.constant root.polynomial (dyadicMidpointSample K outer))
    (step G) (fits_mono root a T (step G) hfit (hTG.trans hinc)) ⟨hred,hconst⟩ hm hm0 hml
    (mono hroot hinc) (hT.trans (hTG.trans hinc)) 0
  have he : iterate 9 (step G)=iterate 10 G := PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add 9 1 G
  exact ⟨hh.1,he ▸ hh.2⟩

theorem table_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ)
    (hfit : Fits root a T) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) (K : ℕ) (outer : Fin K → Bool) :
    Bounds root (PlayerSpecificAlgebraicNestedFirstTable.prepare model root a
      (PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer)) (iterate 32 (base T K)) := by
  have hl:=location_bounds model root a T hfit hm hm0 hml hmT hT K outer
  have hinc : T≤ iterate 10 (base T K) :=
    (show T≤base T K by unfold base; omega).trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 10 _)
  have hb:=PlayerSpecificAlgebraicNestedFirstSizes.bounds model root a _ (iterate 10 (base T K))
    (fits_mono root a T _ hfit hinc) hl hm hm0 hml (mono hmT hinc) (hT.trans hinc)
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hb
  exact hb

theorem draw_heights (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ)
    (hfit : Fits root a T) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) (H K : ℕ) (bits : Fin ((8*H+K)+K) → Bool) :
    ∀ j,HasHeight ((PlayerSpecificAlgebraicNestedFirstDraw.draw model root a H K bits).read j) (height T K) := by
  let outer:=secondBitBlock (8*H+K) K bits
  let s:=PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer
  let table:=PlayerSpecificAlgebraicNestedFirstTable.prepare model root a s
  have hb:=table_bounds model root a T hfit hm hm0 hml hmT hT K outer
  have hinc : T≤ iterate 32 (base T K) :=
    (show T≤base T K by unfold base; omega).trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 32 _)
  exact PlayerSpecificAlgebraicSegmentHeights.sample model root table 8 H K (firstBitBlock (8*H+K) K bits) hm hm0 hml
    (iterate 32 (base T K)) (mono hmT hinc) hb.first hb.second

end Blotto.PlayerSpecificAlgebraicNestedFirstDrawSizes
