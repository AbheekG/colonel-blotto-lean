import Blotto.PlayerSpecificAlgebraicInitialPrimitiveCost

/-! Proof-only names for cached initial-data stages. Every actual row
has one common fixed-depth polynomial height envelope; these views are
never called by the executing routine. -/
namespace Blotto.PlayerSpecificAlgebraicInitialStages
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicInitial
set_option autoImplicit false
set_option maxHeartbeats 2500000

def quotient (model : RationalCostModel) (root : Candidate) (v w : ℚ) : Data :=
  if low model root v w then PlayerSpecificAlgebraicField.divide root.polynomial
    (PlayerSpecificAlgebraicField.constant root.polynomial v) (weighted root w) else
    PlayerSpecificAlgebraicField.divide root.polynomial (weighted root w) (PlayerSpecificAlgebraicField.constant root.polynomial v)
def Bounded (m : Data) (H : ℕ) (a : Data) : Prop := Reduced m a ∧ HasHeight a H

structure Bounds (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) (G : ℕ) : Prop where
  first : Bounded root.polynomial G (PlayerSpecificAlgebraicField.constant root.polynomial v)
  second : Bounded root.polynomial G (weighted root w)
  unit : Bounded root.polynomial G (PlayerSpecificAlgebraicField.constant root.polynomial 1)
  quotient : Bounded root.polynomial G (quotient model root v w)
  numerator : Bounded root.polynomial G (PlayerSpecificAlgebraicInitial.numerator model root v w)
  probabilityA : Bounded root.polynomial G (PlayerSpecificAlgebraicInitial.probabilityA model root v w)
  probabilityB : Bounded root.polynomial G (PlayerSpecificAlgebraicInitial.probabilityB model root v w)
  length : Bounded root.polynomial G (PlayerSpecificAlgebraicInitial.run model root inverseScale v w).length
  initialA : Bounded root.polynomial G (PlayerSpecificAlgebraicInitial.run model root inverseScale v w).initialA
  initialB : Bounded root.polynomial G (PlayerSpecificAlgebraicInitial.run model root inverseScale v w).initialB

theorem step_bounds (H : ℕ) : PlayerSpecificAlgebraicHeightEnvelope.step H≤PlayerSpecificAlgebraicInitialHeights.height H ∧
    PlayerSpecificAlgebraicHeightEnvelope.step (PlayerSpecificAlgebraicHeightEnvelope.step H)≤PlayerSpecificAlgebraicInitialHeights.height H := by
  have h2:=PlayerSpecificAlgebraicHeightEnvelope.large (PlayerSpecificAlgebraicHeightEnvelope.step H)
  have h3:=PlayerSpecificAlgebraicHeightEnvelope.large (PlayerSpecificAlgebraicHeightEnvelope.step (PlayerSpecificAlgebraicHeightEnvelope.step H))
  simp only [PlayerSpecificAlgebraicInitialHeights.height,PlayerSpecificAlgebraicHeightEnvelope.iterate]
  omega

theorem bounds (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hv : RationalHeight v H) (hw : RationalHeight w H) (hH : 1≤H)
    (hinv : Reduced root.polynomial inverseScale) (hinvH : HasHeight inverseScale (PlayerSpecificAlgebraicHeightEnvelope.step H)) :
    Bounds model root inverseScale v w (PlayerSpecificAlgebraicInitialHeights.height H) := by
  have hs:=step_bounds H
  have hf:=PlayerSpecificAlgebraicHeightEnvelope.constant_height root.polynomial v H hmH hv hH hml
  have hsecond:=PlayerSpecificAlgebraicHeightEnvelope.reduce_height root.polynomial [0,w] H hmH
    (cons_height (zero_height.mono hH) (cons_height hw (nil_height _))) hH hml (by simp)
  have hunit:=PlayerSpecificAlgebraicHeightEnvelope.constant_height root.polynomial 1 H hmH (one_height.mono hH) hH hml
  have hp:=PlayerSpecificAlgebraicInitialHeights.component_heights model root v w H hm hm0 hml hmH hv hw hH
  have hr:=PlayerSpecificAlgebraicInitialHeights.result_heights model root inverseScale v w H hm hm0 hml hmH hv hw hH hinv hinvH
  have hred:=PlayerSpecificAlgebraicInitial.reduced_result model root inverseScale v w hm hm0
  constructor
  · exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,mono hf hs.1⟩
  · exact ⟨weighted_reduced root w hm hm0,mono hsecond hs.1⟩
  · exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,mono hunit hs.1⟩
  · constructor
    · simp only [quotient]; split <;> exact PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0
    · by_cases h : low model root v w=true
      · have he : quotient model root v w=PlayerSpecificAlgebraicInitial.probabilityA model root v w := by
          simp only [quotient,PlayerSpecificAlgebraicInitial.probabilityA,h,ite_true]
        rw [he]; exact mono hp.2.1 hs.2
      · have he : quotient model root v w=PlayerSpecificAlgebraicInitial.probabilityB model root v w := by
          simp only [quotient,PlayerSpecificAlgebraicInitial.probabilityB,h,Bool.false_eq_true,ite_false]
        rw [he]; exact mono hp.2.2 hs.2
  · refine ⟨?_,mono hp.1 hs.1⟩
    simp only [PlayerSpecificAlgebraicInitial.numerator]; split
    · exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
    · exact weighted_reduced root w hm hm0
  · refine ⟨?_,mono hp.2.1 hs.2⟩
    simp only [PlayerSpecificAlgebraicInitial.probabilityA]; split
    · exact PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0
    · exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
  · refine ⟨?_,mono hp.2.2 hs.2⟩
    simp only [PlayerSpecificAlgebraicInitial.probabilityB]; split
    · exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
    · exact PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0
  · exact ⟨hred.1,hr.1⟩
  · exact ⟨hred.2.1,hr.2.1⟩
  · exact ⟨hred.2.2,hr.2.2⟩

end Blotto.PlayerSpecificAlgebraicInitialStages
