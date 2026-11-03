import Blotto.PlayerSpecificAlgebraicDescriptorBinary

/-! Binary assembly has three fixed coefficient-height layers. Added
zero-weight slots and endpoint copies do not amplify input heights. -/
namespace Blotto.PlayerSpecificAlgebraicDescriptorBinarySizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bounds {N k m : ℕ} (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 1≤T)
    (hp : Reduced root.polynomial p ∧ HasHeight p T) (hl : Bounds root l T) (hr : Bounds root r T) :
    Bounds root (PlayerSpecificAlgebraicDescriptorBinary.binary root p l r) (iterate 3 T) := by
  have hbase : T≤step T := (Nat.le_succ _).trans (large T)
  have hT2 : T≤step (step T) := PlayerSpecificAlgebraicExpressionBudget.initial_le 2 T
  have hT3 : T≤ iterate 3 T := PlayerSpecificAlgebraicExpressionBudget.initial_le 3 T
  have hone:=constant_height root.polynomial 1 T hmT (one_height.mono hT) hT hml
  have hcomp:=PlayerSpecificShortReduction.minus_height root.polynomial _ p hm hm0
    (PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0) hp.1 (step T) (step T) hone (mono hp.2 hbase)
  have hshort : step T+step T+1≤step (step T) := by
    have h:=calibrate 3 (step T) (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  constructor
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j
      simp only [PlayerSpecificAlgebraicDescriptorBinary.binary,FixedArrayTable.read_ofFn,Fin.addCases_left]
      exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
        times_height root.polynomial p (l.weights.read j) (step (step T)) hm hm0 hml hp.1 (hl.weights j).1
          (mono hmT hT2) (mono hp.2 hT2) (mono (hl.weights j).2 hT2)⟩
    · intro j
      simp only [PlayerSpecificAlgebraicDescriptorBinary.binary,FixedArrayTable.read_ofFn,Fin.addCases_right]
      exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
        times_height root.polynomial _ (r.weights.read j) (step (step T)) hm hm0 hml
          (PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0) (hr.weights j).1
          (mono hmT hT2) (mono hcomp hshort) (mono (hr.weights j).2 hT2)⟩
  · intro slot j
    refine Fin.addCases ?_ ?_ slot
    · intro slot
      simpa only [PlayerSpecificAlgebraicDescriptorBinary.binary,FixedArrayTable.read_ofFn,Fin.addCases_left] using
        And.intro (hl.first slot j).1 (mono (hl.first slot j).2 hT3)
    · intro slot
      simpa only [PlayerSpecificAlgebraicDescriptorBinary.binary,FixedArrayTable.read_ofFn,Fin.addCases_right] using
        And.intro (hr.first slot j).1 (mono (hr.first slot j).2 hT3)
  · intro slot j
    refine Fin.addCases ?_ ?_ slot
    · intro slot
      simpa only [PlayerSpecificAlgebraicDescriptorBinary.binary,FixedArrayTable.read_ofFn,Fin.addCases_left] using
        And.intro (hl.second slot j).1 (mono (hl.second slot j).2 hT3)
    · intro slot
      simpa only [PlayerSpecificAlgebraicDescriptorBinary.binary,FixedArrayTable.read_ofFn,Fin.addCases_right] using
        And.intro (hr.second slot j).1 (mono (hr.second slot j).2 hT3)

end Blotto.PlayerSpecificAlgebraicDescriptorBinarySizes
