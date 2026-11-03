import Blotto.PlayerSpecificAlgebraicSegmentSample

/-! Interpolation has fixed arithmetic depth even when its endpoints are
irrational. The bound includes the actual rational midpoint/complement. -/
namespace Blotto.PlayerSpecificAlgebraicSegmentHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem interpolation {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (slot : Fin slots)
    (q : ℚ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (T : ℕ) (hT : 1≤T) (hmT : HasHeight root.polynomial T)
    (hq : RationalHeight q T) (hcomp : RationalHeight (1-q) T)
    (hP : ∀ j,Reduced root.polynomial ((d.first.read slot).read j) ∧ HasHeight ((d.first.read slot).read j) T)
    (hQ : ∀ j,Reduced root.polynomial ((d.second.read slot).read j) ∧ HasHeight ((d.second.read slot).read j) T) :
    ∀ j,HasHeight ((interpolate root d slot q).read j) (iterate 3 T) := by
  let a:=PlayerSpecificAlgebraicField.constant root.polynomial (1-q)
  let b:=PlayerSpecificAlgebraicField.constant root.polynomial q
  have ha:=constant_height root.polynomial (1-q) T hmT hcomp hT hml
  have hb:=constant_height root.polynomial q T hmT hq hT hml
  have har : Reduced root.polynomial a := PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
  have hbr : Reduced root.polynomial b := PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
  have hinc : T≤step T := (Nat.le_succ _).trans (large T)
  intro j
  have hp:=times_height root.polynomial a ((d.first.read slot).read j) (step T) hm hm0 hml har (hP j).1
    (mono hmT hinc) ha (mono (hP j).2 hinc)
  have hq':=times_height root.polynomial b ((d.second.read slot).read j) (step T) hm hm0 hml hbr (hQ j).1
    (mono hmT hinc) hb (mono (hQ j).2 hinc)
  have hsum:=PlayerSpecificShortReduction.plus_height root.polynomial _ _ hm hm0
    (PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0) (PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0)
    (step (step T)) (step (step T)) hp hq'
  have hc : step (step T)+step (step T)+1≤step (step (step T)) := by
    have h:=calibrate 3 (step (step T)) (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  simp only [interpolate,FixedArrayTable.read_ofFn]
  exact mono hsum hc

theorem sample {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots)
    (fallback : Fin slots) (H K : ℕ) (bits : Fin ((slots-1)*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (T : ℕ) (hmT : HasHeight root.polynomial T)
    (hP : ∀ slot j,Reduced root.polynomial ((d.first.read slot).read j) ∧ HasHeight ((d.first.read slot).read j) T)
    (hQ : ∀ slot j,Reduced root.polynomial ((d.second.read slot).read j) ∧ HasHeight ((d.second.read slot).read j) T) :
    ∀ j,HasHeight ((PlayerSpecificAlgebraicSegmentSample.sample model root d fallback H K bits).read j)
      (iterate 3 (T+2*K+6)) := by
  let scalar:=secondBitBlock ((slots-1)*H) K bits
  have hq:=dyadicMidpointSample_height K scalar
  have hc:=((one_height.mono (show 1≤K+2 by omega)).sub hq)
  have hinc : T≤T+2*K+6 := by omega
  apply interpolation root d _ _ hm hm0 hml (T+2*K+6) (by omega) (mono hmT hinc)
  · exact hq.mono (by omega)
  · exact hc.mono (by omega)
  · intro j; exact ⟨(hP _ j).1,mono (hP _ j).2 hinc⟩
  · intro j; exact ⟨(hQ _ j).1,mono (hQ _ j).2 hinc⟩

end Blotto.PlayerSpecificAlgebraicSegmentHeights
