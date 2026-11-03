import Blotto.GeneralPaperCircleArcMetadata

/-! The linear sweep's ordered metadata and prefix range premises come
from the native builder, not a supplied arc oracle. Actual retained light
weights provide the positive mass and conservation in the original join. -/
namespace Blotto.GeneralPaperCircleMetadataSweep
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem advances (price : ℕ → ℕ) (A R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (weights : List ℕ) (hs : weights.sum=W) :
    (GeneralPaperCircleCursorSweep.run R W t (GeneralPaperCircleArcMetadata.run price A R weights 0).1.arcs 0 (2*W)).advances<2*R := by
  apply GeneralPaperCircleCursorSweep.total_advances R W t hR hW ht
  · intro arc hm
    have h := GeneralPaperCircleArcMetadata.ranges price A R weights 0 arc hm
    simpa only [GeneralPaperCircleArcMetadata.total,hs,Nat.zero_add] using h
  · exact GeneralPaperCircleArcMetadata.ordered price A R weights 0

theorem work (price : ℕ → ℕ) (A R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (weights : List ℕ) (hs : weights.sum=W) :
    (GeneralPaperCircleCursorSweep.run R W t (GeneralPaperCircleArcMetadata.run price A R weights 0).1.arcs 0 (2*W)).work≤
      24*R+36*weights.length+4 := by
  have h := GeneralPaperCircleCursorSweep.linear_work R W t hR hW ht
    (GeneralPaperCircleArcMetadata.run price A R weights 0).1.arcs
    (fun arc hm => by
      have h := GeneralPaperCircleArcMetadata.ranges price A R weights 0 arc hm
      simpa only [GeneralPaperCircleArcMetadata.total,hs,Nat.zero_add] using h)
    (GeneralPaperCircleArcMetadata.ordered price A R weights 0)
  simpa only [GeneralPaperCircleArcMetadata.length] using h

theorem original_advances {n : ℕ} (bits : Bool) (model : RationalCostModel) (A k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model A k input).1.replaced=true)
    (shift : ℕ) (hShift : shift<(GeneralPaperOriginalValueReduction.run bits model A k input).1.representatives*
      (GeneralPaperOriginalValueReduction.run bits model A k input).1.classified.lightWeight) :
    let o := (GeneralPaperOriginalValueReduction.run bits model A k input).1
    let weights := List.ofFn (GeneralPaperCircleActualWeights.weights o)
    let metadata := GeneralPaperCircleArcMetadata.run (if bits then model.rat else fun _ => 1) A o.representatives weights 0
    (GeneralPaperCircleCursorSweep.run o.representatives o.classified.lightWeight shift metadata.1.arcs 0
      (2*o.classified.lightWeight)).advances<2*o.representatives := by
  dsimp only
  have hs : (List.ofFn (GeneralPaperCircleActualWeights.weights (GeneralPaperOriginalValueReduction.run bits model A k input).1)).sum=
      (GeneralPaperOriginalValueReduction.run bits model A k input).1.classified.lightWeight := by
    rw [List.sum_ofFn]
    exact GeneralPaperCircleActualWeights.original_sum bits model A k input
  exact advances _ A _ _ shift (GeneralPaperNativeCircleLoss.original_representatives_positive bits model A k input)
    (GeneralPaperCircleActualWeights.original_total_positive bits model A k input v hv
      (GeneralPaperNativeCircleLoss.original_light_positive bits model A k input hReplace)) hShift _ hs

end Blotto.GeneralPaperCircleMetadataSweep
