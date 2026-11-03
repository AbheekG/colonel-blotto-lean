import Blotto.GeneralPaperAffineCandidateStorage

/-! One actual native candidate pair: both expression constructions, full
temporary predecessor witnesses, guarded crossing arithmetic, retained root
and encoded parent counters. Field/table owners are separate caller joins. -/
namespace Blotto.GeneralPaperAffineCandidatePairStorage
open GeneralPaperEncodedScalarStorage GeneralPaperAffineWitnessStorage GeneralPaperRayAffine
open GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def window {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) (a b : Fin K) : ℕ :=
  let options := GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s
  let first := options a
  let second := options b
  let root := GeneralPaperAffineCrossingPrice.optionalRun model.rat W first.1 second.1
  let result := GeneralPaperCrossingPairsPrice.pairRun model.rat W options a b
  GeneralPaperAffineCandidateStorage.expressionWindow model W field previous s a+
    GeneralPaperAffineCandidateStorage.expressionWindow model W field previous s b+
    GeneralPaperAffineArithmeticStorage.optionalWindow model W first.1 second.1+
    GeneralPaperAffineArithmeticStorage.rootFoot W result.1+
    fields W [first.2,second.2,root.2,result.2,first.2+second.2,first.2+second.2+root.2,16*W]+256*W

def metadataCap (model : RationalCostModel) (W R : ℕ) : ℕ := 1+296*W+17*model.rat (1+2*R)
def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  2*GeneralPaperAffineCandidateStorage.expressionProfile model W m K S R+
    GeneralPaperAffineArithmeticStorage.optionalProfile model W R+GeneralPaperAffineArithmeticStorage.rootProfile W R+
    7*(natBits (metadataCap model W R)+W)+288*W

theorem bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S)
    (s : Fin (S+1)) (a b : Fin K) :
    window model W field previous s a b≤profile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let A := interceptCap m X P
  let B := slopeCap m V
  let options := GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s
  let first := options a
  let second := options b
  let root := GeneralPaperAffineCrossingPrice.optionalRun model.rat W first.1 second.1
  let result := GeneralPaperCrossingPairsPrice.pairRun model.rat W options a b
  have hCaps (l : Fin K) (f : Affine) (hh : (options l).1=some f) : GeneralPaperRayAffineBound.Bounded D E A B f :=
    GeneralPaperAffineCandidateStorage.expression_caps model.rat W D E m X V P n hn field previous hf hp s l f hh
  have hFirst := GeneralPaperAffineCandidateStorage.expression_bounded model W D E m X V P n hD hE hn field previous hf hp hScores s a
  have hSecond := GeneralPaperAffineCandidateStorage.expression_bounded model W D E m X V P n hD hE hn field previous hf hp hScores s b
  change GeneralPaperAffineCandidateStorage.expressionWindow model W field previous s a≤GeneralPaperAffineCandidateStorage.expressionProfile model W m K S R at hFirst
  change GeneralPaperAffineCandidateStorage.expressionWindow model W field previous s b≤GeneralPaperAffineCandidateStorage.expressionProfile model W m K S R at hSecond
  have hCross := GeneralPaperAffineArithmeticStorage.optional_bounded model W D E A B R hD hE le_rfl first.1 second.1 (hCaps a) (hCaps b)
  have hRoot := GeneralPaperAffineArithmeticStorage.root_bound W R result.1 (by
    intro t ht
    rw [GeneralPaperCrossingPairsPrice.pair_data] at ht
    exact GeneralPaperRayCrossingSize.optional hD hE first.1 second.1 (hCaps a) (hCaps b) t ht)
  have hA := GeneralPaperAffineCandidateStorage.expression_work model W D E m X V P n hD hE hn field previous hf hp s a
  have hB := GeneralPaperAffineCandidateStorage.expression_work model W D E m X V P n hD hE hn field previous hf hp s b
  have hC := GeneralPaperAffineCrossingPrice.optional_work model.rat model.monotone W D E A B R hD hE le_rfl first.1 second.1 (hCaps a) (hCaps b)
  change first.2≤104*W+4*model.rat (1+2*R) at hA
  change second.2≤104*W+4*model.rat (1+2*R) at hB
  change root.2≤72*W+9*model.rat (1+2*R) at hC
  have hShape : result.2=first.2+second.2+root.2+16*W := rfl
  have hFields := fields_bound W (natBits (metadataCap model W R))
    [first.2,second.2,root.2,result.2,first.2+second.2,first.2+second.2+root.2,16*W] (by
      intro t ht
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap model W R)+W)+32*W at hFields
  change GeneralPaperAffineCandidateStorage.expressionWindow model W field previous s a+
    GeneralPaperAffineCandidateStorage.expressionWindow model W field previous s b+
    GeneralPaperAffineArithmeticStorage.optionalWindow model W first.1 second.1+GeneralPaperAffineArithmeticStorage.rootFoot W result.1+
    GeneralPaperEncodedScalarStorage.fields W [first.2,second.2,root.2,result.2,first.2+second.2,first.2+second.2+root.2,16*W]+256*W≤profile model W m K S R
  unfold profile
  omega

end Blotto.GeneralPaperAffineCandidatePairStorage
