import Blotto.GeneralPaperFinRangeStorage

/-! Actual native ordered-label-pair traversal. One filterMap row and its
enclosing flatMap retain roots/segments and copy prefixes, while the one
active callback uses the checked complete pair-candidate window. -/
namespace Blotto.GeneralPaperCrossingPairStreamStorage
open GeneralPaperRayAffine GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192

def pairPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 296*W+17*model.rat (1+2*R)
def rowPrice (model : RationalCostModel) (W K R : ℕ) : ℕ := (pairPrice model W R+8*W)*K+2*W

theorem pair_work {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) (a b : Fin K) :
    (GeneralPaperCrossingPairsPrice.pairRun model.rat W (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) a b).2≤
      pairPrice model W (width D E m X V P) := by
  let R := width D E m X V P
  let options := GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s
  have hA := GeneralPaperAffineCandidateStorage.expression_work model W D E m X V P n hD hE hn field previous hf hp s a
  have hB := GeneralPaperAffineCandidateStorage.expression_work model W D E m X V P n hD hE hn field previous hf hp s b
  have hC := GeneralPaperAffineCrossingPrice.optional_work model.rat model.monotone W D E (interceptCap m X P) (slopeCap m V) R hD hE le_rfl
    (options a).1 (options b).1
    (GeneralPaperAffineCandidateStorage.expression_caps model.rat W D E m X V P n hn field previous hf hp s a)
    (GeneralPaperAffineCandidateStorage.expression_caps model.rat W D E m X V P n hn field previous hf hp s b)
  change (options a).2+(options b).2+(GeneralPaperAffineCrossingPrice.optionalRun model.rat W (options a).1 (options b).1).2+16*W≤_
  unfold pairPrice
  dsimp only [options,R] at *
  omega

theorem pair_root {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) (a b : Fin K) (t : ℚ)
    (ht : (GeneralPaperCrossingPairsPrice.pairRun model.rat W (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) a b).1=some t) :
    RationalHeight t (width D E m X V P) := by
  rw [GeneralPaperCrossingPairsPrice.pair_data] at ht
  exact GeneralPaperRayCrossingSize.optional hD hE _ _
    (GeneralPaperAffineCandidateStorage.expression_caps model.rat W D E m X V P n hn field previous hf hp s a)
    (GeneralPaperAffineCandidateStorage.expression_caps model.rat W D E m X V P n hn field previous hf hp s b) t ht

def rowWindow {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) (a : Fin K) (active : Option (Fin K)) : ℕ :=
  GeneralPaperPricedListStreamStorage.filterWindow W
    (GeneralPaperCrossingPairsPrice.pairRun model.rat W (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) a)
    (fun b => GeneralPaperAffineCandidatePairStorage.window model W field previous s a b) active (List.finRange K)

def rowProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperPricedListStreamStorage.filterProfile W R (pairPrice model W R) K (GeneralPaperAffineCandidatePairStorage.profile model W m K S R)

theorem row_bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S)
    (s : Fin (S+1)) (a : Fin K) (active : Option (Fin K)) :
    rowWindow model W field previous s a active≤rowProfile model W m K S (width D E m X V P) := by
  apply GeneralPaperPricedListStreamStorage.filter_bounded W _ _ K _ _ _ active (List.finRange K) (by rw [List.length_finRange])
  · intro b _; exact pair_work model W D E m X V P n hD hE hn field previous hf hp s a b
  · intro b _; exact pair_root model W D E m X V P n hD hE hn field previous hf hp s a b
  · intro b _; exact GeneralPaperAffineCandidatePairStorage.bounded model W D E m X V P n hD hE hn field previous hf hp hScores s a b
  · intro b _; exact List.mem_finRange b

def window {S K : ℕ} (model : RationalCostModel) (W copied : ℕ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) (activeA activeB : Option (Fin K)) : ℕ :=
  let options := GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s
  GeneralPaperPricedListStreamStorage.flatWindow W copied
    (fun a => GeneralPaperPricedListStream.filterMap W (GeneralPaperCrossingPairsPrice.pairRun model.rat W options a) (List.finRange K))
    (fun a => rowWindow model W field previous s a activeB) activeA (List.finRange K)

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperPricedListStreamStorage.flatProfile W R K (rowPrice model W K R) K (rowProfile model W m K S R)

theorem bounded {S K : ℕ} (model : RationalCostModel) (W copied D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S)
    (s : Fin (S+1)) (activeA activeB : Option (Fin K)) :
    window model W copied field previous s activeA activeB≤profile model W m K S (width D E m X V P) := by
  let options := GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s
  apply GeneralPaperPricedListStreamStorage.flat_bounded W _ K _ K _ copied
    (fun a => GeneralPaperPricedListStream.filterMap W (GeneralPaperCrossingPairsPrice.pairRun model.rat W options a) (List.finRange K))
    (fun a => rowWindow model W field previous s a activeB) activeA (List.finRange K) (by rw [List.length_finRange])
  · intro a _
    simpa only [List.length_finRange] using GeneralPaperPricedListStream.filterMap_length W _ (List.finRange K)
  · intro a _
    simpa only [List.length_finRange,rowPrice] using GeneralPaperPricedListStream.filterMap_work W (pairPrice model W (width D E m X V P))
      (GeneralPaperCrossingPairsPrice.pairRun model.rat W options a) (List.finRange K)
      (fun b _ => pair_work model W D E m X V P n hD hE hn field previous hf hp s a b)
  · intro a _ t ht
    rw [GeneralPaperPricedListStream.filterMap_data] at ht
    obtain ⟨b,_,he⟩ := List.mem_filterMap.mp ht
    exact pair_root model W D E m X V P n hD hE hn field previous hf hp s a b t he
  · intro a _
    exact row_bounded model W D E m X V P n hD hE hn field previous hf hp hScores s a activeB
  · intro a _
    exact List.mem_finRange a

end Blotto.GeneralPaperCrossingPairStreamStorage
