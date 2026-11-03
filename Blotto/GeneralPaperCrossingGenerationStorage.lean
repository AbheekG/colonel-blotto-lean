import Blotto.GeneralPaperCrossingPairStreamStorage

/-! Complete native pair-batch generation: score and label iterators,
nested filterMap/flatMap roots/segments/append prefixes, one active full
candidate pair, retained affine field/table and wrapper return counters.
The cursor is an erased local phase observer; executable code is unchanged. -/
namespace Blotto.GeneralPaperCrossingGenerationStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRayAffine GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

structure Cursor (S K : ℕ) where
  score : Option (Fin (S+1))
  first : Option (Fin K)
  second : Option (Fin K)
  scoreCopied : ℕ
  pairCopied : ℕ
  indexCopied : ℕ

def scoreReturn {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (s : Fin (S+1)) : List ℚ×ℕ :=
  let current := GeneralPaperCrossingPairsPrice.run model.rat W (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) (List.finRange K)
  (current.1,current.2+16*(K+1)*W)
def scorePrice (model : RationalCostModel) (W K R : ℕ) : ℕ :=
  GeneralPaperCrossingPairsPrice.profile K W (model.rat (1+2*R)) (104*W+4*model.rat (1+2*R))+16*(K+1)*W

theorem score_work {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) :
    (scoreReturn model W field previous s).2≤scorePrice model W K (width D E m X V P) := by
  have h := GeneralPaperCrossingPairsPrice.work model.rat model.monotone W D E (interceptCap m X P) (slopeCap m V) (width D E m X V P)
    (104*W+4*model.rat (1+2*width D E m X V P)) hD hE le_rfl
    (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) (List.finRange K)
    (fun l _ => GeneralPaperAffineCandidateStorage.expression_caps model.rat W D E m X V P n hn field previous hf hp s l)
    (fun l _ => GeneralPaperAffineCandidateStorage.expression_work model W D E m X V P n hD hE hn field previous hf hp s l)
  rw [List.length_finRange] at h
  exact Nat.add_le_add_right h _

def scoreCap (model : RationalCostModel) (W K S R : ℕ) : ℕ := S+K+1+scorePrice model W K R
def scoreCaller {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (s : Fin (S+1)) : ℕ :=
  let current := GeneralPaperCrossingPairsPrice.run model.rat W (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) (List.finRange K)
  fields W [s.val,K,current.2,current.2+16*(K+1)*W,16*(K+1)*W]+256*W
def scoreCallerProfile (model : RationalCostModel) (W K S R : ℕ) : ℕ := 5*(natBits (scoreCap model W K S R)+W)+288*W

theorem score_caller {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) :
    scoreCaller model W field previous s≤scoreCallerProfile model W K S (width D E m X V P) := by
  let R := width D E m X V P
  let current := GeneralPaperCrossingPairsPrice.run model.rat W (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) (List.finRange K)
  have hWork := score_work model W D E m X V P n hD hE hn field previous hf hp s
  change current.2+16*(K+1)*W≤scorePrice model W K R at hWork
  have hFields := fields_bound W (natBits (scoreCap model W K S R)) [s.val,K,current.2,current.2+16*(K+1)*W,16*(K+1)*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    all_goals unfold scoreCap; have hs := s.isLt; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (scoreCap model W K S R)+W)+32*W at hFields
  change GeneralPaperEncodedScalarStorage.fields W [s.val,K,current.2,current.2+16*(K+1)*W,16*(K+1)*W]+256*W≤scoreCallerProfile model W K S R
  unfold scoreCallerProfile
  omega

def scoreWindow {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (s : Fin (S+1)) (c : Cursor S K) : ℕ :=
  GeneralPaperCrossingPairStreamStorage.window model W c.pairCopied field previous s c.first c.second+scoreCaller model W field previous s
def scoreProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperCrossingPairStreamStorage.profile model W m K S R+scoreCallerProfile model W K S R

theorem score_bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S) (s : Fin (S+1)) (c : Cursor S K) :
    scoreWindow model W field previous s c≤scoreProfile model W m K S (width D E m X V P) :=
  Nat.add_le_add (GeneralPaperCrossingPairStreamStorage.bounded model W c.pairCopied D E m X V P n hD hE hn field previous hf hp hScores s c.first c.second)
    (score_caller model W D E m X V P n hD hE hn field previous hf hp s)

def body {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) : List ℚ×ℕ :=
  GeneralPaperPricedListStream.flatMap W (scoreReturn model W field previous) (List.finRange (S+1))
def bodyWindow {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (c : Cursor S K) : ℕ :=
  GeneralPaperPricedListStreamStorage.flatWindow W c.scoreCopied (scoreReturn model W field previous)
    (fun s => scoreWindow model W field previous s c) c.score (List.finRange (S+1))
def bodyProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperPricedListStreamStorage.flatProfile W R (K*K) (scorePrice model W K R) (S+1) (scoreProfile model W m K S R)

theorem body_bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S) (c : Cursor S K) :
    bodyWindow model W field previous c≤bodyProfile model W m K S (width D E m X V P) := by
  apply GeneralPaperPricedListStreamStorage.flat_bounded W _ (K*K) _ (S+1) _ c.scoreCopied
    (scoreReturn model W field previous) (fun s => scoreWindow model W field previous s c) c.score (List.finRange (S+1)) (by rw [List.length_finRange])
  · intro s _
    simpa only [List.length_finRange,scoreReturn] using GeneralPaperCrossingPairsPrice.length model.rat W
      (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) (List.finRange K)
  · intro s _; exact score_work model W D E m X V P n hD hE hn field previous hf hp s
  · intro s _ t ht
    change t∈(GeneralPaperCrossingPairsPrice.run model.rat W (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s) (List.finRange K)).1 at ht
    rw [GeneralPaperCrossingPairsPrice.data] at ht
    exact GeneralPaperRayCrossingSize.pairs hD hE _ _
      (fun l _ => GeneralPaperAffineCandidateStorage.expression_caps model.rat W D E m X V P n hn field previous hf hp s l) t ht
  · intro s _; exact score_bounded model W D E m X V P n hD hE hn field previous hf hp hScores s c
  · intro s _; exact List.mem_finRange s

def callerCap (model : RationalCostModel) (W K S R : ℕ) : ℕ := S+K+(S+1)*(K*K)+1+GeneralPaperNativeAffinePrices.profile S K W (model.rat (1+2*R))
def caller {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) : ℕ :=
  let result := GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous
  let current := body model W field previous
  fields W [S,K,(S+1)*(K*K),result.1.length,current.2,result.2,16*(S+2)*W,current.2+16*(S+2)*W]+256*W
def callerProfile (model : RationalCostModel) (W K S R : ℕ) : ℕ := 8*(natBits (callerCap model W K S R)+W)+288*W

theorem caller_bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) : caller model W field previous≤callerProfile model W K S (width D E m X V P) := by
  let R := width D E m X V P
  let result := GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous
  let current := body model W field previous
  have hWork := GeneralPaperNativeAffinePrices.crossings_work model.rat model.monotone W D E m X V P n hD hE hn field previous hf hp
  change result.2≤GeneralPaperNativeAffinePrices.profile S K W (model.rat (1+2*R)) at hWork
  have hLen : result.1.length≤(S+1)*(K*K) := by
    dsimp only [result]
    rw [GeneralPaperNativeAffinePrices.crossings_data]
    exact GeneralPaperRayAffineScoreStep.crossings_length field previous
  have hShape : result.2=current.2+16*(S+2)*W := rfl
  have hFields := fields_bound W (natBits (callerCap model W K S R))
    [S,K,(S+1)*(K*K),result.1.length,current.2,result.2,16*(S+2)*W,current.2+16*(S+2)*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (callerCap model W K S R)+W)+32*W at hFields
  change GeneralPaperEncodedScalarStorage.fields W [S,K,(S+1)*(K*K),result.1.length,current.2,result.2,16*(S+2)*W,current.2+16*(S+2)*W]+256*W≤callerProfile model W K S R
  unfold callerProfile
  omega

def window {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (c : Cursor S K) : ℕ :=
  GeneralPaperAffineWitnessStorage.tableFoot W previous+GeneralPaperAffineWitnessStorage.fieldFoot W field+
    2*GeneralPaperFinRangeStorage.window W K c.indexCopied+GeneralPaperFinRangeStorage.window W (S+1) c.indexCopied+
    bodyWindow model W field previous c+caller model W field previous
def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperAffineWitnessStorage.tableProfile W S K m R+GeneralPaperAffineWitnessStorage.fieldProfile W K S R+
    2*GeneralPaperFinRangeStorage.profile W K+GeneralPaperFinRangeStorage.profile W (S+1)+bodyProfile model W m K S R+callerProfile model W K S R

theorem bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S) (c : Cursor S K) :
    window model W field previous c≤profile model W m K S (width D E m X V P) := by
  have hTable := GeneralPaperAffineWitnessStorage.table_bound W D E X V n m P hD hE (by omega) previous hp
  have hField := GeneralPaperAffineWitnessStorage.field_bound W D E X V m P S hD hE (by omega) field hf hScores
  have hLabels := GeneralPaperFinRangeStorage.bounded W K c.indexCopied
  have hScoresRange := GeneralPaperFinRangeStorage.bounded W (S+1) c.indexCopied
  have hBody := body_bounded model W D E m X V P n hD hE hn field previous hf hp hScores c
  have hCaller := caller_bounded model W D E m X V P n hD hE hn field previous hf hp
  unfold window profile
  omega

end Blotto.GeneralPaperCrossingGenerationStorage
