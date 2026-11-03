import Blotto.GeneralPaperNativeAffineScanStorage

/-! One complete native affine DP layer: previous table/current field,
new-table reserved capacity, constructor stack, one full native minimum
scan and selected fill/callback/step/return counters. -/
namespace Blotto.GeneralPaperAffineStepStorage
open RationalOrderCell GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
open GeneralPaperRayUniformSize GeneralPaperAffineWitnessStorage GeneralPaperAffinePickStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector GeneralPaperScoreConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def callback {S K : ℕ} (model : RationalCostModel) (W : ℕ) (sample : ℚ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) : Option (Choice K)×ℕ :=
  GeneralPaperAffineMinimumPrice.scanRun model.rat W sample
    (GeneralPaperAffineCandidatePrice.run model.rat W field previous s) (List.finRange K)

def stepPrice (model : RationalCostModel) (W K S R : ℕ) : ℕ :=
  GeneralPaperAffineStepPrice.profile S K W (model.rat (6*R+9))
def scanPrice (model : RationalCostModel) (W K R : ℕ) : ℕ :=
  GeneralPaperAffineScanStorage.workCap model W R (2*R+3) (GeneralPaperNativeAffineScanStorage.candidatePrice model W R) K

theorem returned_good {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hn : n+1≤m) (sample : ℚ) (field : Field K) (previous : Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) :
    Good m (width D E m X V P) (callback model W sample field previous s).1 :=
  GeneralPaperAffineScanStorage.good model W m (width D E m X V P) sample _ _
    (fun l _ => GeneralPaperNativeAffineScanStorage.candidate_good model W D E m X V P n hD hE hn field previous hf hp s l)

theorem callback_work {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hn : n+1≤m) (sample : ℚ) (ht : RationalHeight sample (2*width D E m X V P+3))
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) :
    (callback model W sample field previous s).2≤scanPrice model W K (width D E m X V P) := by
  have h := GeneralPaperAffineScanStorage.work model W m (width D E m X V P) (2*width D E m X V P+3)
    (GeneralPaperNativeAffineScanStorage.candidatePrice model W (width D E m X V P)) sample ht
    (GeneralPaperAffineCandidatePrice.run model.rat W field previous s) (List.finRange K)
    (fun l _ => GeneralPaperNativeAffineScanStorage.candidate_good model W D E m X V P n hD hE hn field previous hf hp s l)
    (fun l _ => GeneralPaperNativeAffineScanStorage.candidate_work model W D E m X V P n hD hE hn field previous hf hp s l)
  simpa only [List.length_finRange,callback,scanPrice] using h

def metadataCap (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  S+K+m+1+3*stepPrice model W K S R+scanPrice model W K R+44*W

def caller {S K : ℕ} (model : RationalCostModel) (W : ℕ) (sample : ℚ) (field : Field K) (previous : Table S K)
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) : ℕ :=
  let earlier := PaperIndexedArrayConstruction.fill (fun w => w) W (callback model W sample field previous) count hc
  let current := callback model W sample field previous s
  let step := PaperIndexedArrayConstruction.stepWork (fun w => w) W count
  let result := GeneralPaperAffineStepPrice.run model.rat W sample field previous
  fields W [S,K,count,s.val,earlier.2,current.2,step,earlier.2+current.2,earlier.2+current.2+step,result.2]+256*W

def callerProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  10*(natBits (metadataCap model W m K S R)+W)+288*W

theorem caller_bound {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hn : n+1≤m) (sample : ℚ) (ht : RationalHeight sample (2*width D E m X V P+3))
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) :
    caller model W sample field previous count hc s≤callerProfile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let earlier := PaperIndexedArrayConstruction.fill (fun w => w) W (callback model W sample field previous) count hc
  let current := callback model W sample field previous s
  let step := PaperIndexedArrayConstruction.stepWork (fun w => w) W count
  let result := GeneralPaperAffineStepPrice.run model.rat W sample field previous
  have hResult := GeneralPaperNativeAffinePrices.step_work model.rat model.monotone W D E m X V P n hD hE hn sample ht field previous hf hp hW hIndex
  change result.2≤stepPrice model W K S R at hResult
  have hPrefix : earlier.2≤stepPrice model W K S R :=
    (fill_work_mono (fun w => w) W (callback model W sample field previous) count (S+1) hc le_rfl hc).trans hResult
  have hCurrent := callback_work model W D E m X V P n hD hE hn sample ht field previous hf hp s
  change current.2≤scanPrice model W K R at hCurrent
  have hBits := (binaryWordWidth_mono (Nat.add_le_add_right hc 1)).trans hIndex
  have hStep : step≤44*W := by unfold step PaperIndexedArrayConstruction.stepWork; dsimp only; omega
  have hs := s.isLt
  have hFields := fields_bound W (natBits (metadataCap model W m K S R))
    [S,K,count,s.val,earlier.2,current.2,step,earlier.2+current.2,earlier.2+current.2+step,result.2] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤10*(natBits (metadataCap model W m K S R)+W)+32*W at hFields
  change GeneralPaperEncodedScalarStorage.fields W [S,K,count,s.val,earlier.2,current.2,step,earlier.2+current.2,earlier.2+current.2+step,result.2]+256*W≤_
  unfold callerProfile
  dsimp only [R] at hFields
  omega

def window {S K : ℕ} (model : RationalCostModel) (W copied : ℕ) (sample : ℚ) (field : Field K) (previous : Table S K)
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) (active : Option (Fin K)) : ℕ :=
  tableFoot W previous+fieldFoot W field+
    reservedFootprint W (S+1) (optionChoiceFoot W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (callback model W sample field previous) count hc).1+
    constructorFrames (fun w => w) W W (callback model W sample field previous) count hc+
    GeneralPaperNativeAffineScanStorage.window model W copied sample field previous s active+
    caller model W sample field previous count hc s

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  2*tableProfile W S K m R+fieldProfile W K S R+
    constructorProfile W (S+1) (stepPrice model W K S R)+
    GeneralPaperNativeAffineScanStorage.profile model W m K S R+callerProfile model W m K S R

theorem bounded {S K : ℕ} (model : RationalCostModel) (W copied D E m X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hn : n+1≤m) (sample : ℚ) (ht : RationalHeight sample (2*width D E m X V P+3))
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S)
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) (active : Option (Fin K)) :
    window model W copied sample field previous count hc s active≤profile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  have hTable := table_bound W D E X V n m P hD hE (by omega) previous hp
  have hField := GeneralPaperAffineWitnessStorage.field_bound W D E X V m P S hD hE (by omega) field hf hScores
  have hPrefix := indexed_reserved_prefix (fun w => w) W W (optionChoiceProfile W K m R) (optionChoiceFoot W)
    (callback model W sample field previous) (fun s => option_choice_bound W m R _
      (returned_good model W D E m X V P n hD hE hn sample field previous hf hp s)) count hc
  change reservedFootprint W (S+1) (optionChoiceFoot W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (callback model W sample field previous) count hc).1≤tableProfile W S K m R at hPrefix
  have hWork := GeneralPaperNativeAffinePrices.step_work model.rat model.monotone W D E m X V P n hD hE hn sample ht field previous hf hp hW hIndex
  have hConstructor := constructor_bound (fun w => w) W W (stepPrice model W K S R) (callback model W sample field previous) hWork count hc
  have hScan := GeneralPaperNativeAffineScanStorage.bounded model W copied D E m X V P n hD hE hn sample ht field previous hf hp hScores s active
  have hCaller := caller_bound model W D E m X V P n hD hE hn sample ht field previous hf hp hW hIndex count hc s
  unfold window profile
  dsimp only [R] at hPrefix hConstructor
  omega

end Blotto.GeneralPaperAffineStepStorage
