import Blotto.GeneralPaperAffineScanStorage

/-! Instantiate the full minimum-scan window with the actual native affine
predecessor callback. Processed-field/common-lattice invariants derive full
witness lengths, coefficient heights, work and candidate scratch. -/
namespace Blotto.GeneralPaperNativeAffineScanStorage
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
open GeneralPaperRayUniformSize GeneralPaperAffinePickStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def candidatePrice (model : RationalCostModel) (W R : ℕ) : ℕ := 96*W+4*model.rat (1+2*R)

theorem candidate_good {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hn : n+1≤m) (field : Field K) (previous : Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) (l : Fin K) :
    Good m (width D E m X V P) (GeneralPaperAffineCandidatePrice.run model.rat W field previous s l).1 := by
  intro c hc
  rw [GeneralPaperAffineCandidatePrice.data] at hc
  have h := GeneralPaperRayAffineDPSize.candidate D E X V n field previous hf hp s l c hc
  have hCaps := scale_caps m X V P (n+1) hn
  let A := interceptCap m X P
  let B := slopeCap m V
  have hHeight := GeneralPaperAffineValuePrice.coefficients hD hE c.expression
    (GeneralPaperRayAffineBound.mono h.1 hCaps.1 hCaps.2)
  have hR : GeneralPaperRayAffineBound.rootWidth D E A B≤width D E m X V P :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  exact ⟨h.2.le.trans hn,hHeight.1.mono hR,hHeight.2.mono hR⟩

theorem candidate_work {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hn : n+1≤m) (field : Field K) (previous : Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) (l : Fin K) :
    (GeneralPaperAffineCandidatePrice.run model.rat W field previous s l).2≤candidatePrice model W (width D E m X V P) :=
  GeneralPaperAffineCandidatePrice.work model.rat model.monotone W D E (interceptCap m X P) (slopeCap m V)
    (width D E m X V P) hD hE le_rfl field previous
    (GeneralPaperNativeAffinePrices.field_cap D E m X V P (by omega) field hf)
    (GeneralPaperNativeAffinePrices.table_cap D E m X V P n (by omega) previous hp) s l

def window {S K : ℕ} (model : RationalCostModel) (W copied : ℕ) (sample : ℚ) (field : Field K)
    (previous : Table S K) (s : Fin (S+1)) (active : Option (Fin K)) : ℕ :=
  GeneralPaperAffineScanStorage.window model W sample (GeneralPaperAffineCandidatePrice.run model.rat W field previous s)
    (GeneralPaperAffineCandidateStorage.window model W field previous s) (List.finRange K) active+
    GeneralPaperFinRangeStorage.window W K copied+fields W [s.val,K,S]+128*W

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperAffineScanStorage.profile model W K m R (2*R+3) (candidatePrice model W R) K
    (GeneralPaperAffineCandidateStorage.profile model W m K S R)+GeneralPaperFinRangeStorage.profile W K+
      3*(natBits (S+K+1)+W)+160*W

theorem bounded {S K : ℕ} (model : RationalCostModel) (W copied D E m X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hn : n+1≤m) (sample : ℚ) (ht : RationalHeight sample (2*width D E m X V P+3))
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S)
    (s : Fin (S+1)) (active : Option (Fin K)) :
    window model W copied sample field previous s active≤profile model W m K S (width D E m X V P) := by
  have hScan := GeneralPaperAffineScanStorage.bounded model W m (width D E m X V P) (2*width D E m X V P+3)
    (candidatePrice model W (width D E m X V P)) K (GeneralPaperAffineCandidateStorage.profile model W m K S (width D E m X V P))
    sample ht (GeneralPaperAffineCandidatePrice.run model.rat W field previous s) (GeneralPaperAffineCandidateStorage.window model W field previous s)
    (List.finRange K) (by simp only [List.length_finRange,le_refl])
    (fun l _ => candidate_good model W D E m X V P n hD hE hn field previous hf hp s l)
    (fun l _ => candidate_work model W D E m X V P n hD hE hn field previous hf hp s l)
    (fun l _ => GeneralPaperAffineCandidateStorage.bounded model W D E m X V P n hD hE hn field previous hf hp hScores s l)
    active (fun l _ => List.mem_finRange l)
  have hRange := GeneralPaperFinRangeStorage.bounded W K copied
  have hs := s.isLt
  have hFields := fields_bound W (natBits (S+K+1)) [s.val,K,S] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (S+K+1)+W)+32*W at hFields
  unfold window profile
  omega

end Blotto.GeneralPaperNativeAffineScanStorage
