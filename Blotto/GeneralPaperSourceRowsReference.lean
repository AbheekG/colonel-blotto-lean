import Blotto.GeneralPaperSourceRowsStorageRates

/-! One derived logarithmic reference word covers the source, complete
row-postprocessing ownership and a retained first rational output. Its
calibration uses only closed profiles at one, never a runtime memory census. -/
namespace Blotto.GeneralPaperSourceRowsReference
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceRowsStorageRates GeneralPaperClassifierSpaceRates
open GeneralPaperReferenceCapacity GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

noncomputable def profile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperSharpSourceSpaceRate.profile C d (fun _ => W) x+
    GeneralPaperSourceRowsStorage.profile (GeneralPaperFastRationalMajorant.model C d) W
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m ((alphabet x).lambda+1) (alphabet x)+
    GeneralPaperEncodedRationalRows.tableProfile W
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m (binaryWordWidth (alphabet x).C)

theorem profile_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x => profile C d (W x) x) := by
  have hs := GeneralPaperSharpSourceSpaceRate.profile_soft C d W hW
  have hp := lift_source (storageCertificate C d W hW).bound
  have hf := lift_source (returnedCertificate W hW).bound
  exact add_same (add_same hs hp) hf

theorem scaling (C d : ℕ) (x : Input) : Scale (fun W => profile C d W x) := by
  unfold profile GeneralPaperSharpSourceSpaceRate.profile GeneralPaperFastSourceReference.profile
  fun_prop

theorem at_one_small (C d : ℕ) : Small (fun x => profile C d 1 x) := by
  apply soft_small (profile_soft C d (fun _ => 1) (tight_constant 1))
  unfold rate monomial GeneralPaperNativeSourceRates.fields symbols accuracy
  fun_prop

noncomputable def width (C d : ℕ) (x : Input) : ℕ :=
  referenceWord (profile C d 1 x)+GeneralPaperPrecallControlWord.word x.m x.k

theorem positive_width (C d : ℕ) (x : Input) : 1≤width C d x := by
  have h := positive (profile C d 1 x)
  unfold width
  omega

theorem control_word (C d : ℕ) (x : Input) : GeneralPaperPrecallControlWord.word x.m x.k≤width C d x := by
  unfold width
  omega

theorem capacity (C d : ℕ) (x : Input) : profile C d (width C d x) x<2^width C d x :=
  padded_profile_capacity (fun W => profile C d W x) (scaling C d x) _

theorem address_word (C d : ℕ) (x : Input) (address : ℕ)
    (h : address≤profile C d (width C d x) x) : binaryWordWidth address≤width C d x :=
  binaryWordWidth_le_of_lt_pow (positive_width C d x) (h.trans_lt (capacity C d x))

theorem width_tight (C d : ℕ) : Tight (width C d) := by
  have h := tight_mul_left 4 _ (word_tight _ (at_one_small C d))
  exact tight_add _ _ h GeneralPaperLogarithmicSourceReference.controls_tight

theorem reference_bound (C d : ℕ) : ∃ A : ℕ,∀ x,width C d x≤A*logSize x := width_tight C d

theorem quantitative_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,
    profile C d (width C d x) x≤A*rate x*(logSize x)^e := profile_soft C d _ (width_tight C d)

theorem paper_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,1≤x.m →
    profile C d (width C d x) x≤A*GeneralPaperSharpSourceSpaceRate.paperRate x*(logSize x)^e := by
  rcases quantitative_bound C d with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A
    (GeneralPaperSharpSourceSpaceRate.nonempty_rate x hm))).trans_eq (by ring))

end Blotto.GeneralPaperSourceRowsReference
