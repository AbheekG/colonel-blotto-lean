import Blotto.GeneralPaperPhysicalResponseNativeStorage

/-! The existing full source/postprocessing/first-output profile is extended
by one shift construction/resident, one active physical child peak and the
new flag/reference frames. A closed at-one calibration covers all addresses;
no census, encoding-length query or space oracle is executed. -/
namespace Blotto.GeneralPaperPhysicalResponseReference
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperClassifierSpaceRates
open GeneralPaperReferenceCapacity GeneralPaperReferenceScaling GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

def extraCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperPhysicalResponseNativeStorage.extraProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)) := by
  have hp := (GeneralPaperPhysicalResponseStorageRates.storageCertificate C d W hW).bound
  have hs := (GeneralPaperPhysicalResponseStorageRates.shiftCertificate C d W hW).bound
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperPhysicalResponseNativeStorage.extraProfile GeneralPaperPhysicalResponseNativeStorage.flags
      GeneralPaperResponsePhysicalHeights.shiftHeight
    dsimp only
    unfold arrayWord
    source_space⟩

theorem extra_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((extraCertificate C d W hW).fields,(extraCertificate C d W hW).symbols,
      (extraCertificate C d W hW).accuracy)=(1,2,1) := rfl

theorem extra_mono (actual majorant : RationalCostModel) (h : ∀ w,actual.rat w≤majorant.rat w)
    (W m k qbar t : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    GeneralPaperPhysicalResponseNativeStorage.extraProfile actual W m k qbar t a≤
      GeneralPaperPhysicalResponseNativeStorage.extraProfile majorant W m k qbar t a := by
  unfold GeneralPaperPhysicalResponseNativeStorage.extraProfile
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right
    (GeneralPaperPhysicalResponseStorageRates.shift_monotone actual majorant h W m qbar a.C) _)
    (GeneralPaperPhysicalResponseStorageRates.monotone_profile actual majorant h W m qbar t a)) _

noncomputable def profile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperSourceRowsReference.profile C d W x+
    GeneralPaperPhysicalResponseNativeStorage.extraProfile (GeneralPaperFastRationalMajorant.model C d) W x.m x.k
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)

theorem profile_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x => profile C d (W x) x) :=
  add_same (GeneralPaperSourceRowsReference.profile_soft C d W hW)
    (lift_source (weaken (extraCertificate C d W hW).bound (by decide : 1≤1) (by decide : 2≤2) (by decide : 1≤2)))

theorem scaling (C d : ℕ) (x : Input) : Scale (fun W => profile C d W x) := by
  have hs := GeneralPaperSourceRowsReference.scaling C d x
  unfold profile GeneralPaperPhysicalResponseNativeStorage.extraProfile GeneralPaperPhysicalResponseNativeStorage.flags
  dsimp only
  unfold arrayWord
  fun_prop

theorem at_one_small (C d : ℕ) : Small (fun x => profile C d 1 x) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (profile_soft C d (fun _ => 1) (tight_constant 1))
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

theorem address_word (C d : ℕ) (x : Input) (address : ℕ) (h : address≤profile C d (width C d x) x) :
    binaryWordWidth address≤width C d x :=
  binaryWordWidth_le_of_lt_pow (positive_width C d x) (h.trans_lt (capacity C d x))

theorem width_tight (C d : ℕ) : Tight (width C d) := by
  have h := tight_mul_left 4 _ (word_tight _ (at_one_small C d))
  exact tight_add _ _ h GeneralPaperLogarithmicSourceReference.controls_tight

theorem quantitative_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,
    profile C d (width C d x) x≤A*rate x*(logSize x)^e := profile_soft C d _ (width_tight C d)

theorem paper_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,1≤x.m →
    profile C d (width C d x) x≤A*GeneralPaperSharpSourceSpaceRate.paperRate x*(logSize x)^e := by
  rcases quantitative_bound C d with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A
    (GeneralPaperSharpSourceSpaceRate.nonempty_rate x hm))).trans_eq (by ring))

end Blotto.GeneralPaperPhysicalResponseReference
