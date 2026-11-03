import Blotto.GeneralPaperClassifierSpaceRates

/-! Quantitative simultaneous source storage, including the one-time original
ratio, native prepared residents and retained first full trajectory. The
original input height is additive. The common bit reference word is derived. -/
namespace Blotto.GeneralPaperSharpSourceSpaceRate
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperSourceLifetimeRates
open GeneralPaperClassifierSpaceRates GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def inputCertificate (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperPrecallResidentStorage.inputProfile (W x) x.m x.k x.Qv 0
      ((alphabet x).lambda+1) ((alphabet x).lambda+1)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold GeneralPaperPrecallResidentStorage.inputProfile GeneralPaperEncodedScalarStorage.natBits
    source_space⟩

theorem input_degrees (W : Input → ℕ) (hW : Tight W) :
    ((inputCertificate W hW).fields,(inputCertificate W hW).symbols,
      (inputCertificate W hW).accuracy)=(0,1,0) := rfl

theorem input_soft (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x =>
    GeneralPaperPrecallResidentStorage.inputProfile (W x) x.m x.k x.Qv x.B
      ((alphabet x).lambda+1) ((alphabet x).lambda+1)) := by
  have hz : Rated (fun x => GeneralPaperPrecallResidentStorage.inputProfile (W x) x.m x.k x.Qv 0
      ((alphabet x).lambda+1) ((alphabet x).lambda+1)) 1 2 2 :=
    weaken (inputCertificate W hW).bound (by decide : 0≤1) (by decide : 1≤2) (by decide : 0≤2)
  have h := affine 2 hz
  apply dominated h
  intro x
  dsimp only [GeneralPaperPrecallResidentStorage.inputProfile]
  omega

noncomputable def profile (C d : ℕ) (W : Input → ℕ) (x : Input) : ℕ :=
  GeneralPaperFastSourceReference.profile C d (W x) x.k x.Qv x.B
    ((alphabet x).lambda+1) ((alphabet x).lambda+1) (alphabet x) x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)

theorem profile_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate (profile C d W) := by
  have hi := input_soft W hW
  have hr := lift_source (residentCertificate W hW).bound
  have ht := lift_source (trajectoryCertificate W hW).bound
  have hl := lift_source (lifetimeCertificate C d W hW).bound
  have hc := classifier_soft C d W hW
  have hp := lift_source (weaken (preparationCertificate C d W hW).bound
    (by decide : 0≤1) (by decide : 0≤2) (by decide : 0≤2))
  unfold profile GeneralPaperFastSourceReference.profile GeneralPaperPreparedReferenceCapacity.profile
  exact add_same (add_same (add_same (add_same (add_same hi hr) ht) hl) hc) hp

theorem common_word_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,
    profile C d (GeneralPaperLogarithmicSourceReference.width C d) x≤A*rate x*(logSize x)^e :=
  profile_soft C d _ (GeneralPaperLogarithmicSourceReference.width_tight C d)

def paperRate (x : Input) : ℕ := x.B+1+x.m*(alphabet x).lambda^2*2^(2*x.k)

theorem nonempty_rate (x : Input) (hm : 1≤x.m) : rate x≤8*paperRate x := by
  have hl := GeneralPaperSourceAlphabetLower.fields_le_lambda x.m x.k
  change x.m≤(alphabet x).lambda at hl
  have hm' : fields x≤2*x.m := by unfold fields; omega
  have hl' : symbols x≤2*(alphabet x).lambda := by unfold symbols; omega
  have h := Nat.mul_le_mul_right ((accuracy x)^2)
    (Nat.mul_le_mul hm' (Nat.pow_le_pow_left hl' 2))
  have hs : monomial 1 2 2 x≤8*(x.m*(alphabet x).lambda^2*(accuracy x)^2) := by
    simpa only [monomial,pow_one,show (2*x.m)*(2*(alphabet x).lambda)^2*(accuracy x)^2=
      8*(x.m*(alphabet x).lambda^2*(accuracy x)^2) by ring] using h
  have he : (accuracy x)^2=2^(2*x.k) := by
    simp only [accuracy,←pow_mul,Nat.mul_comm x.k 2]
  rw [he] at hs
  dsimp only [rate,paperRate]
  omega

theorem paper_profile_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,1≤x.m →
    profile C d (GeneralPaperLogarithmicSourceReference.width C d) x≤A*paperRate x*(logSize x)^e := by
  rcases common_word_bound C d with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (nonempty_rate x hm))).trans_eq (by ring))

end Blotto.GeneralPaperSharpSourceSpaceRate
