import Blotto.GeneralPaperCompleteCallerReferenceScaling

/-! One derived reference word covers every completed source/compiler/
value/prepared-pair lifetime and every local index. The coefficient uses
closed profiles at one, never an observed memory census. Outer cached/
front constructors and original-field phases remain separate joins. -/
namespace Blotto.GeneralPaperPreparedPairReference
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperReferenceScaling GeneralPaperReferenceCapacity
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

noncomputable def profile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperSourcePreparedPairOwnerRates.reservation (GeneralPaperFastRationalMajorant.model C d) C d W x.m x.k x.Qv x.B+
    GeneralPaperCompilerReference.indexSize x.m x.k*W

theorem scaling (C d : ℕ) (x : Input) : Scale (fun W => profile C d W x) := by
  have h := GeneralPaperCompleteCallerReferenceScaling.complete_reservation (GeneralPaperFastRationalMajorant.model C d) C d x.m x.k x.Qv x.B
  unfold profile
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

theorem index_address (C d : ℕ) (x : Input) (address : ℕ)
    (h : address≤GeneralPaperCompilerReference.indexSize x.m x.k) : binaryWordWidth address≤width C d x := by
  apply address_word C d x address
  have hw := Nat.mul_le_mul_left (GeneralPaperCompilerReference.indexSize x.m x.k) (positive_width C d x)
  unfold profile
  nlinarith only [h,hw,Nat.zero_le (GeneralPaperSourcePreparedPairOwnerRates.reservation
    (GeneralPaperFastRationalMajorant.model C d) C d (width C d x) x.m x.k x.Qv x.B)]

theorem local_words (C d : ℕ) (x : Input) :
    let p := GeneralPaperProxyParameters.prepare x.m x.k
    let W := width C d x
    binaryWordWidth (x.m*(p.K-1)+3)≤W ∧
    binaryWordWidth (p.K+1)≤W ∧ binaryWordWidth (x.m+1)≤W ∧
    binaryWordWidth (p.S+2)≤W ∧ binaryWordWidth ((p.S+1)*(p.K*p.K)+3)≤W ∧
    binaryWordWidth (p.S+4)≤W ∧ binaryWordWidth (x.m+p.K+1)≤W ∧
    binaryWordWidth (2*(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows+p.K+x.m+1)≤W := by
  dsimp only
  refine ⟨index_address C d x _ ?_,index_address C d x _ ?_,index_address C d x _ ?_,
    index_address C d x _ ?_,index_address C d x _ ?_,index_address C d x _ ?_,
    index_address C d x _ ?_,index_address C d x _ ?_⟩
  all_goals unfold GeneralPaperCompilerReference.indexSize;dsimp only [alphabet];omega

theorem at_one_small (C d : ℕ) : Small (fun x => profile C d 1 x) := by
  have h := GeneralPaperSourcePreparedPairOwnerRates.reservation_at_one_small C d
  unfold profile
  fun_prop

theorem width_tight (C d : ℕ) : Tight (width C d) :=
  tight_add _ _ (tight_mul_left 4 _ (word_tight _ (at_one_small C d)))
    GeneralPaperLogarithmicSourceReference.controls_tight

theorem logarithmic_width (C d : ℕ) : ∃ A : ℕ,∀ x,width C d x≤A*logSize x := width_tight C d

def indexCertificate (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperCompilerReference.indexSize x.m x.k*W x) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  refine ⟨_,_,_,by
    unfold GeneralPaperCompilerReference.indexSize
    dsimp only
    source_space⟩

theorem index_degrees (W : Input → ℕ) (hW : Tight W) :
    ((indexCertificate W hW).fields,(indexCertificate W hW).symbols,(indexCertificate W hW).accuracy)=(1,0,3) := rfl

theorem profile_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperSourcePreparedPairOwnerRates.rate
    (fun x => profile C d (W x) x) := by
  have hR := GeneralPaperSourcePreparedPairOwnerRates.majorant_rate C d W hW
  have hi : Rated (fun x => GeneralPaperCompilerReference.indexSize x.m x.k*W x) 3 0 4 :=
    weaken (indexCertificate W hW).bound (by decide : 1≤3) (by decide : 0≤0) (by decide : 3≤4)
  have hI : Soft GeneralPaperSourcePreparedPairOwnerRates.rate (fun x => GeneralPaperCompilerReference.indexSize x.m x.k*W x) := rate_mono hi (fun x => by unfold GeneralPaperSourcePreparedPairOwnerRates.rate;omega)
  exact add_same hR hI

theorem common_word_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,profile C d (width C d x) x≤
    A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := profile_soft C d (width C d) (width_tight C d)
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [GeneralPaperSourcePreparedPairOwnerRates.rate,monomial,pow_zero,Nat.mul_one,
    GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using h x

theorem actual_reserve {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) (W : ℕ) (x : Input) :
    GeneralPaperSourcePreparedPairOwnerRates.reservation actual C d W x.m x.k x.Qv x.B≤profile C d W x :=
  (GeneralPaperSourcePreparedPairOwnerRates.reservation_mono actual (GeneralPaperFastRationalMajorant.model C d)
    (GeneralPaperFastRationalMajorant.dominates hg) C d W x.m x.k x.Qv x.B).trans (Nat.le_add_right _ _)

end Blotto.GeneralPaperPreparedPairReference
