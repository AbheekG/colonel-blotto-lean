import Blotto.GeneralPaperFastDriverIndexReference

/-! Complete native fast-driver address calibration. One closed reservation
contains all earlier owners and the entire actual front/materialization/
compiler caller. Analytic input/constructor index ranges join it before
one logarithmic global reference is derived. Native local words remain. -/
namespace Blotto.GeneralPaperFastDriverReference
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperReferenceScaling GeneralPaperReferenceCapacity
open GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

noncomputable def profile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperFastWholeDriverStorageRates.reservation (GeneralPaperFastRationalMajorant.model C d) C d W x.m x.k x.Qv x.B+
    GeneralPaperFastDriverIndexReference.size x*W

theorem scaling (C d : ℕ) (x : Input) : Scale (fun W => profile C d W x) := by
  have h := GeneralPaperFastWholeDriverStorageRates.reservation_scaling (GeneralPaperFastRationalMajorant.model C d) C d x.m x.k x.Qv x.B
  unfold profile
  fun_prop

def padding (x : Input) : ℕ :=
  GeneralPaperPrecallControlWord.word x.m x.k+
    GeneralPaperControlMaterializationStorage.powerWord x.m (alphabet x).lambda x.k x.Qv+
    GeneralPaperControlMaterializationStorage.gridWord x.m (alphabet x).lambda x.k x.Qv

noncomputable def width (C d : ℕ) (x : Input) : ℕ :=
  referenceWord (profile C d 1 x)+padding x

theorem positive_width (C d : ℕ) (x : Input) : 1≤width C d x := by
  have h := positive (profile C d 1 x)
  unfold width padding
  omega

theorem control_word (C d : ℕ) (x : Input) : GeneralPaperPrecallControlWord.word x.m x.k≤width C d x := by
  unfold width padding
  omega

theorem capacity (C d : ℕ) (x : Input) : profile C d (width C d x) x<2^width C d x :=
  padded_profile_capacity (fun W => profile C d W x) (scaling C d x) _

theorem address_word (C d : ℕ) (x : Input) (address : ℕ)
    (h : address≤profile C d (width C d x) x) : binaryWordWidth address≤width C d x :=
  binaryWordWidth_le_of_lt_pow (positive_width C d x) (h.trans_lt (capacity C d x))

theorem index_address (C d : ℕ) (x : Input) (address : ℕ)
    (h : address≤GeneralPaperFastDriverIndexReference.size x) : binaryWordWidth address≤width C d x := by
  apply address_word C d x address
  have hw := Nat.mul_le_mul_left (GeneralPaperFastDriverIndexReference.size x) (positive_width C d x)
  unfold profile
  nlinarith only [h,hw,Nat.zero_le (GeneralPaperFastWholeDriverStorageRates.reservation
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
  all_goals
    apply le_trans (b:=GeneralPaperCompilerReference.indexSize x.m x.k) ?_ (GeneralPaperFastDriverIndexReference.previous_le x)
    unfold GeneralPaperCompilerReference.indexSize
    dsimp only [GeneralPaperSourceWordGrowth.alphabet]
    omega

theorem at_one_small (C d : ℕ) : Small (fun x => profile C d 1 x) := by
  have h := GeneralPaperFastWholeDriverStorageRates.at_one_small C d
  have hi := GeneralPaperFastDriverIndexReference.size_small
  unfold profile
  fun_prop

theorem padding_tight : Tight padding := by
  have hF := GeneralPaperLogarithmicSourceReference.controls_tight
  have hP := GeneralPaperFastWholeDriverStorageRates.power_word_tight
  have hG := GeneralPaperFastWholeDriverStorageRates.grid_word_tight
  unfold padding
  fun_prop

theorem width_tight (C d : ℕ) : Tight (width C d) :=
  tight_add _ _ (tight_mul_left 4 _ (word_tight _ (at_one_small C d))) padding_tight

theorem logarithmic_width (C d : ℕ) : ∃ A : ℕ,∀ x,width C d x≤A*logSize x := width_tight C d

theorem profile_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperFastFrontStorageRates.rate
    (fun x => profile C d (W x) x) :=
  add_same (GeneralPaperFastWholeDriverStorageRates.reservation_rate C d W hW)
    (GeneralPaperFastDriverIndexReference.rate W hW)

theorem common_word_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,profile C d (width C d x) x≤
    A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := profile_soft C d (width C d) (width_tight C d)
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [GeneralPaperFastFrontStorageRates.rate,monomial,pow_zero,Nat.mul_one,
    GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using h x

theorem actual_reserve {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) (W : ℕ) (x : Input) :
    GeneralPaperFastWholeDriverStorageRates.reservation actual C d W x.m x.k x.Qv x.B≤profile C d W x :=
  (GeneralPaperFastWholeDriverStorageRates.reservation_mono actual (GeneralPaperFastRationalMajorant.model C d)
    (GeneralPaperFastRationalMajorant.dominates hg) C d W x.m x.k x.Qv x.B).trans (Nat.le_add_right _ _)


theorem row_words (C d : ℕ) (x : Input) :
    let W := width C d x
    binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1)≤W ∧
    binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1)≤W := by
  have h := (local_words C d x).2.2.2.2.2.2.2
  refine ⟨?_,?_⟩
  · exact (binaryWordWidth_mono (show
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1≤
      2*(GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+(prepare x.m x.k).K+x.m+1 by omega)).trans h
  · exact (binaryWordWidth_mono (show
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+
        (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1≤
      2*(GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+(prepare x.m x.k).K+x.m+1 by omega)).trans h


theorem cached_reserve_le (model : RationalCostModel) (C d W m k Qv B : ℕ) :
    GeneralPaperCachedBitPairStorageRates.reservation model C d W m k Qv B≤
      GeneralPaperFastWholeDriverStorageRates.reservation model C d W m k Qv B := by
  unfold GeneralPaperFastWholeDriverStorageRates.reservation GeneralPaperSourceControlStorageRates.reservation
    GeneralPaperFastFrontStorageRates.reservation
  omega

theorem prepared_reserve_le (model : RationalCostModel) (C d W m k Qv B : ℕ) :
    GeneralPaperSourcePreparedPairOwnerRates.reservation model C d W m k Qv B≤
      GeneralPaperFastWholeDriverStorageRates.reservation model C d W m k Qv B :=
  (GeneralPaperCachedBitPairReferenceContract.prepared_reserve_le model C d W m k Qv B).trans
    (cached_reserve_le model C d W m k Qv B)

theorem modified_reserve_le (model : RationalCostModel) (C d W m k Qv B : ℕ) :
    GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv≤
      GeneralPaperFastWholeDriverStorageRates.reservation model C d W m k Qv B :=
  (GeneralPaperCachedBitPairReferenceContract.modified_reserve_le model C d W m k Qv B).trans
    (cached_reserve_le model C d W m k Qv B)

theorem complete_reserve_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) :
    GeneralPaperFastWholeDriverStorageRates.reservation model C d (width C d x) x.m x.k x.Qv x.B<2^width C d x :=
  (actual_reserve hg _ x).trans_lt (capacity C d x)

theorem reserved_address {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (address : ℕ)
    (h : address≤GeneralPaperFastWholeDriverStorageRates.reservation model C d (width C d x) x.m x.k x.Qv x.B) :
    binaryWordWidth address≤width C d x :=
  address_word C d x address (h.trans (actual_reserve hg _ x))

theorem native_local_words (C d : ℕ) (x : Input) :
    GeneralPaperControlMaterializationStorage.powerWord x.m (alphabet x).lambda x.k x.Qv≤width C d x ∧
      GeneralPaperControlMaterializationStorage.gridWord x.m (alphabet x).lambda x.k x.Qv≤width C d x := by
  unfold width padding
  omega

theorem constructor_words (C d : ℕ) (x : Input) :
    let W := width C d x
    binaryWordWidth x.B≤W ∧ binaryWordWidth (74+2*x.k+1)≤W ∧
      binaryWordWidth (128*GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv+1)≤W ∧
      binaryWordWidth (GeneralPaperFastDriverIndexReference.gridCount x+1)≤W ∧
      binaryWordWidth (GeneralPaperPrecallControlWord.measure x.m x.k+1)≤W ∧
      binaryWordWidth ((GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).columns+1)≤W ∧
      binaryWordWidth ((GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.size+1)≤W ∧
      binaryWordWidth ((GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent+1)≤W ∧
      binaryWordWidth ((GeneralPaperProxyParameters.prepare x.m x.k).gridBits+6)≤W := by
  have h := GeneralPaperFastDriverIndexReference.construction_ranges x
  exact ⟨index_address C d x _ h.1,index_address C d x _ h.2.1,index_address C d x _ h.2.2.1,
    index_address C d x _ h.2.2.2.1,index_address C d x _ h.2.2.2.2.1,
    index_address C d x _ (GeneralPaperFastDriverIndexReference.power_columns x),
    index_address C d x _ (GeneralPaperFastDriverIndexReference.grid_size x),
    index_address C d x _ (GeneralPaperFastDriverIndexReference.grid_height x),
    index_address C d x _ (GeneralPaperFastDriverIndexReference.front_depth x)⟩

end Blotto.GeneralPaperFastDriverReference
