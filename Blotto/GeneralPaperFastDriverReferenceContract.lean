import Blotto.GeneralPaperFastDriverReference

/-! Actual whole fast driver at the enlarged complete address reference.
Cached child hypotheses, all constructor/caller controls, every observed
window and native work are derived. Source and physical return identities
are inherited from the same once-only native run without acceptance input. -/
namespace Blotto.GeneralPaperFastDriverReferenceContract
open GeneralPaperSourceWordGrowth GeneralPaperFastDriverReference GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem cached_bounds {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    let W := width C d x
    ∀ cursor hc outer ho inner hi,
      GeneralPaperCachedBitPairStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤
        GeneralPaperCachedBitPairStorage.profile model C d W x.m x.k x.Qv x.B ∧
      (GeneralPaperCachedBitPairStorage.run model W x.k x.Qv hQv x.weights hp x.weight_sum x.b).2≤
        GeneralPaperCachedBitPairStorage.price model C d W x.m x.k x.Qv := by
  dsimp only
  intro cursor hc outer ho inner hi
  have hw := positive_width C d x
  have h := local_words C d x
  have hr := row_words C d x
  have hPrepared := GeneralPaperSourcePreparedPairOwners.bounded model (width C d x)
    x.k x.Qv hQv x.weights hp x.weight_sum x.b C d x.B hg hm x.hb x.hB hw h.2.1 h.2.2.1 h.2.2.2.1 h.1 h.2.2.2.2.1 h.2.2.2.2.2.1 hr.2
    cursor hc outer ho inner hi
  exact GeneralPaperCachedBitPairStorage.bounded_of_prepared model C d (width C d x) x.k x.Qv x.B hQv
    x.weights hp x.weight_sum x.b x.hb cursor hc outer ho inner hi hPrepared

theorem native_bounds {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    let W := width C d x
    ∀ (exponent target : ℕ),exponent≤74+2*x.k →
      GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x.m x.k).lambda x.k x.Qv target →
      ∀ (material : GeneralPaperFastPreparedInputStorage.Cursor x.m (alphabet x.m x.k).lambda x.k x.Qv)
        cursor hc outer ho inner hi,
      GeneralPaperFastWholeDriverStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb
          exponent target material cursor hc outer ho inner hi≤GeneralPaperFastWholeDriverStorage.profile model C d W x.m x.k x.Qv x.B ∧
        (GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤
          GeneralPaperFastWholeDriverStorage.price model C d W x.m x.k x.Qv x.B := by
  dsimp only
  intro exponent target he ht material cursor hc outer ho inner hi
  exact GeneralPaperFastWholeDriverStorage.bounded_of_cached model C d (width C d x) x.k x.Qv x.B hQv
    x.weights hp x.weight_sum x.b x.hb x.hB (control_word C d x) exponent target he ht material cursor hc outer ho inner hi
    (cached_bounds hg x hm hQv hp cursor hc outer ho inner hi)

theorem native_window {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    let W := width C d x
    ∀ (exponent target : ℕ),exponent≤74+2*x.k →
      GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x.m x.k).lambda x.k x.Qv target →
      ∀ (material : GeneralPaperFastPreparedInputStorage.Cursor x.m (alphabet x.m x.k).lambda x.k x.Qv)
        cursor hc outer ho inner hi,
      GeneralPaperFastWholeDriverStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb
          exponent target material cursor hc outer ho inner hi≤profile C d W x ∧
        (GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤
          GeneralPaperFastWholeDriverStorage.price model C d W x.m x.k x.Qv x.B ∧
        (∀ address,address≤GeneralPaperFastWholeDriverStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb
          exponent target material cursor hc outer ho inner hi → binaryWordWidth address≤W) := by
  dsimp only
  intro exponent target he ht material cursor hc outer ho inner hi
  have h := native_bounds hg x hm hQv hp exponent target he ht material cursor hc outer ho inner hi
  have hWindow := h.1.trans ((Nat.le_add_left _ _).trans (actual_reserve hg _ x))
  exact ⟨hWindow,h.2,fun address hAddress => address_word C d x address (hAddress.trans hWindow)⟩

theorem paper_space {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),
      let W := width C d x
      ∀ (exponent target : ℕ),exponent≤74+2*x.k →
        GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x.m x.k).lambda x.k x.Qv target →
        ∀ (material : GeneralPaperFastPreparedInputStorage.Cursor x.m (alphabet x.m x.k).lambda x.k x.Qv)
          cursor hc outer ho inner hi,
        GeneralPaperFastWholeDriverStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb
          exponent target material cursor hc outer ho inner hi≤A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := common_word_bound C d
  exact ⟨A,e,fun x hm hQv hp exponent target he ht material cursor hc outer ho inner hi =>
    ((native_window hg x hm hQv hp exponent target he ht material cursor hc outer ho inner hi).1).trans (h x)⟩

theorem actual_return {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (hm : 0<m) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(GeneralPaperFastRationalPairDriver.run model W W k Qv hQv weights hp hs b hb).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hs (b:ℝ)=some pair ∧
      GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs (b:ℝ) pair :=
  GeneralPaperFastRationalPairDriver.actual_return model W W k Qv hQv weights hp hs b hm hb

theorem simultaneous_window {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) (oldOwner : ℕ)
    (hOld : oldOwner≤GeneralPaperSourceControlStorageRates.reservation model C d (width C d x) x.m x.k x.Qv x.B) :
    let W := width C d x
    ∀ (exponent target : ℕ),exponent≤74+2*x.k →
      GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x.m x.k).lambda x.k x.Qv target →
      ∀ (material : GeneralPaperFastPreparedInputStorage.Cursor x.m (alphabet x.m x.k).lambda x.k x.Qv)
        cursor hc outer ho inner hi,
      oldOwner+GeneralPaperFastWholeDriverStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb
        exponent target material cursor hc outer ho inner hi≤profile C d W x := by
  dsimp only
  intro exponent target he ht material cursor hc outer ho inner hi
  have hNative := (native_bounds hg x hm hQv hp exponent target he ht material cursor hc outer ho inner hi).1
  exact (Nat.add_le_add hOld hNative).trans (actual_reserve hg _ x)

end Blotto.GeneralPaperFastDriverReferenceContract
