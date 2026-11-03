import Blotto.GeneralPaperFastPreparedInputStorage

/-! Complete once-only native bit driver, including both construction
phases and the cached pair computation. All original and returned owners
coexist. Whole native work bounds only its encoded parent metadata; new
scratch remains in the already checked scalar and constructor children. -/
namespace Blotto.GeneralPaperFastWholeDriverStorage
open GeneralPaperEncodedScalarStorage GeneralPaperProxyParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

noncomputable def price (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  GeneralPaperFastPreparedInputStorage.price model W m k Qv B+
    GeneralPaperCachedBitPairStorage.price model C d W m k Qv+192*W

noncomputable def metadataCap (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  m+k+Qv+price model C d W m k Qv B+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+
    (prepare m k).K+256*W+1

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hb : 0<b ∧ b<1)
    (exponent target : ℕ) (material : GeneralPaperFastPreparedInputStorage.Cursor m (alphabet m k).lambda k Qv)
    (cursor : ℕ) (hc : cursor≤m) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) : ℕ :=
  let prepared := GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb
  let cached := GeneralPaperCachedBitPairStorage.run model W k Qv hQv weights hp hs b
  let result := GeneralPaperFastRationalPairDriver.run model W W k Qv hQv weights hp hs b hb
  GeneralPaperFastPreparedInputStorage.window model W m k Qv b hb exponent target material+
    GeneralPaperCachedBitPairStorage.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi+
    GeneralPaperFastPreparedInputStorage.inputFoot W b prepared.1+rationalWordWidth b+GeneralPaperEncodedNatArray.footprint W weights+
    GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1+
    fields W [m,k,Qv,W,prepared.2,cached.2,result.2,prepared.2+cached.2,192*W,
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows,(prepare m k).K,128*W]+256*W

noncomputable def profile (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  2*GeneralPaperFastPreparedInputStorage.profile model W m k Qv B+
    3*GeneralPaperCachedBitPairStorage.profile model C d W m k Qv B+
    12*(natBits (metadataCap model C d W m k Qv B)+W)+288*W

theorem parent_fields (W m k Qv rows labels P A B R : ℕ) (he : R=A+B+192*W) (hr : R≤P) :
    fields W [m,k,Qv,W,A,B,R,A+B,192*W,rows,labels,128*W]≤
      12*(natBits (m+k+Qv+P+rows+labels+256*W+1)+W)+32*W := by
  apply fields_bound W _
  intro z hz
  apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem bounded_of_cached {m : ℕ} (model : RationalCostModel) (C d W k Qv B : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hb : 0<b ∧ b<1)
    (hB : RationalHeight b B) (hW : GeneralPaperPrecallControlWord.word m k≤W)
    (exponent target : ℕ) (he : exponent≤74+2*k)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m (alphabet m k).lambda k Qv target)
    (material : GeneralPaperFastPreparedInputStorage.Cursor m (alphabet m k).lambda k Qv)
    (cursor : ℕ) (hc : cursor≤m) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K)
    (hCached : GeneralPaperCachedBitPairStorage.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi≤
        GeneralPaperCachedBitPairStorage.profile model C d W m k Qv B ∧
      (GeneralPaperCachedBitPairStorage.run model W k Qv hQv weights hp hs b).2≤
        GeneralPaperCachedBitPairStorage.price model C d W m k Qv) :
    window model W k Qv hQv weights hp hs b hb exponent target material cursor hc outer ho inner hi≤profile model C d W m k Qv B ∧
      (GeneralPaperFastRationalPairDriver.run model W W k Qv hQv weights hp hs b hb).2≤price model C d W m k Qv B := by
  let prepared := GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb
  let cached := GeneralPaperCachedBitPairStorage.run model W k Qv hQv weights hp hs b
  let result := GeneralPaperFastRationalPairDriver.run model W W k Qv hQv weights hp hs b hb
  have hPrep := GeneralPaperFastPreparedInputStorage.bounded model W m k Qv B b hb hB hW exponent target he ht material
  have hPW : prepared.2≤GeneralPaperFastPreparedInputStorage.price model W m k Qv B := hPrep.2
  have hCW : cached.2≤GeneralPaperCachedBitPairStorage.price model C d W m k Qv := hCached.2
  have hEq := congrArg Prod.snd (GeneralPaperFastRationalPairDriver.run_data model W W k Qv hQv weights hp hs b hb)
  change result.2=prepared.2+cached.2+192*W at hEq
  have hWork : result.2≤price model C d W m k Qv B := by unfold price;omega
  have hInput := (GeneralPaperFastPreparedInputStorage.returned model W m k Qv b hb exponent target material).trans hPrep.1
  have hOriginal : rationalWordWidth b+GeneralPaperEncodedNatArray.footprint W weights≤
      GeneralPaperCachedBitPairStorage.profile model C d W m k Qv B := by
    apply le_trans (b:=GeneralPaperCachedBitPairStorage.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi) ?_ hCached.1
    dsimp only [GeneralPaperCachedBitPairStorage.window,GeneralPaperCachedBitPairStorage.owners]
    omega
  have hReturn := congrArg Prod.fst (GeneralPaperFastRationalPairDriver.run_data model W W k Qv hQv weights hp hs b hb)
  change result.1=cached.1 at hReturn
  have hOutput : GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1≤
      GeneralPaperCachedBitPairStorage.profile model C d W m k Qv B := by
    rw [hReturn]
    change GeneralPaperRetainedCompilerPairStorage.optionFoot W (GeneralPaperCachedBitPairStorage.run model W k Qv hQv weights hp hs b).1≤_
    apply le_trans (b:=GeneralPaperCachedBitPairStorage.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi) ?_ hCached.1
    dsimp only [GeneralPaperCachedBitPairStorage.window]
    omega
  have hf := parent_fields W m k Qv (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K
    (price model C d W m k Qv B) prepared.2 cached.2 result.2 hEq hWork
  change fields W _≤12*(natBits (metadataCap model C d W m k Qv B)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  have hCore := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hPrep.1 hCached.1) hInput) hOriginal) hOutput) hf) (256*W)
  convert hCore using 1 <;> dsimp only [window,profile,prepared,cached,result] <;> ring

theorem at_cached_reference {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (x : GeneralPaperSourceWordGrowth.Input) (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j)
    (exponent target : ℕ) (he : exponent≤74+2*x.k)
    (ht : GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x.m x.k).lambda x.k x.Qv target)
    (material : GeneralPaperFastPreparedInputStorage.Cursor x.m (alphabet x.m x.k).lambda x.k x.Qv)
    (cursor : ℕ) (hc : cursor≤x.m) (outer : ℕ) (ho : outer≤x.m) (inner : ℕ) (hi : inner≤(prepare x.m x.k).K) :
    let W := GeneralPaperCachedBitPairReferenceContract.width C d x
    window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb exponent target material cursor hc outer ho inner hi≤
        profile model C d W x.m x.k x.Qv x.B ∧
      (GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤price model C d W x.m x.k x.Qv x.B :=
  bounded_of_cached model C d _ x.k x.Qv x.B hQv x.weights hp x.weight_sum x.b x.hb x.hB
    (GeneralPaperCachedBitPairReferenceContract.control_word C d x) exponent target he ht material cursor hc outer ho inner hi
    (GeneralPaperCachedBitPairReferenceContract.native_bounds hg x hm hQv hp cursor hc outer ho inner hi)

end Blotto.GeneralPaperFastWholeDriverStorage
