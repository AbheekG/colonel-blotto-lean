import Blotto.GeneralPaperFastInputClassifier

/-! Full once-only bit driver with the efficient original-input front.
The returned control cache feeds one power/grid materialization, then one
cached pair computation. The complete actual work sum and physical Matches
are proved; simultaneous outer constructor storage is joined separately. -/
namespace Blotto.GeneralPaperFastRationalPairDriver
open GeneralPaperProxyParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def prepare (model : RationalCostModel) (Wf m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    GeneralPaperCachedSourcePair.Input m k Qv (b:ℝ)×ℕ :=
  let front := GeneralPaperFastInputClassifier.source model Wf m k Qv b
  let Wg := GeneralPaperSourcePreparationControls.word m front.1.1.1.2.lambda k Qv
  let grid := GeneralPaperMaterializationFromControls.bit model Wg k front.1.2
  let hFront := (GeneralPaperFastInputClassifier.source_data model Wf m k Qv b hb).trans
    (GeneralPaperSourcePrecallPreparation.data model Wf m k Qv b)
  let hA : front.1.1.1.2=alphabet m k := congrArg (fun r => r.1.1.2) hFront
  let hControls : front.1.2=GeneralPaperSourcePreparationCache.specification m front.1.1.1.2.lambda k Qv := by
    rw [hA]
    exact congrArg Prod.snd hFront
  let hGrid := GeneralPaperMaterializationFromControls.bit_data model Wg m front.1.1.1.2.lambda k Qv front.1.2 hControls
  (⟨front.1.1.1.1,front.1.1.1.2,grid.1,front.1.1.2,
      congrArg (fun r => r.1.1.1) hFront,hA,hGrid,congrArg (fun r => r.1.2) hFront⟩,
    front.2+grid.2+128)

theorem prepared_data (model : RationalCostModel) (Wf m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    (prepare model Wf m k Qv b hb).1=GeneralPaperCachedBitPairStorage.input m k Qv b :=
  GeneralPaperRationalSourcePairData.input_unique _ _

def gridPrice (model : RationalCostModel) (m k Qv : ℕ) : ℕ :=
  let lambda := (alphabet m k).lambda
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  (524288*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*
    model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)

def preparePrice (model : RationalCostModel) (Wf m k Qv B : ℕ) : ℕ :=
  GeneralPaperFastInputClassifier.sourceProfile model Wf m k Qv B+gridPrice model m k Qv+128

theorem prepare_work (model : RationalCostModel) (Wf m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    (prepare model Wf m k Qv b hb).2≤preparePrice model Wf m k Qv B := by
  let front := GeneralPaperFastInputClassifier.source model Wf m k Qv b
  have hFront := (GeneralPaperFastInputClassifier.source_data model Wf m k Qv b hb).trans
    (GeneralPaperSourcePrecallPreparation.data model Wf m k Qv b)
  have hA : front.1.1.1.2=alphabet m k := congrArg (fun r => r.1.1.2) hFront
  have hControls : front.1.2=GeneralPaperSourcePreparationCache.specification m front.1.1.1.2.lambda k Qv := by
    rw [hA]
    exact congrArg Prod.snd hFront
  have hGrid := GeneralPaperMaterializationFromControls.bit_work model m front.1.1.1.2.lambda k Qv front.1.2 hControls
  change (GeneralPaperMaterializationFromControls.bit model
      (GeneralPaperSourcePreparationControls.word m front.1.1.1.2.lambda k Qv) k front.1.2).2≤
    (524288*(GeneralPaperSourcePreparationSizes.measure m front.1.1.1.2.lambda k Qv+1)+
      GeneralPaperProfitGridProfile.bound (GeneralPaperProfitParameters.parameters m front.1.1.1.2.lambda k Qv).width
        (GeneralPaperProfitParameters.parameters m front.1.1.1.2.lambda k Qv).exponent)*
      model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m front.1.1.1.2.lambda k Qv) at hGrid
  have hPrice : (524288*(GeneralPaperSourcePreparationSizes.measure m front.1.1.1.2.lambda k Qv+1)+
      GeneralPaperProfitGridProfile.bound (GeneralPaperProfitParameters.parameters m front.1.1.1.2.lambda k Qv).width
        (GeneralPaperProfitParameters.parameters m front.1.1.1.2.lambda k Qv).exponent)*
      model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m front.1.1.1.2.lambda k Qv)=gridPrice model m k Qv := by
    rw [hA]
    rfl
  rw [hPrice] at hGrid
  have hSource := GeneralPaperFastInputClassifier.source_work model Wf m k Qv b hb B hB
  exact Nat.add_le_add_right (Nat.add_le_add hSource hGrid) _

def run {m : ℕ} (model : RationalCostModel) (W Wf k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hb : 0<b ∧ b<1) :=
  let prepared := prepare model Wf m k Qv b hb
  let compiled := GeneralPaperCachedBitSourcePair.run model W k Qv hQv weights hp hs (b:ℝ) prepared.1
  (compiled.1,prepared.2+compiled.2+192*W)

theorem run_data {m : ℕ} (model : RationalCostModel) (W Wf k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hb : 0<b ∧ b<1) :
    run model W Wf k Qv hQv weights hp hs b hb=
      ((GeneralPaperCachedBitPairStorage.run model W k Qv hQv weights hp hs b).1,
        (prepare model Wf m k Qv b hb).2+(GeneralPaperCachedBitPairStorage.run model W k Qv hQv weights hp hs b).2+192*W) := by
  have h := GeneralPaperCachedBitPairStorage.actual_input model W k Qv hQv weights hp hs b (prepare model Wf m k Qv b hb).1
  exact congrArg (fun out => (out.1,(prepare model Wf m k Qv b hb).2+out.2+192*W)) h

noncomputable def price (model : RationalCostModel) (C d W Wf m k Qv B : ℕ) : ℕ :=
  preparePrice model Wf m k Qv B+GeneralPaperCachedBitPairStorage.price model C d W m k Qv+192*W

theorem work_of_cached {m : ℕ} (model : RationalCostModel) (C d W Wf k Qv B : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hb : 0<b ∧ b<1)
    (hB : RationalHeight b B)
    (hCached : (GeneralPaperCachedBitPairStorage.run model W k Qv hQv weights hp hs b).2≤
      GeneralPaperCachedBitPairStorage.price model C d W m k Qv) :
    (run model W Wf k Qv hQv weights hp hs b hb).2≤price model C d W Wf m k Qv B := by
  have h := congrArg Prod.snd (run_data model W Wf k Qv hQv weights hp hs b hb)
  have hPrep := prepare_work model Wf m k Qv b hb B hB
  rw [h]
  exact Nat.add_le_add_right (Nat.add_le_add hPrep hCached) _

theorem work_at_cached_reference {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (x : GeneralPaperSourceWordGrowth.Input) (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j) (Wf : ℕ) :
    let W := GeneralPaperCachedBitPairReferenceContract.width C d x
    (run model W Wf x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤price model C d W Wf x.m x.k x.Qv x.B := by
  have h := (GeneralPaperCachedBitPairReferenceContract.native_bounds hg x hm hQv hp 0 (by omega) 0 (by omega) 0 (by omega)).2
  exact work_of_cached model C d _ Wf x.k x.Qv x.B hQv x.weights hp x.weight_sum x.b x.hb x.hB h

theorem actual_return {m : ℕ} (model : RationalCostModel) (W Wf k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hm : 0<m) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(run model W Wf k Qv hQv weights hp hs b hb).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hs (b:ℝ)=some pair ∧
      GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs (b:ℝ) pair := by
  obtain ⟨physical,pair,hNative,hSource,hMatch,hContract⟩ := GeneralPaperCachedBitPairReferenceContract.actual_return
    model W k Qv hQv weights hp hs b hm hb (prepare model Wf m k Qv b hb).1
  exact ⟨physical,pair,hNative,hSource,hMatch,hContract⟩

end Blotto.GeneralPaperFastRationalPairDriver
