import Blotto.GeneralPaperControlMaterializationStorage

/-! Complete once-only fast prepared-input caller. Its original ratio,
full source front/control cache and returned materialized input remain
resident through both native construction phases. Cursor records and
return identities are erased analysis, not an extra preparation pass. -/
namespace Blotto.GeneralPaperFastPreparedInputStorage
open GeneralPaperEncodedScalarStorage GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

structure Cursor (m lambda k Qv : ℕ) where
  columns : ℕ
  height : ℕ
  copied : ℕ
  count : ℕ
  columns_le : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns
  height_le : height≤(GeneralPaperProfitParameters.parameters m lambda k Qv).exponent
  count_le : count≤(GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size

def controls (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) : GeneralPaperSourcePreparationCache.Cache :=
  (GeneralPaperFastInputClassifier.source model W m k Qv b).1.2

theorem alphabet_data (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    (GeneralPaperFastInputClassifier.source model W m k Qv b).1.1.1.2=alphabet m k := by
  have h := (GeneralPaperFastInputClassifier.source_data model W m k Qv b hb).trans
    (GeneralPaperSourcePrecallPreparation.data model W m k Qv b)
  exact congrArg (fun r => r.1.1.2) h

theorem controls_data (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    controls model W m k Qv b=GeneralPaperSourcePreparationCache.specification m (alphabet m k).lambda k Qv := by
  have h := (GeneralPaperFastInputClassifier.source_data model W m k Qv b hb).trans
    (GeneralPaperSourcePrecallPreparation.data model W m k Qv b)
  exact congrArg Prod.snd h

def materialization (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) :=
  GeneralPaperMaterializationFromControls.bit model
    (GeneralPaperControlMaterializationStorage.powerWord m (alphabet m k).lambda k Qv) k (controls model W m k Qv b)

theorem native_work_data (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    (GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb).2=
      (GeneralPaperFastInputClassifier.source model W m k Qv b).2+(materialization model W m k Qv b).2+128 := by
  change (GeneralPaperFastInputClassifier.source model W m k Qv b).2+
    (GeneralPaperMaterializationFromControls.bit model
      (GeneralPaperSourcePreparationControls.word m (GeneralPaperFastInputClassifier.source model W m k Qv b).1.1.1.2.lambda k Qv)
      k (controls model W m k Qv b)).2+128=_
  rw [alphabet_data model W m k Qv b hb]
  rfl

def inputFoot {m k Qv : ℕ} (W : ℕ) (b : ℚ) (x : GeneralPaperCachedSourcePair.Input m k Qv (b:ℝ)) : ℕ :=
  GeneralPaperClassifierResultStorage.frontFootprint W ((x.control,x.alphabet),x.classified)+
    GeneralPaperMaterializedCacheStorage.gridFootprint W x.grid+rationalWordWidth b+128*W

theorem native_input (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    inputFoot W b (GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb).1=
      GeneralPaperClassifierResultStorage.frontFootprint W (GeneralPaperFastInputClassifier.source model W m k Qv b).1.1+
        GeneralPaperMaterializedCacheStorage.gridFootprint W (materialization model W m k Qv b).1+rationalWordWidth b+128*W := by
  dsimp only [inputFoot,GeneralPaperFastRationalPairDriver.prepare]
  apply congrArg (fun g => GeneralPaperClassifierResultStorage.frontFootprint W
    (GeneralPaperFastInputClassifier.source model W m k Qv b).1.1+
      GeneralPaperMaterializedCacheStorage.gridFootprint W g+rationalWordWidth b+128*W)
  rw [alphabet_data model W m k Qv b hb]
  rfl

def materializationWindow (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (cursor : Cursor m (alphabet m k).lambda k Qv) : ℕ :=
  let c := controls model W m k Qv b
  let hcount : cursor.count≤(GeneralPaperProfitGridPrepare.prepare c.profit.qProf c.profit.width c.profit.exponent).size := by
    dsimp only [c]
    rw [controls_data model W m k Qv b hb]
    exact cursor.count_le
  GeneralPaperControlMaterializationStorage.window model W m (alphabet m k).lambda k Qv c
    cursor.columns cursor.height cursor.copied cursor.count hcount

theorem materialization_bounded (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (cursor : Cursor m (alphabet m k).lambda k Qv) :
    materializationWindow model W m k Qv b hb cursor≤
      GeneralPaperControlMaterializationStorage.profile model W m (alphabet m k).lambda k Qv ∧
      (materialization model W m k Qv b).2≤GeneralPaperControlMaterializationStorage.price model m (alphabet m k).lambda k Qv := by
  apply GeneralPaperControlMaterializationStorage.bounded model W m (alphabet m k).lambda k Qv
    (controls model W m k Qv b) (controls_data model W m k Qv b hb) cursor.columns cursor.height cursor.copied cursor.count
  · rw [controls_data model W m k Qv b hb];exact cursor.columns_le
  · rw [controls_data model W m k Qv b hb];exact cursor.height_le

def price (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  GeneralPaperFastSourceControlStorage.price model W m k Qv B+
    GeneralPaperControlMaterializationStorage.price model m (alphabet m k).lambda k Qv+128

def metadataCap (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  m+k+Qv+price model W m k Qv B+256*W+129

def window (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (exponent target : ℕ) (cursor : Cursor m (alphabet m k).lambda k Qv) : ℕ :=
  let f := GeneralPaperFastInputClassifier.source model W m k Qv b
  let g := materialization model W m k Qv b
  let result := GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb
  GeneralPaperFastSourceControlStorage.window model W m k Qv b exponent target+
    materializationWindow model W m k Qv b hb cursor+inputFoot W b result.1+
    fields W [m,k,Qv,W,f.2,g.2,result.2,f.2+g.2,128,64*W,128*W,256*W]+256*W

def profile (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  2*GeneralPaperFastSourceControlStorage.profile model W m k Qv B+
    2*GeneralPaperControlMaterializationStorage.profile model W m (alphabet m k).lambda k Qv+
    12*(natBits (metadataCap model W m k Qv B)+W)+416*W

theorem parent_fields (W m k Qv P A B R : ℕ) (he : R=A+B+128) (hr : R≤P) :
    fields W [m,k,Qv,W,A,B,R,A+B,128,64*W,128*W,256*W]≤
      12*(natBits (m+k+Qv+P+256*W+129)+W)+32*W := by
  apply fields_bound W _
  intro z hz
  apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem bounded (model : RationalCostModel) (W m k Qv B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) (exponent target : ℕ) (he : exponent≤74+2*k)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m (alphabet m k).lambda k Qv target)
    (cursor : Cursor m (alphabet m k).lambda k Qv) :
    window model W m k Qv b hb exponent target cursor≤profile model W m k Qv B ∧
      (GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb).2≤price model W m k Qv B := by
  let f := GeneralPaperFastInputClassifier.source model W m k Qv b
  let g := materialization model W m k Qv b
  let result := GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb
  have hFront := GeneralPaperFastSourceControlStorage.bounded model W m k Qv B b hb hB hW exponent target he ht
  have hMat := materialization_bounded model W m k Qv b hb cursor
  have hEq := native_work_data model W m k Qv b hb
  change result.2=f.2+g.2+128 at hEq
  have hFW : f.2≤GeneralPaperFastSourceControlStorage.price model W m k Qv B := hFront.2
  have hGW : g.2≤GeneralPaperControlMaterializationStorage.price model m (alphabet m k).lambda k Qv := hMat.2
  have hWork : result.2≤price model W m k Qv B := by unfold price;omega
  have hFrontOwned := (GeneralPaperFastSourceControlStorage.retained_inputs model W m k Qv b exponent target).trans hFront.1
  have hMatOwned := (GeneralPaperControlMaterializationStorage.returned model W m (alphabet m k).lambda k Qv
    (controls model W m k Qv b) cursor.columns cursor.height cursor.copied cursor.count
    (by rw [controls_data model W m k Qv b hb];exact cursor.count_le)).trans hMat.1
  have hInput : inputFoot W b result.1≤GeneralPaperFastSourceControlStorage.profile model W m k Qv B+
      GeneralPaperControlMaterializationStorage.profile model W m (alphabet m k).lambda k Qv+128*W := by
    rw [native_input model W m k Qv b hb]
    change GeneralPaperClassifierResultStorage.frontFootprint W f.1.1+
      GeneralPaperMaterializedCacheStorage.gridFootprint W g.1+rationalWordWidth b+128*W≤_
    change GeneralPaperMaterializedCacheStorage.gridFootprint W g.1≤_ at hMatOwned
    change GeneralPaperClassifierResultStorage.frontFootprint W f.1.1+_+rationalWordWidth b≤_ at hFrontOwned
    omega
  have hf := parent_fields W m k Qv (price model W m k Qv B) f.2 g.2 result.2 hEq hWork
  change fields W _≤12*(natBits (metadataCap model W m k Qv B)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  have hCore := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hFront.1 hMat.1) hInput) hf) (256*W)
  exact hCore.trans_eq (by dsimp only [profile];ring)

theorem returned (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (exponent target : ℕ) (cursor : Cursor m (alphabet m k).lambda k Qv) :
    inputFoot W b (GeneralPaperFastRationalPairDriver.prepare model W m k Qv b hb).1≤
      window model W m k Qv b hb exponent target cursor := by
  dsimp only [window]
  omega

end Blotto.GeneralPaperFastPreparedInputStorage
