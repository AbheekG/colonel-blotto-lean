import Blotto.GeneralPaperFastDriverSharpWork

/-! Unit arithmetic prices for the existing retained source/quantizer.
All source heights are derived from its returned rows. The real price
erases operand lengths; no unit rational bit model is assumed. -/
namespace Blotto.GeneralPaperArithmeticUnitSourceWork
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint GeneralPaperCatalogueShared
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def columnPrice (T K : ℕ) : ℕ :=
  T*64+44*(T+1)+(GeneralPaperNativeRepresentativeSort.profile T 1 1+
    T*(512*(binaryWordWidth T+1)*2+64)+192*(2*T+1)+K*69+44*(K+1)+64)+32

def unitPrice (T m K : ℕ) : ℕ :=
  512*(binaryWordWidth ((T+1)*K)+1)*2+m*(columnPrice T K+64)+44*(m+1)+64+
    (m*(K*66+44*(K+1)+96)+44*(m+1)+2+32)+64

theorem unit_profile (T m K C H : ℕ) (hDiv : K∣T) :
    GeneralPaperNativeUnitSourceJoin.profile (fun _ => 1) 1 C H T m K (T/K)=unitPrice T m K := by
  simp only [GeneralPaperNativeUnitSourceJoin.profile,GeneralPaperNativeQuantizedMatrix.fieldProfile,
    GeneralPaperNativeQuantizedColumn.profile,Nat.mul_div_cancel' hDiv,columnPrice,unitPrice,
    Nat.mul_one,Nat.reduceAdd]

theorem unit_work {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (C H : ℕ)
    (hc : RationalHeight budget C) (hr : ∀ i j,RationalHeight ((rows.read i).read j) H) :
    (GeneralPaperNativeUnitSourceJoin.run (fun _ => 1) (fun _ => 1) 1 hT hK hDiv budget rows).2≤unitPrice T m K := by
  have h := GeneralPaperNativeUnitSourceJoin.work (fun _ => 1) (fun _ => 1) (fun _ _ _ => le_rfl)
    1 C H le_rfl hT hK hDiv budget hc rows hr (fun _ _ => le_rfl)
  rw [GeneralPaperNativeDivisibleColumns.blocks_data,unit_profile T m K C H hDiv] at h
  exact h

def sourcePrice (m k Qv : ℕ) : ℕ :=
  GeneralPaperSourceRowsDriver.arithmeticProfile m k Qv (alphabet m k)+
    unitPrice (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K+64

theorem source_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ)
    (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (shared : Shared m)
    (hs : shared=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (GeneralPaperRetainedSourceColumns.run model k Qv (alphabet m k) c hc weights _ _ shared hs hT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).2≤sourcePrice m k Qv := by
  let rows := GeneralPaperRetainedSourceRows.run false model 1 k Qv (alphabet m k) c hc weights _ _ shared hs hT
  have hd : rows.1.1=GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal := by
    dsimp only [rows]
    rw [GeneralPaperRetainedSourceRows.data,GeneralPaperSourceRowsDriver.rational_data false model 1 k Qv (prepare m k).qbar]
    rfl
  have hr : rows.2≤GeneralPaperSourceRowsDriver.arithmeticProfile m k Qv (alphabet m k) := by
    dsimp only [rows]
    rw [GeneralPaperRetainedSourceRows.data]
    exact GeneralPaperSourceRowsDriver.arithmetic_work model k Qv (alphabet m k) c hc weights _ _ shared hs hw
  have hBudget : RationalHeight shared.Bc (binaryWordWidth (prepare m k).qbar) := by
    rw [hs]
    exact GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal
  have hRows : ∀ i j,RationalHeight ((rows.1.1.read i).read j) (binaryWordWidth (alphabet m k).C) := by
    rw [hd]
    exact GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal
  have hu := unit_work (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) shared.Bc rows.1.1 _ _ hBudget hRows
  change (GeneralPaperNativeUnitSourceJoin.run (fun _ => 1) (fun _ => 1) 1 _ _ _ shared.Bc rows.1.1).2≤
    unitPrice (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K at hu
  change rows.2+(GeneralPaperNativeUnitSourceJoin.run (fun _ => 1) (fun _ => 1) 1 _ _ _ shared.Bc rows.1.1).2+64≤_
  unfold sourcePrice
  omega

def unitCertificate : Certificate (fun x => unitPrice
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperSourceWordGrowth.alphabet x).lambda x.k).rows x.m (prepare x.m x.k).K) := by
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  refine ⟨_,_,_,by
    unfold unitPrice columnPrice GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile
    source_space⟩

theorem unit_degrees : (unitCertificate.fields,unitCertificate.symbols,unitCertificate.accuracy)=(2,0,3) := rfl

theorem unit_rate : Soft GeneralPaperSourceCallerSharpWork.realRate
    (fun x => unitPrice (GeneralPaperTrajectoryParameters.prepare (GeneralPaperSourceWordGrowth.alphabet x).lambda x.k).rows x.m (prepare x.m x.k).K) := by
  apply rate_mono (weaken unitCertificate.bound (show 2≤2 by decide) le_rfl (show 3≤5 by decide))
  intro x
  change monomial 2 0 5 x≤_
  unfold GeneralPaperSourceCallerSharpWork.realRate
  omega

theorem source_rate : Soft GeneralPaperSourceCallerSharpWork.realRate (fun x => sourcePrice x.m x.k x.Qv) := by
  have hc : Soft GeneralPaperSourceCallerSharpWork.realRate (fun _ => 64) := by
    apply rate_mono (weaken (constant 64) (show 0≤2 by decide) le_rfl (show 0≤5 by decide))
    intro x
    unfold GeneralPaperSourceCallerSharpWork.realRate
    omega
  exact add_same (add_same GeneralPaperSourceCallerSharpWork.arithmetic_source_rate unit_rate) hc

end Blotto.GeneralPaperArithmeticUnitSourceWork
