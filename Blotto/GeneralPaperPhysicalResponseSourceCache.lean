import Blotto.GeneralPaperPhysicalResponseSourceExecution

/-! Construct the shared physical shift once before entering the source.
The full trajectory and check flag are returned without a second source,
classifier, selector or encoding pass. -/
namespace Blotto.GeneralPaperPhysicalResponseSourceCache
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperSourceRowsExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def run {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) :
    ((GeneralPaperCatalogueTreeCache.Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) × ℕ :=
  let delta := GeneralPaperPhysicalShiftExecution.run bits model W m qbar a.C
  let produced := GeneralPaperPhysicalResponseSourceExecution.run bits (index bits) model W k Qv a c hc shared delta.1 count
  (produced.1,delta.2+produced.2+128*W)

theorem base_data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) :
    (run bits model W k Qv qbar a c hc shared count).1.1=
      (GeneralPaperGeometricSourceExecution.run bits (index bits) model W k Qv a c hc shared count).1 := by
  unfold run
  dsimp only
  exact GeneralPaperPhysicalResponseSourceExecution.base_data bits (index bits) model W k Qv a c hc shared _ count

theorem data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (run bits model W k Qv qbar a c hc shared count).1.1=GeneralPaperCatalogueOuterLoop.execute shared a k count := by
  dsimp only
  rw [base_data]
  exact GeneralPaperGeometricSourceExecution.data bits (index bits) model W k Qv a c hc weights Bc Br count he

theorem checked {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv q qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (hm : 0<m) (hQv : 0<Qv) (hq : 0<q) (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv)
    (hB : 0≤Br) (hDen : Br.den∣q)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    (run bits model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count).1.2=true := by
  unfold run
  dsimp only
  rw [GeneralPaperPhysicalShiftExecution.data]
  exact GeneralPaperPhysicalResponseSourceExecution.checked bits (index bits) model W k Qv q qbar a c hc weights Bc Br count
    hm hQv hq hCap hw hB hDen he

theorem size {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    (run bits model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count).1.1.2.size=
      count*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period := by
  rw [base_data]
  exact GeneralPaperGeometricSourceExecution.size bits (index bits) model W k Qv a c hc weights Bc Br count he

theorem models_data {m : ℕ} (model : RationalCostModel) (W k Qv q qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (hm : 0<m) (hQv : 0<Qv) (hq : 0<q) (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv)
    (hB : 0≤Br) (hDen : Br.den∣q)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    (run true model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count).1=
      (run false model 1 k Qv qbar a c hc (prepare a k Qv weights Bc Br) count).1 := by
  apply Prod.ext
  · exact (data true model W k Qv qbar a c hc weights Bc Br count he).trans
      (data false model 1 k Qv qbar a c hc weights Bc Br count he).symm
  · rw [checked true model W k Qv q qbar a c hc weights Bc Br count hm hQv hq hCap hw hB hDen he,
      checked false model 1 k Qv q qbar a c hc weights Bc Br count hm hQv hq hCap hw hB hDen he]

def bitExtra {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (shared : Shared m) (count : ℕ) : ℕ :=
  count*GeneralPaperPhysicalResponseSourceExecution.bitExtra model W m qbar t a shared+
    GeneralPaperPhysicalShiftExecution.bitProfile model W m qbar a.C+128*W

def arithmeticExtra {m : ℕ} (a : Alphabet) (shared : Shared m) (count : ℕ) : ℕ :=
  count*GeneralPaperPhysicalResponseSourceExecution.arithmeticExtra a shared+
    64*(binaryWordWidth (m+2)+1)^2+268

theorem bit_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) (hC : 0<a.C)
    (hSpan : shared.profit.parameters.leafCount=2^shared.profit.parameters.height) (hBr : RationalHeight shared.Br t) :
    (run true model W k Qv qbar a c hc shared count).2≤
      (GeneralPaperGeometricSourceExecution.run true (fun w => w) model W k Qv a c hc shared count).2+
      bitExtra model W qbar t a shared count := by
  have hs := GeneralPaperPhysicalResponseSourceExecution.bit_extra model W k Qv qbar t a c hc shared
    (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1 count hSpan
    (GeneralPaperPhysicalShiftExecution.height true model W m qbar a.C) hBr
  have hd := GeneralPaperPhysicalShiftExecution.bit_work model W m qbar a.C hC
  unfold run bitExtra
  dsimp only
  simp only [index,ite_true]
  nlinarith only [hs,hd]

theorem arithmetic_extra {m : ℕ} (model : RationalCostModel) (k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) :
    (run false model 1 k Qv qbar a c hc shared count).2≤
      (GeneralPaperGeometricSourceExecution.run false (fun _ => 1) model 1 k Qv a c hc shared count).2+
      arithmeticExtra a shared count := by
  have hs := GeneralPaperPhysicalResponseSourceExecution.arithmetic_extra model k Qv a c hc shared
    (GeneralPaperPhysicalShiftExecution.run false model 1 m qbar a.C).1 count
  have hd := GeneralPaperPhysicalShiftExecution.arithmetic_work model m qbar a.C
  unfold run arithmeticExtra
  dsimp only
  simp only [index,Bool.false_eq_true,ite_false]
  nlinarith only [hs,hd]

end Blotto.GeneralPaperPhysicalResponseSourceCache
