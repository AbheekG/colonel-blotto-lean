import Blotto.GeneralPaperPowerPreparationEnvelope

/-! Retain parameter controls and their materialized power table together.
The actual data path constructs parameters once, then extends that returned
cache. Arithmetic and bit implementations agree exactly. Profit-grid and
source/query/global-storage joins are subsequent phases.
-/
namespace Blotto.GeneralPaperMaterializedPowerCache
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

structure Cache where
  controls : GeneralPaperSourcePreparationCache.Cache
  powers : GeneralPaperPreparedPowers.Prepared

def specification (m lambda k Qv : ℕ) : Cache :=
  ⟨GeneralPaperSourcePreparationCache.specification m lambda k Qv,GeneralPaperPreparedPowers.prepare lambda k⟩

def extend (primitive : ℕ → ℕ) (W k : ℕ) (controls : GeneralPaperSourcePreparationCache.Cache) : Cache × ℕ :=
  let powers := GeneralPaperCachedPowerPreparation.fromCache primitive W k controls
  (⟨controls,powers.1⟩,powers.2+32*W)

def prepare (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) : Cache × ℕ :=
  let controls := GeneralPaperSourcePreparationCache.prepare primitive W m lambda k Qv
  let result := extend primitive W k controls.1
  (result.1,controls.2+result.2+32*W)

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    (prepare primitive W m lambda k Qv).1=specification m lambda k Qv := by
  simp only [prepare,extend,GeneralPaperSourcePreparationCache.data,
    GeneralPaperCachedPowerPreparation.data primitive W m lambda k Qv _ rfl,specification]

theorem bit_work (model : RationalCostModel) (m lambda k Qv : ℕ) :
    let W := GeneralPaperSourcePreparationControls.word m lambda k Qv
    (prepare model.rat W m lambda k Qv).2≤1048576*GeneralPaperSourcePreparationSizes.measure m lambda k Qv*
      model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  let W := GeneralPaperSourcePreparationControls.word m lambda k Qv
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let P := model.rat H
  have hs := GeneralPaperSourcePreparationControls.bit_work model m lambda k Qv
  have hp := GeneralPaperPowerPreparationEnvelope.bit_work model m lambda k Qv
    (GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).1
    (GeneralPaperSourcePreparationCache.data model.rat W m lambda k Qv)
  have hWidth : GeneralPaperSourcePreparationSizes.width m lambda k Qv≤H := by
    dsimp [H,GeneralPaperSourcePreparationSizes.width,GeneralPaperPowerPreparationEnvelope.operandWidth]
    omega
  have hSource := hs.trans (Nat.mul_le_mul_left (524288*M) (model.monotone hWidth))
  change _≤524288*M*P at hSource
  change _≤262144*M*P at hp
  have hw := (GeneralPaperSourcePreparationControls.word_le_operand_width m lambda k Qv).trans hWidth
  have hWP : W≤P := hw.trans (model.word_le H)
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  have hMP : P≤M*P := by
    have hh : 1≤M := by dsimp only [M]; omega
    simpa only [one_mul] using Nat.mul_le_mul_right P hh
  change (prepare model.rat W m lambda k Qv).2≤1048576*M*P
  unfold prepare extend
  dsimp only
  nlinarith only [hSource,hp,hWP,hMP]

def arithmetic (m lambda k Qv : ℕ) : Cache × ℕ :=
  let controls := GeneralPaperSourcePreparationCache.prepare (fun _ => 1) 1 m lambda k Qv
  let powers := GeneralPaperCachedPowerPreparation.arithmetic k controls.1
  (⟨controls.1,powers.1⟩,controls.2+powers.2+64)

theorem arithmetic_data (m lambda k Qv : ℕ) : (arithmetic m lambda k Qv).1=specification m lambda k Qv := by
  simp only [arithmetic,GeneralPaperSourcePreparationCache.data,
    GeneralPaperCachedPowerPreparation.arithmetic_data m lambda k Qv _ rfl,specification]

theorem arithmetic_work (m lambda k Qv : ℕ) :
    (arithmetic m lambda k Qv).2≤1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have hs := GeneralPaperSourcePreparationEnvelope.unit_work m lambda k Qv
  have hp := (GeneralPaperCachedPowerPreparation.arithmetic_work m lambda k Qv
    (GeneralPaperSourcePreparationCache.prepare (fun _ => 1) 1 m lambda k Qv).1
    (GeneralPaperSourcePreparationCache.data (fun _ => 1) 1 m lambda k Qv)).trans
      (GeneralPaperPowerPreparationEnvelope.arithmetic_profile m lambda k Qv)
  change _≤524288*M at hs
  change _≤262144*(M+1)^2 at hp
  unfold arithmetic
  dsimp only
  change _≤1048576*(M+1)^2
  nlinarith only [hs,hp,Nat.zero_le (M*M)]

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    (prepare primitive W m lambda k Qv).1=(arithmetic m lambda k Qv).1 := by rw [data,arithmetic_data]

theorem returned_properties (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    let c := (prepare primitive W m lambda k Qv).1
    c.powers.table.length=c.controls.precision.parameters.columns ∧
      GeneralPaperDyadicFloat.Normal c.controls.precision.parameters.unit c.powers.base ∧
      0<c.powers.base.mantissa ∧
      GeneralPaperDyadicFloat.value c.powers.base=
        GeneralPaperGeometricLevels.geometricBase c.controls.source.eta c.controls.source.theta := by
  rw [data]
  have hb := GeneralPaperPreparedPowers.prepared_base lambda k
  refine ⟨?_,hb.1,hb.2.1,hb.2.2⟩
  exact GeneralPaperRoundedPowerTable.entries_length _ _ _ _

end Blotto.GeneralPaperMaterializedPowerCache
