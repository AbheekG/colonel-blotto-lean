import Blotto.GeneralPaperExactStoredSampler

/-! Anchor-height and actual primitive-price certificates for exact
row-only/direct and retained circle sampling. No source is rerun by a draw;
physical columns here are erased provenance of the prepared description. -/
namespace Blotto.GeneralPaperExactSamplerSourceBounds
open GeneralPaperOriginalDrawEquilibrium GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
open GeneralPaperClosedBitSampling (profile outputHeight scale_height)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem source_sampler_bounds {n : ℕ} (model : RationalCostModel) (Wv k Ap A B H : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hB : RationalHeight b B) (hA : 1≤A) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∀ (physical : Columns t.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K),
      (∀ j l,RationalHeight ((physical.rich.read j).anchors.read l) H) →
      (∀ j l,RationalHeight ((physical.poor.read j).anchors.read l) H) →
      1+binaryWordWidth (2*n+o.representatives+2)≤A → binaryWordWidth (t.rows+1)≤A →
      let description := (make model.rat (fun w => w) Ap o
        (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
        (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
        (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1
      let sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
        ⟨o,b,GeneralPaperSamplingControls.specification t.rows t.rowBits k hRows,description⟩
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).work≤profile model A t.rowBits k B H o ∧
        ∀ j,RationalHeight ((GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).output.read j) (outputHeight o B H) := by
  dsimp only
  intro physical hRich hPoor hCapacity hRow
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values
  have hCapacity' : 1+binaryWordWidth (2*n+o.representatives+2)≤A := hCapacity
  by_cases hReplace:o.replaced=true
  · obtain ⟨hm,_⟩ := GeneralPaperNativeReductionShape.original_shape true model Wv k values hReplace
    rw [make_circle model.rat (fun w => w) Ap o _ _ _ physical hReplace hm]
    intro reciprocal fresh
    let c := if reciprocal then b else 1
    have hc := scale_height b B hB reciprocal
    have hColumns : ∀ j l,RationalHeight ((((if reciprocal then physical.poor else physical.rich).read j).anchors).read l) H := by
      cases reciprocal <;> assumption
    dsimp only [GeneralPaperExactStoredSampler.run, GeneralPaperExactStoredSampler.bits,
      GeneralPaperExactStoredSampler.shiftBits, GeneralPaperSamplingControls.specification]
    have hW := GeneralPaperCircleActualWeights.original_total_positive true model Wv k values v hv
      (GeneralPaperNativeCircleLoss.original_light_positive true model Wv k values hReplace)
    dsimp only [GeneralPaperExactStoredSampler.bits, GeneralPaperExactStoredSampler.shiftBits,
      GeneralPaperSamplingControls.specification] at fresh
    have hCost := GeneralPaperCachedBitSampling.run_work model A (B+1) H hA model.rat (fun w => w) Ap
      t.rowBits (k+6) t.rows (GeneralPaperNativeSelectedSecurity.count k) hRows (GeneralPaperNativeSelectedSecurity.count_power k)
      o hm hR hW c hc physical reciprocal hColumns (GeneralPaperCircleActualWeights.original_sum true model Wv k values)
      (GeneralPaperLightFieldIndexEquiv.original_bijective true model Wv k values) hCapacity hRow fresh
    constructor
    · dsimp only [profile,o,t,c,hR,hRows] at hCost ⊢
      omega
    · intro j
      exact GeneralPaperCachedBitSampling.run_height model A (B+1) H model.rat (fun w => w) Ap
        t.rowBits (k+6) t.rows (GeneralPaperNativeSelectedSecurity.count k) hRows (GeneralPaperNativeSelectedSecurity.count_power k)
        o hm hR c hc physical reciprocal hColumns (GeneralPaperCircleActualWeights.original_sum true model Wv k values)
        (GeneralPaperLightFieldIndexEquiv.original_bijective true model Wv k values) fresh j
  · have hFalse : o.replaced=false := by cases he:o.replaced <;> simp_all
    obtain ⟨hm,_⟩ := GeneralPaperUnreplacedShape.original_shape true model Wv k values hFalse
    rw [make_direct model.rat (fun w => w) Ap o _ _ _ physical hFalse hm]
    intro reciprocal fresh
    let c := if reciprocal then b else 1
    have hc := scale_height b B hB reciprocal
    have hColumns : ∀ j l,RationalHeight ((((if reciprocal then physical.poor else physical.rich).read j).anchors).read l) H := by
      cases reciprocal <;> assumption
    dsimp only [GeneralPaperExactStoredSampler.run, GeneralPaperExactStoredSampler.bits,
      GeneralPaperExactStoredSampler.shiftBits, GeneralPaperSamplingControls.specification, rationalPrice,indexPrice]
    simp only [ite_true]
    have hIndex (i : ℕ) (hi : i≤n) : binaryWordWidth (i+1)≤A :=
      (binaryWordWidth_mono (by omega : i+1≤2*n+o.representatives+2)).trans (by omega)
    dsimp only [GeneralPaperExactStoredSampler.bits, GeneralPaperExactStoredSampler.shiftBits,
      GeneralPaperSamplingControls.specification] at fresh
    have hCost := GeneralPaperDirectRowExactSampler.bit_work model A (B+1) H t.rowBits t.rows
      hA hRows hm c hc (if reciprocal then physical.poor else physical.rich) hColumns hIndex fresh
    change (GeneralPaperDirectRowExactSampler.run model.rat (fun w => w) model.rat A t.rowBits t.rows hRows hm c
      (if reciprocal then physical.poor else physical.rich) fresh).work ≤ _ at hCost
    have hMono := GeneralPaperDirectRowExactSampler.profile_mono model A t.rowBits (k+6) (B+1) H n
    constructor
    · dsimp only [profile,o,t,c,hRows] at hCost hMono ⊢
      omega
    · intro j
      let i := Fin.cast hRows.symm (bitIndex t.rowBits fresh)
      have hh := GeneralPaperDirectRowSampler.height model.rat (fun w => w) A hm c
        (if reciprocal then physical.poor else physical.rich) (B+1) H hc hColumns i j
      rw [GeneralPaperDirectRowExactSampler.data]
      exact hh.mono (by unfold outputHeight; omega)

end Blotto.GeneralPaperExactSamplerSourceBounds
