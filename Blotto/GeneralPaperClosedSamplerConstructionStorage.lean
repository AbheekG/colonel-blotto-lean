import Blotto.GeneralPaperSamplerControlsConstructionStorage

/-! Native store/close wrappers retain the actual raw prepared input and
complete returned sampler while constructing controls. Both description
branches and every wrapper work field are observed without runtime passes. -/
namespace Blotto.GeneralPaperClosedSamplerConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperClosedDescriptionStorage GeneralPaperClosedStrategyDriver GeneralPaperStoredStrategySampler
open GeneralPaperSamplerControlsConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def rows {n : ℕ} (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : ℕ :=
  (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows

def labels {n : ℕ} (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : ℕ :=
  (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K

def cap (W n T k m : ℕ) : ℕ := n+k+m+GeneralPaperSamplerControlsConstructionStorage.price indexModel W T k+128*W+1

def extraProfile (W n T K k m : ℕ) : ℕ :=
  2*GeneralPaperSamplerControlsConstructionStorage.extraProfile indexModel W n T K k m+
    7*(natBits (cap W n T k m)+W)+320*W

def window {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : ℕ :=
  rawFoot W raw+match raw.strategies.description with
  | none => fields W [(close (fun w => w) W raw).2,64*W]+64*W
  | some description =>
    let o := raw.strategies.original.reduced
    let hDyadic := ⟨_,GeneralPaperTrajectoryParameters.rows_power
      (GeneralPaperProxyParameters.alphabet o.m raw.exponent).lambda raw.exponent⟩
    let made := GeneralPaperSamplingControls.make (fun w => w) W raw.exponent o (fields_positive raw) description hDyadic
    let stored := store (fun w => w) W raw.exponent o (fields_positive raw) raw.budget description hDyadic
    GeneralPaperSamplerControlsConstructionStorage.window indexModel W raw.exponent o (fields_positive raw) description hDyadic+
      footprint W stored.1+fields W [n,raw.exponent,o.m,made.2,stored.2,(close (fun w => w) W raw).2,64*W]+128*W

def profile {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : ℕ :=
  3*rawFoot W raw+extraProfile W n (rows raw) (labels raw) raw.exponent raw.strategies.original.reduced.m

theorem bounded {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : window W raw≤profile W raw := by
  cases he:raw.strategies.description with
  | none =>
    have hw : (close (fun w => w) W raw).2=64*W := by simp only [close,he]
    have hf := fields_bound W (natBits (cap W n (rows raw) raw.exponent raw.strategies.original.reduced.m))
      [(close (fun w => w) W raw).2,64*W] (by
        intro z hz
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold cap
        rcases hz with rfl|rfl <;> omega)
    change fields W _≤2*(natBits (cap W n (rows raw) raw.exponent raw.strategies.original.reduced.m)+W)+32*W at hf
    unfold window profile extraProfile
    rw [he]
    dsimp only
    omega
  | some description =>
    let o := raw.strategies.original.reduced
    let hDyadic : ∃ R,rows raw=2^R := ⟨_,GeneralPaperTrajectoryParameters.rows_power
      (GeneralPaperProxyParameters.alphabet o.m raw.exponent).lambda raw.exponent⟩
    let made := GeneralPaperSamplingControls.make (fun w => w) W raw.exponent o (fields_positive raw) description hDyadic
    let stored := store (fun w => w) W raw.exponent o (fields_positive raw) raw.budget description hDyadic
    have hMade := GeneralPaperSamplerControlsConstructionStorage.work indexModel W raw.exponent o (fields_positive raw) description hDyadic
    change made.2≤GeneralPaperSamplerControlsConstructionStorage.price indexModel W (rows raw) raw.exponent at hMade
    have hControl := GeneralPaperSamplerControlsConstructionStorage.bounded_extra indexModel W raw.exponent o (fields_positive raw) description hDyadic
    change GeneralPaperSamplerControlsConstructionStorage.extraWindow indexModel W raw.exponent o (fields_positive raw) description hDyadic≤
      GeneralPaperSamplerControlsConstructionStorage.extraProfile indexModel W n (rows raw) (labels raw) raw.exponent o.m at hControl
    have hInput : GeneralPaperOriginalReductionRetainedStorage.footprint W o+descriptionFoot W o description+rationalWordWidth raw.budget+192*W≤rawFoot W raw := by
      unfold rawFoot
      rw [he]
      dsimp only [o]
      omega
    have hControlFoot : controlsFoot W made.1≤GeneralPaperSamplerControlsConstructionStorage.extraWindow indexModel W raw.exponent o (fields_positive raw) description hDyadic := by
      unfold GeneralPaperSamplerControlsConstructionStorage.extraWindow
      dsimp only [made,indexModel]
      omega
    have hReturn : footprint W stored.1≤rawFoot W raw+
        GeneralPaperSamplerControlsConstructionStorage.extraProfile indexModel W n (rows raw) (labels raw) raw.exponent o.m+128*W := by
      change GeneralPaperOriginalReductionRetainedStorage.footprint W o+descriptionFoot W o description+
        rationalWordWidth raw.budget+controlsFoot W made.1+128*W≤_
      omega
    have hStored : stored.2=made.2+64*W := rfl
    have hClose : (close (fun w => w) W raw).2=stored.2+64*W := by simp only [close,he];rfl
    have hf := fields_bound W (natBits (cap W n (rows raw) raw.exponent o.m))
      [n,raw.exponent,o.m,made.2,stored.2,(close (fun w => w) W raw).2,64*W] (by
        intro z hz
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold cap
        rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields W _≤7*(natBits (cap W n (rows raw) raw.exponent o.m)+W)+32*W at hf
    unfold window profile extraProfile
    rw [he]
    change rawFoot W raw+(GeneralPaperOriginalReductionRetainedStorage.footprint W o+descriptionFoot W o description+
      GeneralPaperSamplerControlsConstructionStorage.extraWindow indexModel W raw.exponent o (fields_positive raw) description hDyadic+
      footprint W stored.1+fields W [n,raw.exponent,o.m,made.2,stored.2,(close (fun w => w) W raw).2,64*W]+128*W)≤_
    dsimp only [o] at *
    omega

def returnedFoot {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : ℕ :=
  match (close (fun w => w) W raw).1 with | none => 0 | some sampler => footprint W sampler

theorem returned_covered {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : returnedFoot W raw≤window W raw := by
  cases he:raw.strategies.description with
  | none => simp only [returnedFoot,close,he];omega
  | some description =>
    unfold returnedFoot close window
    rw [he]
    dsimp only
    omega

theorem returned_bounded {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : returnedFoot W raw≤profile W raw :=
  (returned_covered W raw).trans (bounded W raw)

@[fun_prop]
theorem extra_scaling (n T K k m : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => extraProfile W n T K k m) := by
  unfold extraProfile cap GeneralPaperSamplerControlsConstructionStorage.price GeneralPaperSamplingControls.profile
  fun_prop

theorem list_scaling {α : Type*} (xs : List α) (encode : α → ℕ → ℕ)
    (h : ∀ x,GeneralPaperReferenceScaling.Scale (encode x)) :
    GeneralPaperReferenceScaling.Scale (fun W => listFootprint W (fun x => encode x W) xs) := by
  have hSum : GeneralPaperReferenceScaling.Scale (fun W => (xs.map (fun x => encode x W)).sum) := by
    induction xs with
    | nil => simp only [List.map_nil,List.sum_nil];fun_prop
    | cons a rest ih => simp only [List.map_cons,List.sum_cons];fun_prop
  unfold listFootprint
  fun_prop

@[fun_prop]
theorem description_scaling {n T K : ℕ} (o : GeneralPaperReducedValuesDriver.Output n)
    (description : GeneralPaperStrategyDescription.Description o T K) :
    GeneralPaperReferenceScaling.Scale (fun W => descriptionFoot W o description) := by
  cases description with
  | direct h columns =>
    unfold descriptionFoot GeneralPaperEnclosingSourceOwners.columnsFoot GeneralPaperEnclosingSourceOwners.columnFoot arrayFootprint
    fun_prop
  | circle h hR pair =>
    have hList : GeneralPaperReferenceScaling.Scale (fun W => listFootprint W (GeneralPaperCachedCircleRetainedStorage.arcBits W) pair.common.metadata.arcs) := by
      apply list_scaling
      intro arc
      unfold GeneralPaperCachedCircleRetainedStorage.arcBits
      fun_prop
    unfold descriptionFoot GeneralPaperCachedCircleRetainedStorage.pairFoot GeneralPaperCachedCircleRetainedStorage.commonFoot
      GeneralPaperCachedCircleRetainedStorage.rowsFoot GeneralPaperCachedCircleRetainedStorage.referenceRowsFoot
      GeneralPaperEnclosingSourceOwners.columnsFoot GeneralPaperEnclosingSourceOwners.columnFoot arrayFootprint
    fun_prop

@[fun_prop]
theorem raw_scaling {n : ℕ} (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) :
    GeneralPaperReferenceScaling.Scale (fun W => rawFoot W raw) := by
  unfold rawFoot
  cases he:raw.strategies.description with
  | none => dsimp only;unfold arrayFootprint;fun_prop
  | some description => dsimp only;unfold arrayFootprint;fun_prop

@[fun_prop]
theorem scaling {n : ℕ} (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) :
    GeneralPaperReferenceScaling.Scale (fun W => profile W raw) := by unfold profile;fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds

theorem index_growth : GeneralPaperFastRationalModel.Growth indexModel 1 0 := by
  intro w
  simp only [indexModel,GeneralPaperFastRationalModel.charge,GeneralPaperFastRationalModel.logFactor,pow_zero,Nat.one_mul,Nat.mul_one,le_refl]

theorem extra_poly (W n T K m : Input → ℕ) (hW : Tight W) (hn : Small n) (hT : Small T) (hK : Small K) (hm : Small m) :
    Polylog (fun x => extraProfile (W x) (n x) (T x) (K x) x.k (m x)) := by
  have hWP := poly_tight W hW
  have hw := of_tight hW
  have hBase := GeneralPaperSamplerControlsConstructionStorage.extra_poly index_growth W n T K m hW hn hT hK hm
  have hPrice := GeneralPaperSamplerControlsConstructionStorage.price_poly index_growth W T hW hT
  have hPriceSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hPrice
  unfold extraProfile cap natBits
  fun_prop

theorem profile_rate (W n : Input → ℕ) (raw : (x : Input) → GeneralPaperAccuracyStrategyDriver.Prepared (n x)) (rate : Input → ℕ)
    (hW : Tight W) (hn : Small n) (hT : Small (fun x => rows (raw x))) (hK : Small (fun x => labels (raw x)))
    (hm : Small (fun x => (raw x).strategies.original.reduced.m)) (he : ∀ x,(raw x).exponent=x.k)
    (hr : ∀ x,1≤rate x) (hRaw : Soft rate (fun x => rawFoot (W x) (raw x))) :
    Soft rate (fun x => profile (W x) (raw x)) := by
  have hExtra := extra_poly W n (fun x => rows (raw x)) (fun x => labels (raw x))
    (fun x => (raw x).strategies.original.reduced.m) hW hn hT hK hm
  have hExtra' := poly_at_rate hExtra hr
  have hTriple := add_same (add_same hRaw hRaw) hRaw
  have hSum := add_same hTriple hExtra'
  apply GeneralPaperSourceSoftBounds.dominated hSum
  intro x
  unfold profile
  conv_lhs =>
    arg 2
    arg 5
    rw [he x]
  omega

end Blotto.GeneralPaperClosedSamplerConstructionStorage
