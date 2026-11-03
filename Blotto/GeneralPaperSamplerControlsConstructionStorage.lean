import Blotto.GeneralPaperDyadicBitConstructionStorage

/-! Actual stored row/shift-control construction: a descriptor metadata
read, native power ceiling, one dyadic constructor and the native addition.
Full original/description owners and actual returned controls are explicit. -/
namespace Blotto.GeneralPaperSamplerControlsConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSamplingControls
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def indexModel : RationalCostModel where
  rat := fun w => w
  monotone := fun _ _ h => h
  word_le := fun _ => le_rfl
  superadditive := fun _ _ => le_rfl

def rowWidth (T : ℕ) : ℕ := 1+binaryWordWidth (2*(T+1))
def price (model : RationalCostModel) (W T k : ℕ) : ℕ := GeneralPaperSamplingControls.profile model.rat W T k

def cap (model : RationalCostModel) (W n T K k m : ℕ) : ℕ :=
  n+2*(T+1)+K+k+m+2^(k+6)+32*rowWidth T+8*(k+6)+price model W T k+256*W+64

def controls {n T K : ℕ} (model : RationalCostModel) (W k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : 0<o.m) (description : GeneralPaperStrategyDescription.Description o T K) (hDyadic : ∃ R,T=2^R) : List ℕ :=
  let rows := rowCount W o hm description
  let rowPrecision := GeneralPaperPowerCeilingBits.run model.rat W rows.1
  let shift := GeneralPaperDyadicPowerBits.run model.rat W (k+6)
  let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) k 6
  [n,T,K,k,o.m,rows.1,rows.2,rowPrecision.1.power,rowPrecision.1.doublings,rowPrecision.1.work,rowPrecision.2,
    k+6,shift.1.power,shift.1.doublings,shift.1.work,shift.2,add,256*W,rows.2+rowPrecision.2,
    rows.2+rowPrecision.2+shift.2,rows.2+rowPrecision.2+shift.2+add,(make model.rat W k o hm description hDyadic).2]

def extraWindow {n T K : ℕ} (model : RationalCostModel) (W k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : 0<o.m) (description : GeneralPaperStrategyDescription.Description o T K) (hDyadic : ∃ R,T=2^R) : ℕ :=
  let rows := rowCount W o hm description
  GeneralPaperPowerCeilingStorage.window model W rows.1 1 (by decide)+
    GeneralPaperDyadicBitConstructionStorage.window model W (k+6)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) k 6+
    GeneralPaperClosedDescriptionStorage.controlsFoot W (make model.rat W k o hm description hDyadic).1+
    fields W (controls model W k o hm description hDyadic)+256*W

def extraProfile (model : RationalCostModel) (W n T K k m : ℕ) : ℕ :=
  GeneralPaperPowerCeilingStorage.profile model W (rowWidth T)+
    GeneralPaperDyadicBitConstructionStorage.profile model W (k+6)+price model W T k+
    26*(natBits (cap model W n T K k m)+W)+320*W

def window {n T K : ℕ} (model : RationalCostModel) (W k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : 0<o.m) (description : GeneralPaperStrategyDescription.Description o T K) (hDyadic : ∃ R,T=2^R) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W o+GeneralPaperClosedDescriptionStorage.descriptionFoot W o description+
    extraWindow model W k o hm description hDyadic

def profile {n T K : ℕ} (model : RationalCostModel) (W k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (description : GeneralPaperStrategyDescription.Description o T K) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W o+GeneralPaperClosedDescriptionStorage.descriptionFoot W o description+
    extraProfile model W n T K k o.m

theorem work {n T K : ℕ} (model : RationalCostModel) (W k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : 0<o.m) (description : GeneralPaperStrategyDescription.Description o T K) (hDyadic : ∃ R,T=2^R) :
    (make model.rat W k o hm description hDyadic).2≤price model W T k :=
  GeneralPaperSamplingControls.work model.rat model.monotone W k o hm description hDyadic

theorem bounded_extra {n T K : ℕ} (model : RationalCostModel) (W k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : 0<o.m) (description : GeneralPaperStrategyDescription.Description o T K) (hDyadic : ∃ R,T=2^R) :
    extraWindow model W k o hm description hDyadic≤extraProfile model W n T K k o.m := by
  let rows := rowCount W o hm description
  let rowPrecision := GeneralPaperPowerCeilingBits.run model.rat W rows.1
  let shift := GeneralPaperDyadicPowerBits.run model.rat W (k+6)
  let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) k 6
  have hRows : rows.1=T := row_count_data W o hm description
  have hRowsWork : rows.2=64*W := row_count_work W o hm description
  have hCeiling := GeneralPaperPowerCeilingStorage.bounded model W T (rowWidth T) le_rfl
  have hDyadicWindow := GeneralPaperDyadicBitConstructionStorage.bounded model W (k+6) (k+6) le_rfl
  have hData := GeneralPaperPowerCeilingStorage.result_bounds model W T 1 (T+1) (rowWidth T) (by decide) (by omega) (by omega) le_rfl
  change (GeneralPaperPowerCeilingBits.run model.rat W T).1.power≤2*(T+1) ∧
    (GeneralPaperPowerCeilingBits.run model.rat W T).1.doublings≤rowWidth T ∧
    (GeneralPaperPowerCeilingBits.run model.rat W T).1.work≤12*rowWidth T+2 at hData
  have hShift := GeneralPaperDyadicBitConstructionStorage.data_bounds model W (k+6) (k+6) le_rfl
  have hShiftPower : shift.1.power=2^(k+6) := by
    rw [GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data (k+6)).1]
  have hw := work model W k o hm description hDyadic
  have hShape : (make model.rat W k o hm description hDyadic).2=rows.2+rowPrecision.2+shift.2+add+256*W := rfl
  have hFields := fields_bound W (natBits (cap model W n T K k o.m)) (controls model W k o hm description hDyadic) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals dsimp only [rows,rowPrecision,shift,add] at *;rw [row_count_data] at *;omega)
  change fields W _≤22*(natBits (cap model W n T K k o.m)+W)+32*W at hFields
  have hControls : GeneralPaperClosedDescriptionStorage.controlsFoot W (make model.rat W k o hm description hDyadic).1≤
      4*(natBits (cap model W n T K k o.m)+W)+32*W := by
    change fields W [rows.1,rowPrecision.1.doublings,shift.1.power,k+6]≤_
    apply fields_bound
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl
    all_goals dsimp only [rows,rowPrecision,shift] at *;rw [row_count_data] at *;omega
  unfold extraWindow extraProfile GeneralPaperDyadicBitConstructionStorage.profile
  dsimp only [rows,rowPrecision,shift,add] at *
  rw [row_count_data] at *
  omega

theorem bounded {n T K : ℕ} (model : RationalCostModel) (W k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : 0<o.m) (description : GeneralPaperStrategyDescription.Description o T K) (hDyadic : ∃ R,T=2^R) :
    window model W k o hm description hDyadic≤profile model W k o description :=
  Nat.add_le_add_left (bounded_extra model W k o hm description hDyadic) _

@[fun_prop]
theorem extra_scaling (model : RationalCostModel) (n T K k m : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => extraProfile model W n T K k m) := by
  unfold extraProfile GeneralPaperPowerCeilingStorage.profile GeneralPaperPowerCeilingStorage.frameProfile
    GeneralPaperPowerCeilingStorage.metadataCap GeneralPaperPowerCeilingStorage.price cap price GeneralPaperSamplingControls.profile
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds

theorem price_poly {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W T : Input → ℕ) (hW : Tight W) (hT : Small T) : Polylog (fun x => price model (W x) (T x) x.k) := by
  have hWP := poly_tight W hW
  have hRow : Polylog (fun x => rowWidth (T x)) := by unfold rowWidth;fun_prop
  have hRowSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hRow
  have hRatRow : Polylog (fun x => model.rat (rowWidth (T x))) := primitive_preserves hg hRow hRowSmall
  have hShift : Polylog (fun x => 8+2*(x.k+6)) := by fun_prop
  have hRatShift : Polylog (fun x => model.rat (8+2*(x.k+6))) :=
    primitive_preserves hg hShift (GeneralPaperCacheConstructionGrowth.small_of_poly hShift)
  have hAddIn : Polylog (fun x => max (1+binaryWordWidth x.k) (1+binaryWordWidth 6)) := by
    have hs : Polylog (fun x => 1+binaryWordWidth x.k+(1+binaryWordWidth 6)) := by fun_prop
    exact GeneralPaperSourceSoftBounds.dominated hs (fun _ => by omega)
  have hAddOut : Polylog (fun x => 1+binaryWordWidth (x.k+6)) := by fun_prop
  have hRatIn : Polylog (fun x => model.rat (max (1+binaryWordWidth x.k) (1+binaryWordWidth 6))) :=
    primitive_preserves hg hAddIn (GeneralPaperCacheConstructionGrowth.small_of_poly hAddIn)
  have hRatOut : Polylog (fun x => model.rat (1+binaryWordWidth (x.k+6))) :=
    primitive_preserves hg hAddOut (GeneralPaperCacheConstructionGrowth.small_of_poly hAddOut)
  unfold price GeneralPaperSamplingControls.profile GeneralPaperNaturalPrimitivePrice.binary GeneralPaperNaturalPrimitivePrice.word
  change Polylog (fun x => 64*(binaryWordWidth (T x)+1)*(W x+model.rat (rowWidth (T x)))+
    64*(x.k+7)*(W x+model.rat (8+2*(x.k+6)))+
    (model.rat (max (1+binaryWordWidth x.k) (1+binaryWordWidth 6))+model.rat (1+binaryWordWidth (x.k+6)))+320*W x)
  fun_prop

theorem extra_poly {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n T K m : Input → ℕ) (hW : Tight W) (hn : Small n) (hT : Small T) (hK : Small K) (hm : Small m) :
    Polylog (fun x => extraProfile model (W x) (n x) (T x) (K x) x.k (m x)) := by
  have hWP := poly_tight W hW
  have hWSmall := of_tight hW
  have hPow := pow_two _ k_tight
  have hRow : Polylog (fun x => rowWidth (T x)) := by unfold rowWidth;fun_prop
  have hRowSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hRow
  have hRatRow : Polylog (fun x => model.rat (rowWidth (T x))) := primitive_preserves hg hRow hRowSmall
  have hRatRowSmall := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hRowSmall
  have hShiftTight : Tight (fun x => x.k+6) := by fun_prop
  have hDyadic := GeneralPaperDyadicBitConstructionStorage.profile_poly hg W (fun x => x.k+6) hW hShiftTight
  have hPrice := price_poly hg W T hW hT
  have hPriceSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hPrice
  unfold extraProfile GeneralPaperPowerCeilingStorage.profile GeneralPaperPowerCeilingStorage.frameProfile
    GeneralPaperPowerCeilingStorage.metadataCap GeneralPaperPowerCeilingStorage.price cap natBits
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperSamplerControlsConstructionStorage
