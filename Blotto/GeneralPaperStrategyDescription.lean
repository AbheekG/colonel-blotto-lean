import Blotto.GeneralPaperUnreplacedSourceContract

/-! One retained description type for both unequal-budget reduction
branches. Preparation inspects the actual reduction flag once. Drawing
uses only the selected retained route, with no source/preparation replay. -/
namespace Blotto.GeneralPaperStrategyDescription
open GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

inductive Description {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) (T K : ℕ) where
  | circle (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives)
      (rows : GeneralPaperCachedCircleRows.Pair T o.representatives K o.classified)
  | direct (hm : o.m=n) (columns : Columns T o.m K)

def make {n T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (columns : Columns T o.m K) : Description o T K×ℕ :=
  if h:o.replaced=true then
    have hm : o.m=o.classified.heavy.size+o.representatives := by obtain ⟨hm,_⟩ := hRep h;exact hm
    let cached := GeneralPaperCachedCircleRows.pair price index A o hm columns
    (.circle hm hR cached.1,cached.2+64*A)
  else
    have hn : o.replaced=false := by cases he:o.replaced <;> simp_all
    have hm : o.m=n := by obtain ⟨hm,_⟩ := hNo hn;exact hm
    (.direct hm columns,64*A)

theorem make_circle {n T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (columns : Columns T o.m K) (h : o.replaced=true)
    (hm : o.m=o.classified.heavy.size+o.representatives) :
    make price index A o hRep hNo hR columns=
      (.circle hm hR (GeneralPaperCachedCircleRows.pair price index A o hm columns).1,
        (GeneralPaperCachedCircleRows.pair price index A o hm columns).2+64*A) := by
  simp only [make,dite_eq_left h]

theorem make_direct {n T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (columns : Columns T o.m K) (h : o.replaced=false) (hm : o.m=n) :
    make price index A o hRep hNo hR columns=(.direct hm columns,64*A) := by
  simp only [make,h,Bool.false_eq_true,not_false_eq_true,dite_eq_right]

def rationalPrice (bits : Bool) (model : RationalCostModel) : ℕ → ℕ := if bits then model.rat else fun _ => 1

def indexPrice (bits : Bool) : ℕ → ℕ := if bits then fun w => w else fun _ => 1

def run {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (description : Description o T K)
    (c : ℚ) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) : GeneralPaperNativeFairSampler.Result n :=
  let selected := match description with
    | .circle _ hR rows => GeneralPaperCachedCircleSampler.run bits primitive A R L T S hT hS model o hR c rows reciprocal fresh
    | .direct hm columns => GeneralPaperDirectRowSampler.run (rationalPrice bits model) (indexPrice bits) primitive A R L T S hT hS hm c
        (if reciprocal then columns.poor else columns.rich) fresh
  {selected with work := selected.work+64*A}

noncomputable def law {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (description : Description o T K)
    (c : ℚ) (reciprocal : Bool) : Mixed n :=
  (fairBitLaw (R+L)).map (fun fresh j => ((run bits primitive A R L S hT hS model o description c reciprocal fresh).output.read j:ℝ))

theorem law_circle {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives)
    (rows : GeneralPaperCachedCircleRows.Pair T o.representatives K o.classified) (c : ℚ) (reciprocal : Bool) :
    law bits primitive A R L S hT hS model o (.circle hm hR rows) c reciprocal=
      GeneralPaperCachedCircleSampler.law bits primitive A R L T S hT hS model o hR c rows reciprocal := rfl

theorem law_direct {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=n)
    (columns : Columns T o.m K) (c : ℚ) (reciprocal : Bool) :
    law bits primitive A R L S hT hS model o (.direct hm columns) c reciprocal=
      GeneralPaperDirectRowSampler.law (rationalPrice bits model) (indexPrice bits) primitive A R L T S hT hS hm c
        (if reciprocal then columns.poor else columns.rich) := rfl

theorem fresh_reads {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (description : Description o T K)
    (c : ℚ) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (run bits primitive A R L S hT hS model o description c reciprocal fresh).freshReads=R+L := by
  cases description with
  | circle hm hR rows => exact GeneralPaperCachedCircleSampler.fresh_reads bits primitive A R L T S hT hS model o hR c rows reciprocal fresh
  | direct hm columns => exact GeneralPaperDirectRowSampler.fresh_reads (rationalPrice bits model) (indexPrice bits) primitive A R L T S hT hS hm c (if reciprocal then columns.poor else columns.rich) fresh

theorem buffer_reads {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (description : Description o T K)
    (c : ℚ) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (run bits primitive A R L S hT hS model o description c reciprocal fresh).bufferReads=R+L := by
  cases description with
  | circle hm hR rows => exact GeneralPaperCachedCircleSampler.buffer_reads bits primitive A R L T S hT hS model o hR c rows reciprocal fresh
  | direct hm columns => exact GeneralPaperDirectRowSampler.buffer_reads (rationalPrice bits model) (indexPrice bits) primitive A R L T S hT hS hm c (if reciprocal then columns.poor else columns.rich) fresh

theorem logarithmic_bits {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (description : Description o T K)
    (c : ℚ) (reciprocal : Bool) (fresh : Fin (R+L) → Bool) :
    (run bits primitive A R L S hT hS model o description c reciprocal fresh).freshReads=Nat.log2 (T*S) := by
  rw [fresh_reads,hT,hS,←pow_add,Nat.log2_two_pow]

theorem independent_players {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (description : Description o T K) (c d : ℚ) :
    MeasureTheory.Measure.map (fun fresh =>
      ((fun j => ((run bits primitive A R L S hT hS model o description c false (firstBitBlock (R+L) (R+L) fresh)).output.read j:ℝ)),
        (fun j => ((run bits primitive A R L S hT hS model o description d true (secondBitBlock (R+L) (R+L) fresh)).output.read j:ℝ))))
      (fairBitLaw ((R+L)+(R+L)) : MeasureTheory.Measure (Fin ((R+L)+(R+L)) → Bool))=
      (law bits primitive A R L S hT hS model o description c false : MeasureTheory.Measure (Allocation n)).prod
        (law bits primitive A R L S hT hS model o description d true : MeasureTheory.Measure (Allocation n)) :=
  fairBitBlocks_map_product (R+L) (R+L)
    (fun fresh j => ((run bits primitive A R L S hT hS model o description c false fresh).output.read j:ℝ))
    (fun fresh j => ((run bits primitive A R L S hT hS model o description d true fresh).output.read j:ℝ))


theorem every_output_feasible {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A R L S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (description : Description o T K)
    (c : ℚ) (reciprocal : Bool) (B : ℝ) (h : Supported B (law bits primitive A R L S hT hS model o description c reciprocal))
    (fresh : Fin (R+L) → Bool) :
    Feasible B (fun j => ((run bits primitive A R L S hT hS model o description c reciprocal fresh).output.read j:ℝ)) := by
  change ∀ᵐ x ∂MeasureTheory.Measure.map
    (fun fresh j => ((run bits primitive A R L S hT hS model o description c reciprocal fresh).output.read j:ℝ))
    (fairBitLaw (R+L) : MeasureTheory.Measure (Fin (R+L) → Bool)),Feasible B x at h
  rw [MeasureTheory.ae_map_iff (measurable_of_countable _).aemeasurable (measurable_feasible B)] at h
  apply (MeasureTheory.ae_iff_of_countable.mp h) fresh
  rw [fairBitLaw_singleton]
  positivity

end Blotto.GeneralPaperStrategyDescription
