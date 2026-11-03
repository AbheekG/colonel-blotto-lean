import Blotto.GeneralPaperStrategyDescription

/-! Actual once-only original-input preparation. One original-value/source
call feeds one retained description constructor. Its reduction shape proofs
are erased consequences of that native return, with no supplied acceptance
or reconstruction oracle. Rational budget scaling is deferred to each draw. -/
namespace Blotto.GeneralPaperOriginalStrategyDriver
open GeneralPaperStrategyDescription GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

structure Prepared (n k : ℕ) where
  original : GeneralPaperOriginalSourceValuePreparation.Output n
  description : Option (Description original.reduced
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet original.reduced.m k).lambda k).rows
    (GeneralPaperProxyParameters.prepare original.reduced.m k).K)

def attach {n k : ℕ} (price index : ℕ → ℕ) (A : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives) : Prepared n k×ℕ :=
  let stored := match source.physical with
    | none => (none,64*A)
    | some columns =>
      let made := make price index A source.original.reduced hRep hNo hR columns
      (some made.1,made.2+64*A)
  (⟨source.original,stored.1⟩,stored.2)

theorem attach_original {n k : ℕ} (price index : ℕ → ℕ) (A : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives) :
    (attach price index A source hRep hNo hR).1.original=source.original := rfl

theorem attach_some {n k : ℕ} (price index : ℕ → ℕ) (A : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives)
    (physical : Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet source.original.reduced.m k).lambda k).rows
      source.original.reduced.m (GeneralPaperProxyParameters.prepare source.original.reduced.m k).K)
    (hSource : source.physical=some physical) :
    (attach price index A source hRep hNo hR).1.description=some (make price index A source.original.reduced hRep hNo hR physical).1 ∧
    (attach price index A source hRep hNo hR).2=(make price index A source.original.reduced hRep hNo hR physical).2+64*A := by
  simp only [attach,hSource]
  exact ⟨trivial,trivial⟩

def bit {n : ℕ} (model : RationalCostModel) (Wv Ws A k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : Prepared n k×ℕ :=
  let source := GeneralPaperOriginalSourceValueDriver.bit model Wv Ws k values v hv b hb
  let stored := attach model.rat (fun w => w) A source.1
    (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
    (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values)
  (stored.1,source.2+stored.2+128*A)

noncomputable def arithmetic {n : ℕ} (model : RationalCostModel) (k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) : Prepared n k×ℕ :=
  let source := GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv b
  let stored := attach (fun _ => 1) (fun _ => 1) 1 source.1
    (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
    (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values)
  (stored.1,source.2+stored.2+128)

theorem bit_original {n : ℕ} (model : RationalCostModel) (Wv Ws A k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) :
    (bit model Wv Ws A k values v hv b hb).1.original=
      (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1 := rfl

theorem arithmetic_original {n : ℕ} (model : RationalCostModel) (k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) :
    (arithmetic model k values v hv b).1.original=
      (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1 := rfl

theorem bit_return {n : ℕ} (model : RationalCostModel) (Wv Ws A k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    ∃ (physical : Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      GeneralPaperRoundedValueCanonical.run true model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      (bit model Wv Ws A k values v hv b hb).1.description=some
        (make model.rat (fun w => w) A o (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
          (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
          (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1 ∧
      (bit model Wv Ws A k values v hv b hb).2=(GeneralPaperOriginalSourceValueDriver.bit model Wv Ws k values v hv b hb).2+
        (make model.rat (fun w => w) A o (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
          (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
          (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).2+192*A := by
  obtain ⟨physical,pair,hRun,hSource,hMatches,_⟩ := GeneralPaperOriginalSourceValueDriver.bit_return model Wv Ws k values v hv b hb
  have h := attach_some model.rat (fun w => w) A _
    (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
    (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical hRun
  dsimp only
  refine ⟨physical,pair,hSource,hMatches,h.1,?_⟩
  have hWork := h.2
  change _=(make (model.rat) (fun w => w) A (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
    (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).2+64*A at hWork
  dsimp only [bit]
  rw [hWork]
  ring_nf
  exact Nat.add_right_comm _ _ _

theorem arithmetic_return {n : ℕ} (model : RationalCostModel) (k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) (hb : 0<b ∧ b<1) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    ∃ (physical : Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      GeneralPaperRoundedValueCanonical.run false model 1 k o.values redValues (fun _ => rfl) b=some pair ∧ Matches physical pair ∧
      (arithmetic model k values v hv b).1.description=some
        (make (fun _ => 1) (fun _ => 1) 1 o (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
          (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
          (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical).1 ∧
      (arithmetic model k values v hv b).2=(GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv b).2+
        (make (fun _ => 1) (fun _ => 1) 1 o (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
          (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
          (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical).2+192 := by
  obtain ⟨physical,pair,hRun,hSource,hMatches,_⟩ := GeneralPaperOriginalSourceValueDriver.arithmetic_return model k values v hv b hb
  have h := attach_some (fun _ => 1) (fun _ => 1) 1 _
    (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
    (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical hRun
  dsimp only
  refine ⟨physical,pair,hSource,hMatches,h.1,?_⟩
  have hWork := h.2
  change _=(make (fun _ => 1) (fun _ => 1) 1 (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
    (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical).2+64*1 at hWork
  dsimp only [arithmetic]
  rw [hWork]
  ring_nf
  rfl


theorem bit_description {n : ℕ} (model : RationalCostModel) (Wv Ws A k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m k).lambda k).rows
      (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m
      (GeneralPaperProxyParameters.prepare (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m k).K)
    (hSource : (GeneralPaperOriginalSourceValueDriver.bit model Wv Ws k values v hv b hb).1.physical=some physical) :
    (bit model Wv Ws A k values v hv b hb).1.description=some
      (make model.rat (fun w => w) A (GeneralPaperOriginalValueReduction.run true model Wv k values).1
        (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
        (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
        (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1 :=
  (attach_some model.rat (fun w => w) A (GeneralPaperOriginalSourceValueDriver.bit model Wv Ws k values v hv b hb).1
    (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
    (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical hSource).1

theorem arithmetic_description {n : ℕ} (model : RationalCostModel) (k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℝ)
    (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k).lambda k).rows
      (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m
      (GeneralPaperProxyParameters.prepare (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k).K)
    (hSource : (GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv b).1.physical=some physical) :
    (arithmetic model k values v hv b).1.description=some
      (make (fun _ => 1) (fun _ => 1) 1 (GeneralPaperOriginalValueReduction.run false model 1 k values).1
        (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
        (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
        (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical).1 :=
  (attach_some (fun _ => 1) (fun _ => 1) 1 (GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv b).1
    (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
    (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical hSource).1

end Blotto.GeneralPaperOriginalStrategyDriver
