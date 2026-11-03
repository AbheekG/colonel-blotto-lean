import Blotto.GeneralPaperCachedCircleWork

/-! The identity branch preserves original field order and the first
rounded values exactly. These are erased observations of the actual
retained return; no reduction, rounding or classifier is executed again. -/
namespace Blotto.GeneralPaperUnreplacedShape
open GeneralPaperReducedValuesDriver
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def Shape {n : ℕ} (o : Output n) : Prop := o.replaced=false →
  ∃ hm:o.m=n,∀ j:Fin n,o.values.read (Fin.cast hm.symm j)=(o.firstWeights.read j:ℚ)/o.denominator

theorem specification_shape {n : ℕ} (Q : ℕ) (weights : FixedArrayTable n ℕ)
    (state : GeneralPaperLightFieldScan.State n) (R : ℕ) : Shape (specification Q weights state R) := by
  unfold specification
  split_ifs
  · intro h
    cases h
  · intro _
    exact ⟨rfl,fun j => FixedArrayTable.read_ofFn _ j⟩

theorem reduced_shape {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    Shape (run bits model W k Q weights).1 := by
  rw [data]
  exact specification_shape _ _ _ _

theorem original_shape {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    Shape (GeneralPaperOriginalValueReduction.run bits model W k values).1 := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact reduced_shape bits model W k _ _

theorem values_ext {n : ℕ} (v w : Values n) (h : v.weight=w.weight) : v=w := by
  cases v
  cases w
  cases h
  rfl

theorem selector_values {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hNo : (GeneralPaperOriginalValueReduction.run bits model W k values).1.replaced=false) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    ∃ hm:o.m=n,GeneralPaperFieldRelabel.values (finCongr hm.symm)
        (GeneralPaperOriginalValueReduction.selector bits model W k values v hv).values=
      (GeneralPaperNativeReductionShape.firstSelector bits model W k values v hv).values := by
  obtain ⟨hm,hValues⟩ := original_shape bits model W k values hNo
  refine ⟨hm,?_⟩
  apply values_ext
  funext j
  change ((GeneralPaperOriginalValueReduction.run bits model W k values).1.values.read (Fin.cast hm.symm j):ℝ)=_
  rw [hValues]
  rfl

end Blotto.GeneralPaperUnreplacedShape
