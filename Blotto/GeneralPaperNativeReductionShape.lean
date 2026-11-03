import Blotto.GeneralPaperFieldRelabel

/-! Exact retained and representative entries of the actual native value
reduction return. Shape and first-round positivity/normalization are
derived from that return, never supplied as reconstruction certificates. -/
namespace Blotto.GeneralPaperNativeReductionShape
open GeneralPaperReducedValuesDriver GeneralPaperLightFieldOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def ReplacedShape {n : ℕ} (o : Output n) : Prop := o.replaced=true →
  ∃ hm:o.m=o.classified.heavy.size+o.representatives,
    ∀ j:Fin (o.classified.heavy.size+o.representatives),o.values.read (Fin.cast hm.symm j)=
      Fin.addCases (fun i:Fin o.classified.heavy.size => (o.firstWeights.read (index o.classified.heavy i):ℚ)/o.denominator)
        (fun _:Fin o.representatives => (o.classified.lightWeight:ℚ)/(o.denominator*o.representatives:ℕ)) j

theorem specification_shape {n : ℕ} (Q : ℕ) (weights : FixedArrayTable n ℕ)
    (state : GeneralPaperLightFieldScan.State n) (R : ℕ) : ReplacedShape (specification Q weights state R) := by
  by_cases he:R<state.light.size
  · rw [specification,ite_eq_left he]
    unfold ReplacedShape
    dsimp only
    intro _
    refine ⟨rfl,?_⟩
    intro j
    simp only [Fin.cast_refl,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [id_eq,Fin.val_castAdd,Fin.addCases_left,dite_eq_left i.isLt,index]
    · intro a
      simp only [id_eq,Fin.val_natAdd,Fin.addCases_right,dite_eq_right (by omega : ¬state.heavy.size+a.val<state.heavy.size)]
  · rw [specification,ite_eq_right he]
    intro h
    cases h

theorem reduced_shape {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    ReplacedShape (run bits model W k Q weights).1 := by
  rw [data]
  exact specification_shape _ _ _ _

theorem original_shape {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    ReplacedShape (GeneralPaperOriginalValueReduction.run bits model W k values).1 := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact reduced_shape bits model W k _ _

def FirstValid {n : ℕ} (o : Output n) : Prop :=
  0<o.denominator ∧ (∀ j,0<o.firstWeights.read j) ∧ (∑ j,o.firstWeights.read j)=o.denominator

theorem original_first_valid {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    FirstValid (GeneralPaperOriginalValueReduction.run bits model W k values).1 := by
  unfold FirstValid
  rw [(GeneralPaperOriginalValueReduction.retained bits model W k values).1,
    (GeneralPaperOriginalValueReduction.retained bits model W k values).2]
  have hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv
  exact ⟨hp.1,hp.2,GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values⟩

noncomputable def firstSelector {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) : RationalFieldSelector n :=
  let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
  let h := original_first_valid bits model W k values v hv
  GeneralPaperNativeRationalValues.selector o.denominator h.1 o.firstWeights h.2.1 h.2.2

theorem original_representatives {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    (GeneralPaperOriginalValueReduction.run bits model W k values).1.representatives=
      GeneralPaperLightFieldReduction.representatives k := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact (retained bits model W k _ _).2.2.2

end Blotto.GeneralPaperNativeReductionShape
