import Blotto.GeneralPaperCatalogueTagFamily

/-! Complete native optimizer preparation from retained signed summaries
and mesh: catalogues, reference projections, tags and option plans. Every
constructor is executed once; proof/word calibration remains erased.
-/
namespace Blotto.GeneralPaperCatalogueOptimizerPreparation
open GeneralPaperCodeAlphabet
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k mesh : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (Summary k))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) : GeneralPaperCatalogueOptimizer.Ready m k × ℕ :=
  let arrays := GeneralPaperCatalogueArraysExecution.run bits index model W a response summaries
  let tags := GeneralPaperCatalogueTagFamily.run bits index (primitive bits model) W arrays.1
  let ready := GeneralPaperCatalogueOptionPlans.run bits index (primitive bits model) W k mesh a response summaries arrays.1
    (GeneralPaperCatalogueArraysExecution.native_data bits index model W k a response summaries) tags.1
    (GeneralPaperCatalogueTagFamily.data bits index (primitive bits model) W arrays.1) hMesh
  (ready.1,arrays.2+tags.2+ready.2+
    GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a*b) 8 a.C+128*W)

def profile (model : RationalCostModel) (W m k : ℕ) (a : Alphabet) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperCatalogueArraysExecution.profile model W m s a+GeneralPaperCatalogueTagFamily.profile model W m (s+2) a.lambda+
    (GeneralPaperOptionPlanFamily.profile model.rat W m (s+2) k (8*a.C)+128*W)+
      2*model.rat (GeneralPaperDecoderControls.operandWidth a.lambda)+128*W

def arithmeticProfile (m k : ℕ) (a : Alphabet) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperCatalogueArraysExecution.arithmeticProfile m s a+GeneralPaperCatalogueTagFamily.arithmeticProfile m (s+2)+
    (GeneralPaperOptionPlanFamily.arithmeticProfile m (s+2) k+128)+2+128

theorem data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k mesh : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (Summary k))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index model W k mesh a response summaries hMesh).1=GeneralPaperCatalogueOptimizer.prepare a response k summaries := by
  unfold run
  dsimp only
  exact GeneralPaperCatalogueOptionPlans.data bits index (primitive bits model) W k mesh a response summaries _ _ _ _ hMesh

theorem same_data {m : ℕ} (model : RationalCostModel) (W k mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run true (fun w => w) model W k mesh a response summaries hMesh).1=
      (run false (fun _ => 1) model 1 k mesh a response summaries hMesh).1 := by
  rw [data,data]

theorem limit_work (model : RationalCostModel) (a : Alphabet) :
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 8 a.C≤
      2*model.rat (GeneralPaperDecoderControls.operandWidth a.lambda) := by
  have hp := a.scalePositive
  exact GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 8 a.C _
    (GeneralPaperDecoderControls.code_word a 8 (by omega))
    (GeneralPaperDecoderControls.code_word a a.C (by omega))
    (GeneralPaperDecoderControls.code_word a (8*a.C) (Nat.le_refl _))

theorem bit_work {m : ℕ} (model : RationalCostModel) (W k mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCodes : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    (run true (fun w => w) model W k mesh a response summaries hMesh).2≤profile model W m k a := by
  let arrays := GeneralPaperCatalogueArraysExecution.run true (fun w => w) model W a response summaries
  let tags := GeneralPaperCatalogueTagFamily.run true (fun w => w) model.rat W arrays.1
  have hData := GeneralPaperCatalogueArraysExecution.native_data true (fun w => w) model W k a response summaries
  have hTags := GeneralPaperCatalogueTagFamily.data true (fun w => w) model.rat W arrays.1
  have hA := GeneralPaperCatalogueArraysExecution.bit_work model W a response summaries hCodes
  have hT := GeneralPaperCatalogueTagFamily.bit_work model W a arrays.1
    (GeneralPaperCatalogueTagValue.native_bounds a response k summaries arrays.1 hData)
  have hP := GeneralPaperCatalogueOptionPlans.bit_work model.rat model.monotone W k mesh a response summaries arrays.1 hData tags.1 hTags hMesh
    (fun j r => (hCodes j r).le)
  have hL := limit_work model a
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hA hT) hP) hL) _

theorem arithmetic_work {m : ℕ} (model : RationalCostModel) (k mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCodes : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    (run false (fun _ => 1) model 1 k mesh a response summaries hMesh).2≤arithmeticProfile m k a := by
  let arrays := GeneralPaperCatalogueArraysExecution.run false (fun _ => 1) model 1 a response summaries
  let tags := GeneralPaperCatalogueTagFamily.run false (fun _ => 1) (fun _ => 1) 1 arrays.1
  have hData := GeneralPaperCatalogueArraysExecution.native_data false (fun _ => 1) model 1 k a response summaries
  have hTags := GeneralPaperCatalogueTagFamily.data false (fun _ => 1) (fun _ => 1) 1 arrays.1
  have hA := GeneralPaperCatalogueArraysExecution.arithmetic_work model a response summaries hCodes
  have hT := GeneralPaperCatalogueTagFamily.arithmetic_work arrays.1
  have hP := GeneralPaperCatalogueOptionPlans.arithmetic_work k mesh a response summaries arrays.1 hData tags.1 hTags hMesh
  have hL : GeneralPaperNaturalPrimitivePrice.binary (fun _ => 1) (fun a b => a*b) 8 a.C≤2 := by rfl
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hA hT) hP) hL) _

end Blotto.GeneralPaperCatalogueOptimizerPreparation
