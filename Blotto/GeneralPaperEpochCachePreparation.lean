import Blotto.GeneralPaperFieldPlanFamily

/-! Complete native epoch-cache preparation from retained summaries and mesh.
Both optimizer Ready objects and the entire field family are constructed once.
The alphabet limit and final reference record are priced; no source, encoding,
length, work-sum or parameter calibration pass is executed.
-/
namespace Blotto.GeneralPaperEpochCachePreparation
open GeneralPaperCodeAlphabet
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k mesh : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) : GeneralPaperCatalogueEpochCache.Cache m k × ℕ :=
  let candidate := GeneralPaperCatalogueOptimizerPreparation.run bits index model W k mesh a false arrays.lambda hMesh
  let response := GeneralPaperCatalogueOptimizerPreparation.run bits index model W k mesh a true arrays.mu hMesh
  let limit := 8*a.C
  let plans := GeneralPaperFieldPlanFamily.run bits index (primitive bits model) W k limit
    arrays.p arrays.q arrays.lambda arrays.mu candidate.1.data.codes response.1.data.codes
  (⟨a,arrays.p,arrays.q,arrays.lambda,arrays.mu,candidate.1,response.1,plans.1,
    GeneralPaperCatalogueOptimizerPreparation.data bits index model W k mesh a false arrays.lambda hMesh,
    GeneralPaperCatalogueOptimizerPreparation.data bits index model W k mesh a true arrays.mu hMesh,
    GeneralPaperFieldPlanFamily.data bits index (primitive bits model) W k limit
      arrays.p arrays.q arrays.lambda arrays.mu candidate.1.data.codes response.1.data.codes⟩,
    candidate.2+response.2+plans.2+
      GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a*b) 8 a.C+256*W)

def profile (model : RationalCostModel) (W m k : ℕ) (a : Alphabet) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  2*GeneralPaperCatalogueOptimizerPreparation.profile model W m k a+
    GeneralPaperFieldPlanFamily.profile model.rat W m (s+2) (s+2) k (8*a.C)+
    2*model.rat (GeneralPaperDecoderControls.operandWidth a.lambda)+256*W

def arithmeticProfile (m k : ℕ) (a : Alphabet) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  2*GeneralPaperCatalogueOptimizerPreparation.arithmeticProfile m k a+
    GeneralPaperFieldPlanFamily.arithmeticProfile m (s+2) (s+2) k+2+256

theorem data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k mesh : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index model W k mesh a arrays hMesh).1=
      GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu := by
  unfold run GeneralPaperCatalogueEpochCache.prepare
  dsimp only
  simp only [GeneralPaperFieldPlanFamily.data,GeneralPaperCatalogueOptimizerPreparation.data]

theorem bit_work {m : ℕ} (model : RationalCostModel) (W k mesh : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hp : ∀ j r,(arrays.p.read j).read r<8*a.C) (hq : ∀ j r,(arrays.q.read j).read r<8*a.C)
    (hl : ∀ j r,(arrays.lambda.read j).read r<2*(8*a.C)) (hm : ∀ j r,(arrays.mu.read j).read r<2*(8*a.C)) :
    (run true (fun w => w) model W k mesh a arrays hMesh).2≤profile model W m k a := by
  let candidate := GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a false arrays.lambda hMesh
  let response := GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a true arrays.mu hMesh
  have hx : ∀ j r,(candidate.1.data.codes.read j).read r<8*a.C := by
    intro j r
    change ((GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a false arrays.lambda hMesh).1.data.codes.read j).read r<_
    rw [GeneralPaperCatalogueOptimizerPreparation.data]
    exact GeneralPaperCatalogueArrays.code_bound a false k arrays.lambda j r
  have hy : ∀ j r,(response.1.data.codes.read j).read r<8*a.C := by
    intro j r
    change ((GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a true arrays.mu hMesh).1.data.codes.read j).read r<_
    rw [GeneralPaperCatalogueOptimizerPreparation.data]
    exact GeneralPaperCatalogueArrays.code_bound a true k arrays.mu j r
  have hc := GeneralPaperCatalogueOptimizerPreparation.bit_work model W k mesh a false arrays.lambda hMesh hl
  have hr := GeneralPaperCatalogueOptimizerPreparation.bit_work model W k mesh a true arrays.mu hMesh hm
  have hf := GeneralPaperFieldPlanFamily.bit_work model.rat model.monotone W k (8*a.C)
    arrays.p arrays.q arrays.lambda arrays.mu candidate.1.data.codes response.1.data.codes hp hq hl hm hx hy
  have hb := GeneralPaperCatalogueOptimizerPreparation.limit_work model a
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc hr) hf) hb) (256*W)
  change candidate.2+response.2+
    (GeneralPaperFieldPlanFamily.run true (fun w => w) model.rat W k (8*a.C)
      arrays.p arrays.q arrays.lambda arrays.mu candidate.1.data.codes response.1.data.codes).2+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 8 a.C+256*W≤_
  refine h.trans_eq ?_
  unfold profile
  ring

theorem arithmetic_work {m : ℕ} (model : RationalCostModel) (k mesh : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hp : ∀ j r,(arrays.p.read j).read r<8*a.C) (hq : ∀ j r,(arrays.q.read j).read r<8*a.C)
    (hl : ∀ j r,(arrays.lambda.read j).read r<2*(8*a.C)) (hm : ∀ j r,(arrays.mu.read j).read r<2*(8*a.C)) :
    (run false (fun _ => 1) model 1 k mesh a arrays hMesh).2≤arithmeticProfile m k a := by
  let candidate := GeneralPaperCatalogueOptimizerPreparation.run false (fun _ => 1) model 1 k mesh a false arrays.lambda hMesh
  let response := GeneralPaperCatalogueOptimizerPreparation.run false (fun _ => 1) model 1 k mesh a true arrays.mu hMesh
  have hx : ∀ j r,(candidate.1.data.codes.read j).read r<8*a.C := by
    intro j r
    change ((GeneralPaperCatalogueOptimizerPreparation.run false (fun _ => 1) model 1 k mesh a false arrays.lambda hMesh).1.data.codes.read j).read r<_
    rw [GeneralPaperCatalogueOptimizerPreparation.data]
    exact GeneralPaperCatalogueArrays.code_bound a false k arrays.lambda j r
  have hy : ∀ j r,(response.1.data.codes.read j).read r<8*a.C := by
    intro j r
    change ((GeneralPaperCatalogueOptimizerPreparation.run false (fun _ => 1) model 1 k mesh a true arrays.mu hMesh).1.data.codes.read j).read r<_
    rw [GeneralPaperCatalogueOptimizerPreparation.data]
    exact GeneralPaperCatalogueArrays.code_bound a true k arrays.mu j r
  have hc := GeneralPaperCatalogueOptimizerPreparation.arithmetic_work model k mesh a false arrays.lambda hMesh hl
  have hr := GeneralPaperCatalogueOptimizerPreparation.arithmetic_work model k mesh a true arrays.mu hMesh hm
  have hf := GeneralPaperFieldPlanFamily.arithmetic_work k (8*a.C)
    arrays.p arrays.q arrays.lambda arrays.mu candidate.1.data.codes response.1.data.codes hp hq hl hm hx hy
  have hb : GeneralPaperNaturalPrimitivePrice.binary (fun _ => 1) (fun a b => a*b) 8 a.C≤2 := by rfl
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc hr) hf) hb) 256
  change candidate.2+response.2+
    (GeneralPaperFieldPlanFamily.run false (fun _ => 1) (fun _ => 1) 1 k (8*a.C)
      arrays.p arrays.q arrays.lambda arrays.mu candidate.1.data.codes response.1.data.codes).2+2+256≤_
  refine h.trans_eq ?_
  unfold arithmeticProfile
  ring

theorem same_data {m : ℕ} (model : RationalCostModel) (W k mesh : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run true (fun w => w) model W k mesh a arrays hMesh).1=
      (run false (fun _ => 1) model 1 k mesh a arrays hMesh).1 := by
  rw [data,data]

end Blotto.GeneralPaperEpochCachePreparation
