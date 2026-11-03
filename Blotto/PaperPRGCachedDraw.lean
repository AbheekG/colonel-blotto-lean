import Blotto.PaperPRGNormalizedCache

/-! A draw constructs normalized parameter arrays once, passes their actual
readers to the priced initializer/source/terminal/fallback, scales the stored
result once and frames that array. Exact old bytes and budgets hold on every
path. The joined cost still needs the remaining controller-record coverage;
this file does not turn a component observer into a full runtime assertion.
-/

namespace Blotto.PaperPRGCachedDraw
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 512

def sample {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : RationalResourceArray n × ℕ :=
  let W := PRGPaperDrawCost.width p.source p.precision
  let cached := PaperPRGNormalizedCache.build p.source model primitive W rich
  let normalized := PaperPRGInitializationFallbackCost.sample cached.1.system model primitive W p.precision bits
  let scaled := PaperStoredRowConstruction.scale model primitive
    (StoredArrayReferenceList.poolAddressWidth n W) p.source.a normalized.1
  (scaled.1,cached.2+normalized.2+scaled.2)

theorem sample_data {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    (sample p model primitive rich bits).1=NativePRGPreparedSampler.sample p rich bits := by
  unfold sample
  dsimp only
  rw [PaperStoredRowConstruction.scale_data,PaperPRGInitializationFallbackCost.sample_data,
    PaperPRGNormalizedCache.build_system]
  cases rich <;> rfl

def output {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : List Bool :=
  let row := sample p model primitive rich bits
  ReferenceStoredRowFrame.frame p.bytes row.1

theorem output_data {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    output p model primitive rich bits=NativePRGPreparedSampler.output p rich bits := by
  unfold output NativePRGPreparedSampler.output
  dsimp only
  rw [sample_data]

theorem output_budget {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then p.source.a else p.source.b)
      (output p model primitive rich bits) := by
  rw [output_data]
  exact NativePRGPreparedSampler.output_read_budget p rich bits

noncomputable def work {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : ℕ :=
  PaperPRGInitializationFallbackCost.work p model primitive c rich bits+
    (PaperPRGNormalizedCache.build p.source model primitive (PRGPaperDrawCost.width p.source p.precision) rich).2

def bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  let W := PRGPaperDrawCost.width i K
  3*h+2^303*(c+1)*((n+1)*model.withWordTraffic.rat W+(n+K+1)*W)

theorem work_bound {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    work p model primitive c rich bits ≤ bound p.source model c p.precision p.bytes.length := by
  let W := PRGPaperDrawCost.width p.source p.precision
  let N := n+p.precision+1
  let A := (n+1)*model.withWordTraffic.rat W
  let B := N*W
  let Z := A+B
  have hOld := PaperPRGInitializationFallbackCost.work_bound p model primitive c hPrimitive rich bits
  have hCache := PaperPRGNormalizedCache.build_work_bound p.source model primitive c hPrimitive p.precision rich
  have hRat : model.rat W ≤ model.withWordTraffic.rat W := Nat.le_add_right _ _
  have hCoefficients : 8*n+5 ≤ 13*(n+1) := by omega
  have hRational := Nat.mul_le_mul hCoefficients hRat
  have hWord := Nat.mul_le_mul_right W (show n+1 ≤ N by dsimp [N]; omega)
  have hWords := Nat.mul_le_mul_left (512*(c+1)) hWord
  have hExtraRat := Nat.mul_le_mul_left 13 (show A ≤ Z by exact Nat.le_add_right _ _)
  have hExtraWord := Nat.mul_le_mul_left (512*(c+1)) (show B ≤ Z by exact Nat.le_add_left _ _)
  have hC : 13*Z ≤ 13*(c+1)*Z := by nlinarith
  have hFinal := Nat.mul_le_mul_right ((c+1)*Z) (show 2^302+13+512 ≤ 2^303 by decide)
  unfold work bound PaperPRGInitializationFallbackCost.bound at *
  dsimp only [W,N,A,B,Z] at hRational hWords hExtraRat hExtraWord hC hFinal ⊢
  norm_num only [Nat.reducePow] at hOld hFinal ⊢
  nlinarith only [hOld,hCache,hRational,hWords,hExtraRat,hExtraWord,hC,hFinal]

end Blotto.PaperPRGCachedDraw
