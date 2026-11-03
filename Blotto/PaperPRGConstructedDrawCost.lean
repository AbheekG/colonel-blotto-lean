import Blotto.PaperStoredTerminalConstruction

/-! The actual constructed-row scaling and reached terminal-array metadata
are joined to the prior draw component ledger. Rational scaling is already
in that ledger and is counted once; only its new array/control overhead is
added. Source initialization/fallback and remaining controller records still
need their execution joins before this becomes a complete runtime theorem.
-/

namespace Blotto.PaperPRGConstructedDrawCost
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 512

def scaleOverhead {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (K : ℕ) : ℕ :=
  PaperIndexedArrayConstruction.overhead primitive
    (StoredArrayReferenceList.poolAddressWidth n (PRGPaperDrawCost.width i K)) n n

theorem scaleOverhead_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (K : ℕ) :
    scaleOverhead i primitive K ≤ 64*(c+1)*(n+1)*PRGPaperDrawCost.width i K := by
  have hf := PRGPaperDrawCost.width_facts i K
  have hn : n ≤ PRGPaperDrawCost.width i K := (show n ≤ n+K+1 by omega).trans hf.2.1
  exact (PaperIndexedArrayConstruction.pool_overhead_bound primitive c hPrimitive
    n (PRGPaperDrawCost.width i K) hn).trans
      (Nat.mul_le_mul_left (64*(c+1)*(n+1)) (PRGPaperSharpDrawCost.logFactor_le_width i K))

theorem actualScalingCost {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (PaperStoredRowConstruction.originalScale i model primitive rich K bits).1 =
      NativePRGPreparedSampler.sample (NativePRGPreparedSampler.ofInput i K) rich bits ∧
    (PaperStoredRowConstruction.originalScale i model primitive rich K bits).2 =
      (if rich then i.richScalingBitWork model K bits else i.poorScalingBitWork model K bits)+
        scaleOverhead i primitive K :=
  ⟨PaperStoredRowConstruction.originalScale_data i model primitive rich K bits,
    PaperStoredRowConstruction.originalScale_work i model primitive rich K bits⟩

noncomputable def work {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : ℕ :=
  PRGPaperDrawCost.work p model primitive c rich bits+
    PaperStoredTerminalConstruction.originalWork p.source primitive rich p.precision bits+
      scaleOverhead p.source primitive p.precision

def bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  let W := PRGPaperDrawCost.width i K
  3*h+2^301*(c+1)*((n+1)*model.withWordTraffic.rat W+(n+K+1)*W)

theorem work_bound {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    work p model primitive c rich bits ≤ bound p.source model c p.precision p.bytes.length := by
  let W := PRGPaperDrawCost.width p.source p.precision
  let N := n+p.precision+1
  let Z := (n+1)*model.withWordTraffic.rat W+N*W
  have hOld := PRGPaperSharpDrawCost.work_bound p model primitive c hPrimitive rich bits
  have hTerminal := PaperStoredTerminalConstruction.originalWork_bound p.source primitive c hPrimitive rich p.precision bits
  have hScale := scaleOverhead_bound p.source primitive c hPrimitive p.precision
  have hExtra : (n+1)*W ≤ Z :=
    (Nat.mul_le_mul_right W (show n+1 ≤ N by dsimp [N]; omega)).trans (Nat.le_add_left _ _)
  have hPay := Nat.mul_le_mul_left (2112*(c+1)) hExtra
  have hCoeff := Nat.mul_le_mul_right ((c+1)*Z) (show 2^300+2112 ≤ 2^301 by decide)
  unfold work bound PRGPaperSharpDrawCost.bound at *
  dsimp only [W,N,Z] at hPay hCoeff ⊢
  norm_num only [Nat.reducePow] at hOld hCoeff ⊢
  nlinarith only [hOld,hTerminal,hScale,hPay,hCoeff]

end Blotto.PaperPRGConstructedDrawCost
