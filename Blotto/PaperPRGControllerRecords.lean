import Blotto.PaperSharedControllerRecords

/-! Reached source and terminal cursor/return fields join the cached draw
ledger. The actual guards and global reader/cap are retained; a bounded
source exhaustion pays no terminal component. No native runtime calibration
is asserted, and complete source coverage still requires its final audit.
-/

namespace Blotto.PaperPRGControllerRecords
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 512

noncomputable def systemWork {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let outer := secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let scalar := secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  let choice := firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  PaperSharedControllerRecords.sourceWork i primitive W (RationalLottoResourceSystem.coinBitBudget n K) choice+
    PaperSharedControllerRecords.terminalWork i model primitive W K (RationalLottoResourceSystem.coinBitBudget n K)
      outer scalar choice

theorem systemWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ} (h : i.OnLattice D)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (W K : ℕ) (hW : 1 ≤ W) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    systemWork i model primitive W K bits ≤ 2^26*(c+1)*(n+K+1)*W := by
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let outer := secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let scalar := secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  let choice := firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  have hSource := PaperSharedControllerRecords.sourceWork_bound i primitive c hPrimitive W
    (RationalLottoResourceSystem.coinBitBudget n K) hW choice
  have hTerminal := PaperSharedControllerRecords.OnLattice_terminalWork_bound h model primitive c hPrimitive W K
    (RationalLottoResourceSystem.coinBitBudget n K) hW outer scalar choice
  have hCount : 2*n+3*RationalLottoResourceSystem.coinBitBudget n K+165 ≤ 10000*(n+K+1) := by
    unfold RationalLottoResourceSystem.coinBitBudget
    omega
  have hCountPay := Nat.mul_le_mul_left (2048*(c+1)*W) hCount
  have hCoefficient := Nat.mul_le_mul_right ((c+1)*(n+K+1)*W) (show 2048*10000 ≤ 2^26 by decide)
  unfold systemWork
  change _+_ ≤ _
  dsimp only [inner,outer,scalar,choice] at hSource hTerminal
  norm_num only [Nat.reducePow] at hCoefficient ⊢
  nlinarith only [hSource,hTerminal,hCountPay,hCoefficient]

noncomputable def originalWork {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then systemWork i.normalizedInput.richNativeSystem model primitive (PRGPaperDrawCost.width i K) K bits
  else systemWork i.normalizedInput.poorNativeSystem model primitive (PRGPaperDrawCost.width i K) K bits

theorem originalWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    originalWork i model primitive rich K bits ≤ 2^26*(c+1)*(n+K+1)*PRGPaperDrawCost.width i K := by
  have hW := (PRGPaperDrawCost.width_facts i K).1
  unfold originalWork
  cases rich with
  | false => exact systemWork_bound i.normalizedInput.poorNativeSystem_on_lattice model primitive c hPrimitive _ K hW bits
  | true => exact systemWork_bound i.normalizedInput.richNativeSystem_on_lattice model primitive c hPrimitive _ K hW bits

noncomputable def work {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : ℕ :=
  PaperPRGCachedDraw.work p model primitive c rich bits+originalWork p.source model primitive rich p.precision bits

def bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  let W := PRGPaperDrawCost.width i K
  3*h+2^304*(c+1)*((n+1)*model.withWordTraffic.rat W+(n+K+1)*W)

theorem work_bound {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    work p model primitive c rich bits ≤ bound p.source model c p.precision p.bytes.length := by
  let W := PRGPaperDrawCost.width p.source p.precision
  let N := n+p.precision+1
  let Z := (n+1)*model.withWordTraffic.rat W+N*W
  have hOld := PaperPRGCachedDraw.work_bound p model primitive c hPrimitive rich bits
  have hRecords := originalWork_bound p.source model primitive c hPrimitive rich p.precision bits
  have hEnvelope : N*W ≤ Z := Nat.le_add_left _ _
  have hPay := Nat.mul_le_mul_left (2^26*(c+1)) hEnvelope
  have hCoefficient := Nat.mul_le_mul_right ((c+1)*Z) (show 2^303+2^26 ≤ 2^304 by decide)
  unfold work bound PaperPRGCachedDraw.bound at *
  dsimp only [W,N,Z] at hPay hCoefficient ⊢
  norm_num only [Nat.reducePow] at hOld hRecords hPay hCoefficient ⊢
  nlinarith only [hOld,hRecords,hPay,hCoefficient]

end Blotto.PaperPRGControllerRecords
