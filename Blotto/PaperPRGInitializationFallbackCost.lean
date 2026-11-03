import Blotto.PaperResourceInitialization

/-! Constructed initialization and direct exhaustion fallback are used on the
actual bounded source/terminal path. Both runtime fields and typed invariants
come from the existing legal input. Their extra costs have original-input
width bounds and join the previously priced draw without repricing rational
initialization or fallback copies already present in its arithmetic ledger.
-/

namespace Blotto.PaperPRGInitializationFallbackCost
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 512

def initializedFixedRun {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (Option (RationalResourceArray n) × ℕ) × ℕ :=
  let A := StoredArrayReferenceList.poolAddressWidth n W
  let initial := PaperResourceInitialization.initial model primitive A i.length i.initial
  have hInvariant : i.SharedInvariant (.ready initial.1) := by
    rw [PaperResourceInitialization.initial_data]
    exact i.initial_invariant
  (i.runStoredWithTerminalIndexed
    (fun value => PaperStoredTerminalConstruction.program (i.terminalData value) model primitive W K outer scalar)
    R choice (.ready initial.1) hInvariant 0 (Nat.zero_le R),initial.2)

theorem initializedFixedRun_data {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (initializedFixedRun i model primitive W K R outer scalar choice).1 = i.storedFixedRun K R outer scalar choice := by
  unfold initializedFixedRun
  simp only [PaperResourceInitialization.initial_data,PaperStoredTerminalConstruction.program_data]
  rfl

theorem initializedFixedRun_work {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (initializedFixedRun i model primitive W K R outer scalar choice).2 =
      rationalInitialDataBitCost model i.length i.initial+
        PaperResourceInitialization.metadata primitive (StoredArrayReferenceList.poolAddressWidth n W) n :=
  PaperResourceInitialization.initial_work model primitive _ i.length i.initial

def fixedSample {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    RationalResourceArray n × ℕ :=
  let initialized := initializedFixedRun i model primitive W K R outer scalar choice
  let returned := PaperStoredFallbackConstruction.finish i primitive
    (StoredArrayReferenceList.poolAddressWidth n W) R initialized.1.1
  (returned.1,initialized.2+returned.2)

theorem fixedSample_data {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (fixedSample i model primitive W K R outer scalar choice).1 = i.storedFixedSample K R outer scalar choice := by
  unfold fixedSample
  dsimp only
  rw [initializedFixedRun_data]
  have h := PaperStoredFallbackConstruction.fixedSample_data i model primitive W K R outer scalar choice
  simpa only [PaperStoredFallbackConstruction.fixedSample,i.paperConstructedFixedRun_data] using h

theorem fixedSample_work {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (fixedSample i model primitive W K R outer scalar choice).2 =
      rationalInitialDataBitCost model i.length i.initial+i.paperFallbackBitWork K R outer scalar choice+
        PaperResourceInitialization.metadata primitive (StoredArrayReferenceList.poolAddressWidth n W) n+
        PaperStoredFallbackConstruction.extra i primitive W K R outer scalar choice := by
  unfold fixedSample
  dsimp only
  rw [initializedFixedRun_work,initializedFixedRun_data]
  have h := PaperStoredFallbackConstruction.fixedSample_work i model primitive W K R outer scalar choice
  simp only [PaperStoredFallbackConstruction.fixedSample,i.paperConstructedFixedRun_data] at h
  omega

def sample {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    RationalResourceArray n × ℕ :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  fixedSample i model primitive W K (RationalLottoResourceSystem.coinBitBudget n K)
    (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)

theorem sample_data {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample i model primitive W K bits).1 = i.storedPaperSample K bits := by
  unfold sample RationalLottoResourceSystem.storedPaperSample
  exact fixedSample_data i model primitive W K _ _ _ _

def systemExtra {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ)
    (W K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  PaperResourceInitialization.metadata primitive (StoredArrayReferenceList.poolAddressWidth n W) n+
    PaperStoredFallbackConstruction.extra i primitive W K (RationalLottoResourceSystem.coinBitBudget n K)
      (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
      (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)
      (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)

def originalExtra {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ)
    (rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then systemExtra i.normalizedInput.richNativeSystem primitive (PRGPaperDrawCost.width i K) K bits
  else systemExtra i.normalizedInput.poorNativeSystem primitive (PRGPaperDrawCost.width i K) K bits

theorem originalExtra_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    originalExtra i primitive rich K bits ≤ 1280*(c+1)*(n+1)*PRGPaperDrawCost.width i K := by
  let W := PRGPaperDrawCost.width i K
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let outer := secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let scalar := secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  let choice := firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  have hf := PRGPaperDrawCost.width_facts i K
  have hn : n ≤ W := (show n ≤ n+K+1 by omega).trans hf.2.1
  have hR : RationalLottoResourceSystem.coinBitBudget n K ≤ W := by
    have h := hf.2.2.2.2.1
    rw [RationalLottoResourceSystem.sampleBitBudget_eq] at h
    unfold RationalLottoResourceSystem.coinBitBudget
    omega
  have hLog := PRGPaperSharpDrawCost.logFactor_le_width i K
  have hInitial := PaperResourceInitialization.metadata_bound primitive c hPrimitive n W hn hf.1 hLog
  have hRich := PaperStoredFallbackConstruction.extra_bound i.normalizedInput.richNativeSystem primitive c hPrimitive
    W K (RationalLottoResourceSystem.coinBitBudget n K) hn hR hf.1 hLog outer scalar choice
  have hPoor := PaperStoredFallbackConstruction.extra_bound i.normalizedInput.poorNativeSystem primitive c hPrimitive
    W K (RationalLottoResourceSystem.coinBitBudget n K) hn hR hf.1 hLog outer scalar choice
  unfold originalExtra systemExtra
  cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> dsimp only [W,inner,outer,scalar,choice] at * <;>
    nlinarith only [hInitial,hRich,hPoor]

noncomputable def work {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : ℕ :=
  PaperPRGConstructedDrawCost.work p model primitive c rich bits+originalExtra p.source primitive rich p.precision bits

def bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  let W := PRGPaperDrawCost.width i K
  3*h+2^302*(c+1)*((n+1)*model.withWordTraffic.rat W+(n+K+1)*W)

theorem work_bound {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    work p model primitive c rich bits ≤ bound p.source model c p.precision p.bytes.length := by
  let W := PRGPaperDrawCost.width p.source p.precision
  let N := n+p.precision+1
  let Z := (n+1)*model.withWordTraffic.rat W+N*W
  have hOld := PaperPRGConstructedDrawCost.work_bound p model primitive c hPrimitive rich bits
  have hExtra := originalExtra_bound p.source primitive c hPrimitive rich p.precision bits
  have hEnvelope : (n+1)*W ≤ Z :=
    (Nat.mul_le_mul_right W (show n+1 ≤ N by dsimp [N]; omega)).trans (Nat.le_add_left _ _)
  have hPay := Nat.mul_le_mul_left (1280*(c+1)) hEnvelope
  have hCoeff := Nat.mul_le_mul_right ((c+1)*Z) (show 2^301+1280 ≤ 2^302 by decide)
  unfold work bound PaperPRGConstructedDrawCost.bound at *
  dsimp only [W,N,Z] at hPay hCoeff ⊢
  norm_num only [Nat.reducePow] at hOld hCoeff ⊢
  nlinarith only [hOld,hExtra,hPay,hCoeff]

end Blotto.PaperPRGInitializationFallbackCost
