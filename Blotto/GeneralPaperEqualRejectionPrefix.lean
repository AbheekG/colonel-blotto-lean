import Blotto.GeneralPaperEqualNativeSampler

/-! One fixed trial tape underlies every first-success truncation. Once a
run succeeds, extending its truncation changes neither output nor fresh-read
count. Concatenating its first blocks gives exactly the checked flat runner.
The tape is a semantic input, not a probability or termination oracle. -/
namespace Blotto.GeneralPaperEqualRejectionPrefix
open GeneralPaperEqualRejectionReads (Result)
open UniformNatRejection (width attempt)
set_option autoImplicit false
set_option maxHeartbeats 600000

def tail {W : ℕ} (tape : ℕ → Fin W → Bool) : ℕ → Fin W → Bool := fun t => tape (t + 1)

def blockRun (N : ℕ) : ℕ → (ℕ → Fin (width N) → Bool) → Result N
  | 0, _ => ⟨none, 0⟩
  | cap + 1, tape =>
    match attempt N (tape 0) with
    | some r => ⟨some r, BinaryPayload.readCount (width N)⟩
    | none =>
      let later := blockRun N cap (tail tape)
      ⟨later.output, BinaryPayload.readCount (width N) + later.reads⟩

def seed (W : ℕ) : (cap : ℕ) → (ℕ → Fin W → Bool) → Fin (cap * W) → Bool
  | 0, _, j => False.elim (by have hj := j.isLt; simp at hj)
  | cap + 1, tape, j =>
    Fin.append (tape 0) (seed W cap (tail tape)) (j.cast (by ring))

theorem first_seed (W cap : ℕ) (tape : ℕ → Fin W → Bool) :
    firstBitBlock W (cap * W) (fun j => seed W (cap + 1) tape (j.cast (by ring))) = tape 0 := by
  funext j
  unfold firstBitBlock
  dsimp only
  conv => lhs; rw [seed.eq_def]
  change Fin.append (tape 0) (seed W cap (tail tape)) (Fin.castAdd (cap * W) j) = tape 0 j
  exact Fin.append_left _ _ j

theorem second_seed (W cap : ℕ) (tape : ℕ → Fin W → Bool) :
    secondBitBlock W (cap * W) (fun j => seed W (cap + 1) tape (j.cast (by ring))) =
      seed W cap (tail tape) := by
  funext j
  unfold secondBitBlock
  dsimp only
  conv => lhs; rw [seed.eq_def]
  change Fin.append (tape 0) (seed W cap (tail tape)) (Fin.natAdd W j) = _
  exact Fin.append_right _ _ j

theorem run_seed (N cap : ℕ) (tape : ℕ → Fin (width N) → Bool) :
    GeneralPaperEqualRejectionReads.run N cap (seed (width N) cap tape) = blockRun N cap tape := by
  induction cap generalizing tape with
  | zero => rfl
  | succ cap ih =>
    rw [GeneralPaperEqualRejectionReads.run, blockRun]
    dsimp only
    rw [first_seed, second_seed, ih]
    cases attempt N (tape 0) <;> rfl

theorem success_stable_one (N cap : ℕ) (tape : ℕ → Fin (width N) → Bool)
    (r : Fin N) (h : (blockRun N cap tape).output = some r) :
    blockRun N (cap + 1) tape = blockRun N cap tape := by
  induction cap generalizing tape with
  | zero => simp only [blockRun] at h; contradiction
  | succ cap ih =>
    rw [blockRun] at h
    conv => lhs; rw [blockRun]
    conv => rhs; rw [blockRun]
    cases he : attempt N (tape 0) with
    | some rank => rfl
    | none =>
      simp only [he] at h ⊢
      rw [ih (tail tape) h]

theorem success_stable (N cap extra : ℕ) (tape : ℕ → Fin (width N) → Bool)
    (r : Fin N) (h : (blockRun N cap tape).output = some r) :
    blockRun N (cap + extra) tape = blockRun N cap tape := by
  induction extra with
  | zero => simp only [Nat.add_zero]
  | succ extra ih =>
    have hs : (blockRun N (cap + extra) tape).output = some r := by rw [ih]; exact h
    rw [Nat.add_succ, success_stable_one N (cap + extra) tape r hs, ih]

def Completes (N : ℕ) (tape : ℕ → Fin (width N) → Bool) (r : Fin N) (reads : ℕ) : Prop :=
  ∃ cap, blockRun N cap tape = ⟨some r, reads⟩

theorem completes_unique (N : ℕ) (tape : ℕ → Fin (width N) → Bool)
    (a b : Fin N) (ra rb : ℕ) (ha : Completes N tape a ra) (hb : Completes N tape b rb) :
    a = b ∧ ra = rb := by
  obtain ⟨ca, ha⟩ := ha
  obtain ⟨cb, hb⟩ := hb
  have h0 : (blockRun N ca tape).output = some a := by rw [ha]
  have h1 : (blockRun N cb tape).output = some b := by rw [hb]
  have hs0 := success_stable N ca cb tape a h0
  have hs1 := success_stable N cb ca tape b h1
  rw [Nat.add_comm cb ca] at hs1
  have he := hs0.symm.trans hs1
  rw [ha, hb] at he
  exact ⟨Option.some.inj (congrArg Result.output he), congrArg Result.reads he⟩

theorem failure_all (N cap : ℕ) (tape : ℕ → Fin (width N) → Bool) :
    (blockRun N cap tape).output = none ↔ ∀ t < cap, attempt N (tape t) = none := by
  induction cap generalizing tape with
  | zero => simp [blockRun]
  | succ cap ih =>
    rw [blockRun]
    cases h : attempt N (tape 0) with
    | some r =>
      simp only [Option.some_ne_none, false_iff]
      intro ha
      have he := ha 0 (by omega)
      rw [h] at he
      contradiction
    | none =>
      dsimp only
      rw [ih]
      constructor
      · intro ha t ht
        cases t with
        | zero => exact h
        | succ t => exact ha t (by omega)
      · intro ha t ht
        exact ha (t + 1) (by omega)

theorem failure_reads (N cap : ℕ) (tape : ℕ → Fin (width N) → Bool)
    (h : (blockRun N cap tape).output = none) : (blockRun N cap tape).reads = cap * width N := by
  induction cap generalizing tape with
  | zero => simp only [blockRun, Nat.zero_mul]
  | succ cap ih =>
    have hFirst := (failure_all N (cap + 1) tape).mp h 0 (by omega)
    rw [blockRun, hFirst] at h ⊢
    dsimp only at h ⊢
    rw [ih (tail tape) h, BinaryPayload.readCount_eq]
    ring

theorem first_success (N cap : ℕ) (tape : ℕ → Fin (width N) → Bool) (r : Fin N)
    (hFail : ∀ t < cap, attempt N (tape t) = none) (hLast : attempt N (tape cap) = some r) :
    blockRun N (cap + 1) tape = ⟨some r, (cap + 1) * width N⟩ := by
  induction cap generalizing tape with
  | zero => simp only [blockRun, hLast, BinaryPayload.readCount_eq, Nat.zero_add, Nat.one_mul]
  | succ cap ih =>
    have h0 := hFail 0 (by omega)
    rw [blockRun, h0]
    have hTail : ∀ t < cap, attempt N (tail tape t) = none := fun t ht => hFail (t + 1) (by omega)
    have hLast' : attempt N (tail tape cap) = some r := hLast
    rw [ih (tail tape) hTail hLast']
    simp only [BinaryPayload.readCount_eq]
    congr 1
    ring

theorem flat_failure_reads (N cap : ℕ) (bits : Fin (cap * width N) → Bool)
    (h : (GeneralPaperEqualRejectionReads.run N cap bits).output = none) :
    (GeneralPaperEqualRejectionReads.run N cap bits).reads = cap * width N := by
  induction cap with
  | zero => simp only [GeneralPaperEqualRejectionReads.run, Nat.zero_mul]
  | succ cap ih =>
    rw [GeneralPaperEqualRejectionReads.run] at h ⊢
    dsimp only at h ⊢
    cases he : attempt N (firstBitBlock (width N) (cap * width N)
      (fun j => bits (j.cast (by ring)))) with
    | some r => rw [he] at h; cases h
    | none =>
      rw [he] at h
      dsimp only at h ⊢
      rw [ih _ h, BinaryPayload.readCount_eq]
      ring

theorem blocks_ext (W R : ℕ) (a b : Fin (W + R) → Bool)
    (hf : firstBitBlock W R a = firstBitBlock W R b)
    (hs : secondBitBlock W R a = secondBitBlock W R b) : a = b := by
  calc
    a = Fin.append (firstBitBlock W R a) (secondBitBlock W R a) := Fin.append_castAdd_natAdd.symm
    _ = Fin.append (firstBitBlock W R b) (secondBitBlock W R b) := congrArg₂ Fin.append hf hs
    _ = b := Fin.append_castAdd_natAdd

theorem seed_congr (W cap : ℕ) (a b : ℕ → Fin W → Bool)
    (h : ∀ t < cap, a t = b t) : seed W cap a = seed W cap b := by
  induction cap generalizing a b with
  | zero =>
    funext j
    have hj := j.isLt
    simp at hj
  | succ cap ih =>
    have hSize : (cap + 1) * W = W + cap * W := by ring
    have he : (fun j : Fin (W + cap * W) => seed W (cap + 1) a (j.cast hSize.symm)) =
        (fun j : Fin (W + cap * W) => seed W (cap + 1) b (j.cast hSize.symm)) := by
      apply blocks_ext W (cap * W)
      ·
        rw [first_seed, first_seed]
        exact h 0 (by omega)
      ·
        rw [second_seed, second_seed]
        exact ih (tail a) (tail b) (fun t ht => h (t + 1) (by omega))
    funext j
    have hj := congrFun he (j.cast hSize)
    simpa only [Fin.cast_cast, Fin.cast_refl, id_eq] using hj

theorem seed_surjective (W cap : ℕ) : Function.Surjective (seed W cap) := by
  induction cap with
  | zero =>
    intro bits
    refine ⟨fun _ _ => false, ?_⟩
    funext j
    have hj := j.isLt
    simp at hj
  | succ cap ih =>
    intro bits
    have hSize : (cap + 1) * W = W + cap * W := by ring
    let flat : Fin (W + cap * W) → Bool := fun j => bits (j.cast hSize.symm)
    obtain ⟨later, hl⟩ := ih (secondBitBlock W (cap * W) flat)
    let tape : ℕ → Fin W → Bool := fun t => match t with
      | 0 => firstBitBlock W (cap * W) flat
      | t + 1 => later t
    refine ⟨tape, ?_⟩
    have he : (fun j : Fin (W + cap * W) => seed W (cap + 1) tape (j.cast hSize.symm)) = flat := by
      apply blocks_ext W (cap * W)
      ·
        rw [first_seed]
      ·
        rw [second_seed]
        exact hl
    funext j
    have hj := congrFun he (j.cast hSize)
    simpa only [flat, Fin.cast_cast, Fin.cast_refl, id_eq] using hj

end Blotto.GeneralPaperEqualRejectionPrefix
