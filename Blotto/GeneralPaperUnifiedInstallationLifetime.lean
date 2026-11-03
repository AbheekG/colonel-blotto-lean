import Blotto.GeneralPaperStoredConstructorMemoryOwnership

/-! Complete data/activation window for the actual unified installer:
typed input entries, both lifted value lists, both lifting recursions,
both paper-RAM write recursions and saved parent price accumulations.
Resident memory has a separate additive finite-ownership bound. Every
payload is charged by its own width. Collection/count/cursor frames belong
to their enclosing callers and are not claimed by this window. -/
namespace Blotto.GeneralPaperUnifiedInstallationLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadMemoryOwnership (Bounded payload cellSize)
open GeneralPaperUnifiedFieldValue (Memory Value encode)
open GeneralPaperUnifiedFieldMemory
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def entryFoot {α : Type*} (S A : ℕ) (code : α → ℕ) (entry : GeneralPaperPayloadMemory.Entry A α) : ℕ :=
  A + code entry.2 + 64 * S

theorem entry_list {α : Type*} (S A : ℕ) (code : α → ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A α)) :
    listFootprint S (entryFoot S A code) entries = payload code entries + entries.length * (A + 66 * S) + 32 * S := by
  induction entries with
  | nil => simp only [listFootprint,payload,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons entry entries ih =>
    simp only [listFootprint,payload,entryFoot,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    nlinarith only [ih]

def dataFoot (S A : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) : ℕ :=
  listFootprint S (fun _ : GeneralPaperReferenceSlotConstruction.Entry A => 2 * A + 64 * S) words +
    listFootprint S (entryFoot S A GeneralPaperRetainedScalarValue.encode) scalars +
    listFootprint S (entryFoot S A encode) (liftWords S A words).1 +
    listFootprint S (entryFoot S A encode) (liftScalars S A scalars).1

def dataBound (S A Nw Ns E : ℕ) : ℕ :=
  2 * Nw * (2 * A + 66 * S) + 2 * E + 2 * Ns * (A + 66 * S) + 128 * S

theorem data_bound (S A : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) :
    dataFoot S A words scalars ≤ dataBound S A words.length scalars.length (payload GeneralPaperRetainedScalarValue.encode scalars) := by
  have hWords := list_bound S (2 * A + 64 * S)
    (fun _ : GeneralPaperReferenceSlotConstruction.Entry A => 2 * A + 64 * S) words (fun _ _ => le_rfl)
  have hScalars := entry_list S A GeneralPaperRetainedScalarValue.encode scalars
  have hw := entry_list S A encode (liftWords S A words).1
  have hs := entry_list S A encode (liftScalars S A scalars).1
  have hwLength : (liftWords S A words).1.length = words.length := by rw [lift_words_data,List.length_map]
  have hsLength : (liftScalars S A scalars).1.length = scalars.length := by rw [lift_scalars_data,List.length_map]
  unfold payload at hw hs
  rw [word_payload,hwLength] at hw
  rw [scalar_payload,hsLength] at hs
  unfold dataFoot dataBound
  dsimp only [payload] at *
  nlinarith only [hWords,hScalars,hw,hs]

def liftFrameBound (S A Q : ℕ) : ℕ :=
  4 * (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q) + S) + 160 * S + 64

def liftFrames {α : Type*} (S A : ℕ) (code : α → ℕ) (work : List α → ℕ) : List α → ℕ
  | [] => fields S [S,A,work []] + 64 * S
  | entry :: entries => code entry + fields S [S,A,work entries,work (entry :: entries)] + 128 * S +
      liftFrames S A code work entries

theorem lift_frames_bound {α : Type*} (S A Q : ℕ) (code : α → ℕ) (work : List α → ℕ) (entries : List α)
    (hStep : ∀ entry rest,work rest ≤ work (entry :: rest)) (hWork : work entries ≤ Q) :
    liftFrames S A code work entries ≤ (entries.map code).sum + (entries.length + 1) * liftFrameBound S A Q := by
  induction entries with
  | nil =>
    have hFields := fields_bound S (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q)) [S,A,work []] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold GeneralPaperPayloadInstallationLifetime.cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q) + S) + 32 * S at hFields
    simp only [liftFrames,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
    unfold liftFrameBound
    omega
  | cons entry entries ih =>
    have hTailWork := (hStep entry entries).trans hWork
    have hTail := ih hTailWork
    have hFields := fields_bound S (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q))
      [S,A,work entries,work (entry :: entries)] (by
        intro x hx
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        unfold GeneralPaperPayloadInstallationLifetime.cap
        rcases hx with rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 4 * (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q) + S) + 32 * S at hFields
    simp only [liftFrames,List.map_cons,List.sum_cons,List.length_cons]
    unfold liftFrameBound at hTail ⊢
    nlinarith only [hFields,hTail]

theorem address_payload {α : Type*} (A : ℕ) (code : α → ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A α)) :
    (entries.map (fun entry => A + code entry.2)).sum = entries.length * A + payload code entries := by
  induction entries with
  | nil => simp only [payload,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons entry entries ih =>
    simp only [payload,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    nlinarith only [ih]

def controls (S A : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) (memory : Memory) : List ℕ :=
  let w := liftWords S A words
  let first := GeneralPaperPayloadMemory.install S A encode memory w.1
  let s := liftScalars S A scalars
  let second := GeneralPaperPayloadMemory.install S A encode first.1 s.1
  [S,A,w.2,first.2,s.2,second.2,w.2 + first.2,w.2 + first.2 + s.2,(prepare S A words scalars memory).2]

theorem component_prices (S A Q : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) (memory : Memory)
    (hWork : (prepare S A words scalars memory).2 ≤ Q) :
    (liftWords S A words).2 ≤ Q ∧ (liftScalars S A scalars).2 ≤ Q ∧
      (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).2 ≤ Q ∧
      (GeneralPaperPayloadMemory.install S A encode
        (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).1 (liftScalars S A scalars).1).2 ≤ Q := by
  dsimp only [prepare] at hWork
  omega

theorem controls_bounded (S A Q : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) (memory : Memory)
    (hWork : (prepare S A words scalars memory).2 ≤ Q) :
    ∀ x ∈ controls S A words scalars memory,x ≤ GeneralPaperPayloadInstallationLifetime.cap S A Q := by
  have hWhole := hWork
  dsimp only [prepare] at hWork
  intro x hx
  simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
  unfold GeneralPaperPayloadInstallationLifetime.cap
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def window (S A : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) (memory : Memory) : ℕ :=
  dataFoot S A words scalars +
    liftFrames S A (fun _ : GeneralPaperReferenceSlotConstruction.Entry A => 2 * A) (fun xs => (liftWords S A xs).2) words +
    liftFrames S A (fun entry : GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar => A + GeneralPaperRetainedScalarValue.encode entry.2)
      (fun xs => (liftScalars S A xs).2) scalars +
    GeneralPaperPayloadInstallationLifetime.frames S A encode memory (liftWords S A words).1 +
    GeneralPaperPayloadInstallationLifetime.frames S A encode
      (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).1 (liftScalars S A scalars).1 +
    fields S (controls S A words scalars memory) + 128 * S

def profile (S A Nw Ns E Q : ℕ) : ℕ :=
  dataBound S A Nw Ns E + (2 * Nw * A + (Nw + 1) * liftFrameBound S A Q) +
    (Ns * A + E + (Ns + 1) * liftFrameBound S A Q) +
    GeneralPaperPayloadInstallationLifetime.profile S A (Nw * A) Nw Q +
    GeneralPaperPayloadInstallationLifetime.profile S A E Ns Q +
    9 * (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q) + S) + 160 * S

theorem profile_mono (S A Nw Ns E Mw Ms F Q : ℕ) (hw : Nw ≤ Mw) (hs : Ns ≤ Ms) (he : E ≤ F) :
    profile S A Nw Ns E Q ≤ profile S A Mw Ms F Q := by
  unfold profile dataBound GeneralPaperPayloadInstallationLifetime.profile
  gcongr

theorem window_bound (S A Q : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) (memory : Memory)
    (hWork : (prepare S A words scalars memory).2 ≤ Q) :
    window S A words scalars memory ≤ profile S A words.length scalars.length (payload GeneralPaperRetainedScalarValue.encode scalars) Q := by
  have hData := data_bound S A words scalars
  have hPrices := component_prices S A Q words scalars memory hWork
  have hwLift := lift_frames_bound S A Q (fun _ : GeneralPaperReferenceSlotConstruction.Entry A => 2 * A)
    (fun xs => (liftWords S A xs).2) words (fun entry rest => by dsimp only [liftWords]; omega) hPrices.1
  have hwSum : (words.map (fun _ => 2 * A)).sum = 2 * words.length * A := by
    simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
    ring
  rw [hwSum] at hwLift
  have hsLift := lift_frames_bound S A Q
    (fun entry : GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar => A + GeneralPaperRetainedScalarValue.encode entry.2)
    (fun xs => (liftScalars S A xs).2) scalars (fun entry rest => by dsimp only [liftScalars]; omega) hPrices.2.1
  rw [address_payload] at hsLift
  have hwInstall := GeneralPaperPayloadInstallationLifetime.frames_bound S A Q encode memory (liftWords S A words).1 hPrices.2.2.1
  have hsInstall := GeneralPaperPayloadInstallationLifetime.frames_bound S A Q encode
    (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).1 (liftScalars S A scalars).1 hPrices.2.2.2
  have hwLength : (liftWords S A words).1.length = words.length := by rw [lift_words_data,List.length_map]
  have hsLength : (liftScalars S A scalars).1.length = scalars.length := by rw [lift_scalars_data,List.length_map]
  unfold payload at hwInstall hsInstall
  rw [word_payload,hwLength] at hwInstall
  rw [scalar_payload,hsLength] at hsInstall
  have hFields := fields_bound S (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q)) (controls S A words scalars memory) (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono (controls_bounded S A Q words scalars memory hWork x hx)) 1)
  change fields S _ ≤ 9 * (natBits (GeneralPaperPayloadInstallationLifetime.cap S A Q) + S) + 32 * S at hFields
  unfold window profile
  dsimp only [payload] at *
  omega

theorem resident_coexistence (S A B Q : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar)) (memory : Memory)
    (hMemory : Bounded encode memory B) (hWork : (prepare S A words scalars memory).2 ≤ Q) :
    ∃ keys : Finset ℕ,(∀ key,(prepare S A words scalars memory).1 key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (prepare S A words scalars memory).1 key) + window S A words scalars memory ≤
        B + words.length * A + payload GeneralPaperRetainedScalarValue.encode scalars +
          profile S A words.length scalars.length (payload GeneralPaperRetainedScalarValue.encode scalars) Q := by
  obtain ⟨keys,hSupport,hResident⟩ := GeneralPaperUnifiedInstallationOwnership.prepare_bounded S A B words scalars memory hMemory
  have hWindow := window_bound S A Q words scalars memory hWork
  exact ⟨keys,hSupport,Nat.add_le_add hResident hWindow⟩

@[fun_prop]
theorem lift_frame_rate {α : Type*} (S A Q L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hS : Tight S L) (hA : Tight A L) (hQ : Small Q L) :
    Polylog (fun x => liftFrameBound (S x) (A x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => GeneralPaperPayloadInstallationLifetime.cap (S x) (A x) (Q x)) L := by
    unfold GeneralPaperPayloadInstallationLifetime.cap
    fun_prop
  unfold liftFrameBound
  fun_prop

theorem profile_rate {α : Type*} (S A Nw Ns E Q r L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hNw : Bound Nw r L) (hNs : Bound Ns r L) (hE : Bound E r L) (hQ : Small Q L) :
    Bound (fun x => profile (S x) (A x) (Nw x) (Ns x) (E x) (Q x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hwPayload : Bound (fun x => Nw x * A x) r L := by fun_prop
  have hwInstall := GeneralPaperPayloadInstallationLifetime.profile_rate S A (fun x => Nw x * A x) Nw Q r L hL hr hS hA hwPayload hNw hQ
  have hsInstall := GeneralPaperPayloadInstallationLifetime.profile_rate S A E Ns Q r L hL hr hS hA hE hNs hQ
  have hLift := lift_frame_rate S A Q L hL hS hA hQ
  have hwCount : Bound (fun x => Nw x + 1) r L := by fun_prop
  have hsCount : Bound (fun x => Ns x + 1) r L := by fun_prop
  have hwFrames := bound_mul_polylog _ _ r L hwCount hLift
  have hsFrames := bound_mul_polylog _ _ r L hsCount hLift
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => GeneralPaperPayloadInstallationLifetime.cap (S x) (A x) (Q x)) L := by
    unfold GeneralPaperPayloadInstallationLifetime.cap
    fun_prop
  unfold profile dataBound
  fun_prop (config := {maxSteps := 30000})

end Blotto.GeneralPaperUnifiedInstallationLifetime
