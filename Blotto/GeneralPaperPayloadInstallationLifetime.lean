import Blotto.GeneralPaperUnifiedInstallationOwnership

/-! Actual paper-RAM installation activations. Each saved entry and write
scratch pays for its own payload; suffix price fields contribute only their
encoded width. Source entries and resident RAM are separate owners. No
largest-payload-times-entry-count term is introduced. -/
namespace Blotto.GeneralPaperPayloadInstallationLifetime
open GeneralPaperPayloadMemory (Memory Entry write install)
open GeneralPaperPayloadMemoryOwnership (payload)
open GeneralPaperEncodedScalarStorage
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def cap (S A Q : ℕ) : ℕ := S + A + Q + 1

def controls {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α)
    (entry : Entry A α) (entries : List (Entry A α)) : List ℕ :=
  let current := write A encode memory entry
  let later := install S A encode current.1 entries
  [S,A,current.2,later.2,current.2 + later.2,(install S A encode memory (entry :: entries)).2]

theorem controls_bounded {α : Type*} (S A Q : ℕ) (encode : α → ℕ) (memory : Memory α)
    (entry : Entry A α) (entries : List (Entry A α))
    (hWork : (install S A encode memory (entry :: entries)).2 ≤ Q) :
    ∀ x ∈ controls S A encode memory entry entries,x ≤ cap S A Q := by
  have hWhole := hWork
  change (write A encode memory entry).2 + (install S A encode (write A encode memory entry).1 entries).2 +
    64 * (S + A + 1) ≤ Q at hWork
  intro x hx
  simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
  unfold cap
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def localFoot {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α)
    (entry : Entry A α) (entries : List (Entry A α)) : ℕ :=
  2 * encode entry.2 + 2 * A + fields S (controls S A encode memory entry entries) + 192 * S + 64

def frameBound (S A Q : ℕ) : ℕ := 6 * (natBits (cap S A Q) + S) + 224 * S + 2 * A + 64

theorem local_bound {α : Type*} (S A Q : ℕ) (encode : α → ℕ) (memory : Memory α)
    (entry : Entry A α) (entries : List (Entry A α))
    (hWork : (install S A encode memory (entry :: entries)).2 ≤ Q) :
    localFoot S A encode memory entry entries ≤ 2 * encode entry.2 + frameBound S A Q := by
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A encode memory entry entries) (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono (controls_bounded S A Q encode memory entry entries hWork x hx)) 1)
  change fields S _ ≤ 6 * (natBits (cap S A Q) + S) + 32 * S at hFields
  unfold localFoot frameBound
  omega

def baseFoot {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α) : ℕ :=
  fields S [S,A,(install S A encode memory []).2] + 64 * S

theorem base_bound {α : Type*} (S A Q : ℕ) (encode : α → ℕ) (memory : Memory α)
    (hWork : (install S A encode memory []).2 ≤ Q) : baseFoot S A encode memory ≤ frameBound S A Q := by
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(install S A encode memory []).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  unfold baseFoot frameBound
  omega

def frames {α : Type*} (S A : ℕ) (encode : α → ℕ) : Memory α → List (Entry A α) → ℕ
  | memory,[] => baseFoot S A encode memory
  | memory,entry :: entries => localFoot S A encode memory entry entries + frames S A encode (write A encode memory entry).1 entries

def profile (S A B N Q : ℕ) : ℕ := 2 * B + (N + 1) * frameBound S A Q

theorem frames_bound {α : Type*} (S A Q : ℕ) (encode : α → ℕ) (memory : Memory α)
    (entries : List (Entry A α)) (hWork : (install S A encode memory entries).2 ≤ Q) :
    frames S A encode memory entries ≤ profile S A (payload encode entries) entries.length Q := by
  induction entries generalizing memory with
  | nil =>
    simpa only [frames,profile,payload,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.one_mul] using
      base_bound S A Q encode memory hWork
  | cons entry entries ih =>
    have hLocal := local_bound S A Q encode memory entry entries hWork
    have hChildWork : (install S A encode (write A encode memory entry).1 entries).2 ≤ Q := by
      change (write A encode memory entry).2 + (install S A encode (write A encode memory entry).1 entries).2 +
        64 * (S + A + 1) ≤ Q at hWork
      omega
    have hChild := ih (write A encode memory entry).1 hChildWork
    simp only [frames,profile,payload,List.map_cons,List.sum_cons,List.length_cons] at hChild ⊢
    nlinarith only [hLocal,hChild]

theorem reached_frames {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α)
    (entries : List (Entry A α)) (depth : ℕ) :
    frames S A encode (install S A encode memory (entries.take depth)).1 (entries.drop depth) ≤
      frames S A encode memory entries := by
  induction entries generalizing memory depth with
  | nil => simp only [List.take_nil,List.drop_nil,install,le_refl]
  | cons entry entries ih =>
    cases depth with
    | zero => simp only [List.take_zero,List.drop_zero,install,le_refl]
    | succ depth =>
      have h := ih (write A encode memory entry).1 depth
      simpa only [List.take_succ_cons,List.drop_succ_cons,install] using
        h.trans (show frames S A encode (write A encode memory entry).1 entries ≤ frames S A encode memory (entry :: entries) by
          change _ ≤ localFoot S A encode memory entry entries + frames S A encode (write A encode memory entry).1 entries
          omega)

@[fun_prop]
theorem frame_rate {α : Type*} (S A Q L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hS : Tight S L) (hA : Tight A L) (hQ : Small Q L) :
    Polylog (fun x => frameBound (S x) (A x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => cap (S x) (A x) (Q x)) L := by unfold cap; fun_prop
  unfold frameBound
  fun_prop

theorem profile_rate {α : Type*} (S A B N Q r L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hB : Bound B r L) (hN : Bound N r L) (hQ : Small Q L) :
    Bound (fun x => profile (S x) (A x) (B x) (N x) (Q x)) r L := by
  have hFrame := frame_rate S A Q L hL hS hA hQ
  have hCount : Bound (fun x => N x + 1) r L := by fun_prop
  have hFrames := bound_mul_polylog _ _ r L hCount hFrame
  have hPayload : Bound (fun x => 2 * B x) r L := by fun_prop
  simpa only [profile] using bound_add _ _ r L hL hPayload hFrames

end Blotto.GeneralPaperPayloadInstallationLifetime
