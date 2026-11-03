import Blotto.BinaryTerminalCacheLifetime

/-! One operational resource-to-cache prefix. The resource state which the
traced Boolean loop actually returns supplies the terminal input; that input
is classified, packed and cached by the traced producer. Exact certified
states, cache fields and absolute positions agree with the retained request
path. Every reservation remains live, including simultaneous old/new arrays.
The original input and seed are explicitly borrowed. Selected continuation,
factory and output lifetimes are not included in this prefix certificate. -/
set_option autoImplicit false
namespace Blotto.BinaryPRGCachedPrefixLifetime
open BinarySeedPreparationSpace BinaryPRGResourceWork BinaryPRGTerminalWork
open BinaryPRGResourceLifetime BinaryTerminalCacheLifetime

def CachedResult {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :=
  Σ state : BinaryResourcePair.Certified (resourceInput request rich).length,
    CacheData (terminalInput request rich state)

def reference {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) : Option (CachedResult request rich) × ℕ :=
  let resource := resourceWork request rich N bits
  (resource.1.1.map (fun state => ⟨state,erase (BinaryCachedTerminalPreparation.prepare
    (terminalInput request rich state))⟩),resource.1.2)

def runWithTrace {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) : (Option (CachedResult request rich) × ℕ) × Trace :=
  let resource := requestWithTrace request rich N bits
  match resource.1.1 with
  | none => ((none,resource.1.2),[.frames 2,.arrayAllocation 8] ++ under 2 resource.2)
  | some state =>
      let cached := cacheWithTrace (terminalInput request rich state)
      ((some ⟨state,cached.1⟩,resource.1.2),[.frames 2,.arrayAllocation 8] ++
        under 2 resource.2 ++ under 2 cached.2)

theorem runWithTrace_erases {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (runWithTrace request rich N bits).1 = reference request rich N bits := by
  unfold runWithTrace reference CachedResult
  dsimp only
  rw [← requestWithTrace_erases]
  cases hs : (requestWithTrace request rich N bits).1.1 <;>
    simp only [Option.map_none,Option.map_some,cacheWithTrace_erases]

noncomputable def bound {n : ℕ} (request : BinaryPRGRequest.Request n) (N : ℕ) : ℕ :=
  requestBound n request.source.originalInputWordWidth N + cacheBound request + 8

noncomputable def frames {n : ℕ} (request : BinaryPRGRequest.Request n) (N : ℕ) : ℕ :=
  N+4*n+2*request.source.originalInputWordWidth+30

theorem runWithTrace_bounds {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    listCells (runWithTrace request rich N bits).2+arraySlots (runWithTrace request rich N bits).2 ≤
      bound request N ∧ framePeak (runWithTrace request rich N bits).2 ≤ frames request N := by
  have hr := requestWithTrace_bound request rich N bits
  have hrf := framePeak_under 2 (requestWithTrace request rich N bits).2
  unfold runWithTrace
  dsimp only
  cases hs : (requestWithTrace request rich N bits).1.1 with
  | none =>
      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under]
      unfold bound frames
      exact ⟨by omega,by omega⟩
  | some state =>
      have hState : (resourceWork request rich N bits).1.1=some state := by
        rw [← requestWithTrace_erases]; exact hs
      have hc := reached_cache_bound request rich N bits state hState
      have hcf := framePeak_under 2 (cacheWithTrace (terminalInput request rich state)).2
      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under]
      unfold bound frames
      exact ⟨by omega,by omega⟩

theorem runWithTrace_position {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) : (runWithTrace request rich N bits).1.2 ≤ N := by
  rw [runWithTrace_erases]
  exact resourceWork_position request rich N bits

theorem all_prefix_heap {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (borrowedInputCells borrowedSeedCells steps : ℕ) :
    retainedHeap (borrowedInputCells+borrowedSeedCells) (runWithTrace request rich N bits).2 steps ≤
      borrowedInputCells+borrowedSeedCells+bound request N := by
  have hb := (runWithTrace_bounds request rich N bits).1
  have hl := listCells_take_le (runWithTrace request rich N bits).2 steps
  have ha := arraySlots_take_le (runWithTrace request rich N bits).2 steps
  unfold retainedHeap
  omega

theorem all_prefix_frames {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (steps : ℕ) :
    framePeak ((runWithTrace request rich N bits).2.take steps) ≤ frames request N :=
  (framePeak_take_le _ _).trans (runWithTrace_bounds request rich N bits).2

theorem parsed_all_prefix_polynomial (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n)×List Bool)
    (hParsed : (BinaryPRGAccuracyRulerRequest.read frame).1=some parsed) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision)
    (borrowedInputCells originalSeedLength steps : ℕ) :
    retainedHeap (borrowedInputCells+originalSeedLength)
      (runWithTrace parsed.1.2.request rich
        (RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 steps ≤
      borrowedInputCells+originalSeedLength+(2^56+2^60+8)*(frame.length+1)^5 := by
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hParsed
  have hS := BinaryPRGFrameCostJoin.read_source_width frame parsed hParsed
  have hc := (envelope_mono hn hS).trans (BinaryTerminalCacheLifetime.frameBound_polynomial frame.length)
  rw [← cacheBound_eq] at hc
  have h0 : 1 ≤ (frame.length+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have hFull := (runWithTrace_bounds parsed.1.2.request rich
    (RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).1
  -- Use the source-derived resource bound again, with the cache envelope.
  have hN := BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed hParsed
  have hChoice : RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision ≤ 8*frame.length+3025 := by
    have hle : RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision ≤
        RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.request.precision := by
      unfold RationalLottoResourceSystem.sampleBitBudget RationalLottoResourceSystem.innerBitBudget
      omega
    exact hle.trans hN
  have hR := (requestBound_mono hn hS hChoice).trans
    (BinaryPRGResourceLifetime.frameBound_polynomial frame.length)
  have hl := listCells_take_le
    (runWithTrace parsed.1.2.request rich
      (RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 steps
  have ha := arraySlots_take_le
    (runWithTrace parsed.1.2.request rich
      (RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 steps
  unfold retainedHeap bound at *
  unfold BinaryPRGResourceLifetime.polynomialBound at hR
  unfold BinaryTerminalCacheLifetime.polynomialBound at hc
  nlinarith only [hFull,hR,hc,hl,ha,h0]

end Blotto.BinaryPRGCachedPrefixLifetime
