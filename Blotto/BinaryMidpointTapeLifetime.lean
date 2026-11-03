import Blotto.BinaryDirectDyadicMidpoint
import Blotto.BinaryPRGHeapTraceUsage

/-! A midpoint follows actual Boolean tapes: reverse/scan/reverse trims its
odd numerator, and a tape-recursive builder writes the already canonical
power-of-two denominator. There is no numeric precision/countdown, generic
normalizer or work/storage replay in the traced data producer. -/
namespace Blotto.BinaryMidpointTapeLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def dropWithTrace : List Bool → List Bool × Trace
  | [] => ([],[.frames 1])
  | bits@(true::_) => (bits,[.frames 1])
  | false::rest => let later := dropWithTrace rest; (later.1,[.frames 1]++under 1 later.2)

def dropWithWork : List Bool → List Bool × ℕ
  | [] => ([],2)
  | bits@(true::_) => (bits,2)
  | false::rest => let later := dropWithWork rest; (later.1,later.2+4)

theorem drop_state (bits : List Bool) : (dropWithTrace bits).1 = BinaryBigEndian.trim bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [dropWithTrace,BinaryBigEndian.trim,ih]

theorem drop_work_state (bits : List Bool) : (dropWithWork bits).1 = (dropWithTrace bits).1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [dropWithWork,dropWithTrace,ih]

theorem drop_work (bits : List Bool) : (dropWithWork bits).2 ≤ 4*bits.length+2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [dropWithWork,List.length_cons] <;> omega

theorem drop_bounds (bits : List Bool) : listCells (dropWithTrace bits).2 = 0 ∧
    arraySlots (dropWithTrace bits).2 = 0 ∧ framePeak (dropWithTrace bits).2 ≤ bits.length+1 := by
  induction bits with
  | nil => simp [dropWithTrace,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      cases bit
      · have hu := framePeak_under 1 (dropWithTrace rest).2
        simp only [dropWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
          listCells_under,arraySlots_under,List.length_cons]
        exact ⟨by omega,by omega,by omega⟩
      · simp [dropWithTrace,listCells,arraySlots,framePeak]

def reverseWithWork : List Bool → List Bool → List Bool × ℕ
  | [],acc => (acc,2)
  | bit::rest,acc => let later := reverseWithWork rest (bit::acc); (later.1,later.2+4)

theorem reverse_work_state (bits acc : List Bool) : (reverseWithWork bits acc).1 = List.reverseAux bits acc := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih => exact ih (bit::acc)

theorem reverse_work (bits acc : List Bool) : (reverseWithWork bits acc).2 = 4*bits.length+2 := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih => simp only [reverseWithWork,ih,List.length_cons]; omega

def trimWithTrace (bits : List Bool) : List Bool × Trace :=
  let front := BinarySeedPreparationSpace.reverseWithTrace bits []
  let dropped := dropWithTrace front.1
  let back := BinarySeedPreparationSpace.reverseWithTrace dropped.1 []
  (back.1,[.frames 2,.arrayAllocation 8]++under 2 front.2++under 2 dropped.2++under 2 back.2)

def trimWithWork (bits : List Bool) : List Bool × ℕ :=
  let front := reverseWithWork bits []
  let dropped := dropWithWork front.1
  let back := reverseWithWork dropped.1 []
  (back.1,front.2+dropped.2+back.2+8)

theorem trim_state (bits : List Bool) : (trimWithTrace bits).1 = BinaryCanonicalMagnitude.trim bits := by
  simp only [trimWithTrace,reverseWithTrace_result,List.reverseAux_eq,List.append_nil,drop_state,BinaryCanonicalMagnitude.trim]

theorem trim_work_state (bits : List Bool) : (trimWithWork bits).1 = (trimWithTrace bits).1 := by
  simp only [trimWithWork,trimWithTrace,reverse_work_state,reverseWithTrace_result,
    List.reverseAux_eq,List.append_nil,drop_work_state]

theorem trim_bounds (bits : List Bool) : listCells (trimWithTrace bits).2+arraySlots (trimWithTrace bits).2 ≤ 2*bits.length+8 ∧
    framePeak (trimWithTrace bits).2 ≤ bits.length+3 := by
  let front := BinarySeedPreparationSpace.reverseWithTrace bits []
  let dropped := dropWithTrace front.1
  let back := BinarySeedPreparationSpace.reverseWithTrace dropped.1 []
  have hFront : front.1.length = bits.length := by simp only [front,reverseWithTrace_result,List.reverseAux_eq,List.append_nil,List.length_reverse]
  have hDrop : dropped.1.length ≤ bits.length := by
    have h := BinaryBigEndian.trim_length front.1
    simpa only [dropped,drop_state,hFront] using h
  have hc := reverseWithTrace_cells bits []
  have ha := reverseWithTrace_arrays bits []
  have hf := reverseWithTrace_frames bits []
  have hd := drop_bounds front.1
  have bc := reverseWithTrace_cells dropped.1 []
  have ba := reverseWithTrace_arrays dropped.1 []
  have bf := reverseWithTrace_frames dropped.1 []
  have hfu := framePeak_under 2 front.2
  have hdu := framePeak_under 2 dropped.2
  have hbu := framePeak_under 2 back.2
  change listCells front.2 = _ at hc
  change arraySlots front.2 = _ at ha
  change framePeak front.2 ≤ _ at hf
  change listCells dropped.2 = _ ∧ arraySlots dropped.2 = _ ∧ framePeak dropped.2 ≤ _ at hd
  change listCells back.2 = _ at bc
  change arraySlots back.2 = _ at ba
  change framePeak back.2 ≤ _ at bf
  rw [hFront] at hd
  change listCells ([.frames 2,.arrayAllocation 8]++under 2 front.2++under 2 dropped.2++under 2 back.2)+
      arraySlots ([.frames 2,.arrayAllocation 8]++under 2 front.2++under 2 dropped.2++under 2 back.2) ≤ _ ∧
    framePeak ([.frames 2,.arrayAllocation 8]++under 2 front.2++under 2 dropped.2++under 2 back.2) ≤ _
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem trim_work (bits : List Bool) : (trimWithWork bits).2 ≤ 12*bits.length+14 := by
  have hd := drop_work (reverseWithWork bits []).1
  have hf : (reverseWithWork bits []).1.length = bits.length := by simp only [reverse_work_state,List.reverseAux_eq,List.append_nil,List.length_reverse]
  have hDrop : (dropWithWork (reverseWithWork bits []).1).1.length ≤ bits.length := by
    rw [drop_work_state,drop_state]
    exact (BinaryBigEndian.trim_length _).trans_eq hf
  unfold trimWithWork
  dsimp only
  rw [reverse_work,reverse_work]
  rw [hf] at hd
  omega

def denominatorWithTrace : List Bool → List Bool × Trace
  | [] => ([true],[.frames 1,.listAllocation 1])
  | _::rest => let later := denominatorWithTrace rest; (false::later.1,[.frames 1,.listAllocation 1]++under 1 later.2)

def denominatorWithWork : List Bool → List Bool × ℕ
  | [] => ([true],2)
  | _::rest => let later := denominatorWithWork rest; (false::later.1,later.2+4)

theorem denominator_state (seed : List Bool) : (denominatorWithTrace seed).1 = seed.map (fun _ => false)++[true] := by
  induction seed with
  | nil => rfl
  | cons bit rest ih => simp only [denominatorWithTrace,List.map_cons,List.cons_append,ih]

theorem denominator_work_state (seed : List Bool) : (denominatorWithWork seed).1 = (denominatorWithTrace seed).1 := by
  induction seed with
  | nil => rfl
  | cons bit rest ih => simp only [denominatorWithWork,denominatorWithTrace,ih]

theorem denominator_work (seed : List Bool) : (denominatorWithWork seed).2 = 4*seed.length+2 := by
  induction seed with
  | nil => rfl
  | cons bit rest ih => simp only [denominatorWithWork,List.length_cons,ih]; omega

theorem denominator_bounds (seed : List Bool) : listCells (denominatorWithTrace seed).2 = seed.length+1 ∧
    arraySlots (denominatorWithTrace seed).2 = 0 ∧ framePeak (denominatorWithTrace seed).2 ≤ seed.length+1 := by
  induction seed with
  | nil => simp [denominatorWithTrace,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      have hu := framePeak_under 1 (denominatorWithTrace rest).2
      simp only [denominatorWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,List.length_cons]
      exact ⟨by omega,by omega,by omega⟩

theorem denominator_trim (seed : List Bool) :
    BinaryCanonicalMagnitude.trim (false::(denominatorWithTrace seed).1) = false::(denominatorWithTrace seed).1 := by
  rw [denominator_state]
  unfold BinaryCanonicalMagnitude.trim
  simp only [List.reverse_cons,List.reverse_append,List.reverse_singleton,List.singleton_append]
  simp [BinaryBigEndian.trim,List.dropWhile_cons]

def sampleWithTrace (seed : List Bool) : SignedWord × Trace :=
  let numerator := trimWithTrace (true::seed)
  let denominator := denominatorWithTrace seed
  (⟨false,numerator.1,false::denominator.1⟩,[.frames 2,.arrayAllocation 8,.listAllocation 2]++
    under 2 numerator.2++under 2 denominator.2)

def sampleWithWork (seed : List Bool) : SignedWord × ℕ :=
  let numerator := trimWithWork (true::seed)
  let denominator := denominatorWithWork seed
  (⟨false,numerator.1,false::denominator.1⟩,numerator.2+denominator.2+8)

theorem sample_state (seed : List Bool) : (sampleWithTrace seed).1 = BinaryDirectDyadicMidpoint.sample seed := by
  have hd := denominator_trim seed
  rw [denominator_state] at hd
  simp only [sampleWithTrace,trim_state,denominator_state,BinaryDirectDyadicMidpoint.sample,
    BinaryDirectDyadicMidpoint.raw,BinaryDirectDyadicMidpoint.denominator,BinaryRationalOpcode.trimWord,hd]

theorem sample_work_state (seed : List Bool) : (sampleWithWork seed).1 = (sampleWithTrace seed).1 := by
  simp only [sampleWithWork,sampleWithTrace,trim_work_state,denominator_work_state]

theorem sample_work (seed : List Bool) : (sampleWithWork seed).2 ≤ 20*(seed.length+2) := by
  have hn := trim_work (true::seed)
  have hd := denominator_work seed
  simp only [List.length_cons] at hn
  change _+_+8 ≤ _
  omega

theorem sample_bounds (seed : List Bool) : listCells (sampleWithTrace seed).2+arraySlots (sampleWithTrace seed).2 ≤ 19*seed.length+50 ∧
    framePeak (sampleWithTrace seed).2 ≤ 2*seed.length+8 := by
  have hn := trim_bounds (true::seed)
  have hd := denominator_bounds seed
  have hnu := framePeak_under 2 (trimWithTrace (true::seed)).2
  have hdu := framePeak_under 2 (denominatorWithTrace seed).2
  simp only [List.length_cons] at hn
  simp only [sampleWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem sample_contract (seed : List Bool) :
    BinaryRationalEncoding.CanonicalWord (sampleWithTrace seed).1 ∧ width (sampleWithTrace seed).1 ≤ seed.length+2 ∧
      0 < value (sampleWithTrace seed).1 ∧ value (sampleWithTrace seed).1 < 1 := by
  rw [sample_state]
  have h := BinaryDirectDyadicMidpoint.sample_contract seed
  exact ⟨h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

theorem all_prefix (seed : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (sampleWithTrace seed).2 steps ≤ borrowed+21*seed.length+58 ∧
      framePeak ((sampleWithTrace seed).2.take steps) ≤ 21*seed.length+58 := by
  have h := sample_bounds seed
  have hu : usage (sampleWithTrace seed).2 ≤ 21*seed.length+58 := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ hu borrowed steps

end Blotto.BinaryMidpointTapeLifetime
