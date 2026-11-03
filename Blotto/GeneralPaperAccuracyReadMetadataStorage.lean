import Blotto.GeneralPaperBinaryAccuracyConstructionStorage

/-! Literal natural-valued metadata traversals of the actual accuracy
reader. List length, delimiter visits and consumed-copy counters each retain
all reached scalar/partial-return fields. All caps are erased length bounds;
no observer or new pass is executed by the native reader. -/
namespace Blotto.GeneralPaperAccuracyReadMetadataStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBooleanRulerWorkStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem single_bound (W C a : ℕ) (ha : a≤C+64) : node W [a]≤2*budget W C :=
  node_bound W C [a] (by norm_num) (fun z hz => by simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;simpa only [hz] using ha)

def lengthMeta (W : ℕ) : List Bool → ℕ
  | [] => node W [0]
  | _::rest => node W [rest.length,1,rest.length+1]+lengthMeta W rest

def findMeta (W : ℕ) : List Bool → ℕ
  | [] => node W [1]
  | true::_ => node W [1]
  | false::rest => node W [UnaryPayload.findSteps rest,1,UnaryPayload.findSteps rest+1]+findMeta W rest

def consumeMeta (W : ℕ) : List Bool → List Bool → ℕ
  | [],_ => node W [0]
  | true::_,_ => node W [0]
  | false::_,[] => node W [0]
  | false::ruler,_::payload =>
    node W [UnaryPayload.consumeCopies ruler payload,1,UnaryPayload.consumeCopies ruler payload+1]+consumeMeta W ruler payload

def stepsControls (frame : List Bool) : List ℕ :=
  [UnaryPayload.findSteps frame,UnaryPayload.readSteps frame]++match UnaryPayload.findPayload frame with
  | none => []
  | some payload => [UnaryPayload.consumeCopies frame payload,UnaryPayload.consumeCopies frame payload+1,1]

def stepsMeta (W : ℕ) (frame : List Bool) : ℕ :=
  findMeta W frame+node W (stepsControls frame)+match UnaryPayload.findPayload frame with
  | none => 0
  | some payload => consumeMeta W frame payload

def lengthProfile (W E : ℕ) : ℕ := 2*(E+1)*budget W E

def stepsProfile (W E : ℕ) : ℕ := (4*(E+1)+2)*budget W (E+1)

theorem length_bound (W C : ℕ) (bits : List Bool) (hc : bits.length≤C) :
    lengthMeta W bits≤2*(bits.length+1)*budget W C := by
  induction bits with
  | nil => simpa only [lengthMeta,List.length_nil,Nat.zero_add,Nat.mul_one] using single_bound W C 0 (by omega)
  | cons b rest ih =>
    have hi := ih (by simp only [List.length_cons] at hc;omega)
    have hn := node_bound W C [rest.length,1,rest.length+1] (by norm_num) (by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl <;> simp only [List.length_cons] at hc <;> omega)
    change node W _+lengthMeta W rest≤_
    simp only [List.length_cons]
    nlinarith only [hn,hi]

theorem find_bound (W C : ℕ) (frame : List Bool) (hc : frame.length≤C) :
    findMeta W frame≤2*UnaryPayload.findSteps frame*budget W (C+1) := by
  induction frame with
  | nil => simpa only [findMeta,UnaryPayload.findSteps,Nat.mul_one] using single_bound W (C+1) 1 (by omega)
  | cons b rest ih => cases b with
    | true => simpa only [findMeta,UnaryPayload.findSteps,Nat.mul_one] using single_bound W (C+1) 1 (by omega)
    | false =>
      have hi := ih (by simp only [List.length_cons] at hc;omega)
      have hw := UnaryPayload.findSteps_bound rest
      have hn := node_bound W (C+1) [UnaryPayload.findSteps rest,1,UnaryPayload.findSteps rest+1] (by norm_num) (by
        intro z hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl <;> simp only [List.length_cons] at hc <;> omega)
      change node W _+findMeta W rest≤2*(UnaryPayload.findSteps rest+1)*budget W (C+1)
      nlinarith only [hn,hi]

theorem consume_bound (W C : ℕ) (ruler payload : List Bool) (hc : ruler.length≤C) :
    consumeMeta W ruler payload≤2*(UnaryPayload.consumeCopies ruler payload+1)*budget W (C+1) := by
  induction ruler generalizing payload with
  | nil => simpa only [consumeMeta,UnaryPayload.consumeCopies,Nat.zero_add,Nat.mul_one] using single_bound W (C+1) 0 (by omega)
  | cons b rest ih => cases b with
    | true => simpa only [consumeMeta,UnaryPayload.consumeCopies,Nat.zero_add,Nat.mul_one] using single_bound W (C+1) 0 (by omega)
    | false => cases payload with
      | nil => simpa only [consumeMeta,UnaryPayload.consumeCopies,Nat.zero_add,Nat.mul_one] using single_bound W (C+1) 0 (by omega)
      | cons bit tail =>
        have hi := ih tail (by simp only [List.length_cons] at hc;omega)
        have hw := UnaryPayload.consumeCopies_ruler_bound rest tail
        have hn := node_bound W (C+1) [UnaryPayload.consumeCopies rest tail,1,UnaryPayload.consumeCopies rest tail+1] (by norm_num) (by
          intro z hz
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with rfl|rfl|rfl <;> simp only [List.length_cons] at hc <;> omega)
        change node W _+consumeMeta W rest tail≤2*(UnaryPayload.consumeCopies rest tail+1+1)*budget W (C+1)
        nlinarith only [hn,hi]

theorem steps_bound (W C : ℕ) (frame : List Bool) (hc : frame.length≤C) :
    stepsMeta W frame≤(4*(frame.length+1)+2)*budget W (C+1) := by
  have hf := find_bound W C frame hc
  have hFind := UnaryPayload.findSteps_bound frame
  have hRead := UnaryPayload.readSteps_bound frame
  have hn := node_bound W (C+1) (stepsControls frame) (by
    unfold stepsControls
    split <;> norm_num) (by
    intro z hz
    unfold stepsControls at hz
    split at hz
    · simp only [List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl <;> omega
    · rename_i payload hp
      have hCopy := UnaryPayload.consumeCopies_ruler_bound frame payload
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with (rfl|rfl)|(rfl|rfl|rfl) <;> omega)
  unfold stepsMeta
  cases hp:UnaryPayload.findPayload frame with
  | none => dsimp only;nlinarith only [hf,hn,hFind,Nat.zero_le (budget W (C+1))]
  | some payload =>
    have hCopy := UnaryPayload.consumeCopies_ruler_bound frame payload
    have hm := consume_bound W C frame payload hc
    dsimp only
    nlinarith only [hf,hn,hm,hFind,hCopy,Nat.zero_le (budget W (C+1))]

@[fun_prop]
theorem length_scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => lengthProfile W E) := by
  unfold lengthProfile budget
  fun_prop

@[fun_prop]
theorem steps_scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => stepsProfile W E) := by
  unfold stepsProfile budget
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem length_rate (W E : Input → ℕ) (hW : Tight W) (hE : Small E) : Linear (fun x => lengthProfile (W x) (E x)) E := by
  have hw := of_tight hW
  have hp := poly_tight W hW
  unfold lengthProfile budget natBits
  fun_prop

theorem steps_rate (W E : Input → ℕ) (hW : Tight W) (hE : Small E) : Linear (fun x => stepsProfile (W x) (E x)) E := by
  have hw := of_tight hW
  have hp := poly_tight W hW
  unfold stepsProfile budget natBits
  fun_prop

end Blotto.GeneralPaperAccuracyReadMetadataStorage
