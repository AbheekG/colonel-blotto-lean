import Blotto.GeneralPaperProfitCapacity

/-! Construct the balanced optimizer tree in battlefield order, padding
with actual zero-profit/zero-resource dummy fields. No allocation product is
enumerated. The split traversal is part of preparation; full work/space
prices and the source's native catalogue assembly remain separate joins.
-/
namespace Blotto.GeneralPaperProfitTreeBuild
open GeneralPaperBalancedProfitDP GeneralPaperProfitCapacity GeneralPaperBalancedProfitRetention
set_option autoImplicit false
set_option maxHeartbeats 3500000

abbrev WeightedField (K : ℕ) := Field K × ℕ

def dummy (K : ℕ) : WeightedField K := (FixedArrayTable.ofFn (fun _ => (0,0)),0)

def pad {K : ℕ} (height : ℕ) (fields : List (WeightedField K)) : List (WeightedField K) :=
  fields++List.replicate (2^height-fields.length) (dummy K)

def build {K : ℕ} : (height : ℕ) → List (WeightedField K) → Tree K height
  | 0,fields => .leaf (fields.headD (dummy K)).1
  | height+1,fields => .node (build height (fields.take (2^height))) (build height (fields.drop (2^height)))

def fields {K : ℕ} : {height : ℕ} → Tree K height → List (Field K)
  | _,.leaf field => [field]
  | _,.node left right => fields left++fields right

theorem pad_length {K : ℕ} (height : ℕ) (input : List (WeightedField K)) (hLen : input.length≤2^height) :
    (pad height input).length=2^height := by
  simp only [pad,List.length_append,List.length_replicate]
  omega

theorem pad_weight {K : ℕ} (height : ℕ) (input : List (WeightedField K)) :
    ((pad height input).map Prod.snd).sum=(input.map Prod.snd).sum := by
  simp [pad,List.map_append,List.map_replicate,dummy]

theorem take_length {K : ℕ} (height : ℕ) (input : List (WeightedField K)) (hLen : input.length=2^(height+1)) :
    (input.take (2^height)).length=2^height := by
  simp only [List.length_take,hLen,pow_succ]
  omega

theorem drop_length {K : ℕ} (height : ℕ) (input : List (WeightedField K)) (hLen : input.length=2^(height+1)) :
    (input.drop (2^height)).length=2^height := by
  simp only [List.length_drop,hLen,pow_succ]
  omega

theorem fields_build {K : ℕ} (height : ℕ) (input : List (WeightedField K)) (hLen : input.length=2^height) :
    fields (build height input)=input.map Prod.fst := by
  induction height generalizing input with
  | zero =>
    cases input with
    | nil => simp only [List.length_nil,pow_zero] at hLen; omega
    | cons field rest =>
      have hr : rest=[] := by have he := hLen; simp only [List.length_cons,pow_zero] at he; exact List.length_eq_zero_iff.mp (by omega)
      subst rest
      rfl
  | succ height ih =>
    rw [build,fields,ih (input.take (2^height)) (take_length height input hLen),
      ih (input.drop (2^height)) (drop_length height input hLen),←List.map_append,List.take_append_drop]

theorem capacity_build {K : ℕ} (D height : ℕ) (input : List (WeightedField K)) (hLen : input.length=2^height)
    (hFields : ∀ field∈input, Capacity D (.leaf field.1) field.2) :
    Capacity D (build height input) (input.map Prod.snd).sum := by
  induction height generalizing input with
  | zero =>
    cases input with
    | nil => simp only [List.length_nil,pow_zero] at hLen; omega
    | cons field rest =>
      have hr : rest=[] := by have he := hLen; simp only [List.length_cons,pow_zero] at he; exact List.length_eq_zero_iff.mp (by omega)
      subst rest
      simpa only [build,List.headD_cons,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hFields field (List.mem_cons_self)
  | succ height ih =>
    have hl := ih (input.take (2^height)) (take_length height input hLen)
      (fun field hf => hFields field (List.mem_of_mem_take hf))
    have hr := ih (input.drop (2^height)) (drop_length height input hLen)
      (fun field hf => hFields field (List.mem_of_mem_drop hf))
    refine ⟨_,_,hl,hr,?_⟩
    rw [←List.sum_append,←List.map_append,List.take_append_drop]

theorem dummy_capacity (K D : ℕ) : Capacity D (.leaf (dummy K).1) (dummy K).2 := by
  intro a
  simp only [dummy,FixedArrayTable.read_ofFn,Nat.mul_zero,le_refl]

theorem padded_capacity {K : ℕ} (D height : ℕ) (input : List (WeightedField K)) (hLen : input.length≤2^height)
    (hFields : ∀ field∈input, Capacity D (.leaf field.1) field.2) :
    Capacity D (build height (pad height input)) (input.map Prod.snd).sum := by
  have hf : ∀ field∈pad height input, Capacity D (.leaf field.1) field.2 := by
    intro field hField
    rcases List.mem_append.mp hField with h|h
    · exact hFields field h
    · have he : field=dummy K := List.mem_replicate.mp h |>.2
      subst field
      exact dummy_capacity K D
  have he := capacity_build D height (pad height input) (pad_length height input hLen) hf
  rw [pad_weight] at he
  exact he

theorem fields_padded {K : ℕ} (height : ℕ) (input : List (WeightedField K)) (hLen : input.length≤2^height) :
    fields (build height (pad height input))=(input.map Prod.fst)++
      List.replicate (2^height-input.length) (dummy K).1 := by
  rw [fields_build height _ (pad_length height input hLen)]
  simp only [pad,List.map_append,List.map_replicate]

end Blotto.GeneralPaperProfitTreeBuild
