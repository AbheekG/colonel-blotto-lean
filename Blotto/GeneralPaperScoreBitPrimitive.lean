import Blotto.GeneralPaperScoreStoredBits
import Blotto.RationalExpressionBitCost

/-! Bit prices for the actual score-DP addition and minimum selection.
Rational primitives use the actual operand widths in the paper's Rat model.
W is the source reference/control word; the caller must establish its index
and stored-score capacity. No predecessor-list traversal is performed by a
candidate or minimum: an extension writes one label and one tail reference.
-/
namespace Blotto.GeneralPaperScoreBitPrimitive
open GeneralPaperMinimum GeneralPaperExactScoreDP
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Width {K : ℕ} (a : Option (Selection K)) (H : ℕ) : Prop :=
  ∀ chosen,a=some chosen → rationalWordWidth chosen.cost≤H

def additionPrice (model : RationalCostModel) (a b : ℚ) : ℕ :=
  model.rat (RationalExpression.pairWidth a b)+rationalWordWidth (a+b)

theorem additionPrice_le (model : RationalCostModel) (a b : ℚ) (H : ℕ)
    (ha : rationalWordWidth a≤H) (hb : rationalWordWidth b≤H) (hc : rationalWordWidth (a+b)≤H) :
    additionPrice model a b≤2*model.rat H := by
  have hp := model.monotone (max_le ha hb)
  have ho := hc.trans (model.word_le H)
  unfold additionPrice RationalExpression.pairWidth at *
  omega

def pickRun {K : ℕ} (model : RationalCostModel) (W : ℕ) (a b : Option (Selection K)) : Option (Selection K) × ℕ :=
  match a,b with
  | some x,some y => (if x.cost≤y.cost then some x else some y,
      8*W+model.rat (RationalExpression.pairWidth x.cost y.cost))
  | _,_ => (pick a b,8*W)

theorem pick_data {K : ℕ} (model : RationalCostModel) (W : ℕ) (a b : Option (Selection K)) :
    (pickRun model W a b).1=pick a b := by
  cases a <;> cases b <;> rfl

theorem pick_width {K : ℕ} (a b : Option (Selection K)) (H : ℕ) (ha : Width a H) (hb : Width b H) :
    Width (pick a b) H := by
  cases a with
  | none => exact hb
  | some x =>
    cases b with
    | none => exact ha
    | some y =>
      simp only [pick]
      split
      · exact ha
      · exact hb

theorem pick_work {K : ℕ} (model : RationalCostModel) (W H : ℕ) (a b : Option (Selection K))
    (ha : Width a H) (hb : Width b H) : (pickRun model W a b).2≤8*W+model.rat H := by
  cases a with
  | none => simp only [pickRun]; omega
  | some x =>
    cases b with
    | none => simp only [pickRun]; omega
    | some y =>
      have hp := model.monotone (max_le (ha x rfl) (hb y rfl))
      change 8*W+model.rat (RationalExpression.pairWidth x.cost y.cost)≤_
      exact Nat.add_le_add_left hp _

def scanRun {α : Type*} {K : ℕ} (model : RationalCostModel) (W : ℕ)
    (evaluate : α → Option (Selection K) × ℕ) : List α → Option (Selection K) × ℕ
  | [] => (none,2*W)
  | a::rest =>
      let current := evaluate a
      let later := scanRun model W evaluate rest
      let selected := pickRun model W current.1 later.1
      (selected.1,current.2+later.2+selected.2+4*W)

theorem scan_data {α : Type*} {K : ℕ} (model : RationalCostModel) (W : ℕ)
    (evaluate : α → Option (Selection K) × ℕ) (xs : List α) :
    (scanRun model W evaluate xs).1=scan (fun a => (evaluate a).1) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [scanRun,pick_data,scan,ih]

theorem scan_width {α : Type*} {K : ℕ} (model : RationalCostModel) (W H : ℕ)
    (evaluate : α → Option (Selection K) × ℕ) (xs : List α)
    (h : ∀ a ∈ xs,Width (evaluate a).1 H) : Width (scanRun model W evaluate xs).1 H := by
  induction xs with
  | nil => intro chosen hc; cases hc
  | cons a rest ih =>
    simp only [scanRun,pick_data]
    exact pick_width _ _ H (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem scan_work {α : Type*} {K : ℕ} (model : RationalCostModel) (W H E : ℕ)
    (evaluate : α → Option (Selection K) × ℕ) (xs : List α)
    (hWidth : ∀ a ∈ xs,Width (evaluate a).1 H) (hWork : ∀ a ∈ xs,(evaluate a).2≤E) :
    (scanRun model W evaluate xs).2≤(E+12*W+model.rat H)*xs.length+2*W := by
  induction xs with
  | nil => simp only [scanRun,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons a rest ih =>
    have hr := ih (fun b hb => hWidth b (by simp [hb])) (fun b hb => hWork b (by simp [hb]))
    have hw := scan_width model W H evaluate rest (fun b hb => hWidth b (by simp [hb]))
    have hp := pick_work model W H (evaluate a).1 (scanRun model W evaluate rest).1 (hWidth a (by simp)) hw
    have ha := hWork a (by simp)
    change (evaluate a).2+(scanRun model W evaluate rest).2+
      (pickRun model W (evaluate a).1 (scanRun model W evaluate rest).1).2+4*W≤_
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def candidateRun {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K)
    (previous : FixedArrayTable (S+1) (Option (Selection K))) (s : Fin (S+1)) (l : Fin K) :
    Option (Selection K) × ℕ :=
  let data := field.read l
  if h : data.1≤s.val then
    match previous.read ⟨s.val-data.1,by omega⟩ with
    | none => (none,64*W)
    | some tail => (some (extend l data.2 tail),64*W+additionPrice model data.2 tail.cost)
  else (none,64*W)

theorem candidate_data {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K)
    (previous : FixedArrayTable (S+1) (Option (Selection K))) (s : Fin (S+1)) (l : Fin K) :
    (candidateRun model W field previous s l).1=candidate field previous s l := by
  unfold candidateRun candidate
  dsimp only
  split
  · rename_i hScore
    cases he : previous.read ⟨s.val-(field.read l).1,by omega⟩ <;>
      simp only [he,Option.map_none,Option.map_some]
  · rfl

def resourceWidth (A r : ℕ) : ℕ := 1+2*((A+1)*r+1)

theorem resourceWidth_mono (A : ℕ) {r t : ℕ} (h : r≤t) : resourceWidth A r≤resourceWidth A t := by
  have hm := Nat.mul_le_mul_left (A+1) h
  unfold resourceWidth
  omega

theorem inputWidth_le (A r : ℕ) : 1+2*A≤resourceWidth A (r+1) := by
  have hm := Nat.mul_le_mul_left (A+1) (show 1≤r+1 by omega)
  unfold resourceWidth
  omega

theorem candidate_width {K S : ℕ} (model : RationalCostModel) (W A : ℕ) (field : Field K) (rest : List (Field K))
    (hFields : CostHeight (field::rest) A) (s : Fin (S+1)) (l : Fin K) :
    Width (candidateRun model W field (run S rest) s l).1 (resourceWidth A (rest.length+1)) := by
  rw [candidate_data]
  intro chosen hc
  exact rationalWordWidth_of_height (candidate_some_height field rest A hFields s l chosen hc)

theorem candidate_work {K S : ℕ} (model : RationalCostModel) (W A : ℕ) (field : Field K) (rest : List (Field K))
    (hFields : CostHeight (field::rest) A) (s : Fin (S+1)) (l : Fin K) :
    (candidateRun model W field (run S rest) s l).2≤64*W+2*model.rat (resourceWidth A (rest.length+1)) := by
  have hHead := hFields field (by simp) l
  have hRest : CostHeight rest A := fun f hf => hFields f (by simp [hf])
  unfold candidateRun
  dsimp only
  split
  · rename_i hScore
    let index : Fin (S+1) := ⟨s.val-(field.read l).1,by omega⟩
    change (match (run S rest).read index with
      | none => (none,64*W)
      | some tail => (some (extend l (field.read l).2 tail),64*W+additionPrice model (field.read l).2 tail.cost)).2≤_
    cases he : (run S rest).read index with
    | none => simp only [he]; omega
    | some tail =>
      have ht := run_some_width S rest A hRest index tail he
      have ht' : rationalWordWidth tail.cost≤resourceWidth A (rest.length+1) :=
        ht.trans (resourceWidth_mono A (by omega))
      have hf := (rationalWordWidth_of_height hHead).trans (inputWidth_le A rest.length)
      have hc : candidate field (run S rest) s l=some (extend l (field.read l).2 tail) := by
        simp only [candidate,dite_eq_left hScore]
        change Option.map (extend l (field.read l).2) ((run S rest).read index)=_
        rw [he]
        rfl
      have ho := rationalWordWidth_of_height (candidate_some_height field rest A hFields s l _ hc)
      have hp := additionPrice_le model (field.read l).2 tail.cost (resourceWidth A (rest.length+1)) hf ht' ho
      simp only [he]
      exact Nat.add_le_add_left hp _
  · omega

end Blotto.GeneralPaperScoreBitPrimitive
