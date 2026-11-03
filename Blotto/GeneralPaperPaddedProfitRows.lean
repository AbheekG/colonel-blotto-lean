import Blotto.GeneralPaperRowPrefix

/-! Actual zero dummy fields disappear from resource and profit sums when
trimming a decoded balanced tuple to its original field count. Conversely
any full tuple of option indices realizes a state-independent exact cost and
profit in the actual tree; this is a proof witness, not tuple enumeration.
-/
namespace Blotto.GeneralPaperPaddedProfitRows
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitTreeBuild GeneralPaperOrderedProfitRows
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

theorem dummy_resource_sum {K : ℕ} (n : ℕ) (labels : List (Fin K)) :
    (resources (List.replicate n (dummy R K).1) labels).sum=0 := by
  induction n generalizing labels with
  | zero => simp [resources]
  | succ n ih =>
    cases labels with
    | nil => simp [resources]
    | cons a rest =>
      simpa only [resources,List.replicate_succ,List.zip_cons_cons,List.map_cons,List.sum_cons,
        dummy,FixedArrayTable.read_ofFn,zero_add] using ih rest

theorem dummy_profit_sum {K : ℕ} (n : ℕ) (labels : List (Fin K)) :
    (profits (List.replicate n (dummy R K).1) labels).sum=0 := by
  induction n generalizing labels with
  | zero => simp [profits]
  | succ n ih =>
    cases labels with
    | nil => simp [profits]
    | cons a rest =>
      simpa only [profits,List.replicate_succ,List.zip_cons_cons,List.map_cons,List.sum_cons,
        dummy,FixedArrayTable.read_ofFn,Nat.zero_add] using ih rest

theorem padded_sums {K : ℕ} (height : ℕ) (input : List (WeightedField R K))
    (hLen : input.length≤2^height) (labels : List (Fin K)) (hLabels : labels.length=2^height) :
    (resources (fields (build height (pad height input))) labels).sum=
        (resources (input.map Prod.fst) (labels.take input.length)).sum ∧
      (profits (fields (build height (pad height input))) labels).sum=
        (profits (input.map Prod.fst) (labels.take input.length)).sum := by
  have hTake : (input.map Prod.fst).length=(labels.take input.length).length := by
    simp only [List.length_map,List.length_take,hLabels,Nat.min_eq_left hLen]
  have hR := resources_append (input.map Prod.fst) (List.replicate (2^height-input.length) (dummy R K).1)
    (labels.take input.length) (labels.drop input.length) hTake
  have hP := profits_append (input.map Prod.fst) (List.replicate (2^height-input.length) (dummy R K).1)
    (labels.take input.length) (labels.drop input.length) hTake
  rw [List.take_append_drop] at hR hP
  rw [fields_padded height input hLen,hR,hP]
  simp only [List.sum_append,dummy_resource_sum,dummy_profit_sum,add_zero,Nat.add_zero,and_self]

theorem realizes_trim {K : ℕ} (height : ℕ) (input : List (WeightedField R K)) (hLen : input.length≤2^height)
    (labels : List (Fin K)) (cost : R) (P : ℕ) (hRealizes : Realizes (build height (pad height input)) labels cost P) :
    (resources (input.map Prod.fst) (labels.take input.length)).sum=cost ∧
      (profits (input.map Prod.fst) (labels.take input.length)).sum=P := by
  obtain ⟨hResource,hProfit⟩ := realizes_sums _ labels cost P hRealizes
  obtain ⟨hR,hP⟩ := padded_sums height input hLen labels (realizes_length _ labels cost P hRealizes)
  exact ⟨hR.symm.trans hResource,hP.symm.trans hProfit⟩

theorem realizes_complete {K h : ℕ} (tree : Tree R K h) (labels : List (Fin K)) (hLabels : labels.length=2^h) :
    ∃ cost P, Realizes tree labels cost P := by
  induction tree generalizing labels with
  | leaf field =>
    cases labels with
    | nil => simp only [List.length_nil,pow_zero] at hLabels; omega
    | cons a rest =>
      have hr : rest=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_cons,pow_zero] using Nat.succ.inj hLabels)
      subst rest
      exact ⟨(field.read a).2,(field.read a).1,a,rfl,rfl,rfl⟩
  | @node h left right ihl ihr =>
    have hl : (labels.take (2^h)).length=2^h := by simp only [List.length_take,hLabels,pow_succ]; omega
    have hr : (labels.drop (2^h)).length=2^h := by simp only [List.length_drop,hLabels,pow_succ]; omega
    obtain ⟨lc,lp,hlr⟩ := ihl (labels.take (2^h)) hl
    obtain ⟨rc,rp,hrr⟩ := ihr (labels.drop (2^h)) hr
    exact ⟨lc+rc,lp+rp,_,lc,lp,_,rc,rp,hlr,hrr,(List.take_append_drop _ _).symm,rfl,rfl⟩

end Blotto.GeneralPaperPaddedProfitRows
