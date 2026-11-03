import Blotto.GeneralPaperCommonLatticeMinimumBits
import Blotto.GeneralPaperEncodedBasisStorage

/-! Actual exact-score witnesses, including the complete retained label
list and its links. Counting each list separately is an ownership upper
bound even when native candidates share tails. Bounds cover candidates and
partial recursive scans, not only accepted or finally selected witnesses. -/
namespace Blotto.GeneralPaperScoreSelectionStorage
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def labelBits {K : ℕ} (l : Fin K) : ℕ := natBits l.val

theorem label_bound {K : ℕ} (l : Fin K) : labelBits l≤1+binaryWordWidth K :=
  Nat.add_le_add_left (binaryWordWidth_mono l.isLt.le) 1

def selectionFootprint {K : ℕ} (W : ℕ) (a : Selection K) : ℕ :=
  rationalWordWidth a.cost+listFootprint W labelBits a.labels+32*W

def selectionProfile (W K r P : ℕ) : ℕ := P+r*(1+binaryWordWidth K+2*W)+64*W

def optionFootprint {K : ℕ} (W : ℕ) : Option (Selection K) → ℕ
  | none => 1
  | some a => 1+selectionFootprint W a+8*W

def optionProfile (W K r P : ℕ) : ℕ := 1+selectionProfile W K r P+8*W

def Bounded {K : ℕ} (r P : ℕ) (a : Option (Selection K)) : Prop :=
  ∀ chosen,a=some chosen → chosen.labels.length≤r ∧ rationalWordWidth chosen.cost≤P

theorem bounded_mono {K r r' P P' : ℕ} {a : Option (Selection K)} (h : Bounded r P a)
    (hr : r≤r') (hp : P≤P') : Bounded r' P' a := fun chosen hc =>
  ⟨(h chosen hc).1.trans hr,(h chosen hc).2.trans hp⟩

theorem selection_bound {K : ℕ} (W r P : ℕ) (a : Selection K)
    (hr : a.labels.length≤r) (hp : rationalWordWidth a.cost≤P) :
    selectionFootprint W a≤selectionProfile W K r P := by
  have hl := list_bound W (1+binaryWordWidth K) labelBits a.labels (fun l _ => label_bound l)
  have hm := Nat.mul_le_mul_right (1+binaryWordWidth K+2*W) hr
  unfold selectionFootprint selectionProfile
  omega

theorem option_bound {K : ℕ} (W r P : ℕ) (a : Option (Selection K)) (h : Bounded r P a) :
    optionFootprint W a≤optionProfile W K r P := by
  cases a with
  | none =>
    change 1≤1+selectionProfile W K r P+8*W
    omega
  | some a =>
    have ha := selection_bound W r P a (h a rfl).1 (h a rfl).2
    change 1+selectionFootprint W a+8*W≤1+selectionProfile W K r P+8*W
    omega

theorem pick_bounded {K r P : ℕ} (a b : Option (Selection K)) (ha : Bounded r P a) (hb : Bounded r P b) :
    Bounded r P (pick a b) := by
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      change Bounded r P (if a.cost≤b.cost then some a else some b)
      split_ifs
      · exact ha
      · exact hb

theorem scan_bounded {α : Type*} {K r P : ℕ} (evaluate : α → Option (Selection K))
    (xs : List α) (h : ∀ a∈xs,Bounded r P (evaluate a)) : Bounded r P (scan evaluate xs) := by
  induction xs with
  | nil => intro chosen hc; cases hc
  | cons a rest ih =>
    exact pick_bounded _ _ (h a List.mem_cons_self) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem native_scan_bounded {α : Type*} {K r P : ℕ} (model : RationalCostModel) (W : ℕ)
    (evaluate : α → Option (Selection K)×ℕ) (xs : List α)
    (h : ∀ a∈xs,Bounded r P (evaluate a).1) :
    Bounded r P (GeneralPaperScoreBitPrimitive.scanRun model W evaluate xs).1 := by
  rw [GeneralPaperScoreBitPrimitive.scan_data]
  exact scan_bounded _ xs h

theorem run_bounded {K : ℕ} (S A r : ℕ) (fields : List (Field K)) (hFields : CostHeight fields A)
    (hLen : fields.length≤r) (s : Fin (S+1)) :
    Bounded r (GeneralPaperScoreBitPrimitive.resourceWidth A r) ((run S fields).read s) := by
  intro chosen hc
  have hb := run_best S fields s
  rw [hc] at hb
  exact ⟨(fits_length fields s.val chosen hb.1).le.trans hLen,
    (run_some_width S fields A hFields s chosen hc).trans (GeneralPaperScoreBitPrimitive.resourceWidth_mono A hLen)⟩

theorem candidate_bounded {K S : ℕ} (model : RationalCostModel) (W A r : ℕ)
    (field : Field K) (rest : List (Field K)) (hFields : CostHeight (field::rest) A)
    (hLen : rest.length+1≤r) (s : Fin (S+1)) (l : Fin K) :
    Bounded r (GeneralPaperScoreBitPrimitive.resourceWidth A r)
      (GeneralPaperScoreBitPrimitive.candidateRun model W field (run S rest) s l).1 := by
  rw [GeneralPaperScoreBitPrimitive.candidate_data]
  intro chosen hc
  have hf := candidate_some_fits field rest s l chosen hc
  have hL := fits_length (field::rest) s.val chosen hf
  exact ⟨hL.le.trans hLen,(rationalWordWidth_of_height (candidate_some_height field rest A hFields s l chosen hc)).trans
    (GeneralPaperScoreBitPrimitive.resourceWidth_mono A hLen)⟩

theorem lattice_run_bounded {K : ℕ} (D M r S : ℕ) (hD : 0<D) (fields : List (Field K))
    (hf : ∀ f∈fields,∀ l,GeneralPaperRayRationalBound.Bounded D M (f.read l).2)
    (hLen : fields.length≤r) (s : Fin (S+1)) :
    Bounded r (GeneralPaperCommonLatticeDPBits.width D M r) ((run S fields).read s) := by
  intro chosen hc
  have hb := run_best S fields s
  rw [hc] at hb
  exact ⟨(fits_length fields s.val chosen hb.1).le.trans hLen,
    GeneralPaperCommonLatticeDPBits.run_width D M r S hD fields hf hLen s chosen hc⟩

@[fun_prop]
theorem selection_profile_scale (K r P : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => selectionProfile W K r P) := by
  unfold selectionProfile
  fun_prop

@[fun_prop]
theorem option_profile_scale (K r P : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => optionProfile W K r P) := by
  unfold optionProfile
  fun_prop

end Blotto.GeneralPaperScoreSelectionStorage
