import Blotto.GeneralPaperScoreTableStorage

/-! Native recursive minimum scans with independent scan cardinality J and
witness alphabet K. Suspended/later/selected witnesses and all actual native
work metadata are retained. Primitive scratch remains a separate maximum.
These erased observers cover high-score scans as well as label scans. -/
namespace Blotto.GeneralPaperIndexedMinimumStorage
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreSelectionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def trace {J K : ℕ} (model : RationalCostModel) (W : ℕ)
    (evaluate : Fin J → Option (Selection K)×ℕ) : List (Fin J) → ℕ
  | [] => fields W [0,2*W]+128*W+1
  | l::rest =>
    let current := evaluate l
    let later := GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest
    let selected := GeneralPaperScoreBitPrimitive.pickRun model W current.1 later.1
    optionFootprint W current.1+optionFootprint W later.1+optionFootprint W selected.1+
      fields W [(l::rest).length,l.val,current.2,later.2,selected.2,
        (GeneralPaperScoreBitPrimitive.scanRun model W evaluate (l::rest)).2]+224*W+trace model W evaluate rest

def primitivePeak {J K : ℕ} (model : RationalCostModel) (W : ℕ)
    (evaluate : Fin J → Option (Selection K)×ℕ) : List (Fin J) → ℕ
  | [] => 0
  | l::rest => max (evaluate l).2 (max (primitivePeak model W evaluate rest)
      (GeneralPaperScoreBitPrimitive.pickRun model W (evaluate l).1
        (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1).2)

def workCap (W J E Q : ℕ) : ℕ := J+1+(E+12*W+Q)*J+2*W+(8*W+Q)+E

def frameProfile (W J K r P E Q : ℕ) : ℕ :=
  3*optionProfile W K r P+6*(natBits (workCap W J E Q)+W)+256*W+1

def profile (W J K r P E Q : ℕ) : ℕ := (J+1)*frameProfile W J K r P E Q+E+8*W+Q

theorem width_of_bounded {K r P : ℕ} {a : Option (Selection K)} (h : Bounded r P a) :
    GeneralPaperScoreBitPrimitive.Width a P := fun chosen hc => (h chosen hc).2

theorem scan_work_cap {J K r P : ℕ} (model : RationalCostModel) (W E : ℕ)
    (evaluate : Fin J → Option (Selection K)×ℕ) (xs : List (Fin J)) (hLen : xs.length≤J)
    (hb : ∀ l∈xs,Bounded r P (evaluate l).1) (hw : ∀ l∈xs,(evaluate l).2≤E) :
    (GeneralPaperScoreBitPrimitive.scanRun model W evaluate xs).2≤workCap W J E (model.rat P) := by
  have hs := GeneralPaperScoreBitPrimitive.scan_work model W P E evaluate xs
    (fun l hl => width_of_bounded (hb l hl)) hw
  have hm := Nat.mul_le_mul_left (E+12*W+model.rat P) hLen
  unfold workCap
  omega

theorem trace_bound {J K r P : ℕ} (model : RationalCostModel) (W E : ℕ)
    (evaluate : Fin J → Option (Selection K)×ℕ) (xs : List (Fin J)) (hLen : xs.length≤J)
    (hb : ∀ l∈xs,Bounded r P (evaluate l).1) (hw : ∀ l∈xs,(evaluate l).2≤E) :
    trace model W evaluate xs≤(xs.length+1)*frameProfile W J K r P E (model.rat P) := by
  induction xs with
  | nil =>
    have hf := fields_bound W (natBits (workCap W J E (model.rat P))) [0,2*W] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact Nat.zero_le _
      · unfold workCap; omega)
    change fields W [0,2*W]+128*W+1≤1*frameProfile W J K r P E (model.rat P)
    change fields W [0,2*W]≤2*(natBits (workCap W J E (model.rat P))+W)+32*W at hf
    unfold frameProfile
    omega
  | cons l rest ih =>
    have hrLen : rest.length≤J := by simp only [List.length_cons] at hLen; omega
    have hbr := fun a ha => hb a (List.mem_cons_of_mem _ ha)
    have hwr := fun a ha => hw a (List.mem_cons_of_mem _ ha)
    have hRec := ih hrLen hbr hwr
    have hLater := native_scan_bounded model W evaluate rest hbr
    have hChosen := pick_bounded (evaluate l).1 (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1
      (hb l List.mem_cons_self) hLater
    have hCurrentFoot := option_bound W r P (evaluate l).1 (hb l List.mem_cons_self)
    have hLaterFoot := option_bound W r P _ hLater
    have hSelectedFoot : optionFootprint W (GeneralPaperScoreBitPrimitive.pickRun model W (evaluate l).1
        (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1).1≤optionProfile W K r P := by
      rw [GeneralPaperScoreBitPrimitive.pick_data]
      exact option_bound W r P _ hChosen
    have hCurrentWork := hw l List.mem_cons_self
    have hLaterWork := scan_work_cap model W E evaluate rest hrLen hbr hwr
    have hTotalWork := scan_work_cap model W E evaluate (l::rest) hLen hb hw
    have hPickWork := GeneralPaperScoreBitPrimitive.pick_work model W P (evaluate l).1
      (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1
      (width_of_bounded (hb l List.mem_cons_self)) (width_of_bounded hLater)
    have hf := fields_bound W (natBits (workCap W J E (model.rat P)))
      [(l::rest).length,l.val,(evaluate l).2,(GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).2,
        (GeneralPaperScoreBitPrimitive.pickRun model W (evaluate l).1 (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1).2,
        (GeneralPaperScoreBitPrimitive.scanRun model W evaluate (l::rest)).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      · unfold workCap; omega
      · have hl := l.isLt; unfold workCap; omega
      · unfold workCap; omega
      · exact hLaterWork
      · unfold workCap; omega
      · exact hTotalWork)
    change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (workCap W J E (model.rat P))+W)+32*W at hf
    change optionFootprint W (evaluate l).1+optionFootprint W (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1+
      optionFootprint W (GeneralPaperScoreBitPrimitive.pickRun model W (evaluate l).1
        (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1).1+GeneralPaperEncodedScalarStorage.fields W _+224*W+trace model W evaluate rest≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at *
    unfold frameProfile at *
    omega

theorem primitive_peak_bound {J K r P : ℕ} (model : RationalCostModel) (W E : ℕ)
    (evaluate : Fin J → Option (Selection K)×ℕ) (xs : List (Fin J))
    (hb : ∀ l∈xs,Bounded r P (evaluate l).1) (hw : ∀ l∈xs,(evaluate l).2≤E) :
    primitivePeak model W evaluate xs≤E+8*W+model.rat P := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons l rest ih =>
    have hbr := fun a ha => hb a (List.mem_cons_of_mem _ ha)
    have hwr := fun a ha => hw a (List.mem_cons_of_mem _ ha)
    have hRec := ih hbr hwr
    have hLater := native_scan_bounded model W evaluate rest hbr
    have hPick := GeneralPaperScoreBitPrimitive.pick_work model W P (evaluate l).1
      (GeneralPaperScoreBitPrimitive.scanRun model W evaluate rest).1
      (width_of_bounded (hb l List.mem_cons_self)) (width_of_bounded hLater)
    change max (evaluate l).2 (max _ _)≤_
    exact max_le (by have := hw l List.mem_cons_self; omega) (max_le hRec (by omega))

theorem complete_bound {J K r P : ℕ} (model : RationalCostModel) (W E : ℕ)
    (evaluate : Fin J → Option (Selection K)×ℕ) (xs : List (Fin J)) (hLen : xs.length≤J)
    (hb : ∀ l∈xs,Bounded r P (evaluate l).1) (hw : ∀ l∈xs,(evaluate l).2≤E) :
    trace model W evaluate xs+primitivePeak model W evaluate xs≤profile W J K r P E (model.rat P) := by
  have ht := trace_bound model W E evaluate xs hLen hb hw
  have hp := primitive_peak_bound model W E evaluate xs hb hw
  have hm := Nat.mul_le_mul_right (frameProfile W J K r P E (model.rat P)) (Nat.add_le_add_right hLen 1)
  unfold profile
  omega

end Blotto.GeneralPaperIndexedMinimumStorage

