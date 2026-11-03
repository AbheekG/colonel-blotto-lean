import Blotto.GeneralPaperScoreSelectionStorage

/-! Owned full-score tables and actual native constructor prefixes. Slots
are reserved once per table; every witness and list is charged in full.
No dynamic table census executes. All score cells, including absent cells
and unsuccessful candidates, are covered by the same profile. -/
namespace Blotto.GeneralPaperScoreTableStorage
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreSelectionStorage
open GeneralPaperEncodedReferenceVector
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def tableFootprint {K S : ℕ} (W : ℕ) (table : FixedArrayTable (S+1) (Option (Selection K))) : ℕ :=
  footprint W (optionFootprint W) table.data

def tableProfile (W K S r P : ℕ) : ℕ := (S+1)*(optionProfile W K r P+W)+64*W

theorem table_bound {K S : ℕ} (W r P : ℕ) (table : FixedArrayTable (S+1) (Option (Selection K)))
    (h : ∀ s,Bounded r P (table.read s)) : tableFootprint W table≤tableProfile W K S r P := by
  have hb := bounded W (optionProfile W K r P) (optionFootprint W) table.data (by
    intro i
    let s : Fin (S+1) := ⟨i.val,i.isLt.trans_eq table.size⟩
    exact option_bound W r P (table.read s) (h s))
  simpa only [tableFootprint,tableProfile,table.size] using hb

theorem native_return {K : ℕ} (model : RationalCostModel) (W S A r : ℕ) (fields : List (Field K))
    (hFields : CostHeight fields A) (hLen : fields.length≤r) :
    tableFootprint W (GeneralPaperScoreDPBits.runWithBits model W S fields).1≤
      tableProfile W K S r (GeneralPaperScoreBitPrimitive.resourceWidth A r) := by
  rw [GeneralPaperScoreDPBits.run_data]
  exact table_bound W r _ _ (run_bounded S A r fields hFields hLen)

theorem lattice_return {K : ℕ} (model : RationalCostModel) (W D M r S : ℕ) (hD : 0<D)
    (fields : List (Field K)) (hf : ∀ f∈fields,∀ l,GeneralPaperRayRationalBound.Bounded D M (f.read l).2)
    (hLen : fields.length≤r) :
    tableFootprint W (GeneralPaperScoreDPBits.runWithBits model W S fields).1≤
      tableProfile W K S r (GeneralPaperCommonLatticeDPBits.width D M r) := by
  rw [GeneralPaperScoreDPBits.run_data]
  exact table_bound W r _ _ (lattice_run_bounded D M r S hD fields hf hLen)

theorem scan_cell {K S : ℕ} (model : RationalCostModel) (W A r : ℕ)
    (field : Field K) (rest : List (Field K)) (hFields : CostHeight (field::rest) A)
    (hLen : rest.length+1≤r) (s : Fin (S+1)) (xs : List (Fin K)) :
    Bounded r (GeneralPaperScoreBitPrimitive.resourceWidth A r)
      (GeneralPaperScoreBitPrimitive.scanRun model W
        (GeneralPaperScoreBitPrimitive.candidateRun model W field (run S rest) s) xs).1 :=
  native_scan_bounded model W _ xs (fun l _ => candidate_bounded model W A r field rest hFields hLen s l)

theorem step_prefix {K S : ℕ} (model : RationalCostModel) (W A r : ℕ)
    (field : Field K) (rest : List (Field K)) (hFields : CostHeight (field::rest) A)
    (hLen : rest.length+1≤r) (count : ℕ) (hc : count≤S+1) :
    reservedFootprint W (S+1) (optionFootprint W)
      (PaperIndexedArrayConstruction.fill (fun w => w) W
        (fun s => GeneralPaperScoreBitPrimitive.scanRun model W
          (GeneralPaperScoreBitPrimitive.candidateRun model W field (run S rest) s) (List.finRange K)) count hc).1≤
      tableProfile W K S r (GeneralPaperScoreBitPrimitive.resourceWidth A r) :=
  indexed_reserved_prefix (fun w => w) W W (optionProfile W K r (GeneralPaperScoreBitPrimitive.resourceWidth A r))
    (optionFootprint W) _ (fun s => option_bound W r _ _ (scan_cell model W A r field rest hFields hLen s _)) count hc

theorem initial_prefix (_model : RationalCostModel) (W K S count : ℕ) (hc : count≤S+1) :
    reservedFootprint W (S+1) (optionFootprint W)
      (PaperIndexedArrayConstruction.fill (fun w => w) W
        (fun s : Fin (S+1) => (if s.val=0 then some (⟨0,[]⟩ : Selection K) else none,2*W+3)) count hc).1≤
      tableProfile W K S 0 3 := by
  apply indexed_reserved_prefix
  intro s
  apply option_bound
  split
  · intro chosen he
    cases Option.some.inj he
    exact ⟨by simp,by change rationalWordWidth (0:ℚ)≤3; decide⟩
  · intro chosen he
    cases he

@[fun_prop]
theorem profile_scale (K S r P : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => tableProfile W K S r P) := by
  unfold tableProfile
  fun_prop

end Blotto.GeneralPaperScoreTableStorage
