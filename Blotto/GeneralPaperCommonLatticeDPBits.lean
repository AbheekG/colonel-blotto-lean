import Blotto.GeneralPaperCrossingPriceEnvelope
import Blotto.GeneralPaperScoreDPBits

/-! Sharp bit prices for the existing complete-score DP on a common lattice.
Every addition/selection pays actual operand widths. The shared denominator
is used only in proofs; no conversion or coefficient reconstruction is run.
Unlike an independent-denominator bound, width grows only logarithmically
with the number of fields. W's full source score/index capacity joins remain
the caller's obligation, as in the original priced DP.
-/
namespace Blotto.GeneralPaperCommonLatticeDPBits
open GeneralPaperRayRationalBound GeneralPaperExactScoreDP GeneralPaperScoreBitPrimitive
set_option autoImplicit false
set_option maxHeartbeats 4500000

def width (D M m : ℕ) : ℕ :=
  1+2*(binaryWordWidth ((m+1)*M+1)+binaryWordWidth D)

theorem bounded_width (D M m : ℕ) (hD : 0<D) {U : ℕ} {q : ℚ}
    (hq : Bounded D U q) (hU : U≤(m+1)*M) : rationalWordWidth q≤width D M m :=
  rationalWordWidth_of_height ((hq.mono hU).height hD)

theorem input_width (D M m : ℕ) (hD : 0<D) (q : ℚ) (hq : Bounded D M q) :
    rationalWordWidth q≤width D M m := by
  apply bounded_width D M m hD hq
  have hh := Nat.mul_le_mul_right M (show 1≤m+1 by omega)
  simpa only [Nat.one_mul] using hh

theorem run_width {K : ℕ} (D M m S : ℕ) (hD : 0<D) (fields : List (Field K))
    (hf : ∀ f∈fields,∀ l,Bounded D M (f.read l).2) (hLen : fields.length≤m)
    (s : Fin (S+1)) : Width ((GeneralPaperExactScoreDP.run S fields).read s) (width D M m) := by
  intro chosen hc
  exact bounded_width D M m hD (GeneralPaperRayFixedQuerySize.run D M S fields hf s chosen hc)
    (Nat.mul_le_mul_right M (by omega))

theorem candidate_width {K S : ℕ} (model : RationalCostModel) (W D M m : ℕ) (hD : 0<D)
    (field : Field K) (rest : List (Field K))
    (hf : ∀ f∈field::rest,∀ l,Bounded D M (f.read l).2) (hLen : rest.length≤m)
    (s : Fin (S+1)) (l : Fin K) :
    Width (GeneralPaperScoreBitPrimitive.candidateRun model W field (GeneralPaperExactScoreDP.run S rest) s l).1
      (width D M m) := by
  rw [GeneralPaperScoreBitPrimitive.candidate_data]
  intro chosen hc
  exact bounded_width D M m hD
    (GeneralPaperRayFixedQuerySize.candidate D M field rest hf s l chosen hc)
    (Nat.mul_le_mul_right M (Nat.add_le_add_right hLen 1))

theorem candidate_work {K S : ℕ} (model : RationalCostModel) (W D M m : ℕ) (hD : 0<D)
    (field : Field K) (rest : List (Field K))
    (hf : ∀ f∈field::rest,∀ l,Bounded D M (f.read l).2) (hLen : rest.length≤m)
    (s : Fin (S+1)) (l : Fin K) :
    (GeneralPaperScoreBitPrimitive.candidateRun model W field (GeneralPaperExactScoreDP.run S rest) s l).2≤
      64*W+2*model.rat (width D M m) := by
  have hHead := hf field List.mem_cons_self l
  have hRest : ∀ f∈rest,∀ l,Bounded D M (f.read l).2 :=
    fun f hh => hf f (List.mem_cons_of_mem _ hh)
  unfold GeneralPaperScoreBitPrimitive.candidateRun
  dsimp only
  split
  · rename_i hScore
    let index : Fin (S+1) := ⟨s.val-(field.read l).1,by omega⟩
    change (match (GeneralPaperExactScoreDP.run S rest).read index with
      | none => (none,64*W)
      | some tail => (some (GeneralPaperMinimum.extend l (field.read l).2 tail),
          64*W+additionPrice model (field.read l).2 tail.cost)).2≤_
    cases he : (GeneralPaperExactScoreDP.run S rest).read index with
    | none => dsimp only; omega
    | some tail =>
      have ht := run_width D M m S hD rest hRest hLen index tail he
      have hh := input_width D M m hD (field.read l).2 hHead
      have hc : GeneralPaperExactScoreDP.candidate field (GeneralPaperExactScoreDP.run S rest) s l=
          some (GeneralPaperMinimum.extend l (field.read l).2 tail) := by
        simp only [GeneralPaperExactScoreDP.candidate,dite_eq_left hScore]
        change Option.map (GeneralPaperMinimum.extend l (field.read l).2)
          ((GeneralPaperExactScoreDP.run S rest).read index)=_
        rw [he]
        rfl
      have ho := candidate_width model W D M m hD field rest hf hLen s l
      rw [GeneralPaperScoreBitPrimitive.candidate_data] at ho
      have hp := additionPrice_le model (field.read l).2 tail.cost (width D M m) hh ht (ho _ hc)
      dsimp only
      exact Nat.add_le_add_left hp _
  · omega

theorem step_work {K S : ℕ} (model : RationalCostModel) (W D M m : ℕ) (hD : 0<D)
    (field : Field K) (rest : List (Field K))
    (hf : ∀ f∈field::rest,∀ l,Bounded D M (f.read l).2) (hLen : rest.length≤m)
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (GeneralPaperScoreDPBits.stepRun model W field (GeneralPaperExactScoreDP.run S rest)).2≤
      GeneralPaperScoreDPBits.stepProfile K S W (model.rat (width D M m)) := by
  let P := model.rat (width D M m)
  have hEach (s : Fin (S+1)) :
      (scanRun model W (GeneralPaperScoreBitPrimitive.candidateRun model W field
        (GeneralPaperExactScoreDP.run S rest) s) (List.finRange K)).2≤(76*W+3*P)*K+2*W := by
    have hh := scan_work model W (width D M m) (64*W+2*P)
      (GeneralPaperScoreBitPrimitive.candidateRun model W field (GeneralPaperExactScoreDP.run S rest) s)
      (List.finRange K)
      (fun l _ => candidate_width model W D M m hD field rest hf hLen s l)
      (fun l _ => candidate_work model W D M m hD field rest hf hLen s l)
    simp only [List.length_finRange] at hh
    convert hh using 1
    dsimp only [P]
    ring
  have hSum := Finset.sum_le_sum (fun s (_ : s∈Finset.univ) => hEach s)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have hArray := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun s => scanRun model W (GeneralPaperScoreBitPrimitive.candidateRun model W field
      (GeneralPaperExactScoreDP.run S rest) s) (List.finRange K))
  change (GeneralPaperScoreDPBits.stepRun model W field (GeneralPaperExactScoreDP.run S rest)).2≤
    (∑ s,(scanRun model W (GeneralPaperScoreBitPrimitive.candidateRun model W field
      (GeneralPaperExactScoreDP.run S rest) s) (List.finRange K)).2)+
      (S+2)*(6*W+10*binaryWordWidth (S+2)+28) at hArray
  unfold GeneralPaperScoreDPBits.stepProfile
  exact hArray.trans (Nat.add_le_add hSum (GeneralPaperScoreDPBits.array_overhead S W hW hIndex))

theorem run_work {K : ℕ} (model : RationalCostModel) (W D M m S : ℕ) (hD : 0<D)
    (fields : List (Field K)) (hf : ∀ f∈fields,∀ l,Bounded D M (f.read l).2)
    (hLen : fields.length≤m) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (GeneralPaperScoreDPBits.runWithBits model W S fields).2≤
      GeneralPaperScoreDPBits.profile fields.length K S W (model.rat (width D M m)) := by
  induction fields with
  | nil =>
    simpa only [GeneralPaperScoreDPBits.runWithBits,GeneralPaperScoreDPBits.profile,
      List.length_nil,Nat.zero_mul,Nat.add_zero] using GeneralPaperScoreDPBits.initial_work model W K S hW hIndex
  | cons field rest ih =>
    have hr := ih (fun f hh => hf f (List.mem_cons_of_mem _ hh))
      (by simp only [List.length_cons] at hLen; omega)
    have hs := step_work model W D M m hD field rest hf
      (by simp only [List.length_cons] at hLen; omega) hW hIndex
    have hs' : (GeneralPaperScoreDPBits.stepRun model W field
        (GeneralPaperScoreDPBits.runWithBits model W S rest).1).2≤
        GeneralPaperScoreDPBits.stepProfile K S W (model.rat (width D M m)) := by
      rw [GeneralPaperScoreDPBits.run_data]
      exact hs
    change (GeneralPaperScoreDPBits.runWithBits model W S rest).2+
      (GeneralPaperScoreDPBits.stepRun model W field (GeneralPaperScoreDPBits.runWithBits model W S rest).1).2+4*W≤_
    unfold GeneralPaperScoreDPBits.profile at hr ⊢
    simp only [List.length_cons]
    nlinarith only [hr,hs']

end Blotto.GeneralPaperCommonLatticeDPBits
