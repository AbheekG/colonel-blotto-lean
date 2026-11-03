import Blotto.GeneralPaperRayParametricRunSize

/-! Common-denominator bounds for the executed fixed-point complete-score
queries. Every DP cell/candidate has the partial-sum bound; the native
high-score minimum and its budget comparison inherit it. Negative ray
velocities do not require nonnegative intermediate costs.
-/
namespace Blotto.GeneralPaperRayFixedQuerySize
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperExactScoreDP
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem fits {K : ℕ} (D M : ℕ) (fields : List (Field K))
    (hf : ∀ f∈fields,∀ l,Bounded D M (f.read l).2) (s : ℕ) (c : GeneralPaperMinimum.Selection K)
    (hc : Fits fields s c) : Bounded D (fields.length*M) c.cost := by
  induction fields generalizing s c with
  | nil =>
    rw [hc.2]
    simpa only [List.length_nil,Nat.zero_mul] using Bounded.zero D
  | cons field rest ih =>
    obtain ⟨l,_,tail,ht,rfl⟩ := hc
    have hTail := ih (fun f h => hf f (List.mem_cons_of_mem _ h)) _ tail ht
    have hh := (hf field List.mem_cons_self l).add hTail
    have he : M+rest.length*M=(rest.length+1)*M := by ring
    rw [he] at hh
    exact hh

theorem run {K : ℕ} (D M S : ℕ) (fields : List (Field K))
    (hf : ∀ f∈fields,∀ l,Bounded D M (f.read l).2) (s : Fin (S+1)) (c : GeneralPaperMinimum.Selection K)
    (hc : (GeneralPaperExactScoreDP.run S fields).read s=some c) : Bounded D (fields.length*M) c.cost := by
  have hb := run_best S fields s
  rw [hc] at hb
  exact fits D M fields hf s.val c hb.1

theorem candidate {K S : ℕ} (D M : ℕ) (field : Field K) (rest : List (Field K))
    (hf : ∀ f∈field::rest,∀ l,Bounded D M (f.read l).2) (s : Fin (S+1)) (l : Fin K)
    (c : GeneralPaperMinimum.Selection K)
    (hc : GeneralPaperExactScoreDP.candidate field (GeneralPaperExactScoreDP.run S rest) s l=some c) :
    Bounded D ((rest.length+1)*M) c.cost := by
  have hb := candidate_best field rest (GeneralPaperExactScoreDP.run S rest) (fun s => run_best S rest s) s l
  rw [hc] at hb
  exact fits D M (field::rest) hf s.val c ⟨l,hb.1⟩

theorem cost {m K : ℕ} (D E X W : ℕ) (hED : E∣D) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (t : ℚ) (ht : 0≤t ∧ t≤1)
    (j : Fin m) (l : Fin K) : Bounded (D*t.den) (X+W) (GeneralPaperRayAnchorCosts.costs x w t j l) := by
  have hX := (GeneralPaperRayAnchorBound.anchor D X x hx j l).enlarge (Nat.dvd_mul_right D t.den)
  have hW := (GeneralPaperRayAnchorBound.anchor E W w hw j l).enlarge hED
  have hT : Bounded t.den 1 t := ⟨dvd_refl _,by rw [abs_of_nonneg ht.1]; exact ht.2⟩
  have hTW : Bounded (D*t.den) W (t*GeneralPaperRayAnchorCosts.anchorQ w j l) := by
    simpa only [Nat.mul_comm t.den D,Nat.one_mul] using hT.mul hW
  exact hX.add hTW

theorem native_minimum {m K : ℕ} (D E X W : ℕ) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (S h : ℕ) (c : GeneralPaperMinimum.Selection K)
    (hc : (GeneralPaperRayQueryWork.minimumRun matrix x w t S h).1=some c) : Bounded (D*t.den) (m*(X+W)) c.cost := by
  rw [GeneralPaperRayQueryWork.minimum_data] at hc
  have hb := GeneralPaperRayHighMinimum.minimum_best (GeneralPaperRayQueryWork.scores matrix) (GeneralPaperRayAnchorCosts.costs x w t) S h
  rw [hc] at hb
  obtain ⟨s,_,hs⟩ := hb.1
  have hFields : ∀ f∈GeneralPaperExactScoreDP.fields (GeneralPaperRayQueryWork.scores matrix) (GeneralPaperRayAnchorCosts.costs x w t),
      ∀ l,Bounded (D*t.den) (X+W) (f.read l).2 := by
    intro f hf l
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
    simpa only [FixedArrayTable.read_ofFn] using cost D E X W hED x w hx hw t ht j l
  have hh := fits (D*t.den) (X+W) _ hFields s.val c hs
  simpa only [GeneralPaperExactScoreDP.fields,List.length_ofFn] using hh

theorem predicate_heights {m K : ℕ} (D E X W P : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a))
    (beta : ℚ) (hb : Bounded D P beta) (t : ℚ) (ht : 0≤t ∧ t≤1) (S h : ℕ)
    (c : GeneralPaperMinimum.Selection K) (hc : (GeneralPaperRayQueryWork.minimumRun matrix x w t S h).1=some c) :
    RationalHeight beta (binaryWordWidth (P+m*(X+W)+1)+binaryWordWidth (D*t.den)) ∧
      RationalHeight c.cost (binaryWordWidth (P+m*(X+W)+1)+binaryWordWidth (D*t.den)) := by
  have hPos := Nat.mul_pos hD t.den_pos
  have hB := (hb.enlarge (Nat.dvd_mul_right D t.den)).mono (show P≤P+m*(X+W) by omega)
  have hC := (native_minimum D E X W hED matrix x w hx hw t ht S h c hc).mono (show m*(X+W)≤P+m*(X+W) by omega)
  exact ⟨hB.height hPos,hC.height hPos⟩

end Blotto.GeneralPaperRayFixedQuerySize
