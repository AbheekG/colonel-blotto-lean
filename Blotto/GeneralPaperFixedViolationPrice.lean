import Blotto.GeneralPaperFinalRefinementPrice

/-! Price the early-exit scan of the FIXED affine table. It evaluates each
visited high-score entry once and returns the same first violating entry;
there is no additional complete DP or tuple search.
-/
namespace Blotto.GeneralPaperFixedViolationPrice
open GeneralPaperRayAffine GeneralPaperRayAffineScoreStep GeneralPaperRayFixedViolation
set_option autoImplicit false
set_option maxHeartbeats 4500000

def candidateRun {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K)
    (h : ℕ) (beta t : ℚ) (s : Fin (S+1)) : Option (Entry S K) × ℕ :=
  if h<s.val then
    match table.read s with
    | none => (none,32*W)
    | some c =>
      let value := GeneralPaperAffineValuePrice.run primitive W c.expression t
      (if value.1<beta then some (s,c) else none,
        value.2+32*W+primitive (RationalExpression.pairWidth value.1 beta))
  else (none,32*W)

theorem candidate_data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K)
    (h : ℕ) (beta t : ℚ) (s : Fin (S+1)) :
    (candidateRun primitive W table h beta t s).1=GeneralPaperRayFixedViolation.candidate table h beta t s := by
  unfold candidateRun GeneralPaperRayFixedViolation.candidate
  split
  · cases table.read s <;> rfl
  · rfl

theorem candidate_work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R u : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (table : Table S K)
    (hp : ∀ s,GeneralPaperAffineMinimumPrice.Bounded D E A B (table.read s))
    (h : ℕ) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u) (s : Fin (S+1)) :
    (candidateRun primitive W table h beta t s).2≤48*W+5*primitive (1+2*(R+u+1)) := by
  unfold candidateRun
  split
  · cases he : table.read s with
    | none => dsimp only; omega
    | some c =>
      have hc := hp s c he
      have hv := GeneralPaperAffineValuePrice.work primitive hMono W D E A B R u hD hE c.expression hc hR t ht
      have hHeight : RationalHeight (c.expression.value t) (R+u+1) := by
        apply (GeneralPaperRayAffineBound.value_height hD hE hc t ht).mono
        unfold GeneralPaperRayAffineBound.rootWidth at hR
        omega
      have hBeta := hb.mono (show R≤R+u+1 by omega)
      have hCompare := hMono (max_le (rationalWordWidth_of_height hHeight) (rationalWordWidth_of_height hBeta))
      change primitive (RationalExpression.pairWidth (c.expression.value t) beta)≤primitive (1+2*(R+u+1)) at hCompare
      change (GeneralPaperAffineValuePrice.run primitive W c.expression t).2+32*W+
        primitive (RationalExpression.pairWidth (c.expression.value t) beta)≤_
      omega
  · omega

def scan {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) :
    List (Fin (S+1)) → Result S K
  | [] => ⟨none,2*W⟩
  | s::rest =>
    let current := candidateRun primitive W table h beta t s
    match current.1 with
    | some entry => ⟨some entry,current.2+8*W⟩
    | none =>
      let later := scan primitive W table h beta t rest
      ⟨later.value,current.2+later.work+8*W⟩

theorem scan_data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K)
    (h : ℕ) (beta t : ℚ) (xs : List (Fin (S+1))) :
    (scan primitive W table h beta t xs).value=(GeneralPaperRayFixedViolation.scan table h beta t xs).value := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    rw [scan,GeneralPaperRayFixedViolation.scan]
    simp only [candidate_data]
    cases GeneralPaperRayFixedViolation.candidate table h beta t s <;> simp only [ih]

theorem scan_work {S K : ℕ} (primitive : ℕ → ℕ) (W C : ℕ) (table : Table S K)
    (h : ℕ) (beta t : ℚ) (xs : List (Fin (S+1)))
    (hEach : ∀ s∈xs,(candidateRun primitive W table h beta t s).2≤C) :
    (scan primitive W table h beta t xs).work≤(C+8*W)*xs.length+2*W := by
  induction xs with
  | nil => simp only [scan,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons s rest ih =>
    have hc := hEach s List.mem_cons_self
    rw [scan]
    split
    · dsimp only
      simp only [List.length_cons]
      nlinarith only [hc,Nat.zero_le ((C+8*W)*rest.length)]
    · have hr := ih (fun q hq => hEach q (List.mem_cons_of_mem _ hq))
      dsimp only
      simp only [List.length_cons]
      nlinarith only [hc,hr]

def run {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) : Result S K :=
  let result := scan primitive W table h beta t (List.finRange (S+1))
  ⟨result.value,result.work+16*(S+2)*W⟩

theorem data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) :
    (run primitive W table h beta t).value=(GeneralPaperRayFixedViolation.run table h beta t).value := by
  simp only [run,scan_data,GeneralPaperRayFixedViolation.run]

def profile (S W P : ℕ) : ℕ := (S+1)*(56*W+5*P)+(16*(S+2)+2)*W

theorem work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R u : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (table : Table S K)
    (hp : ∀ s,GeneralPaperAffineMinimumPrice.Bounded D E A B (table.read s))
    (h : ℕ) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u) :
    (run primitive W table h beta t).work≤profile S W (primitive (1+2*(R+u+1))) := by
  have hh := scan_work primitive W (48*W+5*primitive (1+2*(R+u+1))) table h beta t (List.finRange (S+1))
    (fun s _ => candidate_work primitive hMono W D E A B R u hD hE hR table hp h beta t hb ht s)
  simp only [List.length_finRange] at hh
  change (scan primitive W table h beta t (List.finRange (S+1))).work+16*(S+2)*W≤_
  unfold profile
  nlinarith only [hh]

end Blotto.GeneralPaperFixedViolationPrice
