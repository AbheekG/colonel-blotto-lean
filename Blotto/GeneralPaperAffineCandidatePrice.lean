import Blotto.GeneralPaperAffineMinimumPrice

/-! One native affine predecessor candidate, including its two rational
coefficient additions, indexed reads, score guard and shared predecessor cons.
-/
namespace Blotto.GeneralPaperAffineCandidatePrice
open GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) (label : Fin K) : Option (Choice K) × ℕ :=
  let data := field.read label
  if h : data.1≤s.val then
    match previous.read ⟨s.val-data.1,by omega⟩ with
    | none => (none,64*W)
    | some tail =>
      let sum := GeneralPaperAffineValuePrice.addRun primitive W data.2 tail.expression
      (some ⟨sum.1,label::tail.labels⟩,64*W+sum.2)
  else (none,64*W)

theorem data {S K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (field : Field K) (previous : Table S K)
    (s : Fin (S+1)) (label : Fin K) :
    (run primitive W field previous s label).1=GeneralPaperRayAffineScoreStep.candidate field previous s label := by
  unfold run GeneralPaperRayAffineScoreStep.candidate
  dsimp only
  split
  · cases previous.read ⟨s.val-(field.read label).1,by omega⟩ <;> rfl
  · rfl

theorem bounded {S K : ℕ} (primitive : ℕ → ℕ) (W D E A B : ℕ) (field : Field K) (previous : Table S K)
    (hf : ∀ l,GeneralPaperRayAffineBound.Bounded D E A B (field.read l).2)
    (hp : ∀ s,GeneralPaperAffineMinimumPrice.Bounded D E A B (previous.read s))
    (s : Fin (S+1)) (label : Fin K) :
    GeneralPaperAffineMinimumPrice.Bounded D E (A+A) (B+B) (run primitive W field previous s label).1 := by
  rw [data]
  intro chosen hc
  dsimp only [GeneralPaperRayAffineScoreStep.candidate] at hc
  split at hc
  · cases he : previous.read ⟨s.val-(field.read label).1,by omega⟩ with
    | none => simp only [he,Option.map_none] at hc; contradiction
    | some tail =>
      have hh : GeneralPaperRayAffineScoreStep.extend label (field.read label).2 tail=chosen := by
        simpa only [he,Option.map_some,Option.some.injEq] using hc
      rw [←hh]
      exact GeneralPaperRayAffineBound.add (hf label) (hp _ tail he)
  · contradiction

theorem work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D E A B R : ℕ)
    (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R)
    (field : Field K) (previous : Table S K)
    (hf : ∀ l,GeneralPaperRayAffineBound.Bounded D E A B (field.read l).2)
    (hp : ∀ s,GeneralPaperAffineMinimumPrice.Bounded D E A B (previous.read s))
    (s : Fin (S+1)) (label : Fin K) :
    (run primitive W field previous s label).2≤96*W+4*primitive (1+2*R) := by
  have hBase := (GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B)
    (Nat.le_add_right _ _) (Nat.le_add_right _ _)).trans hR
  have hHeights (f : Affine) (hb : GeneralPaperRayAffineBound.Bounded D E A B f) :
      RationalHeight f.intercept R ∧ RationalHeight f.slope R := by
    have hh := GeneralPaperAffineValuePrice.coefficients hD hE f hb
    exact ⟨hh.1.mono hBase,hh.2.mono hBase⟩
  unfold run
  dsimp only
  split
  · cases he : previous.read ⟨s.val-(field.read label).1,by omega⟩ with
    | none => dsimp only; omega
    | some tail =>
      have hs := GeneralPaperRayAffineBound.add (hf label) (hp _ tail he)
      have hc := GeneralPaperAffineValuePrice.coefficients hD hE _ hs
      have hSum := GeneralPaperAffineValuePrice.add_work primitive hMono W R (field.read label).2 tail.expression
        (hHeights _ (hf label)) (hHeights _ (hp _ tail he)) ⟨hc.1.mono hR,hc.2.mono hR⟩
      change 64*W+(GeneralPaperAffineValuePrice.addRun primitive W (field.read label).2 tail.expression).2≤_
      omega
  · omega

end Blotto.GeneralPaperAffineCandidatePrice
