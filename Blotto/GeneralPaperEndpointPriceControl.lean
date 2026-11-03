import Blotto.GeneralPaperStaticScanPrice

/-! The shared native static-or-high endpoint control flow. Concrete unit
and bit wrappers discharge the static, query and high-search contracts;
abstract callback prices alone are not a complete endpoint bound.
-/
namespace Blotto.GeneralPaperEndpointPriceControl
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayMinimum
set_option autoImplicit false
set_option maxHeartbeats 4500000

abbrev Query := ℚ → Bool × ℕ
abbrev High (m K : ℕ) := ℚ → ℚ → Option (GeneralPaperRayHighSearch.Answer m K) × ℕ

def run {T m K : ℕ} (W : ℕ) (static : Result (StaticIndex T m K)) (query : Query) (high : High m K) :
    Option (GeneralPaperRayEndpoint.Answer T m K) × ℕ :=
  match static.choice with
  | none => (none,static.work+8*W)
  | some c =>
    let accepted := query c.time
    if accepted.1=true then
      (some ⟨c.time,.inl c.blocker⟩,static.work+accepted.2+16*W)
    else
      let answer := high 0 c.time
      (answer.1.map (fun out => ⟨out.time,.inr out.labels⟩),static.work+accepted.2+answer.2+32*W)

theorem data {T m K : ℕ} (W : ℕ) (static : Result (StaticIndex T m K)) (query : Query) (high : High m K)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ)
    (hStatic : static.choice=(GeneralPaperStaticRayScan.scan labels x w).choice)
    (hQuery : ∀ t,(query t).1=(GeneralPaperRayPricedPredicate.query matrix x w S h beta t).1)
    (hHigh : ∀ lo hi,(high lo hi).1=GeneralPaperRayHighSearch.prepared matrix S h beta x w lo hi) :
    (run W static query high).1=GeneralPaperRayEndpoint.prepared labels matrix S h beta x w := by
  unfold run GeneralPaperRayEndpoint.prepared
  simp only [hStatic]
  cases (GeneralPaperStaticRayScan.scan labels x w).choice with
  | none => rfl
  | some c =>
    simp only [hQuery]
    split
    · rfl
    · simp only [hHigh]

def profile (T m K S W Q : ℕ) : ℕ :=
  8192*(m*(K-1)+m*T+1)*(W+Q)+4096*(m+1)*(K+1)*(S+1)*(W+Q) +
    GeneralPaperHighSearchPriceFacts.profile m S K W Q+32*W

theorem work {T m K : ℕ} (W C E H : ℕ) (static : Result (StaticIndex T m K)) (query : Query) (high : High m K)
    (hStatic : static.work≤C)
    (hQuery : ∀ c,static.choice=some c → (query c.time).2≤E)
    (hHigh : ∀ c,static.choice=some c → (high 0 c.time).2≤H) :
    (run W static query high).2≤C+E+H+32*W := by
  rw [run]
  cases hs : static.choice with
  | none => dsimp only; omega
  | some c =>
    have hq := hQuery c hs
    dsimp only
    split
    · dsimp only; omega
    · have hh := hHigh c hs
      dsimp only
      omega

end Blotto.GeneralPaperEndpointPriceControl
