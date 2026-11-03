import Blotto.PlayerSpecificRationalOutputSourceCost

/-! An explicit polynomial envelope for the measured dyadic rounding of
all original output coordinates. This bounds the actual source-cost
expression, including the predicate calls, search, conversion and frame. -/
namespace Blotto.PlayerSpecificRationalOutputSourcePolynomial
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private def size (T P : ℕ) : ℕ := T+P+5
private def heightBound (T P : ℕ) : ℕ :=
  PlayerSpecificAlgebraicHeightEnvelope.coefficient*size T P
private def rate (U : ℕ) : ℕ :=
  let W:=PlayerSpecificAlgebraicComparisonCost.widthCoefficient*(U+1)
  W*W+W

def polynomial (N T P : ℕ) : ℕ :=
  let S:=size T P
  let U:=heightBound T P
  let R:=rate U
  let predicate:=(256*S+8000000408+
    PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1))*R
  let search:=S*(predicate+150*R)+(256*S+157)*R
  let round:=search+(256*S+278)*R
  N*round+(141+138*N)*rate (U+N+6)

private theorem size_bounds (T P : ℕ) :
    P+2≤size T P ∧
    PlayerSpecificOutputFloorPredicateSourceCost.height T P≤heightBound T P := by
  constructor
  · dsimp [size]; omega
  · have hm : max T (P+2)+3≤size T P := by
      dsimp [size]
      omega
    unfold PlayerSpecificOutputFloorPredicateSourceCost.height
      PlayerSpecificOutputFloorPredicateSourceCost.inputHeight heightBound
      PlayerSpecificAlgebraicHeightEnvelope.step
    exact Nat.mul_le_mul_left _ hm

private theorem rate_eq (U : ℕ) :
    RationalCostModel.schoolbook.rat
      (PlayerSpecificAlgebraicComparisonExecution.width U)=rate U := by
  rw [PlayerSpecificAlgebraicComparisonCost.width_linear]
  rfl

private theorem rate_mono : Monotone rate := by
  intro a b hab
  rw [←rate_eq,←rate_eq]
  exact RationalCostModel.schoolbook.monotone
    (PlayerSpecificSegmentSelectionSizes.width_mono hab)

theorem work_bound (N T P : ℕ) :
    PlayerSpecificRationalOutputSourceCost.work N T P≤polynomial N T P := by
  let S:=size T P
  let U:=heightBound T P
  let H:=PlayerSpecificOutputFloorPredicateSourceCost.height T P
  let R:=rate U
  let R₀:=rate H
  let F:=PlayerSpecificRationalOutputSourceCost.frameHeight N T P
  let Fmax:=U+N+6
  have hS:= (size_bounds T P).1
  have hH:= (size_bounds T P).2
  have hR : R₀≤R := rate_mono hH
  have hF : F≤Fmax := by
    dsimp only [F,Fmax,PlayerSpecificRationalOutputSourceCost.frameHeight]
    omega
  have hRF : rate F≤rate Fmax := rate_mono hF
  have hcoeff :
      256*(P+1)+8000000408+
        PlayerSpecificAlgebraicComparisonExecution.coefficient*(H+1)≤
      256*S+8000000408+
        PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1) := by
    have hc:=Nat.mul_le_mul_left PlayerSpecificAlgebraicComparisonExecution.coefficient
      (Nat.add_le_add_right hH 1)
    change PlayerSpecificAlgebraicComparisonExecution.coefficient*(H+1)≤
      PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1) at hc
    change P+2≤S at hS
    omega
  have hpred : PlayerSpecificOutputFloorPredicateSourceCost.work T P≤
      (256*S+8000000408+
        PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1))*R := by
    unfold PlayerSpecificOutputFloorPredicateSourceCost.work
    rw [rate_eq]
    exact Nat.mul_le_mul hcoeff hR
  have hsearch : PlayerSpecificOutputFloorSearchSourceCost.work T P≤
      S*((256*S+8000000408+
        PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1))*R+150*R)+
        (256*S+157)*R := by
    have hsum : (P+2)*(PlayerSpecificOutputFloorPredicateSourceCost.work T P+150*R₀)+
        (256*(P+1)+157)*R₀≤
        S*((256*S+8000000408+
          PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1))*R+150*R)+
          (256*S+157)*R := by
      have hinside:=Nat.add_le_add hpred (Nat.mul_le_mul_left 150 hR)
      have hleft:=Nat.mul_le_mul hS hinside
      have hright:=Nat.mul_le_mul
        (by omega : 256*(P+1)+157≤256*S+157) hR
      exact Nat.add_le_add hleft hright
    simpa only [PlayerSpecificOutputFloorSearchSourceCost.work,
      PlayerSpecificOutputFloorSearchSourceCost.width,rate_eq,R₀,H] using hsum
  have hround : PlayerSpecificOutputFloorRoundSourceCost.work T P≤
      S*((256*S+8000000408+
        PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1))*R+150*R)+
      (256*S+157)*R+(256*S+278)*R := by
    have hsum:=Nat.add_le_add hsearch (Nat.mul_le_mul
      (by omega : 256*(P+1)+278≤256*S+278) hR)
    simpa only [PlayerSpecificOutputFloorRoundSourceCost.work,
      PlayerSpecificOutputFloorSearchSourceCost.width,rate_eq,R₀,H] using hsum
  have hsum:=Nat.add_le_add (Nat.mul_le_mul_left N hround)
    (Nat.mul_le_mul_left (141+138*N) hRF)
  simpa only [PlayerSpecificRationalOutputSourceCost.work,
    PlayerSpecificRationalOutputSourceCost.width,rate_eq,polynomial,
    F,Fmax,PlayerSpecificRationalOutputSourceCost.frameHeight,
    S,U,R] using hsum

theorem polynomial_mono_height (N P : ℕ) {T V : ℕ} (h : T≤V) :
    polynomial N T P≤polynomial N V P := by
  have hs : size T P≤size V P := by dsimp [size]; omega
  have hu : heightBound T P≤heightBound V P :=
    Nat.mul_le_mul_left _ hs
  have hr : rate (heightBound T P)≤rate (heightBound V P) := rate_mono hu
  have hrf : rate (heightBound T P+N+6)≤rate (heightBound V P+N+6) :=
    rate_mono (by omega)
  simp only [polynomial]
  gcongr

theorem work_with_control (N T P : ℕ) :
    PlayerSpecificRationalOutputSourceCost.work N T P+
      3*RationalCostModel.schoolbook.rat
        (PlayerSpecificRationalOutputSourceCost.width N T P)≤
      2*polynomial N T P := by
  let F:=PlayerSpecificRationalOutputSourceCost.frameHeight N T P
  let U:=heightBound T P
  let R:=rate (U+N+6)
  have hF : F≤U+N+6 := by
    have hh:=(size_bounds T P).2
    dsimp only [F,PlayerSpecificRationalOutputSourceCost.frameHeight,U]
    omega
  have hrate : rate F≤R := rate_mono hF
  have hcontrol : 3*rate F≤(141+138*N)*R :=
    Nat.mul_le_mul (by omega) hrate
  have hfloor : (141+138*N)*R≤polynomial N T P := by
    simp only [polynomial]
    dsimp only [R,U]
    omega
  have hsource:=work_bound N T P
  have hsum:=Nat.add_le_add hsource (hcontrol.trans hfloor)
  have hsum' : PlayerSpecificRationalOutputSourceCost.work N T P+
      3*rate F≤2*polynomial N T P := by omega
  simpa only [PlayerSpecificRationalOutputSourceCost.width,rate_eq,
    F] using hsum'

theorem source_cost {N : ℕ}
    (root : PlayerSpecificAlgebraicCandidates.Candidate)
    (y : FixedArrayTable N PlayerSpecificDensePolynomial.Data)
    (T P : ℕ)
    (hm : PlayerSpecificPolynomialNormalization.Normalized root.polynomial)
    (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4)
    (hv : root.interval.lo<root.interval.hi)
    (hroot : PlayerSpecificPolynomialHeights.HasHeight root.polynomial T)
    (hends : PlayerSpecificPolynomialHeights.HasHeight
      [root.interval.lo,root.interval.hi] T)
    (hy : ∀ j : Fin N,
      PlayerSpecificAlgebraicReduction.Reduced root.polynomial (y.read j) ∧
      PlayerSpecificPolynomialHeights.HasHeight (y.read j) T) :
    (PlayerSpecificRationalOutputExecution.run root y P).2≤polynomial N T P :=
  (PlayerSpecificRationalOutputSourceCost.cost root y T P hm hm0 hml hv
    hroot hends hy).trans (work_bound N T P)

end Blotto.PlayerSpecificRationalOutputSourcePolynomial
