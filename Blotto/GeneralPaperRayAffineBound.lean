import Blotto.GeneralPaperRayRationalBound

/-! Affine coefficient bounds survive sums and selection. Crossings are
computed from the original bounded coefficients; midpoint heights are a
constant multiple of root heights, without bracket-history accumulation.
-/
namespace Blotto.GeneralPaperRayAffineBound
open GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 3500000

def Bounded (D E A B : ℕ) (f : Affine) : Prop :=
  GeneralPaperRayRationalBound.Bounded D A f.intercept ∧ GeneralPaperRayRationalBound.Bounded E B f.slope

theorem zero (D E : ℕ) : Bounded D E 0 0 ⟨0,0⟩ :=
  ⟨GeneralPaperRayRationalBound.Bounded.zero D,GeneralPaperRayRationalBound.Bounded.zero E⟩

theorem add {D E A B U V : ℕ} {f g : Affine} (hf : Bounded D E A B f) (hg : Bounded D E U V g) :
    Bounded D E (A+U) (B+V) (GeneralPaperRayAffineScoreStep.add f g) := ⟨hf.1.add hg.1,hf.2.add hg.2⟩

theorem difference {D E A B U V : ℕ} {f g : Affine} (hf : Bounded D E A B f) (hg : Bounded D E U V g) :
    Bounded D E (A+U) (B+V) (GeneralPaperRayAffineComparison.difference f g) := ⟨hf.1.sub hg.1,hf.2.sub hg.2⟩

theorem mono {D E A B U V : ℕ} {f : Affine} (hf : Bounded D E A B f) (hA : A≤U) (hB : B≤V) :
    Bounded D E U V f := ⟨hf.1.mono hA,hf.2.mono hB⟩

def rootWidth (D E A B : ℕ) : ℕ := binaryWordWidth (A+1)+binaryWordWidth D+binaryWordWidth (B+1)+binaryWordWidth E

theorem rootWidth_mono (D E A B U V : ℕ) (hA : A≤U) (hB : B≤V) : rootWidth D E A B≤rootWidth D E U V := by
  have ha := binaryWordWidth_mono (Nat.add_le_add_right hA 1)
  have hb := binaryWordWidth_mono (Nat.add_le_add_right hB 1)
  unfold rootWidth
  omega

theorem crossing_height {D E A B : ℕ} {f : Affine} (hD : 0<D) (hE : 0<E) (hf : Bounded D E A B f) :
    RationalHeight f.crossing (rootWidth D E A B) := by
  have hh := (hf.1.height hD).neg.div (hf.2.height hE)
  simpa only [Affine.crossing,rootWidth,Nat.add_assoc] using hh

theorem midpoint_height {s : ℕ} {lo hi : ℚ} (hlo : RationalHeight lo s) (hhi : RationalHeight hi s) :
    RationalHeight ((lo+hi)/2) (2*s+3) := by
  have hTwo : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hh := (hlo.add hhi).div hTwo
  convert hh using 1
  omega

theorem value_height {D E A B s : ℕ} {f : Affine} (hD : 0<D) (hE : 0<E)
    (hf : Bounded D E A B f) (t : ℚ) (ht : RationalHeight t s) :
    RationalHeight (f.value t)
      (binaryWordWidth (A+1)+binaryWordWidth D+(binaryWordWidth (B+1)+binaryWordWidth E+s)+1) := by
  exact (hf.1.height hD).add ((hf.2.height hE).mul ht)

end Blotto.GeneralPaperRayAffineBound
