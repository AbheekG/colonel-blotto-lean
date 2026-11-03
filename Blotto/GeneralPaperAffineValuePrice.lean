import Blotto.GeneralPaperRationalPrimitivePrice

/-! Price the two native rational operations in one affine evaluation and
the two coefficient additions of an affine predecessor extension. Bounds
come from the original common lattices, independently of sample history.
-/
namespace Blotto.GeneralPaperAffineValuePrice
open GeneralPaperRayAffine GeneralPaperRationalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem coefficients {D E A B : ℕ} (hD : 0<D) (hE : 0<E) (f : Affine)
    (hf : GeneralPaperRayAffineBound.Bounded D E A B f) :
    RationalHeight f.intercept (GeneralPaperRayAffineBound.rootWidth D E A B) ∧
    RationalHeight f.slope (GeneralPaperRayAffineBound.rootWidth D E A B) := by
  have ha := hf.1.height hD
  have hb := hf.2.height hE
  exact ⟨ha.mono (by unfold GeneralPaperRayAffineBound.rootWidth; omega),
    hb.mono (by unfold GeneralPaperRayAffineBound.rootWidth; omega)⟩

def run (primitive : ℕ → ℕ) (W : ℕ) (f : Affine) (t : ℚ) : ℚ × ℕ :=
  let product := f.slope*t
  (f.intercept+product,16*W+binary primitive (·*·) f.slope t+
    binary primitive (·+·) f.intercept product)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (f : Affine) (t : ℚ) :
    (run primitive W f t).1=f.value t := rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D E A B R s : ℕ)
    (hD : 0<D) (hE : 0<E) (f : Affine) (hf : GeneralPaperRayAffineBound.Bounded D E A B f)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (t : ℚ) (ht : RationalHeight t s) :
    (run primitive W f t).2≤16*W+4*primitive (1+2*(R+s+1)) := by
  have hc := coefficients hD hE f hf
  have hp := hc.2.mul ht
  have hv := GeneralPaperRayAffineBound.value_height hD hE hf t ht
  have ha' := hc.1.mono (show GeneralPaperRayAffineBound.rootWidth D E A B≤R+s+1 by omega)
  have hb' := hc.2.mono (show GeneralPaperRayAffineBound.rootWidth D E A B≤R+s+1 by omega)
  have ht' := ht.mono (show s≤R+s+1 by omega)
  have hp' := hp.mono (show GeneralPaperRayAffineBound.rootWidth D E A B+s≤R+s+1 by omega)
  have hv' : RationalHeight (f.value t) (R+s+1) := hv.mono (by
    unfold GeneralPaperRayAffineBound.rootWidth at hR
    omega)
  have hm := binary_le primitive hMono (·*·) f.slope t (1+2*(R+s+1))
    (rationalWordWidth_of_height hb') (rationalWordWidth_of_height ht') (rationalWordWidth_of_height hp')
  have ha := binary_le primitive hMono (·+·) f.intercept (f.slope*t) (1+2*(R+s+1))
    (rationalWordWidth_of_height ha') (rationalWordWidth_of_height hp') (rationalWordWidth_of_height hv')
  change 16*W+binary primitive (·*·) f.slope t+binary primitive (·+·) f.intercept (f.slope*t)≤_
  omega

def addRun (primitive : ℕ → ℕ) (W : ℕ) (f g : Affine) : Affine × ℕ :=
  (GeneralPaperRayAffineScoreStep.add f g,32*W+binary primitive (·+·) f.intercept g.intercept+
    binary primitive (·+·) f.slope g.slope)

theorem add_data (primitive : ℕ → ℕ) (W : ℕ) (f g : Affine) :
    (addRun primitive W f g).1=GeneralPaperRayAffineScoreStep.add f g := rfl

theorem add_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W R : ℕ) (f g : Affine)
    (hf : RationalHeight f.intercept R ∧ RationalHeight f.slope R)
    (hg : RationalHeight g.intercept R ∧ RationalHeight g.slope R)
    (hs : RationalHeight (f.intercept+g.intercept) R ∧ RationalHeight (f.slope+g.slope) R) :
    (addRun primitive W f g).2≤32*W+4*primitive (1+2*R) := by
  have ha := binary_le primitive hMono (·+·) f.intercept g.intercept (1+2*R)
    (rationalWordWidth_of_height hf.1) (rationalWordWidth_of_height hg.1) (rationalWordWidth_of_height hs.1)
  have hb := binary_le primitive hMono (·+·) f.slope g.slope (1+2*R)
    (rationalWordWidth_of_height hf.2) (rationalWordWidth_of_height hg.2) (rationalWordWidth_of_height hs.2)
  change 32*W+binary primitive (·+·) f.intercept g.intercept+binary primitive (·+·) f.slope g.slope≤_
  omega

end Blotto.GeneralPaperAffineValuePrice
