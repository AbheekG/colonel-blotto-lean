import Blotto.GeneralPaperBasisUpdateOperandSize

/-! Actual source-derived fixed-grid and auxiliary-numerator bounds.
The grid/unit and ratio-cap premises come from the actual source and
classifier, rather than supplied size certificates.
-/
namespace Blotto.GeneralPaperSourceBasisGridSize
open GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls
open GeneralPaperBasisStoredProducts
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

def auxiliaryBound (m k : ℕ) : ℕ := 4*m*(prepare m k).H*(prepare m k).qbar*(prepare m k).qbar+m

theorem auxiliary {m : ℕ} (k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    (GeneralPaperBasisGridInputs.auxiliaryNumerator m (prepare m k).H f.num f.den reciprocal).natAbs≤auxiliaryBound m k := by
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hp : f.num≤(prepare m k).qbar := hf.2.1.le.trans hf.2.2
  have hq : f.den≤(prepare m k).qbar := hf.2.2
  have hs : (if reciprocal then f.den*f.den else f.num*f.num)≤(prepare m k).qbar*(prepare m k).qbar := by
    cases reciprocal
    · exact Nat.mul_le_mul hp hp
    · exact Nat.mul_le_mul hq hq
  have hc := Nat.mul_le_mul_left (4*m*(prepare m k).H) hs
  have hh := Int.natAbs_add_le ((4*m*(prepare m k).H*(if reciprocal then f.den*f.den else f.num*f.num):ℕ):ℤ) (-(m:ℤ))
  simp only [Int.natAbs_natCast,Int.natAbs_neg] at hh
  change (GeneralPaperBasisGridInputs.auxiliaryNumerator m (prepare m k).H f.num f.den reciprocal).natAbs≤_
  unfold GeneralPaperBasisGridInputs.auxiliaryNumerator auxiliaryBound
  simpa only [←sub_eq_add_neg,Nat.mul_assoc] using hh.trans (Nat.add_le_add_right hc m)

theorem grid {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) f.num f.den reciprocal
    ∀ a,(inputs.initialGrid.read a).natAbs≤ inputs.controls.N := by
  have hSource := GeneralPaperSourceInitializer.sound k Qv hm hQv weights hp hs b hb reciprocal
  have hGrid (a : RationalOrderCell.Variable m (prepare m k).K) :
      OnRationalLattice (controls m k b reciprocal).N (GeneralPaperSourceBasis.initialCoordinates k Qv hQv weights hp hs b reciprocal a) := hSource.2.2 a.1 _
  have hUnit (a : RationalOrderCell.Variable m (prepare m k).K) :
      0≤GeneralPaperSourceBasis.initialCoordinates k Qv hQv weights hp hs b reciprocal a ∧
        GeneralPaperSourceBasis.initialCoordinates k Qv hQv weights hp hs b reciprocal a≤1 :=
    ⟨hSource.1.nonnegative a.1 _,hSource.1.bounded a.1 _⟩
  change ∀ a,((GeneralPaperBasisGridInputs.grid (controls m k b reciprocal).N
    (GeneralPaperSourceBasis.initialCoordinates k Qv hQv weights hp hs b reciprocal)).read a).natAbs≤
      (controls m k b reciprocal).N
  intro a
  have hh := GeneralPaperBasisGridInputs.grid_bounds (controls m k b reciprocal).N
    (GeneralPaperSourceBasis.initialCoordinates k Qv hQv weights hp hs b reciprocal) hGrid hUnit a
  have ha : (((GeneralPaperBasisGridInputs.grid (controls m k b reciprocal).N
      (GeneralPaperSourceBasis.initialCoordinates k Qv hQv weights hp hs b reciprocal)).read a).natAbs:ℤ)≤
        ((controls m k b reciprocal).N:ℤ) := by
    rw [Int.natCast_natAbs,abs_of_nonneg hh.1]
    exact hh.2
  exact_mod_cast ha

end Blotto.GeneralPaperSourceBasisGridSize
