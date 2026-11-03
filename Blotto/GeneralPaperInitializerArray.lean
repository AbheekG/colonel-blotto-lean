import Blotto.GeneralPaperInitializerRootGap

/-! Native stored initializer anchors. Every original labelled anchor is
rounded once into an m-by-K array; the returned reader retains row identity.
Arithmetic counters include quotient work and array/control overhead;
complete fast-bit and abstract live-storage prices remain separate.
-/
namespace Blotto.GeneralPaperInitializerArray
set_option autoImplicit false

structure Result (m K : ℕ) where
  anchors : FixedArrayTable m (FixedArrayTable K ℚ)
  work : ℕ

def build {m K : ℕ} (N depth : ℕ) (input : Fin m → Fin K → ℚ) : Result m K :=
  ⟨FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun l => (GeneralPaperInitializerRounding.run N depth (input j l)).value)),
    m*(K*(12*depth+32)+16)+16⟩

theorem read {m K : ℕ} (N depth : ℕ) (input : Fin m → Fin K → ℚ) (j : Fin m) (l : Fin K) :
    (((build N depth input).anchors.read j).read l)=(GeneralPaperInitializerRounding.run N depth (input j l)).value := by
  simp only [build,FixedArrayTable.read_ofFn]

theorem work {m K : ℕ} (N depth : ℕ) (input : Fin m → Fin K → ℚ) :
    (build N depth input).work=m*(K*(12*depth+32)+16)+16 := rfl

end Blotto.GeneralPaperInitializerArray
