import Blotto.GeneralPaperBasisAppendCache
import Blotto.RationalLatticeWords

/-! Executable original-grid packing uses the forward coordinate index
only. The auxiliary budget numerator is computed directly from the
initializer controls, including the reciprocal normalization branch.
-/
namespace Blotto.GeneralPaperBasisGridInputs
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisCoordinates
set_option autoImplicit false
set_option maxHeartbeats 3500000

def pack {m K : ℕ} (value : Variable m K → ℤ) : Vector (m*(K-1)) :=
  (FixedArrayTable.ofFn (fun _ => 0)).patch
    ((GeneralPaperStaticRayRows.variableList m K).map (fun v => (index v,value v)))

theorem pack_read {m K : ℕ} (value : Variable m K → ℤ) (v : Variable m K) :
    (pack value).read (index v)=value v := by
  unfold pack
  apply FixedArrayTable.read_patch_at
  · intro e he hKey
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp he
    have hu : u=v := index_injective m K hKey
    exact congrArg value hu
  · apply List.mem_map.mpr
    refine ⟨(index v,value v),?_,rfl⟩
    exact List.mem_map.mpr ⟨v,GeneralPaperStaticRayRows.variableList_mem m K v,rfl⟩

def grid {m K : ℕ} (N : ℕ) (initial : Variable m K → ℚ) : Vector (m*(K-1)) :=
  pack (fun v => latticeNumerator N (initial v))

theorem grid_decode {m K : ℕ} (N : ℕ) (hN : 0<N) (initial : Variable m K → ℚ)
    (hGrid : ∀ v,OnRationalLattice N (initial v)) (v : Variable m K) :
    ((grid N initial).read (index v):ℚ)/(N:ℚ)=initial v := by
  rw [grid,pack_read]
  exact latticeNumerator_decode hN (hGrid v)

theorem grid_bounds {m K : ℕ} (N : ℕ) (initial : Variable m K → ℚ)
    (hGrid : ∀ v,OnRationalLattice N (initial v)) (hUnit : ∀ v,0 ≤ initial v ∧ initial v ≤ 1)
    (k : Fin (m*(K-1))) :
    0≤(grid N initial).read k ∧ (grid N initial).read k≤(N:ℤ) := by
  obtain ⟨v,rfl⟩ := index_surjective m K k
  rw [grid,pack_read]
  exact latticeNumerator_bounds (hGrid v) (hUnit v)

def auxiliaryNumerator (m H p q : ℕ) (reciprocal : Bool) : ℤ :=
  ((4*m*H*(if reciprocal then q*q else p*p):ℕ):ℤ)-(m:ℤ)

theorem auxiliary_scaled (m H p q : ℕ) (reciprocal : Bool)
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    (auxiliaryNumerator m H p q reciprocal:ℚ)=
      (GeneralPaperInitializerParameters.prepare m H p q reciprocal).auxiliary*
        ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).N:ℚ) := by
  have hN : ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).N:ℚ)≠0 := by
    exact_mod_cast (GeneralPaperInitializerParameters.N_positive m H p q reciprocal hm hH hp hq).ne'
  rw [(GeneralPaperInitializerParameters.data m H p q reciprocal).2.2.2,
    sub_mul,GeneralPaperInitializerParameters.scaled_budget m H p q reciprocal hp hq,
    (GeneralPaperInitializerParameters.data m H p q reciprocal).2.2.1,div_mul_cancel₀ _ hN]
  simp only [auxiliaryNumerator,Int.cast_sub,Int.cast_natCast]

theorem auxiliary_decode (m H p q : ℕ) (reciprocal : Bool)
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    (auxiliaryNumerator m H p q reciprocal:ℚ)/
      ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).N:ℚ)=
        (GeneralPaperInitializerParameters.prepare m H p q reciprocal).auxiliary := by
  rw [auxiliary_scaled m H p q reciprocal hm hH hp hq]
  apply mul_div_cancel_right₀
  exact_mod_cast (GeneralPaperInitializerParameters.N_positive m H p q reciprocal hm hH hp hq).ne'

end Blotto.GeneralPaperBasisGridInputs
