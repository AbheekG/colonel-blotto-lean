import Blotto.PlayerSpecificAlgebraicNestedTerminalSizes

/-! Actual terminal nested sampling restores the reached focus swap.
Every bit string has the required budget and the original long-length box. -/
namespace Blotto.PlayerSpecificAlgebraicNestedTerminalDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedTerminalInput
open PlayerSpecificAlgebraicNestedTerminalSizes PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def restore (p : Equiv.Perm (Fin 3)) (y : FixedArrayTable 3 Data) : FixedArrayTable 3 Data :=
  FixedArrayTable.ofFn (fun j => y.read (p j))

theorem restore_value (p : Equiv.Perm (Fin 3)) (y : FixedArrayTable 3 Data) (x : ℝ) :
    values (restore p y) x=permuteAllocation p (values y x) := by
  funext j
  simp only [PlayerSpecificAlgebraicSegment.values,restore,FixedArrayTable.read_ofFn,permuteAllocation]

def draw (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin ((17*H+K)+K) → Bool) : FixedArrayTable 3 Data :=
  let p := prepare model root a
  let y := PlayerSpecificAlgebraicNestedSpecDraw.draw model root p.input H K bits
  restore p.permutation y

theorem every_path (model : RationalCostModel) (root : Candidate) (a : Input) (i : TerminalResources)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedTerminalInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    FullBudget i.M (values (draw model root a H K bits) x) ∧ InBox i.long (values (draw model root a H K bits) x) := by
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let p := prepare model root a
  let y := PlayerSpecificAlgebraicNestedSpecDraw.draw model root p.input H K bits
  have hp := PlayerSpecificAlgebraicNestedTerminalInput.values model root a i hm hirr hv x hx ha (fun j => (hfit.capacity j).1)
  have hf := PlayerSpecificAlgebraicNestedTerminalSizes.bounds model root a T hfit hm hm0 hml hmT (by omega)
  have hi : T ≤ step T := (Nat.le_succ _).trans (large T)
  have hy := PlayerSpecificAlgebraicNestedSpecDraw.every_path model root p.input i.input hm hirr hv x hx hp.1
    (step T) hf hml (mono hmT hi) (hT.trans hi) H K bits
  have hrestore : values (draw model root a H K bits) x=permuteAllocation i.permutation (values y x) := by
    change values (restore p.permutation y) x=_
    rw [restore_value,hp.2]
  rw [hrestore]
  refine ⟨permuteAllocation_fullBudget i.permutation hy.1,?_⟩
  have caps : ∀ j : Fin 3, (![i.input.a,i.input.d,i.input.c] j) ≤ (permuteAllocation i.permutation i.long) j := by
    intro j
    fin_cases j
    · exact i.endpoint_long _
    · exact i.endpoint_long _
    · change i.long i.focus ≤ i.long (i.permutation 2)
      rw [i.permutation_last]
  have hb := inBox_mono caps hy.2
  intro j
  have hj := hb (i.permutation j)
  simpa only [permuteAllocation,TerminalResources.permutation,Equiv.swap_apply_self] using hj

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    ∀ j,Reduced root.polynomial ((draw model root a H K bits).read j) ∧
      HasHeight ((draw model root a H K bits).read j) (PlayerSpecificAlgebraicNestedInteriorDraw.height (step T) K) := by
  let p := prepare model root a
  have hf := PlayerSpecificAlgebraicNestedTerminalSizes.bounds model root a T ha hm hm0 hml hmT (by omega)
  have hi : T ≤ step T := (Nat.le_succ _).trans (large T)
  have hy := PlayerSpecificAlgebraicNestedSpecDraw.heights model root p.input (step T) hf hm hm0 hml
    (mono hmT hi) (hT.trans hi) H K bits
  have hr := PlayerSpecificAlgebraicNestedSpecDraw.reduced model root p.input H K bits hm hm0
  intro j
  simp only [draw,restore,FixedArrayTable.read_ofFn]
  exact ⟨hr _,hy _⟩

end Blotto.PlayerSpecificAlgebraicNestedTerminalDraw
