import Blotto.GeneralPaperInitializerArray

/-! Hard-budget and order guarantees for the actual stored rounded
dictionary. The original whole-row labels are unchanged; every high tuple
loses strictly less than m/N, giving the auxiliary-budget polytope point.
-/
namespace Blotto.GeneralPaperInitializerDictionary
open GeneralPaperDictionary GeneralPaperTransferPreparation GeneralPaperAffineConstraintRows
open GeneralPaperTransferPolytopePoint
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

def build {T m K : ℕ} (d : Dictionary T m K) (N depth : ℕ) : Dictionary T m K :=
  let a := GeneralPaperInitializerArray.build N depth d.anchor
  GeneralPaperStrictScore.replace d (fun j l => (a.anchors.read j).read l)

theorem field {T m K : ℕ} (d : Dictionary T m K) (N depth : ℕ) (j : Fin m) (l : Fin K) :
    (build d N depth).anchor j l=(GeneralPaperInitializerRounding.run N depth (d.anchor j l)).value :=
  GeneralPaperInitializerArray.read N depth d.anchor j l

theorem labels {T m K : ℕ} (d : Dictionary T m K) (N depth : ℕ) : (build d N depth).label=d.label := rfl

theorem unit {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hu : UnitDictionary d hT hK) (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) :
    UnitDictionary (build d N depth) hT hK := by
  have hBounds (j : Fin m) (l : Fin K) := GeneralPaperInitializerRounding.bounds N depth hN hCap (d.anchor j l)
    ⟨hu.nonnegative j l,hu.bounded j l⟩
  have hf (i : Fin T) : Blotto.Feasible 1 ((law (build d N depth) hT).realRow i) := by
    refine ⟨?_,?_⟩
    · intro j
      change (0:ℝ)≤((build d N depth).anchor j (d.label i j):ℝ)
      rw [field]
      exact_mod_cast (hBounds j (d.label i j)).1
    · apply le_trans (b:=cost d (d.label i))
      · apply Finset.sum_le_sum
        intro j hj
        change ((build d N depth).anchor j (d.label i j):ℝ)≤(d.anchor j (d.label i j):ℝ)
        rw [field]
        exact_mod_cast (hBounds j (d.label i j)).2.1
      · exact (hu.feasible i).2
  refine ⟨hu.balanced,?_,?_,?_,?_,hf,?_⟩
  · intro j
    rw [field,hu.zero,GeneralPaperInitializerRounding.zero N depth hN hCap]
  · intro j l r hlr
    rw [field,field]
    exact GeneralPaperInitializerRounding.monotone N depth hN hCap _ _
      ⟨hu.nonnegative j l,hu.bounded j l⟩ ⟨hu.nonnegative j r,hu.bounded j r⟩ (hu.ordered j hlr)
  · intro j l
    rw [field]
    exact (hBounds j l).1
  · intro j l
    rw [field]
    exact (hBounds j l).2.1.trans (hu.bounded j l)
  · exact RationalWholeRowLaw.law_supported _ 1 hf

theorem tuple_loss {T m K : ℕ} (hm : 0<m) (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hu : UnitDictionary d hT hK) (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) (l : Fin m → Fin K) :
    cost d l-(m:ℝ)/N<cost (build d N depth) l := by
  have ht := GeneralPaperInitializerRounding.tuple_loss hm N depth hN hCap (fun j => d.anchor j (l j))
    (fun j => ⟨hu.nonnegative j (l j),hu.bounded j (l j)⟩)
  have he : (∑ j,(build d N depth).anchor j (l j))=∑ j,(GeneralPaperInitializerRounding.run N depth (d.anchor j (l j))).value := by
    exact Finset.sum_congr rfl (fun j _ => field d N depth j (l j))
  rw [←he] at ht
  change (∑ j,(d.anchor j (l j):ℝ))-(m:ℝ)/N<∑ j,((build d N depth).anchor j (l j):ℝ)
  have hr := (Rat.cast_lt (K:=ℝ)).mpr ht
  simpa only [Rat.cast_sub,Rat.cast_sum,Rat.cast_div,Rat.cast_natCast] using hr

theorem lattice {T m K : ℕ} (d : Dictionary T m K) (N depth : ℕ) (hN : 0<N) (j : Fin m) (l : Fin K) :
    OnRationalLattice N ((build d N depth).anchor j l) := by
  rw [field]
  exact GeneralPaperInitializerRounding.lattice N depth hN _

theorem auxiliary_feasible {T m K : ℕ} (hm : 0<m) (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hu : UnitDictionary d hT hK) (scores : Fin m → Fin K → ℕ) (h : ℕ) (beta : ℚ)
    (hBad : ∀ l : HighTuple scores h,(beta:ℝ)≤cost d l.val)
    (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) :
    GeneralPaperAffineConstraintRows.Feasible d.label scores h ((beta:ℝ)-(m:ℝ)/N) (coordinates (build d N depth)) := by
  apply dictionary_feasible (build d N depth) hT hK (unit d hT hK hu N depth hN hCap) scores h _
  intro l
  have hl := tuple_loss hm d hT hK hu N depth hN hCap l.val
  have hb := hBad l
  linarith only [hl,hb]

end Blotto.GeneralPaperInitializerDictionary
