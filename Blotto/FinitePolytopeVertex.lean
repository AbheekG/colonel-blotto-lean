import Blotto.RationalOrderCell

/-! A compact finite-coordinate set has an actual midpoint vertex, obtained
by successively maximizing its coordinates. The construction needs no
supplied extreme-point selector and no additional dependency. Applied to the
order cell's maximal-margin face, it gives a positive-margin vertex of the
original cell even when that cell has lower affine dimension. Active-row
full rank and the integer determinant/rational witness are assembled by
the separate active-kernel, square and rational-witness modules. -/

namespace Blotto.FinitePolytopeVertex
open Set RationalOrderCell
open scoped Classical

noncomputable def midpoint {d : Type*} (first second : d → ℝ) : d → ℝ :=
  fun coordinate => (first coordinate + second coordinate) / 2

def MidpointFace {d : Type*} (parent face : Set (d → ℝ)) : Prop :=
  face ⊆ parent ∧ ∀ first second, first ∈ parent → second ∈ parent →
    midpoint first second ∈ face → first ∈ face ∧ second ∈ face

def MidpointVertex {d : Type*} (parent : Set (d → ℝ)) (vertex : d → ℝ) : Prop :=
  vertex ∈ parent ∧ ∀ first second, first ∈ parent → second ∈ parent →
    midpoint first second = vertex → first = vertex ∧ second = vertex

theorem midpointFace_self {d : Type*} (parent : Set (d → ℝ)) : MidpointFace parent parent :=
  ⟨Subset.rfl,fun _ _ hFirst hSecond _ => ⟨hFirst,hSecond⟩⟩

theorem midpointFace_trans {d : Type*} {parent first second : Set (d → ℝ)}
    (hFirst : MidpointFace parent first) (hSecond : MidpointFace first second) : MidpointFace parent second := by
  refine ⟨hSecond.1.trans hFirst.1,?_⟩
  intro a b ha hb hMid
  have hab := hFirst.2 a b ha hb (hSecond.1 hMid)
  exact hSecond.2 a b hab.1 hab.2 hMid

theorem coordinate_max_face {d : Type*} (parent : Set (d → ℝ))
    (hCompact : IsCompact parent) (hNonempty : parent.Nonempty) (coordinate : d) :
    ∃ face : Set (d → ℝ), IsCompact face ∧ face.Nonempty ∧ MidpointFace parent face ∧
      ∀ first ∈ face, ∀ second ∈ face, first coordinate = second coordinate := by
  obtain ⟨maximizer,hMaximizer,hMax⟩ := hCompact.exists_isMaxOn hNonempty (continuous_apply coordinate).continuousOn
  let face : Set (d → ℝ) := {x ∈ parent | x coordinate = maximizer coordinate}
  have hClosed : IsClosed {x : d → ℝ | x coordinate = maximizer coordinate} :=
    isClosed_eq (continuous_apply coordinate) continuous_const
  refine ⟨face,hCompact.inter_right hClosed,⟨maximizer,hMaximizer,rfl⟩,?_,?_⟩
  · refine ⟨fun _ hx => hx.1,?_⟩
    intro first second hFirst hSecond hMid
    have hf := hMax hFirst
    have hs := hMax hSecond
    change first coordinate ≤ maximizer coordinate at hf
    change second coordinate ≤ maximizer coordinate at hs
    have hm := hMid.2
    change (first coordinate + second coordinate) / 2 = maximizer coordinate at hm
    exact ⟨⟨hFirst,by linarith⟩,⟨hSecond,by linarith⟩⟩
  · intro first hFirst second hSecond
    exact hFirst.2.trans hSecond.2.symm

theorem finite_coordinate_face {d : Type*} [DecidableEq d] (parent : Set (d → ℝ))
    (hCompact : IsCompact parent) (hNonempty : parent.Nonempty) (processed : Finset d) :
    ∃ face : Set (d → ℝ), IsCompact face ∧ face.Nonempty ∧ MidpointFace parent face ∧
      ∀ first ∈ face, ∀ second ∈ face, ∀ coordinate ∈ processed, first coordinate = second coordinate := by
  induction processed using Finset.induction_on with
  | empty =>
    refine ⟨parent,hCompact,hNonempty,midpointFace_self parent,?_⟩
    intro first hFirst second hSecond coordinate hCoordinate
    exact False.elim (Finset.notMem_empty coordinate hCoordinate)
  | @insert coordinate processed hFresh ih =>
    obtain ⟨first,hFirstCompact,hFirstNonempty,hFirstFace,hFirstFixed⟩ := ih
    obtain ⟨second,hSecondCompact,hSecondNonempty,hSecondFace,hSecondFixed⟩ :=
      coordinate_max_face first hFirstCompact hFirstNonempty coordinate
    refine ⟨second,hSecondCompact,hSecondNonempty,midpointFace_trans hFirstFace hSecondFace,?_⟩
    intro a ha b hb queried hQueried
    rcases Finset.mem_insert.mp hQueried with rfl | hPrior
    · exact hSecondFixed a ha b hb
    · exact hFirstFixed a (hSecondFace.1 ha) b (hSecondFace.1 hb) queried hPrior

theorem compact_face_has_vertex {d : Type*} [Fintype d] [DecidableEq d]
    (parent face : Set (d → ℝ)) (hCompact : IsCompact face) (hNonempty : face.Nonempty)
    (hFace : MidpointFace parent face) : ∃ vertex ∈ face, MidpointVertex parent vertex := by
  obtain ⟨last,hLastCompact,hLastNonempty,hLastFace,hLastFixed⟩ :=
    finite_coordinate_face face hCompact hNonempty Finset.univ
  obtain ⟨vertex,hVertex⟩ := hLastNonempty
  have hParent := midpointFace_trans hFace hLastFace
  refine ⟨vertex,hLastFace.1 hVertex,hParent.1 hVertex,?_⟩
  intro first second hFirst hSecond hMid
  have hInLast : midpoint first second ∈ last := hMid.symm ▸ hVertex
  have hab := hParent.2 first second hFirst hSecond hInLast
  exact ⟨funext (fun coordinate => hLastFixed first hab.1 vertex hVertex coordinate (Finset.mem_univ _)),
    funext (fun coordinate => hLastFixed second hab.2 vertex hVertex coordinate (Finset.mem_univ _))⟩

/-- This vertex is constructed from the actual order cell and its positive
original point; neither a vertex nor an active subsystem is an input. -/
theorem order_cell_has_positive_vertex {m K : ℕ} (budgets : Fin 2 → ℚ)
    (original : Variable m K → ℝ) (hOriginal : ∀ v, original v ∈ Icc (0 : ℝ) 1) :
    ∃ vertex : Coordinate m K → ℝ, MidpointVertex (polytope budgets original) vertex ∧
      0 < vertex none ∧ ∀ y, FeasibleCell budgets original y → y none ≤ vertex none := by
  obtain ⟨maximizer,hMaximizer,hPositive,hMax⟩ := exists_positive_margin_maximizer budgets original hOriginal
  let parent := polytope budgets original
  let face : Set (Coordinate m K → ℝ) := {x ∈ parent | x none = maximizer none}
  have hCompact : IsCompact face := (polytope_compact budgets original).inter_right
    (isClosed_eq (continuous_apply none) continuous_const)
  have hFace : MidpointFace parent face := by
    refine ⟨fun _ hx => hx.1,?_⟩
    intro first second hFirst hSecond hMid
    have hf := hMax first hFirst
    have hs := hMax second hSecond
    have hm := hMid.2
    change (first none + second none) / 2 = maximizer none at hm
    exact ⟨⟨hFirst,by linarith⟩,⟨hSecond,by linarith⟩⟩
  obtain ⟨vertex,hVertex,hExtreme⟩ := compact_face_has_vertex parent face hCompact
    ⟨maximizer,hMaximizer,rfl⟩ hFace
  exact ⟨vertex,hExtreme,hVertex.2.symm ▸ hPositive,fun y hy => hVertex.2.symm ▸ hMax y hy⟩

end Blotto.FinitePolytopeVertex
