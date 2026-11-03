import Blotto.PlayerSpecificAlgebraicLeafPartition

/-! Direct allocation to original leaves computes one original-length /
cached-group-total quotient and one product for each group member. A
native array is patched once; the optional fractional coordinate is copied.
There is no chain of recursive proportional products. -/
namespace Blotto.PlayerSpecificAlgebraicLeafAssignments
open PlayerSpecificDensePolynomial PlayerSpecificAlgebraicGrouping PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def slot {m : ℕ} (g : Fin m) : Fin 4 := Fin.ofNat 4 g.val

def assignments {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) : List (Fin N × Data) :=
  (List.finRange groups.length).flatMap (fun g => (groups.get g).members.map (fun j =>
    (j,PlayerSpecificAlgebraicField.times root.polynomial
      (PlayerSpecificAlgebraicField.divide root.polynomial (length j) (groups.get g).total) (y.read (slot g)))))

def emit {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) : FixedArrayTable N Data :=
  (FixedArrayTable.ofFn (fun _ => [])).patch (assignments root length groups y)

def emitMixed {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (fractional : Option (Fin N)) (y : FixedArrayTable 4 Data) : FixedArrayTable N Data :=
  let result := emit root length groups y
  match fractional with
  | none => result
  | some j => result.write j (y.read 3)

theorem mem_assignments {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (e : Fin N × Data) :
    e ∈ assignments root length groups y ↔ ∃ g : Fin groups.length,e.1 ∈ (groups.get g).members ∧
      e.2=PlayerSpecificAlgebraicField.times root.polynomial
        (PlayerSpecificAlgebraicField.divide root.polynomial (length e.1) (groups.get g).total) (y.read (slot g)) := by
  simp only [assignments,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  constructor
  · rintro ⟨g,j,hj,he⟩
    cases he
    exact ⟨g,hj,rfl⟩
  · rintro ⟨g,hj,he⟩
    refine ⟨g,e.1,hj,?_⟩
    exact Prod.ext rfl he.symm

theorem keys {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (j : Fin N) :
    j ∈ (assignments root length groups y).map Prod.fst ↔ ∃ g : Fin groups.length,j ∈ (groups.get g).members := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e,he,hj⟩
    obtain ⟨g,hg,_⟩ := (mem_assignments root length groups y e).mp he
    exact ⟨g,hj ▸ hg⟩
  · rintro ⟨g,hj⟩
    refine ⟨(j,PlayerSpecificAlgebraicField.times root.polynomial
      (PlayerSpecificAlgebraicField.divide root.polynomial (length j) (groups.get g).total) (y.read (slot g))),?_,rfl⟩
    exact (mem_assignments root length groups y _).mpr ⟨g,hj,rfl⟩

theorem emit_group {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (hn : (groups.map Group.members).flatten.Nodup)
    (g : Fin groups.length) (j : Fin N) (hj : j ∈ (groups.get g).members) :
    (emit root length groups y).read j=PlayerSpecificAlgebraicField.times root.polynomial
      (PlayerSpecificAlgebraicField.divide root.polynomial (length j) (groups.get g).total) (y.read (slot g)) := by
  apply FixedArrayTable.read_patch_at
  · intro e he hej
    obtain ⟨h,hm,hv⟩ := (mem_assignments root length groups y e).mp he
    have hsame := PlayerSpecificAlgebraicLeafPartition.indices_unique groups hn h g j (hej ▸ hm) hj
    rw [hv,hej,hsame]
  · exact (keys root length groups y j).mpr ⟨g,hj⟩

theorem emit_inactive {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (j : Fin N) (hj : ∀ g : Fin groups.length,j ∉ (groups.get g).members) :
    (emit root length groups y).read j=[] := by
  have he : j ∉ (assignments root length groups y).map Prod.fst := by
    rw [keys]
    rintro ⟨g,hg⟩
    exact hj g hg
  rw [emit,FixedArrayTable.patch_preserves _ _ _ he,FixedArrayTable.read_ofFn]

theorem emitMixed_pivot {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (j : Fin N) : (emitMixed root length groups (some j) y).read j=y.read 3 := by
  simp only [emitMixed,FixedArrayTable.read_write,ite_true]

theorem emitMixed_other {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N))
    (y : FixedArrayTable 4 Data) (pivot j : Fin N) (hj : j ≠ pivot) :
    (emitMixed root length groups (some pivot) y).read j=(emit root length groups y).read j := by
  simp only [emitMixed,FixedArrayTable.read_write,ite_eq_right hj]

end Blotto.PlayerSpecificAlgebraicLeafAssignments
