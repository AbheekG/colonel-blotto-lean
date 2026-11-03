import Blotto.BinaryNestedSpecProfile

/-! Actual terminal resource states prepare and compile a complete nested table
and return its endpoints to original coordinate order. Exact source-table
refinement is derived from the stored system/resource words. -/

namespace Blotto.BinaryTerminalProfileCompiler
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryReflectedFourSetup BinaryNestedTerminalInput

def permute {n k : ℕ} (table : Segment n k) (pi : Equiv.Perm (Fin n)) : Segment n k where
  weight := table.weight
  P := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun field => (table.P.read slot).read (pi field)))
  Q := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun field => (table.Q.read slot).read (pi field)))

theorem permute_canonical {n k : ℕ} (table : Segment n k) (pi : Equiv.Perm (Fin n)) (h : table.Canonical) :
    (permute table pi).Canonical := by
  refine ⟨h.1,?_,?_⟩
  · intro slot field; simp only [permute,FixedArrayTable.read_ofFn]; exact h.2.1 _ _
  · intro slot field; simp only [permute,FixedArrayTable.read_ofFn]; exact h.2.2 _ _

theorem permutation_value {n : ℕ} (pi : Equiv.Perm (Fin n)) (row : Fin n → ℚ) (field : Fin n) :
    (RationalAffineAllocation.permutation pi).value row field = row (pi field) := by
  simp [RationalAffineAllocation.value,RationalAffineAllocation.permutation]

theorem permute_refines {n k : ℕ} (table : Segment n k) (pi : Equiv.Perm (Fin n)) (source : RationalSegmentLottery n k)
    (h : table.Refines source) : (permute table pi).Refines (source.mapped (RationalAffineAllocation.permutation pi)) := by
  refine ⟨h.1,?_,?_⟩
  · intro slot field
    simp only [permute,FixedArrayTable.read_ofFn,RationalSegmentLottery.mapped,permutation_value]
    exact h.2.1 _ _
  · intro slot field
    simp only [permute,FixedArrayTable.read_ofFn,RationalSegmentLottery.mapped,permutation_value]
    exact h.2.2 _ _

def profile (system : System) (state : State) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 :=
  permute (BinaryNestedSpecProfile.profile (prepare system state) K bits) (permutation system state)

theorem profile_canonical (system : System) (state : State) (hC : system.Canonical)
    (hState : ∀ j, CanonicalWord (state.resource.read j)) (K : ℕ) (bits : Fin K → Bool) :
    (profile system state K bits).Canonical :=
  permute_canonical _ _ (BinaryNestedSpecProfile.profile_canonical _ (prepare_canonical system state hC hState) K bits)

theorem profile_refines (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hr : DataRefines system state source) (K : ℕ) (bits : Fin K → Bool) :
    (profile system state K bits).Refines (source.profile K bits) := by
  have he := BinaryNestedSpecProfile.profile_refines _ _ (prepare_canonical system state hC hState)
    (prepare_refines system state source hC hState hr) K bits
  have ht := permute_refines _ (permutation system state) _ he
  simpa only [profile,RationalTerminalResources.profile,permutation_refines system state source hC hState hr] using ht

theorem profile_endpoints (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hr : DataRefines system state source) (K : ℕ) (bits : Fin K → Bool) (slot : Fin 18) :
    FullBudget (value system.M : ℝ) (fun field => (value (((profile system state K bits).P.read slot).read field) : ℝ)) ∧
      FullBudget (value system.M : ℝ) (fun field => (value (((profile system state K bits).Q.read slot).read field) : ℝ)) := by
  have he := profile_refines system state source hC hState hr K bits
  have hp : (fun field => (value (((profile system state K bits).P.read slot).read field) : ℝ)) = (source.profile K bits).real.P slot := by
    funext field; exact congrArg (fun q : ℚ => (q : ℝ)) (he.2.1 slot field)
  have hq : (fun field => (value (((profile system state K bits).Q.read slot).read field) : ℝ)) = (source.profile K bits).real.Q slot := by
    funext field; exact congrArg (fun q : ℚ => (q : ℝ)) (he.2.2 slot field)
  rw [hp,hq,hr.1]
  exact source.profile_endpoints K bits slot

theorem profile_box (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hr : DataRefines system state source) (K : ℕ) (bits : Fin K → Bool) (slot : Fin 18) :
    InBox (fun field => (value (system.long.read field) : ℝ))
      (fun field => (value (((profile system state K bits).P.read slot).read field) : ℝ)) ∧
    InBox (fun field => (value (system.long.read field) : ℝ))
      (fun field => (value (((profile system state K bits).Q.read slot).read field) : ℝ)) := by
  have he := profile_refines system state source hC hState hr K bits
  have hl : (fun field => (value (system.long.read field) : ℝ)) = fun field => (source.long field : ℝ) := by
    funext field; exact congrArg (fun q : ℚ => (q : ℝ)) (hr.2.1 field)
  have hp : (fun field => (value (((profile system state K bits).P.read slot).read field) : ℝ)) = (source.profile K bits).real.P slot := by
    funext field; exact congrArg (fun q : ℚ => (q : ℝ)) (he.2.1 slot field)
  have hq : (fun field => (value (((profile system state K bits).Q.read slot).read field) : ℝ)) = (source.profile K bits).real.Q slot := by
    funext field; exact congrArg (fun q : ℚ => (q : ℝ)) (he.2.2 slot field)
  rw [hl,hp,hq]
  exact source.profile_box K bits slot

end Blotto.BinaryTerminalProfileCompiler
