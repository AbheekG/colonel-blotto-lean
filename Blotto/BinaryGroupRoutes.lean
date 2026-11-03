import Blotto.BinaryGreedyPacking
import Blotto.PreparedGroupOutput

/-! Native cached routes are prepared by traversing each group's members and
stored total once. Emission reads one route and one sampled group coordinate;
it performs no member search or group summation. Array copy/ownership prices
remain separate from exact native semantics. -/

namespace Blotto.BinaryGroupRoutes
open BinaryRationalNormalization BinaryRationalEncoding

abbrev Route (m : ℕ) := Option (Fin m) × SignedWord

def assignments {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) : List (Fin n × Route m) :=
  (List.finRange m).flatMap (fun g => (groups.read g).1.map (fun j =>
    (j,(some g,BinaryRationalOpcode.apply .div (length.read j) (groups.read g).2))))

def prepare {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) : FixedArrayTable n (Route m) :=
  (FixedArrayTable.ofFn (fun _ => (none,BinaryRationalOpcode.zero))).patch (assignments length groups)

noncomputable def routeValue {m : ℕ} (route : Route m) : GroupRoute m := (route.1,value route.2)

theorem assignments_refines {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (source : RationalProportionalGroups n m)
    (hLength : ∀ j, CanonicalWord (length.read j)) (hTotals : ∀ g, CanonicalWord (groups.read g).2)
    (hL : ∀ j, value (length.read j)=source.length j) (hM : ∀ g, (groups.read g).1=source.members g)
    (hT : ∀ g, value (groups.read g).2=source.total g) :
    (assignments length groups).map (fun entry => (entry.1,routeValue entry.2)) = source.routeAssignments := by
  unfold assignments RationalProportionalGroups.routeAssignments
  rw [List.map_flatMap]
  apply congrArg (List.flatMap · (List.finRange m))
  funext g
  rw [List.map_map,hM g]
  apply congrArg (List.map · (source.members g))
  funext j
  simp only [Function.comp_def,routeValue]
  rw [BinaryRationalOpcode.apply_value .div _ _ (hLength j).1 (hTotals g).1,hL j,hT g]
  rfl

theorem patch_refines {n m : ℕ} (table : FixedArrayTable n (Route m)) (source : FixedArrayTable n (GroupRoute m))
    (h : ∀ j, routeValue (table.read j)=source.read j) (entries : List (Fin n × Route m)) :
    ∀ j, routeValue ((table.patch entries).read j)=
      (source.patch (entries.map (fun entry => (entry.1,routeValue entry.2)))).read j := by
  induction entries generalizing table source with
  | nil => exact h
  | cons entry entries ih =>
    apply ih
    intro j
    rw [FixedArrayTable.read_write,FixedArrayTable.read_write]
    split_ifs
    · rfl
    · exact h j

theorem prepare_refines {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (source : RationalProportionalGroups n m)
    (hLength : ∀ j, CanonicalWord (length.read j)) (hTotals : ∀ g, CanonicalWord (groups.read g).2)
    (hL : ∀ j, value (length.read j)=source.length j) (hM : ∀ g, (groups.read g).1=source.members g)
    (hT : ∀ g, value (groups.read g).2=source.total g) :
    ∀ j, routeValue ((prepare length groups).read j)=source.routes.read j := by
  have he := patch_refines (FixedArrayTable.ofFn (fun _ : Fin n => (none,BinaryRationalOpcode.zero)))
    (FixedArrayTable.ofFn (fun _ => (none,0))) (by
      intro j; simp only [FixedArrayTable.read_ofFn,routeValue]; rw [BinaryRationalOpcode.zero_value])
    (assignments length groups)
  rw [assignments_refines length groups source hLength hTotals hL hM hT] at he
  exact he

theorem patch_canonical {n m : ℕ} (table : FixedArrayTable n (Route m))
    (h : ∀ j, CanonicalWord (table.read j).2) (entries : List (Fin n × Route m))
    (he : ∀ entry ∈ entries, CanonicalWord entry.2.2) : ∀ j, CanonicalWord ((table.patch entries).read j).2 := by
  induction entries generalizing table with
  | nil => exact h
  | cons entry entries ih =>
    apply ih
    · intro j
      rw [FixedArrayTable.read_write]
      split
      · exact he entry (by simp)
      · exact h j
    · intro next hn
      exact he next (by simp [hn])

theorem prepare_canonical {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (hLength : ∀ j, CanonicalWord (length.read j)) (hTotals : ∀ g, CanonicalWord (groups.read g).2) :
    ∀ j, CanonicalWord ((prepare length groups).read j).2 := by
  apply patch_canonical
  · intro j; rw [FixedArrayTable.read_ofFn]
    change CanonicalWord BinaryRationalOpcode.zero
    exact ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  · intro entry he
    obtain ⟨g,hg,he⟩ := List.mem_flatMap.mp he
    obtain ⟨item,hi,hEntry⟩ := List.mem_map.mp he
    subst entry
    exact BinaryReflectedFourSetup.opcode_canonical .div _ _ (hLength item) (hTotals g)

def emit {n m : ℕ} (routes : FixedArrayTable n (Route m)) (sampled : FixedArrayTable m SignedWord) : FixedArrayTable n SignedWord :=
  FixedArrayTable.ofFn (fun j => match (routes.read j).1 with
    | none => BinaryRationalOpcode.zero
    | some g => BinaryRationalOpcode.apply .mul (routes.read j).2 (sampled.read g))

theorem emit_canonical {n m : ℕ} (routes : FixedArrayTable n (Route m)) (sampled : FixedArrayTable m SignedWord)
    (hRoutes : ∀ j, CanonicalWord (routes.read j).2) (hSampled : ∀ g, CanonicalWord (sampled.read g)) :
    ∀ j, CanonicalWord ((emit routes sampled).read j) := by
  intro j
  rw [emit,FixedArrayTable.read_ofFn]
  split
  · exact ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  · exact BinaryReflectedFourSetup.opcode_canonical .mul _ _ (hRoutes j) (hSampled _)

theorem emit_refines {n m : ℕ} (routes : FixedArrayTable n (Route m)) (sampled : FixedArrayTable m SignedWord)
    (source : RationalProportionalGroups n m) (hRoutes : ∀ j, CanonicalWord (routes.read j).2)
    (hSampled : ∀ g, CanonicalWord (sampled.read g)) (hr : ∀ j, routeValue (routes.read j)=source.routes.read j) (j : Fin n) :
    value ((emit routes sampled).read j) = (source.emit source.routes (fun g => value (sampled.read g))).allocation j := by
  rw [emit,FixedArrayTable.read_ofFn,RationalProportionalGroups.emit,RationalResourceArray.allocation_ofAllocation]
  rw [← hr j]
  unfold routeValue
  dsimp only
  cases hRoute : (routes.read j).1 with
  | none => exact BinaryRationalOpcode.zero_value
  | some g =>
    rw [BinaryRationalOpcode.apply_value .mul _ _ (hRoutes j).1 (hSampled _).1]
    rfl

def emitMixed {n m : ℕ} (routes : FixedArrayTable n (Route m)) (pivot : Fin n)
    (sampled : FixedArrayTable (m+1) SignedWord) : FixedArrayTable n SignedWord :=
  let uniform := FixedArrayTable.ofFn (fun g : Fin m => sampled.read g.castSucc)
  let old := emit routes uniform
  old.write pivot (BinaryRationalOpcode.apply .add (old.read pivot) (sampled.read (Fin.last m)))

theorem emitMixed_canonical {n m : ℕ} (routes : FixedArrayTable n (Route m)) (pivot : Fin n)
    (sampled : FixedArrayTable (m+1) SignedWord) (hRoutes : ∀ j, CanonicalWord (routes.read j).2)
    (hSampled : ∀ g, CanonicalWord (sampled.read g)) :
    ∀ j, CanonicalWord ((emitMixed routes pivot sampled).read j) := by
  have he := emit_canonical routes (FixedArrayTable.ofFn (fun g : Fin m => sampled.read g.castSucc)) hRoutes
    (fun g => by rw [FixedArrayTable.read_ofFn]; exact hSampled _)
  intro j
  rw [emitMixed,FixedArrayTable.read_write]
  split
  · exact BinaryReflectedFourSetup.opcode_canonical .add _ _ (he pivot) (hSampled _)
  · exact he j

theorem emitMixed_refines {n m : ℕ} (routes : FixedArrayTable n (Route m)) (pivot : Fin n)
    (sampled : FixedArrayTable (m+1) SignedWord) (source : RationalProportionalGroups n m)
    (hRoutes : ∀ j, CanonicalWord (routes.read j).2) (hSampled : ∀ g, CanonicalWord (sampled.read g))
    (hr : ∀ j, routeValue (routes.read j)=source.routes.read j) (j : Fin n) :
    value ((emitMixed routes pivot sampled).read j) =
      (source.emitMixed source.routes pivot (fun g => value (sampled.read g))).allocation j := by
  let uniform := FixedArrayTable.ofFn (fun g : Fin m => sampled.read g.castSucc)
  have hUniform : ∀ g, CanonicalWord (uniform.read g) := by intro g; rw [FixedArrayTable.read_ofFn]; exact hSampled _
  have he := emit_refines routes uniform source hRoutes hUniform hr
  have hc := emit_canonical routes uniform hRoutes hUniform
  rw [RationalProportionalGroups.emitMixed_allocation_add]
  unfold emitMixed
  rw [FixedArrayTable.read_write]
  by_cases hj : j=pivot
  · rw [ite_eq_left hj,hj,ite_eq_left rfl]
    rw [BinaryRationalOpcode.apply_value .add _ _ (hc pivot).1 (hSampled _).1,he]
    simp only [RealArithmeticOp.applyRat,uniform,FixedArrayTable.read_ofFn]
  · rw [ite_eq_right hj,ite_eq_right hj,add_zero]
    simpa only [uniform,FixedArrayTable.read_ofFn] using he j

theorem emit_fullBudget {n m : ℕ} (routes : FixedArrayTable n (Route m)) (sampled : FixedArrayTable m SignedWord)
    (source : RationalProportionalGroups n m) (hRoutes : ∀ j, CanonicalWord (routes.read j).2)
    (hSampled : ∀ g, CanonicalWord (sampled.read g)) (hr : ∀ j, routeValue (routes.read j)=source.routes.read j)
    (B : ℚ) (hBudget : FullBudget (B : ℝ) (fun g => (value (sampled.read g) : ℝ))) :
    FullBudget (B : ℝ) (fun j => (value ((emit routes sampled).read j) : ℝ)) := by
  have he : (fun j => (value ((emit routes sampled).read j) : ℝ)) =
      (source.emit source.routes (fun g => value (sampled.read g))).realAllocation := by
    funext j
    exact congrArg (fun q : ℚ => (q : ℝ)) (emit_refines routes sampled source hRoutes hSampled hr j)
  rw [he]
  exact source.emit_fullBudget hBudget

theorem emitMixed_fullBudget {n m : ℕ} (routes : FixedArrayTable n (Route m)) (pivot : Fin n)
    (sampled : FixedArrayTable (m+1) SignedWord) (source : RationalProportionalGroups n m)
    (hRoutes : ∀ j, CanonicalWord (routes.read j).2) (hSampled : ∀ g, CanonicalWord (sampled.read g))
    (hr : ∀ j, routeValue (routes.read j)=source.routes.read j) (B : ℚ)
    (hBudget : FullBudget (B : ℝ) (fun g => (value (sampled.read g) : ℝ))) :
    FullBudget (B : ℝ) (fun j => (value ((emitMixed routes pivot sampled).read j) : ℝ)) := by
  have he : (fun j => (value ((emitMixed routes pivot sampled).read j) : ℝ)) =
      (source.emitMixed source.routes pivot (fun g => value (sampled.read g))).realAllocation := by
    funext j
    exact congrArg (fun q : ℚ => (q : ℝ)) (emitMixed_refines routes pivot sampled source hRoutes hSampled hr j)
  rw [he]
  exact source.emitMixed_fullBudget pivot hBudget

end Blotto.BinaryGroupRoutes
