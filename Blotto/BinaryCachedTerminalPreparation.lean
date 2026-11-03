import Blotto.BinaryTerminalClassificationWork

/-! One terminal classification/packing pass supplies a stored group count,
member/total table, total array, routes and pivot data. The old group count and
packing occur only in erased correctness proofs. Runtime samplers use the
stored count and words, without rebuilding grouping inside group-input reads.
Route construction and descriptor/sampling/storage prices remain separate. -/

namespace Blotto.BinaryCachedTerminalPreparation
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryTerminalGrouping BinaryTerminalClassificationWork

def castTable {m k : ℕ} {α : Type*} (h : m = k) (table : FixedArrayTable m α) : FixedArrayTable k α := h ▸ table
def castRoutes {n m k : ℕ} (h : m = k) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    FixedArrayTable n (BinaryGroupRoutes.Route k) := h ▸ routes

theorem castTable_data {m k : ℕ} {α : Type*} (h : m = k) (table : FixedArrayTable m α) :
    (castTable h table).data = table.data := by cases h; rfl

theorem castTable_read {m k : ℕ} {α : Type*} (h : m = k) (table : FixedArrayTable m α) (j : Fin m) :
    (castTable h table).read (j.cast h) = table.read j := by cases h; rfl

theorem table_eq_of_data {n : ℕ} {α : Type*} (first second : FixedArrayTable n α)
    (h : first.data = second.data) : first = second := by
  cases first
  cases second
  cases h
  rfl

theorem totals_cast {n m k : ℕ} (h : m = k) (budget : SignedWord)
    (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    BinaryTerminalGroupInputs.castUniform h
      (⟨budget, FixedArrayTable.ofFn (fun g => (packing.read g).2)⟩ : BinaryGroupInputs.UniformInput m) =
        ⟨budget, FixedArrayTable.ofFn (fun g => ((castTable h packing).read g).2)⟩ := by
  cases h
  rfl

theorem routes_cast {n m k : ℕ} (h : m = k) (length : FixedArrayTable n SignedWord)
    (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    castRoutes h (BinaryGroupRoutes.prepare length packing) = BinaryGroupRoutes.prepare length (castTable h packing) := by
  cases h
  rfl

def selectedLength {n : ℕ} (input : Input n) : Option (Fin n) → SignedWord
  | none => zero
  | some j => input.length.read j

def selectedProbability {n : ℕ} (input : Input n) : Option (Fin n) → SignedWord
  | none => zero
  | some j => apply .div (input.resource.read j) (input.length.read j)

theorem mixed_cast_from_uniform {m k : ℕ} (h : m = k) (budget ell probability : SignedWord)
    (totals : FixedArrayTable m SignedWord) :
    BinaryTerminalGroupInputs.castMixed h
      (⟨budget, totals, ell, probability⟩ : BinaryGroupInputs.MixedInput m) =
      ⟨budget, (BinaryTerminalGroupInputs.castUniform h
        (⟨budget, totals⟩ : BinaryGroupInputs.UniformInput m)).total, ell, probability⟩ := by
  cases h
  rfl

structure Prepared {n : ℕ} (input : Input n) where
  count : ℕ
  packing : FixedArrayTable count (List (Fin n) × SignedWord)
  totals : FixedArrayTable count SignedWord
  routes : FixedArrayTable n (BinaryGroupRoutes.Route count)
  pivot : Option (Fin n)
  ell : SignedWord
  probability : SignedWord
  prefixWork : ℕ
  count_eq : count = (groups input).length
  packing_eq : packing.data = (packed input).toArray
  totals_eq : totals = FixedArrayTable.ofFn (fun g => (packing.read g).2)
  routes_eq : routes = BinaryGroupRoutes.prepare input.length packing
  pivot_eq : pivot = BinaryTerminalGrouping.pivot input
  ell_eq : ell = selectedLength input pivot
  probability_eq : probability = selectedProbability input pivot

def prepare {n : ℕ} (input : Input n) : Prepared input :=
  let assembled := classifyAndPack input
  let entries := assembled.2.1
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n) × SignedWord) := ⟨entries.toArray, by simp [count]⟩
  let totals := FixedArrayTable.ofFn (fun g => (packing.read g).2)
  let routes := BinaryGroupRoutes.prepare input.length packing
  let pivot := assembled.1.pivot
  let extra := match pivot with
    | none => (zero, zero)
    | some j => (input.length.read j, apply .div (input.resource.read j) (input.length.read j))
  { count := count
    packing := packing
    totals := totals
    routes := routes
    pivot := pivot
    ell := extra.1
    probability := extra.2
    prefixWork := assembled.1.booleanWork + assembled.2.2
    count_eq := by
      change (classifyAndPack input).2.1.length = (groups input).length
      rw [(classifyAndPack_state input).2]
      simp [groups]
    packing_eq := congrArg List.toArray (classifyAndPack_state input).2
    totals_eq := rfl
    routes_eq := rfl
    pivot_eq := (classifyAndPack_state input).1
    ell_eq := by dsimp only [extra]; cases pivot <;> rfl
    probability_eq := by dsimp only [extra]; cases pivot <;> rfl }

def Prepared.uniform {n : ℕ} {input : Input n} (prepared : Prepared input) : BinaryGroupInputs.UniformInput prepared.count :=
  ⟨input.budget, prepared.totals⟩

def Prepared.mixed {n : ℕ} {input : Input n} (prepared : Prepared input) : BinaryGroupInputs.MixedInput prepared.count :=
  ⟨input.budget, prepared.totals, prepared.ell, prepared.probability⟩

theorem Prepared.packing_cast {n : ℕ} {input : Input n} (prepared : Prepared input) :
    castTable prepared.count_eq prepared.packing = BinaryTerminalPacking.prepare input := by
  apply table_eq_of_data
  rw [castTable_data]
  exact prepared.packing_eq

theorem Prepared.uniform_cast {n : ℕ} {input : Input n} (prepared : Prepared input) :
    BinaryTerminalGroupInputs.castUniform prepared.count_eq prepared.uniform = BinaryTerminalGroupInputs.uniform input := by
  unfold Prepared.uniform
  rw [prepared.totals_eq, totals_cast, prepared.packing_cast]
  rfl

theorem Prepared.mixed_cast {n : ℕ} {input : Input n} (prepared : Prepared input) (selected : Fin n)
    (h : prepared.pivot = some selected) :
    BinaryTerminalGroupInputs.castMixed prepared.count_eq prepared.mixed = BinaryTerminalGroupInputs.mixed input selected := by
  have hEll : prepared.ell = input.length.read selected := by rw [prepared.ell_eq, h]; rfl
  have hProb : prepared.probability = apply .div (input.resource.read selected) (input.length.read selected) := by
    rw [prepared.probability_eq, h]
    rfl
  have hUniform := prepared.uniform_cast
  unfold Prepared.uniform at hUniform
  unfold Prepared.mixed
  rw [hEll, hProb]
  rw [mixed_cast_from_uniform, hUniform]
  rfl

theorem Prepared.routes_cast {n : ℕ} {input : Input n} (prepared : Prepared input) :
    castRoutes prepared.count_eq prepared.routes = BinaryTerminalRoutes.prepare input := by
  rw [prepared.routes_eq, Blotto.BinaryCachedTerminalPreparation.routes_cast, prepared.packing_cast]
  rfl

theorem Prepared.count_bound {n : ℕ} {input : Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input) : prepared.count = 2 ∨ prepared.count = 3 := by
  rw [prepared.count_eq]
  exact BinaryTerminalPromises.groupCount input hC hAd

theorem uniform_canonical_cast {m k : ℕ} (h : m = k) (input : BinaryGroupInputs.UniformInput m)
    (hC : (BinaryTerminalGroupInputs.castUniform h input).Canonical) : input.Canonical := by cases h; exact hC

theorem mixed_canonical_cast {m k : ℕ} (h : m = k) (input : BinaryGroupInputs.MixedInput m)
    (hC : (BinaryTerminalGroupInputs.castMixed h input).Canonical) : input.Canonical := by cases h; exact hC

theorem Prepared.uniform_canonical {n : ℕ} {input : Input n} (prepared : Prepared input) (hC : input.Canonical) :
    prepared.uniform.Canonical := by
  apply uniform_canonical_cast prepared.count_eq
  rw [prepared.uniform_cast]
  exact BinaryTerminalGroupInputs.uniform_canonical input hC

theorem Prepared.mixed_canonical {n : ℕ} {input : Input n} (prepared : Prepared input) (hC : input.Canonical)
    (selected : Fin n) (h : prepared.pivot = some selected) : prepared.mixed.Canonical := by
  apply mixed_canonical_cast prepared.count_eq
  rw [prepared.mixed_cast selected h]
  exact BinaryTerminalGroupInputs.mixed_canonical input hC selected

end Blotto.BinaryCachedTerminalPreparation
