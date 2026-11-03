import Blotto.BinaryGroupRoutes

/-! Mapping a partial sampled group row through cached native routes preserves
none and exact original-field source emission. No independent coordinate
sampling or exhaustion fallback is introduced by output restoration. -/

namespace Blotto.BinaryRoutePartialRefinement
open BinaryRationalNormalization BinaryRationalEncoding

noncomputable def sourceRow {n : ℕ} (row : FixedArrayTable n SignedWord) : Fin n → ℚ := fun j => value (row.read j)

theorem emit_option {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (source : RationalProportionalGroups n m) (hRoutes : ∀ j, CanonicalWord (routes.read j).2)
    (hr : ∀ j, BinaryGroupRoutes.routeValue (routes.read j)=source.routes.read j)
    (rows : Option (FixedArrayTable m SignedWord)) (hc : ∀ row, rows=some row → ∀ g, CanonicalWord (row.read g)) :
    (rows.map (BinaryGroupRoutes.emit routes)).map sourceRow =
      (rows.map sourceRow).map (fun row => (source.emit source.routes row).allocation) := by
  cases hs : rows with
  | none => rfl
  | some row =>
    simp only [Option.map_some]
    apply congrArg some
    funext j
    exact BinaryGroupRoutes.emit_refines routes row source hRoutes (hc row hs) hr j

theorem emitMixed_option {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (source : RationalProportionalGroups n m) (pivot : Fin n) (hRoutes : ∀ j, CanonicalWord (routes.read j).2)
    (hr : ∀ j, BinaryGroupRoutes.routeValue (routes.read j)=source.routes.read j)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) (hc : ∀ row, rows=some row → ∀ g, CanonicalWord (row.read g)) :
    (rows.map (BinaryGroupRoutes.emitMixed routes pivot)).map sourceRow =
      (rows.map sourceRow).map (fun row => (source.emitMixed source.routes pivot row).allocation) := by
  cases hs : rows with
  | none => rfl
  | some row =>
    simp only [Option.map_some]
    apply congrArg some
    funext j
    exact BinaryGroupRoutes.emitMixed_refines routes pivot row source hRoutes (hc row hs) hr j

end Blotto.BinaryRoutePartialRefinement
