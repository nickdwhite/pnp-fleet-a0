import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_17137 : (¬ (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (13 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates)) := by

  intro h
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [10, 9]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [21, 8]⟩, ⟨.and, [6, 10]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [23, 24]⟩, ⟨.and, [2, 19]⟩, ⟨.or, [25, 26]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [28, 22]⟩, ⟨.or, [27, 29]⟩, ⟨.and, [9, 22]⟩, ⟨.or, [30, 31]⟩, ⟨.or, [32, 18]⟩], 33⟩
  have model : PEqualNP.TopForm.IsAO2 (11 : ℕ) C := by
    decide
  have right : ∀ (x6 : Fin (11 : ℕ) → Bool), x6 ⟨(3 : ℕ), by omega⟩ = Bool.false →
      PEqualNP.MetaComplexity.circuitFun (11 : ℕ) C x6 = PEqualNP.MetaComplexity.NestedCover.graphFun
        (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]) ∅ x6 := by
    decide +kernel
  have ors : List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) C.gates = (12 : ℕ) := by
    decide
  have := h ⟨(3 : ℕ), by omega⟩ C (by decide) model right
  rw [ors] at this
  omega
