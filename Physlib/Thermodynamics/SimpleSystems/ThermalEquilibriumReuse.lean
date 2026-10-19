/-
Copyright (c) 2026 Omar Aguilar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Omar Aguilar, Fabio Anza
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.Linarith
public import Physlib.Thermodynamics.FundamentalRelation.Intensive
public import Physlib.Thermodynamics.SimpleSystems.Postulates

/-!
# Application: thermal equilibrium of two subsystems

Equality of inverse temperatures from constrained entropy maximization.

## i. Overview

This file derives equality of inverse temperatures for two single-component
subsystems at an entropy maximum. The subsystems can exchange energy while
their total energy is conserved and each subsystem's volume and particle
number remain fixed. The argument assumes an admissible variation with
nonzero first-order energy exchange.

**Dependencies and attribution**

This example connects the state, wall-constraint, and postulate framework to
Nathaneal Sajan's fundamental-relation development.

The definitions available here through
`Physlib.Thermodynamics.SimpleSystems.Postulates` correspond to
the following files in the simple-system development:

* `EquilibriumState.lean`: `StateCoordinates`, `EquilibriumState`, and
  `CompositeState` describe the subsystem coordinates and composite states.
* `WallsAndConstraints.lean`: `Wall` and `Constraints` specify which quantities
  remain fixed. `thermalWalls` specializes this framework to thermal contact.
* `Postulates.lean`: `IsEntropyMaximum` supplies the maximization condition,
  and `Postulate3.additive` identifies total entropy with subsystem entropy sums.

From Nathaneal Sajan's
[thermodynamics-foundations branch](https://github.com/nateabr/physlib/tree/thermodynamics-foundations/Physlib/Thermodynamics),
this file reuses `FundamentalRelation` and its entropy function `S`,
`ExtensiveState` and its coordinate accessors, the temperature definition
`FundamentalRelation.temperature` (`T = (dS_dU)⁻¹`), and the derivative theorem
`FundamentalRelation.hasDerivAt_dS_dU` at fixed `V` and `N`.
These definitions and results supply the connection between entropy derivatives
and inverse temperatures used in the equilibrium argument.

`FundamentalRelation.entropyOnState` is an adapter defined in this file. It
evaluates the entropy function from Nathaneal's `FundamentalRelation` on an
`EquilibriumState`, matching the subsystem entropy type in the postulates.
The thermal wall configuration and the lemmas
connecting constraints, entropy maximization, and inverse temperatures are also
defined here.

**Scope and assumptions**

The constraints, stationarity, additivity, and energy-conservation lemmas allow
any number of chemical components. The entropy differential uses Nathaneal's
single-component `FundamentalRelation`, evaluated on our states through
`entropyOnState`. Final U, V, and N are positive, as required by his
`ExtensiveState` type.

A supplied virtual variation passes through the final state and satisfies the
thermal constraints for all sufficiently small positive and negative parameters.
Nathaneal's `hasDerivAt_dS_dU` theorem and temperature definition give
`∂S/∂U = 1/T`. His derivative theorem relies on the `smooth` assumption in his
`FundamentalRelation`; of the assumptions bundled in our `Postulate3`, this proof
uses only additivity for the same subsystem entropies. At an entropy maximum,
a nonzero first-order energy exchange then implies equality of inverse temperatures.

The equilibrium lemmas take `IsEntropyMaximum` directly as a hypothesis. To obtain it from
Postulate II, first choose its entropy witness `S` and its equivalence
`h_equilibrium`; an equilibrium hypothesis gives
`(h_equilibrium thermalWalls state_0 state_f).mp h_eq` as `h_max`.
Postulate III must then be supplied for that same `S`.
Postulate I is not an explicit premise: the initial and final states are already
supplied. The argument does not use Postulate IV.

The existence of such a nonzero allowed variation is an assumption here. This is
a necessary equilibrium condition, not a proof that equal temperatures imply
a global entropy maximum.

## ii. Key results

* `thermal_equilibrium_dS_eq_zero`: entropy stationarity at an entropy maximum.
* `thermal_entropy_differential_reduced`: the entropy differential after
  applying energy conservation.
* `thermal_equilibrium_inverse_temperatures_eq`: equality of inverse
  temperatures at an entropy maximum admitting nonzero first-order energy exchange.

## iii. Table of contents

- A. Thermal constraints and entropy maximization
- B. Entropy adapter
- C. Thermal differentials and equilibrium condition

## iv. References

Callen, second edition, section 2.4, equations (2.30)-(2.37).
-/

@[expose] public section

namespace Thermodynamics

open Set Filter
open scoped Topology BigOperators

/-! ## A. Thermal constraints and entropy maximization -/

section ThermalSetup

variable {r : ℕ}
variable {D : Fin 2 → Set (StateCoordinates r)}
variable {S : CompositeState D → ℝ}
variable {state_0 state_f : CompositeState D}

/-- Two rigid, impermeable subsystems can exchange energy; their total energy is fixed. -/
def thermalWalls (subsystems : Finset (Fin 2)) : Wall r where
  restrictsEnergy := subsystems = Finset.univ
  restrictsVolume := True
  restrictsMoleNumber := fun _ => True

/-- In thermal contact, total energy is conserved and each subsystem's
volume and mole numbers remain fixed (Callen, Eq. 2.30). -/
lemma thermal_constraints
    (h_constraints : Constraints thermalWalls state_0 state_f) :
    (state_f 0).U + (state_f 1).U =(state_0 0).U + (state_0 1).U ∧
    ∀ i, (state_f i).V = (state_0 i).V ∧ (state_f i).N = (state_0 i).N := by
  constructor
  · simpa [Fin.sum_univ_two] using
      (h_constraints Finset.univ).1 rfl
  · intro i
    constructor
    · simpa using (h_constraints {i}).2.1 trivial
    · funext j
      simpa using (h_constraints {i}).2.2 j trivial

/-- At thermal equilibrium, the first-order entropy change along
an allowed virtual variation vanishes (Callen, Eq. 2.31). -/
lemma thermal_equilibrium_dS_eq_zero
    (h_max : IsEntropyMaximum S thermalWalls state_0 state_f)
    (variation : ℝ → CompositeState D)
    (h_at : variation 0 = state_f)
    (h_constraints : ∀ᶠ ε in 𝓝 (0 : ℝ),
      Constraints thermalWalls state_0 (variation ε))
    {dS : ℝ}
    (h_deriv : HasDerivAt (fun ε => S (variation ε)) dS 0) :
    dS = 0 := by
  have h_local : IsLocalMax (fun ε => S (variation ε)) 0 := by
    filter_upwards [h_constraints] with ε hε
    rw [h_at]
    apply h_max.2
    refine ⟨hε, ?_, ?_, ?_⟩
    · simpa using (hε Finset.univ).1 rfl
    · simpa using (hε Finset.univ).2.1 trivial
    · intro j
      simpa using (hε Finset.univ).2.2 j trivial
  exact h_local.hasDerivAt_eq_zero h_deriv

/-- The entropy of a two-subsystem composite is the sum of its
subsystem entropies (Callen, Eq. 2.32). -/
lemma entropy_additivity_two
    {S_subsystem : (i : Fin 2) → EquilibriumState (D i) → ℝ}
    (h3 : Postulate3 S S_subsystem)
    (state_f : CompositeState D) :
    S state_f =
      S_subsystem 0 (state_f 0) + S_subsystem 1 (state_f 1) := by
  simpa only [Fin.sum_univ_two] using h3.additive state_f

end ThermalSetup

/-! ## B. Entropy adapter -/

/-- Adapter defined here to evaluate the entropy function from Nathaneal Sajan's
`FundamentalRelation` on our `EquilibriumState`:
`Φ.entropyOnState state = Φ.S state.U state.V (state.N 0)`.
This gives the same entropy value from one state instead of three real inputs,
matching the subsystem entropy type in our postulates. `N 0` selects the sole
chemical component's coordinate. -/
def FundamentalRelation.entropyOnState {D : Set (StateCoordinates 1)}
    (Φ : FundamentalRelation) (state : EquilibriumState D) : ℝ :=
  Φ.S state.U state.V (state.N 0)

/-! ## C. Thermal differentials and equilibrium condition -/

section ThermalDifferential

variable {D : Fin 2 → Set (StateCoordinates 1)}
variable (Φ : Fin 2 → FundamentalRelation)
variable {S : CompositeState D → ℝ}
variable {state_0 state_f : CompositeState D}
variable (h_positive : ∀ i, 0 < (state_f i).U ∧
  0 < (state_f i).V ∧ 0 < (state_f i).N 0)
variable (h3 : Postulate3 S (fun i => (Φ i).entropyOnState))
variable (variation : ℝ → CompositeState D)
variable (h_at : variation 0 = state_f)
variable (h_allowed : ∀ᶠ ε in 𝓝 (0 : ℝ),
  Constraints thermalWalls state_0 (variation ε))
variable (dU : Fin 2 → ℝ)
variable (hU : ∀ i, HasDerivAt (fun ε => (variation ε i).U) (dU i) 0)

/- Express each final subsystem state using Nathaneal Sajan's `ExtensiveState`:
   e i := ⟨((state_f i).U, (state_f i).V, (state_f i).N 0), h_positive i⟩. -/
local notation "e" => fun i => (Subtype.mk
  (EquilibriumState.U (state_f i), EquilibriumState.V (state_f i),
    EquilibriumState.N (state_f i) 0) (h_positive i) : ExtensiveState)

-- Subsystem temperatures from Nathaneal Sajan's definition `T = (∂S/∂U)⁻¹`.
local notation "T" => fun i =>
  FundamentalRelation.temperature (Φ i) (e i)

include h3 h_at h_allowed hU in
/-- Along a thermal variation, dS = (1/T₁)dU₁ + (1/T₂)dU₂
(Callen, Eqs. 2.33–2.34). -/
lemma thermal_entropy_differential :
    HasDerivAt (fun ε => S (variation ε))
      ((1 / T 0) * dU 0 + (1 / T 1) * dU 1) 0 := by
  -- Apply Nathaneal Sajan's `hasDerivAt_dS_dU` and Mathlib's chain rule
  -- to each subsystem entropy at fixed V and N.
  have hs (i : Fin 2) : HasDerivAt
      (fun ε => (Φ i).S (variation ε i).U
        (state_f i).V ((state_f i).N 0))
      ((1 / T i) * dU i) 0 := by
    have h := ((Φ i).hasDerivAt_dS_dU (e i)).comp_of_eq
      0 (hU i) (by simp [h_at, ExtensiveState.U])
    simpa [FundamentalRelation.temperature, Function.comp_def, one_div,
      ExtensiveState.U, ExtensiveState.V, ExtensiveState.N] using h

  -- Add the derivatives and identify the sum with our total entropy.
  apply ((hs 0).add (hs 1)).congr_of_eventuallyEq
  have hf := (thermal_constraints h_allowed.self_of_nhds).2
  simp only [h_at] at hf
  filter_upwards [h_allowed] with ε hε
  have hfixed := (thermal_constraints hε).2
  rw [entropy_additivity_two h3]
  dsimp only [FundamentalRelation.entropyOnState]
  rw [(hfixed 0).1, (hfixed 0).2, (hfixed 1).1, (hfixed 1).2,
    (hf 0).1, (hf 0).2, (hf 1).1, (hf 1).2]
  rfl


/-- Conservation of total energy gives dU₂ = -dU₁
along a thermal variation (Callen, Eq. 2.35). -/
lemma thermal_energy_differential {r : ℕ}
    {D : Fin 2 → Set (StateCoordinates r)}
    {state_0 : CompositeState D}
    (variation : ℝ → CompositeState D)
    (h_allowed : ∀ᶠ ε in 𝓝 (0 : ℝ),
      Constraints thermalWalls state_0 (variation ε))
    (dU : Fin 2 → ℝ)
    (hU : ∀ i, HasDerivAt (fun ε => (variation ε i).U) (dU i) 0) :
    dU 1 = -dU 0 := by
  -- The derivative of total energy is the sum of the derivatives.
  have h_sum := (hU 0).add (hU 1)

  -- Our conservation equation makes total energy locally constant.
  have h_const := (hasDerivAt_const (0 : ℝ)
    ((state_0 0).U + (state_0 1).U)).congr_of_eventuallyEq
      (h_allowed.mono fun ε hε => (thermal_constraints hε).1)

  -- Equate the two derivatives and rearrange.
  linarith [h_sum.unique h_const]

include h3 h_at h_allowed hU in
/-- Using energy conservation, dS = (1/T₁ - 1/T₂)dU₁
(Callen, Eq. 2.36). -/
lemma thermal_entropy_differential_reduced :
    HasDerivAt (fun ε => S (variation ε))
      ((1 / T 0 - 1 / T 1) * dU 0) 0 := by
  have hS := thermal_entropy_differential
    Φ h_positive h3 variation h_at h_allowed dU hU
  simpa only [thermal_energy_differential variation h_allowed dU hU,
    mul_neg, ← sub_eq_add_neg, ← sub_mul] using hS

include h3 h_at h_allowed hU in
/-- At an entropy maximum admitting a nonzero virtual energy exchange,
the inverse temperatures agree (Callen, Eq. 2.37). -/
lemma thermal_equilibrium_inverse_temperatures_eq
    (h_max : IsEntropyMaximum S thermalWalls state_0 state_f)
    (h_exchange : dU 0 ≠ 0) :
    1 / T 0 = 1 / T 1 := by
  have hS := thermal_entropy_differential_reduced
    Φ h_positive h3 variation h_at h_allowed dU hU
  have h_zero := thermal_equilibrium_dS_eq_zero
    h_max variation h_at h_allowed hS
  exact sub_eq_zero.mp ((mul_eq_zero.mp h_zero).resolve_right h_exchange)

end ThermalDifferential

end Thermodynamics
