/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Mathematics.InnerProductSpace.Gaussian
public import Physlib.Mathematics.HasTemperateGrowth
public import Physlib.Mathematics.KroneckerDelta.Basic
public import Physlib.Mathematics.SpecialFunctions.PhysHermite
public import Physlib.QuantumMechanics.HarmonicOscillator.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
public import Physlib.Meta.Sorry
/-!

# Energy eigenstates of the quantum harmonic oscillator

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Energy eigenvalues
- B. Cartesian basis
  - B.1. Eigenfunctions
  - B.2. Eigenstates

## iv. References

-/
@[expose] public section

TODO "Prove that the QHO eigenstates in the Cartesian basis (Hermite polynomials) are orthonormal."

TODO "Prove that the QHO eigenstates in the Cartesian basis (Hermite polynomials) satisfy the TISE."

TODO "Prove that the (point) spectrum of the self-adjoint Hamiltonian is `Set.range Q.eigenEnergy`."

TODO "Prove that the ground-state of the QHO is non-degenerate."

TODO "Determine the energy eigenstates of the isotropic quantum harmonic oscillator
  in the 'spherical basis' in terms of spherical harmonics."

noncomputable section
namespace QuantumMechanics
namespace HarmonicOscillator

open Complex Constants Finset InnerProductSpace Polynomial SchwartzMap Space SpaceDHilbertSpace
open scoped Nat Real ComplexConjugate

variable {d : ℕ} (Q : HarmonicOscillator d) (n n' : Fin d → ℕ) (x : Space d)

/-!
## A. Energy eigenvalues
-/

def eigenEnergy : ℝ := ∑ i, ℏ * Q.ω i * (n i + 1 / 2)

lemma eigenEnergy_eq : Q.eigenEnergy n = ∑ i, ℏ * Q.ω i * (n i + 1 / 2) := rfl

lemma eigenEnergy_strictMono : StrictMono Q.eigenEnergy := by
  intro n n' h
  obtain ⟨h, i, hi⟩ := Pi.lt_def.mp h
  exact sum_lt_sum (fun i _ ↦ by simp [h i]) ⟨i, mem_univ i, by simp [hi]⟩

/-!
## B. Cartesian basis
-/

/-!
### B.1. Eigenfunctions
-/

def coeff (i : Fin d) : ℝ := 1 / √(2 ^ n i * (n i)! * √π * √(Q.ξ i))

lemma coeff_eq (i : Fin d) : Q.coeff n i = 1 / √(2 ^ n i * (n i)! * √π * √(Q.ξ i)) := rfl

def eigenfunction : 𝓢(Space d, ℂ) :=
  compCLMOfContinuousLinearEquiv ℂ Q.ξEquiv.symm <|
    smulLeftCLM ℂ (fun x ↦ ∏ i, Q.coeff n i * physHermite (n i) (x i)) (stdGaussian (Space d) ℂ)

lemma eigenfunction_eq :
    Q.eigenfunction n = compCLMOfContinuousLinearEquiv ℂ Q.ξEquiv.symm (smulLeftCLM ℂ
      (fun x ↦ ∏ i, Q.coeff n i * physHermite (n i) (x i)) (stdGaussian (Space d) ℂ)) := rfl

lemma eigenfunction_apply :
    Q.eigenfunction n x =
      ∏ i, Q.coeff n i * physHermite (n i) (x i / Q.ξ i) * cexp (-2⁻¹ * (x i / Q.ξ i) ^ 2) := by
  rw [eigenfunction_eq, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smulLeftCLM_apply_apply (by fun_prop), ξEquiv_symm_apply]
  simp [div_eq_mul_inv, prod_mul_distrib, exp_neg, norm_sq_eq, mul_sum, mul_comm, exp_sum]

/-!
### B.2. Eigenstates
-/

def eigenstate : SchwartzSubmodule d := schwartzEquiv _ (Q.eigenfunction n)

lemma eigenstate_eq : Q.eigenstate n = schwartzEquiv _ (Q.eigenfunction n) := rfl

/-- The energy eigenstates are orthonormal. -/
@[simp, sorryful]
lemma eigenstates_orthonormal : ⟪Q.eigenstate n, Q.eigenstate n'⟫_ℂ = δ[n,n'] :=
  -- It might help to first prove an analogue of
  -- `MeasureTheory.integral_fin_nat_prod_(volume_)eq_prod` for `Space d` in order to split
  -- `∫ x : Space d, Π i : Fin d, fᵢ (x i) = ∏ i : Fin d, ∫ xᵢ : ℝ, fᵢ xᵢ`.
  sorry

end HarmonicOscillator
end QuantumMechanics
end
