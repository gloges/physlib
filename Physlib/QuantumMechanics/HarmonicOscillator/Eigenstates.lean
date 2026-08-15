/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.Basic
/-!

# Energy eigenstates of the quantum harmonic oscillator

-/
@[expose] public section

noncomputable section
namespace QuantumMechanics
namespace HarmonicOscillator

open Constants Finset

variable {d : ℕ} (Q : HarmonicOscillator d) (n : Fin d → ℕ)

/-!
## A. Energy eigenvalues
-/

def eigenEnergy : ℝ := ∑ i, ℏ * Q.ω i * (n i + 1 / 2)

lemma eigenEnergy_eq : Q.eigenEnergy n = ∑ i, ℏ * Q.ω i * (n i + 1 / 2) := rfl

lemma eigenEnergy_strictMono : StrictMono Q.eigenEnergy := by
  intro n n' h
  obtain ⟨h, i, hi⟩ := Pi.lt_def.mp h
  exact sum_lt_sum (fun i _ ↦ by simp [h i]) ⟨i, mem_univ i, by simp [hi]⟩

end HarmonicOscillator
end QuantumMechanics
end
