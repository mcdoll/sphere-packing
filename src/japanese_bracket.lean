/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import measure_theory.integral.integral_eq_improper
import measure_theory.integral.layercake
import tactic.positivity

/-!
# Japanese Bracket
In this file, we show that Japanese bracket $(1 + \|x\|^2)^{1/2}$ can be estimated from above
and below by $1 + \|x\|$.
The functions $(1 + \|x\|^2)^{-r/2}$ and $(1 + |x|)^{-r}$ are integrable provided that `r` is larger
than the dimension.
## Main statements
* `integrable_one_add_norm`: the function $(1 + |x|)^{-r}$ is integrable
* `integrable_jap` the Japanese bracket is integrable
-/


noncomputable theory

open_locale big_operators nnreal filter topological_space ennreal

open asymptotics filter set real measure_theory finite_dimensional

variables {E : Type*} [normed_add_comm_group E]

lemma sqrt_one_add_norm_sq_le (x : E) : real.sqrt (1 + ∥x∥^2) ≤ 1 + ∥x∥ := sorry

lemma one_add_norm_le_sqrt_two_mul_sqrt (x : E) : 1 + ∥x∥ ≤ (real.sqrt 2) * sqrt (1 + ∥x∥^2) := sorry

lemma rpow_neg_one_add_norm_sq_le {r : ℝ} (x : E) (hr : 0 < r) :
  (1 + ∥x∥^2)^(-r/2) ≤ 2^(r/2) * (1 + ∥x∥)^(-r) := sorry

lemma le_rpow_one_add_norm_iff_norm_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : E) :
  t ≤ (1 + ∥x∥) ^ -r ↔ ∥x∥ ≤ t ^ -r⁻¹ - 1 := sorry

variables (E)

lemma closed_ball_rpow_sub_one_eq_empty_aux {r t : ℝ} (hr : 0 < r) (ht : 1 < t) :
  metric.closed_ball (0 : E) (t^(-r⁻¹) - 1) = ∅ := sorry

variables [normed_space ℝ E] [finite_dimensional ℝ E]

variables {E}

lemma finite_integral_rpow_sub_one_pow_aux {r : ℝ} (n : ℕ) (hnr : (n : ℝ) < r) :
  ∫⁻ (x : ℝ) in Ioc 0 1, ennreal.of_real ((x ^ -r⁻¹ - 1) ^ n) < ∞ := sorry

lemma finite_integral_one_add_norm [measure_space E] [borel_space E]
  [(@volume E _).is_add_haar_measure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  ∫⁻ (x : E), ennreal.of_real ((1 + ∥x∥) ^ -r) < ∞ := sorry

lemma integrable_rpow_neg_one_add_norm [measure_space E] [borel_space E] [(@volume E _).is_add_haar_measure]
  {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  integrable (λ (x : E), (1 + ∥x∥) ^ -r) := sorry

lemma mem_ℒp_rpow_neg_one_add_norm [measure_space E] [borel_space E]
  [(@volume E _).is_add_haar_measure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  mem_ℒp (λ (x : E), (1 + ∥x∥) ^ -r) 1 :=
begin
  rw mem_ℒp_one_iff_integrable,
  exact integrable_rpow_neg_one_add_norm hnr,
end

lemma integrable_rpow_neg_one_add_norm_sq [measure_space E] [borel_space E]
  [(@volume E _).is_add_haar_measure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  integrable (λ (x : E), (1 + ∥x∥^2) ^ (-r/2)) := sorry

lemma mem_ℒp_rpow_neg_one_add_norm_sq [measure_space E] [borel_space E]
  [(@volume E _).is_add_haar_measure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  mem_ℒp (λ (x : E), (1 + ∥x∥^2) ^ (-r/2)) 1 :=
begin
  rw mem_ℒp_one_iff_integrable,
  exact integrable_rpow_neg_one_add_norm_sq hnr,
end
