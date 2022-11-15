import japanese_bracket
import analysis.schwartz_space

noncomputable theory

open_locale big_operators nnreal filter topological_space ennreal schwartz_space

open asymptotics filter set real measure_theory finite_dimensional 

variables {E F : Type*}

namespace schwartz_map

variables [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
variables [measure_space E] [borel_space E] [(@volume E _).is_add_haar_measure]
variables [normed_add_comm_group F] [normed_space ℝ F] 

@[protected, measurability] lemma ae_strongly_measurable (f : 𝓢(E, F)) : ae_strongly_measurable (f : E → F) volume :=
f.continuous.ae_strongly_measurable

lemma one_add_pow_smul_le (f : 𝓢(E, F)) (x : E) (n : ℕ): ∥(1 + ∥x∥) ^ n • f x∥ ≤
  ∑ (m : ℕ) in finset.range (n + 1), (n.choose m : ℝ) * (schwartz_map.seminorm ℝ m 0) f :=
begin
  rw add_comm,
  rw add_pow,
  rw finset.sum_smul,
  simp only [one_pow, mul_one],
  refine (norm_sum_le (finset.range (n + 1)) _).trans _,
  refine finset.sum_le_sum (λ m hm, _),
  rw mul_comm,
  simp only [←smul_smul, norm_smul, norm_coe_nat, norm_pow, norm_norm],
  exact mul_le_mul_of_nonneg_left (f.norm_pow_mul_le_seminorm ℝ _ _) (by positivity),
end

/-- To be generalized to all p -/
@[protected] lemma mem_ℒp_one (f : 𝓢(E, F)) : mem_ℒp (f : E → F) 1 volume :=
begin
  have hr : (finrank ℝ E : ℝ) < finrank ℝ E + 1 := lt_add_one (finrank ℝ E), 
  have h := mem_ℒp_rpow_neg_one_add_norm hr,
  let c := ∑ (m : ℕ) in finset.range ((finrank ℝ E + 1) + 1),
    ((finrank ℝ E + 1).choose m : ℝ) * (schwartz_map.seminorm ℝ m 0) f,
  have h' : ∀ x : E, ∥f x∥ ≤ c * ∥(1 + ∥x∥) ^ -((finrank ℝ E : ℝ) + 1)∥ :=
  begin
    intros x,
    have hpos : 0 < 1 + ∥x∥ := by positivity,
    rw ←one_smul ℝ (f x),
    nth_rewrite 0 ←real.rpow_zero (1 + ∥x∥),
    rw ←sub_self ((finrank ℝ E : ℝ) + 1),
    rw sub_eq_neg_add,
    rw real.rpow_add hpos,
    rw ←smul_smul,
    rw norm_smul,
    rw mul_comm,
    refine mul_le_mul_of_nonneg_right _ (by positivity),
    norm_cast,
    exact one_add_pow_smul_le _ _ _,
  end,
  exact h.of_le_mul (by measurability) (ae_of_all _ h'),
end

@[protected] lemma integrable (f : 𝓢(E, F)) : integrable (f : E → F) :=
begin
  rw ←mem_ℒp_one_iff_integrable,
  exact f.mem_ℒp_one,
end

end schwartz_map

section fourier_transform_aux

variables [inner_product_space ℝ E]
variables [normed_add_comm_group F] [normed_space ℝ F] [complete_space F] [finite_dimensional ℝ F]
variables [has_smul ℂ F]

lemma complex.differentiable_at_coe {f : E → ℝ} {x : E} (hf : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ y, (f y : ℂ)) x :=
complex.of_real_clm.differentiable_at.comp _ hf

lemma complex.differentiable_coe {f : E → ℝ} (hf : differentiable ℝ f) :
  differentiable ℝ (λ x, (f x : ℂ)) :=
complex.of_real_clm.differentiable.comp hf

lemma complex.fderiv_coe {f : E → ℝ} {y : E} (hf : differentiable_at ℝ f y) :
  fderiv ℝ (λ x, (f x : ℂ)) y = complex.of_real_clm.comp (fderiv ℝ f y) :=
begin
  change fderiv ℝ (λ x, complex.of_real_clm (f x)) y = complex.of_real_clm.comp (fderiv ℝ f y),
  convert fderiv.comp _ complex.of_real_clm.differentiable_at hf,
  exact complex.of_real_clm.fderiv.symm,
end

lemma complex.fderiv_exp {f : E → ℂ} {x : E} (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λ x, complex.exp (f x)) x = complex.exp (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.cexp.fderiv

lemma inner_differentiable_at {y : E} {z : E} : differentiable_at ℝ (λ x, @inner ℝ _ _ y x) z :=
(@innerSL ℝ _ _ _ y).differentiable_at

lemma inner_differentiable {y : E} : differentiable ℝ (λ x, @inner ℝ _ _ y x) :=
(@innerSL ℝ _ _ _ y).differentiable

lemma fderiv_inner {y x₀ : E} : fderiv ℝ (λ x, @inner ℝ _ _ y x) x₀ = innerSL y :=
(@innerSL ℝ _ _ _ y).fderiv

lemma fderiv_exp_inner_left (x₀ ξ : E) : fderiv ℝ (λ x, complex.exp (- complex.I * @inner ℝ _ _ x ξ)) x₀ =
  (complex.exp (-complex.I * (@inner ℝ _ _ x₀ ξ)) * -complex.I) • complex.of_real_clm.comp (innerSL ξ) :=
begin
  have hdiff_inner : differentiable_at ℝ (λ (x : E), ↑(inner ξ x)) x₀ :=
  (complex.differentiable_coe inner_differentiable).differentiable_at,
  have hdiff_inner' : differentiable_at ℝ (λ (x : E), -complex.I * ↑(inner ξ x)) x₀ :=
  differentiable_at.const_mul hdiff_inner _,
  --((complex.differentiable_coe inner_differentiable).const_mul _).differentiable_at,
  simp_rw real_inner_comm,
  rw complex.fderiv_exp hdiff_inner',
  rw fderiv_const_mul hdiff_inner,
  rw complex.fderiv_coe inner_differentiable_at,
  rw fderiv_inner,
  rw ←mul_smul,
  simp only [real_inner_comm x₀ ξ],
  /-simp_rw real_inner_comm,
  rw ←fderiv_exp_inner_left ξ₀ x,
  congr,
  ext1,
  rw real_inner_comm,-/
end

lemma fderiv_exp_inner_right (ξ₀ x : E) : fderiv ℝ (λ ξ, complex.exp (- complex.I * @inner ℝ _ _ x ξ)) ξ₀ =
  (complex.exp (-complex.I * (@inner ℝ _ _ x ξ₀)) * -complex.I) • complex.of_real_clm.comp (innerSL x) :=
begin
  have hdiff_inner : differentiable_at ℝ (λ (ξ : E), ↑(inner x ξ)) ξ₀ :=
  (complex.differentiable_coe inner_differentiable).differentiable_at,
  have hdiff_inner' : differentiable_at ℝ (λ (ξ : E), -complex.I * ↑(inner x ξ)) ξ₀ :=
  differentiable_at.const_mul hdiff_inner _,
  rw complex.fderiv_exp hdiff_inner',
  rw fderiv_const_mul hdiff_inner,
  rw complex.fderiv_coe inner_differentiable_at,
  rw fderiv_inner,
  rw ←mul_smul,
end

end fourier_transform_aux

.

section normedC

variables [inner_product_space ℝ E]
variables [normed_add_comm_group F] [normed_space ℝ F] [complete_space F] [finite_dimensional ℝ F]
variables [normed_space ℂ F]

variables (c : ℂ)

def innerSL_mul (f : 𝓢(E, F)) : 𝓢(E, E →L[ℝ] F) :=
{ to_fun := λ x, ((@continuous_linear_map.lsmul ℝ F _ _ _ ℝ _ _ _ _).flip (f x)).comp (innerSL x),
  -- not clear whether this is the correct definition
  smooth' := sorry,
  decay' := sorry,
}

variables (x : E) (f : 𝓢(E, F)) (g : 𝓢(E, E→L[ℝ] F))

#check c • g

#check complex.of_real_clm.comp (innerSL x)
#check f x
#check ((@continuous_linear_map.lsmul ℝ F _ _ _ ℝ _ _ _ _).flip (f x)).comp (innerSL x)
#check (@continuous_linear_map.lsmul ℂ F _ _ _ ℂ _ _ _ _).flip (f x)--F →L[ℝ] ℝ →L[ℝ] F)


#check λ y, complex.of_real_clm.comp (innerSL x) y • f x

end normedC

#exit

variables [measure_space E] --[borel_space E] [(@volume E _).is_add_haar_measure]

/-- The Fourier transform -/
def fourier_transform_aux (f : E → F) (ξ : E) : F :=
  (2 * real.pi)^(-(finrank ℝ E : ℝ) / 2) • ∫ x, complex.exp (- complex.I * (@inner ℝ _ _ x ξ)) • f x

def fourier_transform (f : 𝓢(E, F)) : 𝓢(E, F) :=
  { to_fun := fourier_transform_aux f,
    smooth' := begin
      rw cont_diff_top,
      intro n,
      sorry,
    end,
    decay' := begin
      intros k n,
      sorry,
    end }


end fourier_transform
