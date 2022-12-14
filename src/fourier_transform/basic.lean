import japanese_bracket
import analysis.schwartz_space

noncomputable theory

open_locale big_operators nnreal filter topological_space ennreal schwartz_space

open asymptotics filter set real measure_theory finite_dimensional 

variables {E F : Type*}

namespace schwartz_map

variables [normed_add_comm_group E] [normed_space β E] [finite_dimensional β E]
variables [measure_space E] [borel_space E] [(@volume E _).is_add_haar_measure]
variables [normed_add_comm_group F] [normed_space β F] 

@[protected, measurability] lemma ae_strongly_measurable (f : π’(E, F)) : ae_strongly_measurable (f : E β F) volume :=
f.continuous.ae_strongly_measurable

lemma one_add_pow_smul_le (f : π’(E, F)) (x : E) (n : β): β₯(1 + β₯xβ₯) ^ n β’ f xβ₯ β€
  β (m : β) in finset.range (n + 1), (n.choose m : β) * (schwartz_map.seminorm β m 0) f :=
begin
  rw add_comm,
  rw add_pow,
  rw finset.sum_smul,
  simp only [one_pow, mul_one],
  refine (norm_sum_le (finset.range (n + 1)) _).trans _,
  refine finset.sum_le_sum (Ξ» m hm, _),
  rw mul_comm,
  simp only [βsmul_smul, norm_smul, norm_coe_nat, norm_pow, norm_norm],
  exact mul_le_mul_of_nonneg_left (f.norm_pow_mul_le_seminorm β _ _) (by positivity),
end

/-- To be generalized to all p -/
@[protected] lemma mem_βp_one (f : π’(E, F)) : mem_βp (f : E β F) 1 volume :=
begin
  have hr : (finrank β E : β) < finrank β E + 1 := lt_add_one (finrank β E), 
  have h := mem_βp_rpow_neg_one_add_norm hr,
  let c := β (m : β) in finset.range ((finrank β E + 1) + 1),
    ((finrank β E + 1).choose m : β) * (schwartz_map.seminorm β m 0) f,
  have h' : β x : E, β₯f xβ₯ β€ c * β₯(1 + β₯xβ₯) ^ -((finrank β E : β) + 1)β₯ :=
  begin
    intros x,
    have hpos : 0 < 1 + β₯xβ₯ := by positivity,
    rw βone_smul β (f x),
    nth_rewrite 0 βreal.rpow_zero (1 + β₯xβ₯),
    rw βsub_self ((finrank β E : β) + 1),
    rw sub_eq_neg_add,
    rw real.rpow_add hpos,
    rw βsmul_smul,
    rw norm_smul,
    rw mul_comm,
    refine mul_le_mul_of_nonneg_right _ (by positivity),
    norm_cast,
    exact one_add_pow_smul_le _ _ _,
  end,
  exact h.of_le_mul (by measurability) (ae_of_all _ h'),
end

@[protected] lemma integrable (f : π’(E, F)) : integrable (f : E β F) :=
begin
  rw βmem_βp_one_iff_integrable,
  exact f.mem_βp_one,
end

end schwartz_map

section fourier_transform_aux

variables [inner_product_space β E]
variables [normed_add_comm_group F] [normed_space β F] [complete_space F] [finite_dimensional β F]
variables [has_smul β F]

lemma complex.differentiable_at_coe {f : E β β} {x : E} (hf : differentiable_at β f x) :
  differentiable_at β (Ξ» y, (f y : β)) x :=
complex.of_real_clm.differentiable_at.comp _ hf

lemma complex.differentiable_coe {f : E β β} (hf : differentiable β f) :
  differentiable β (Ξ» x, (f x : β)) :=
complex.of_real_clm.differentiable.comp hf

lemma complex.fderiv_coe {f : E β β} {y : E} (hf : differentiable_at β f y) :
  fderiv β (Ξ» x, (f x : β)) y = complex.of_real_clm.comp (fderiv β f y) :=
begin
  change fderiv β (Ξ» x, complex.of_real_clm (f x)) y = complex.of_real_clm.comp (fderiv β f y),
  convert fderiv.comp _ complex.of_real_clm.differentiable_at hf,
  exact complex.of_real_clm.fderiv.symm,
end

lemma complex.fderiv_exp {f : E β β} {x : E} (hc : differentiable_at β f x) :
  fderiv β (Ξ» x, complex.exp (f x)) x = complex.exp (f x) β’ (fderiv β f x) :=
hc.has_fderiv_at.cexp.fderiv

lemma inner_differentiable_at {y : E} {z : E} : differentiable_at β (Ξ» x, @inner β _ _ y x) z :=
(@innerSL β _ _ _ y).differentiable_at

lemma inner_differentiable {y : E} : differentiable β (Ξ» x, @inner β _ _ y x) :=
(@innerSL β _ _ _ y).differentiable

lemma fderiv_inner {y xβ : E} : fderiv β (Ξ» x, @inner β _ _ y x) xβ = innerSL y :=
(@innerSL β _ _ _ y).fderiv

lemma fderiv_exp_inner_left (xβ ΞΎ : E) : fderiv β (Ξ» x, complex.exp (- complex.I * @inner β _ _ x ΞΎ)) xβ =
  (complex.exp (-complex.I * (@inner β _ _ xβ ΞΎ)) * -complex.I) β’ complex.of_real_clm.comp (innerSL ΞΎ) :=
begin
  have hdiff_inner : differentiable_at β (Ξ» (x : E), β(inner ΞΎ x)) xβ :=
  (complex.differentiable_coe inner_differentiable).differentiable_at,
  have hdiff_inner' : differentiable_at β (Ξ» (x : E), -complex.I * β(inner ΞΎ x)) xβ :=
  differentiable_at.const_mul hdiff_inner _,
  --((complex.differentiable_coe inner_differentiable).const_mul _).differentiable_at,
  simp_rw real_inner_comm,
  rw complex.fderiv_exp hdiff_inner',
  rw fderiv_const_mul hdiff_inner,
  rw complex.fderiv_coe inner_differentiable_at,
  rw fderiv_inner,
  rw βmul_smul,
  simp only [real_inner_comm xβ ΞΎ],
  /-simp_rw real_inner_comm,
  rw βfderiv_exp_inner_left ΞΎβ x,
  congr,
  ext1,
  rw real_inner_comm,-/
end

lemma fderiv_exp_inner_right (ΞΎβ x : E) : fderiv β (Ξ» ΞΎ, complex.exp (- complex.I * @inner β _ _ x ΞΎ)) ΞΎβ =
  (complex.exp (-complex.I * (@inner β _ _ x ΞΎβ)) * -complex.I) β’ complex.of_real_clm.comp (innerSL x) :=
begin
  have hdiff_inner : differentiable_at β (Ξ» (ΞΎ : E), β(inner x ΞΎ)) ΞΎβ :=
  (complex.differentiable_coe inner_differentiable).differentiable_at,
  have hdiff_inner' : differentiable_at β (Ξ» (ΞΎ : E), -complex.I * β(inner x ΞΎ)) ΞΎβ :=
  differentiable_at.const_mul hdiff_inner _,
  rw complex.fderiv_exp hdiff_inner',
  rw fderiv_const_mul hdiff_inner,
  rw complex.fderiv_coe inner_differentiable_at,
  rw fderiv_inner,
  rw βmul_smul,
end

end fourier_transform_aux

.

section normedC

variables [inner_product_space β E]
variables [normed_add_comm_group F] [normed_space β F] [complete_space F] [finite_dimensional β F]
variables [normed_space β F]

variables (c : β)

def innerSL_mul (f : π’(E, F)) : π’(E, E βL[β] F) :=
{ to_fun := Ξ» x, ((@continuous_linear_map.lsmul β F _ _ _ β _ _ _ _).flip (f x)).comp (innerSL x),
  -- not clear whether this is the correct definition
  smooth' := sorry,
  decay' := sorry,
}

variables (x : E) (f : π’(E, F)) (g : π’(E, EβL[β] F))

#check c β’ g

#check complex.of_real_clm.comp (innerSL x)
#check f x
#check ((@continuous_linear_map.lsmul β F _ _ _ β _ _ _ _).flip (f x)).comp (innerSL x)
#check (@continuous_linear_map.lsmul β F _ _ _ β _ _ _ _).flip (f x)--F βL[β] β βL[β] F)


#check Ξ» y, complex.of_real_clm.comp (innerSL x) y β’ f x

end normedC

#exit

variables [measure_space E] --[borel_space E] [(@volume E _).is_add_haar_measure]

/-- The Fourier transform -/
def fourier_transform_aux (f : E β F) (ΞΎ : E) : F :=
  (2 * real.pi)^(-(finrank β E : β) / 2) β’ β« x, complex.exp (- complex.I * (@inner β _ _ x ΞΎ)) β’ f x

def fourier_transform (f : π’(E, F)) : π’(E, F) :=
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
