theory Coefficients
  imports
    "Budan_Fourier.Descartes_Roots_Test"
    "Three_Circles.Three_Circles"
begin

lemma reciprocal_shift_rescale_eq_fcompose:
  fixes P :: "real poly" and a b :: real
  defines "p \<equiv> degree P"
  defines "R \<equiv> P \<circ>\<^sub>p [:b,1:] \<circ>\<^sub>p [:0, a-b:]"
  shows "(reciprocal_poly p R) \<circ>\<^sub>p [:1,1:] = fcompose P [:a,b:] [:1,1:]"
proof -
  let ?L = "(reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]"
  let ?M = "fcompose P [:a,b:] [:1,1:]"
  let ?D = "?L - ?M"

  have eval_eq: "\<And>x. x \<noteq> -1 \<Longrightarrow> poly ?L x = poly ?M x"
    proof -
      fix x :: real
      assume hx: "x \<noteq> -1"

      let ?den = "poly [:1,1:] x"   
      have hden: "?den \<noteq> 0"
        using hx by simp
    
      have L_eval0: "poly ?L x = poly (reciprocal_poly p R) ?den"
        by (simp add: poly_pcompose)
    
      have L_eval1: "poly (reciprocal_poly p R) ?den = ?den^p * poly R (inverse ?den)"
        using poly_reciprocal hden
        by (smt (verit, del_insts) One_nat_def R_def degree_pCons_eq_if degree_pcompose diff_is_0_eq diff_zero
            le_eq_less_or_eq mult.right_neutral mult_zero_right not_less p_def)
    
      have R_at_inv: "poly R (inverse ?den) = poly P (b + (a - b) * inverse ?den)"
        unfolding R_def
        by (simp add: poly_pcompose algebra_simps)
    
      have frac_id: "b + (a - b) * inverse ?den = (a + b*x) / ?den"
      proof -
        have den_simp: "?den = 1 + x" by simp
        have hden': "1 + x \<noteq> 0"
          using hx by simp
        show ?thesis
          unfolding den_simp
          using hden'
          by (simp add: field_simps)
      qed
    
      have L_eval:
        "poly ?L x = ?den^p * poly P ((a + b*x) / ?den)"
        using L_eval0 L_eval1 R_at_inv frac_id
        by simp

      have M_eval0:
        "poly ?M x =
           poly P (poly [:a,b:] x / poly [:1,1:] x) * (poly [:1,1:] x) ^ degree P"
        using poly_fcompose[OF hden]
        by simp
    
      have M_eval:
        "poly ?M x = poly P ((a + b*x) / ?den) * ?den^p"
        unfolding p_def
        using M_eval0
        by (simp add: algebra_simps)

      show "poly ?L x = poly ?M x"
        using L_eval M_eval
        by simp
    qed

  have sub_roots: "range (of_nat :: nat \<Rightarrow> real) \<subseteq> {x. poly ?D x = 0}"
  proof
    fix x :: real
    assume "x \<in> range (of_nat :: nat \<Rightarrow> real)"
    then obtain n :: nat where x_def: "x = of_nat n" by blast
    have xne: "x \<noteq> -1"
      by (simp add: x_def)
    show "x \<in> {x. poly ?D x = 0}"
      using eval_eq[OF xne] unfolding x_def by simp
  qed

  have inf_sub: "infinite (range (of_nat :: nat \<Rightarrow> real))"
    by (rule range_inj_infinite) simp

  have inf_roots: "infinite {x. poly ?D x = 0}"
    using inf_sub sub_roots finite_subset by blast

  have D0: "?D = 0"
    using inf_roots poly_roots_finite[of ?D] by blast

  from D0 show ?thesis by simp
qed

lemma changes_Bernstein_coeffs_eq_changes_coeffs:
  fixes P :: "real poly" and a b :: real
  defines "p \<equiv> degree P"
  defines "R \<equiv> P \<circ>\<^sub>p [:b,1:] \<circ>\<^sub>p [:0, a-b:]"
  shows "changes (Bernstein_coeffs p b a P)
       = changes (coeffs ((reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]))"
proof -
  (* your list is exactly the 01-Bernstein coefficient list of the rescaled poly R *)
  have coeffs_id:
    "Bernstein_coeffs p b a P = Bernstein_coeffs_01 p R"
    unfolding Bernstein_coeffs_def Bernstein_coeffs_01_def R_def
    by (simp add: pcompose_assoc)

  have degR_le: "degree R \<le> p"
    unfolding R_def p_def
    by (metis (no_types, lifting) One_nat_def degree_pCons_eq_if degree_pcompose le_eq_less_or_eq
        mult.right_neutral mult_zero_right zero_le)
    
  (* Bernstein_changes_01 is int-coerced nat(changes ...); remove the coercion using changes_nonneg *)
  have B01_is_changes:
    "Bernstein_changes_01 p R = changes (Bernstein_coeffs_01 p R)"
    unfolding Bernstein_changes_01_def
    using changes_nonneg[of "Bernstein_coeffs_01 p R"] by simp

  have "changes (Bernstein_coeffs_01 p R)
      = changes (coeffs ((reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]))"
    using Bernstein_changes_01_eq_changes[OF degR_le]
    unfolding B01_is_changes
    by simp

  thus ?thesis
    using coeffs_id by simp
qed


theorem descartes_roots_test_eq_Bernstein_changes:
  fixes P :: "real poly" and a b :: real
  defines "p \<equiv> degree P"
  shows "descartes_roots_test a b P = Bernstein_changes p b a P"
proof -
  define R where "R = P \<circ>\<^sub>p [:b,1:] \<circ>\<^sub>p [:0, a-b:]"

  have poly_id:
    "(reciprocal_poly p R) \<circ>\<^sub>p [:1,1:] = fcompose P [:a,b:] [:1,1:]"
    using R_def p_def reciprocal_shift_rescale_eq_fcompose by presburger

  have ch_id:
    "changes (Bernstein_coeffs p b a P) = changes (coeffs (fcompose P [:a,b:] [:1,1:]))"
    using changes_Bernstein_coeffs_eq_changes_coeffs p_def reciprocal_shift_rescale_eq_fcompose
    by presburger

  show ?thesis
    unfolding descartes_roots_test_def Bernstein_changes_def
    using ch_id by simp
qed

end
