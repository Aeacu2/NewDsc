theory Bernstein_Split

imports
  Main
  "List_changes"
  "Three_Circles.Bernstein"
  "Descartes_Sign_Rule.Descartes_Sign_Rule"
begin


lemma changes_filter_zeros: "changes xs = changes (filter (\<lambda>x. x \<noteq> 0) xs)"
proof (induction xs rule: changes.induct)
  case 1 then show ?case by simp
next
  case (2 x) then show ?case by simp
next
  case (3 x1 x2 xs)
  show ?case
  proof (cases "x2 = 0")
    case True
    (* If x2 is 0, changes skips it. Filter also removes it. *)
    have "changes (x1 # x2 # xs) = changes (x1 # xs)"
      using True by (simp)
    also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # xs))"
      by (metis changes_filter_eq)
    also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # x2 # xs))"
      using True by simp
    finally show ?thesis .
  next
    case False
    (* If x2 != 0, we check x1 *)
    note x2_nz = False
    show ?thesis
    proof (cases "x1 = 0")
      case True
      (* If x1 is 0, changes (0 # x2 # xs). 0*x2 is 0 (not < 0). x2!=0. 
         So changes reduces to changes (x2 # xs).
         Filter removes x1. Result matches. *)
      have "changes (x1 # x2 # xs) = changes (x2 # xs)"
        using True x2_nz by simp
      also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x2 # xs))"
        using "3.IH"(1,3) x2_nz by blast
      also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # x2 # xs))"
        using True by simp
      finally show ?thesis .
    next
      case False
      (* Both non-zero. Changes logic applies. Filter keeps both. *)
      have "changes (x1 # x2 # xs) = (if x1*x2 < 0 then 1 else 0) + changes (x2 # xs)"
        using x2_nz by simp
      also have "\<dots> = (if x1*x2 < 0 then 1 else 0) + changes (filter (\<lambda>x. x \<noteq> 0) (x2 # xs))"
        using "3.IH"(1,3) x2_nz by presburger
      also have "\<dots> = changes (x1 # x2 # (filter (\<lambda>x. x \<noteq> 0) xs))"
        using x2_nz False by simp
      also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # x2 # xs))"
        using x2_nz False by simp
      finally show ?thesis .
    qed
  qed
qed

(* Lemma 2: Equivalence for zero-free lists *)
lemma changes_eq_sign_changes_no_zeros:
  assumes "\<forall>x \<in> set xs. x \<noteq> 0"
  shows "changes xs = int (sign_changes xs)"
  using assms
proof (induction xs rule: induct_list012)
  case 1 then show ?case by (simp add: sign_changes_def)
next
  case (2 x) then show ?case 
    by (simp add: sign_changes_def Let_def)
next
  case (3 x1 x2 xs)
  have x1_nz: "x1 \<noteq> 0" and x2_nz: "x2 \<noteq> 0" and xs_nz: "\<forall>x \<in> set xs. x \<noteq> 0"
    using 3 by auto
    
  (* Simplify sign_changes for the list x1#x2#xs *)
  let ?L = "x1 # x2 # xs"
  let ?sgn_L = "remdups_adj (map sgn ?L)"
  
  (* Determine if signs flip *)
  have sgn_rel: "sgn x1 \<noteq> sgn x2 \<longleftrightarrow> x1 * x2 < 0"
    using x1_nz x2_nz
    by (simp add: mult_less_0_iff sgn_1_neg sgn_if)
    
  show ?case
  proof (cases "x1 * x2 < 0")
    case True
    (* Signs differ *)
    have "sgn x1 \<noteq> sgn x2" using sgn_rel True by simp
    
    (* changes logic: *)
    have ch_L: "changes ?L = 1 + changes (x2 # xs)"
      using True by simp
      
    (* sign_changes logic: *)
    (* Since x1, x2 != 0, filter keeps them. *)
    (* remdups_adj (sgn x1 # sgn x2 # ...) keeps sgn x1 because it differs from sgn x2 *)
    
    have "sign_changes ?L = length (remdups_adj (map sgn (x1#x2#xs))) - 1"
      using x1_nz x2_nz xs_nz 
      unfolding sign_changes_def 
      by (simp add: filter_id_conv sgn_eq_0_iff)
    also have "\<dots> = length (sgn x1 # remdups_adj (map sgn (x2#xs))) - 1"
      using `sgn x1 \<noteq> sgn x2` by auto
    also have "\<dots> = 1 + (length (remdups_adj (map sgn (x2#xs))) - 1)"
      (* map sgn (x2#xs) is non-empty, so remdups is non-empty *)
      by (simp add: algebra_simps)
    also have "\<dots> = 1 + sign_changes (x2 # xs)"
      using x2_nz xs_nz unfolding sign_changes_def 
      by (metis True calculation sign_changes_Cons_Cons_different
          sign_changes_def)
      
    finally show ?thesis 
      using "3.IH"(2) ch_L x2_nz xs_nz by auto
  next
    case False
    (* Signs same (or zero, but zero ruled out) *)
    have "sgn x1 = sgn x2" 
      using sgn_rel False x1_nz x2_nz 
      by metis
      
    (* changes logic: *)
    have ch_L: "changes ?L = changes (x2 # xs)"
      using False x2_nz by simp
      
    (* sign_changes logic: *)
    have "remdups_adj (map sgn (x1#x2#xs)) = remdups_adj (map sgn (x2#xs))"
      using `sgn x1 = sgn x2` by force
      
    then have "sign_changes ?L = sign_changes (x2 # xs)"
      unfolding sign_changes_def using x1_nz x2_nz xs_nz 
      by force
      
    show ?thesis
      using "3.IH"(2) \<open>sign_changes (x1 # x2 # xs) = sign_changes (x2 # xs)\<close> ch_L x2_nz
        xs_nz by force
  qed
qed

lemma changes_eq_sign_changes: "changes xs = int (sign_changes xs)"
proof -
  let ?xs' = "filter (\<lambda>x. x \<noteq> 0) xs"
  
  (* 1. changes is invariant under filter *)
  have "changes xs = changes ?xs'" 
    using changes_filter_zeros 
  by blast
    
  (* 2. sign_changes is invariant under filter (by definition) *)
  have "sign_changes xs = sign_changes ?xs'"
    unfolding sign_changes_def 
    by (metis sign_changes_def sign_changes_filter)
    
  (* 3. Equivalence holds for zero-free lists *)
  have "changes ?xs' = int (sign_changes ?xs')"
    apply (rule changes_eq_sign_changes_no_zeros)
    by simp
    
  show ?thesis
    using `changes xs = changes ?xs'` `sign_changes xs = sign_changes ?xs'` 
          `changes ?xs' = int (sign_changes ?xs')`
    by simp
qed

lemma Bernstein_changes_01_eq_sign_changes:
  "Bernstein_changes_01 p P = sign_changes (Bernstein_coeffs_01 p P)"
proof -
  have "Bernstein_changes_01 p P = nat (changes (Bernstein_coeffs_01 p P))"
    by (simp add: Bernstein_changes_01_def)
  also have "... = nat (int (sign_changes (Bernstein_coeffs_01 p P)))"
    by (simp add: changes_eq_sign_changes)
  also have "... = sign_changes (Bernstein_coeffs_01 p P)"
    by simp
  finally show ?thesis .
qed

theorem Bernstein_changes_01_split:
  assumes t0: "0 < t" and t1: "t < 1" and deg: "degree P \<le> p"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) +
         Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) \<le> Bernstein_changes_01 p P"
proof -
  let ?xs = "Bernstein_coeffs_01 p P"

  have L: "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:0, t:]) = dc_left t ?xs"
    using Bernstein_coeffs_01_split_left[OF deg] .
  have R: "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:t, 1-t:]) = dc_right t ?xs"
    using Bernstein_coeffs_01_split_right[OF deg] .

  have sc: "sign_changes (dc_left t ?xs) + sign_changes (dc_right t ?xs)
            \<le> sign_changes ?xs"
    using sign_changes_dc_split[OF t0 t1] 
    by (simp add: sign_changes_final t0 t1)

  (* unfold Bernstein_changes_01 to changes(Bernstein_coeffs_01 ...) and use changes_eq_sign_changes *)
  show ?thesis
    unfolding Bernstein_changes_01_def L R
    by (metis changes_eq_sign_changes nat_int of_nat_add of_nat_le_iff sc)
qed


lemma Bernstein_changes_split:
  fixes P :: "real poly"
  assumes ac: "a < c" and cb: "c < b" 
      and deg: "degree P \<le> p"
  shows "Bernstein_changes p a c P + Bernstein_changes p c b P \<le> Bernstein_changes p a b P"
proof -
  (* 1. Define the rescaling factor to map [a,b] to [0,1] *)
  let ?t = "(c - a) / (b - a)"
  
  (* 2. Verify t is in (0,1) *)
  from ac cb have ab: "a < b" by simp
  then have anb : "a \<noteq> b" by simp
  have t_pos: "0 < ?t" using ac ab by simp
  have t_less: "?t < 1" using cb ab by (simp add: field_simps)

  (* 3. Express the polynomial on [a,b] rescaled to [0,1] *)
  define Q where "Q = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]"
  have degQ: "degree Q \<le> p" 
    using deg Q_def by (simp)

  (* 4. Use the rescaling lemma to relate general Bernstein changes to [0,1] *)
  have "Bernstein_changes p a b P = Bernstein_changes_01 p Q"
    using Bernstein_changes_eq_rescale[OF \<open>a \<noteq> b\<close> deg] Q_def by simp
    
  (* 5. Relate the left sub-interval [a,c] to [0,t] on the reference interval *)
  moreover have "Bernstein_changes p a c P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:0, ?t:])"
  proof -
    (* Transformation algebra: mapping [0,1] -> [0,t] -> [a,b] is same as [0,1] -> [a,c] *)
    have "Q \<circ>\<^sub>p [:0, ?t:] = (P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]) \<circ>\<^sub>p [:0, (c - a) / (b - a):]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:0, (c - a) / (b - a):])"
      by (simp add: pcompose_assoc)
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]"
      using \<open>a < b\<close> by (simp add: pcompose_pCons)
    finally have "Q \<circ>\<^sub>p [:0, ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]" .
    
    then show ?thesis
      using Bernstein_changes_eq_rescale ac deg by auto
  qed

  (* 6. Relate the right sub-interval [c,b] to [t,1] on the reference interval *)
  moreover have "Bernstein_changes p c b P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:?t, 1 - ?t:])"
  proof -
    have "1 - ?t = (b - c) / (b - a)"
      using ab by (simp add: field_simps)
      
    (* Transformation algebra *)
    have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:])"
      by (simp add: pcompose_assoc)
    
    (* Check the inner composition: [:0, w:] o [:t, 1-t:] = [: w*t, w*(1-t) :] *)
    have "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: (b-a)*?t, (b-a)*(1-?t) :]"
      by (simp add: pcompose_pCons)

    then have composite: "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: c - a, b - c :]" 
      using \<open>1 - (c - a) / (b - a) = (b - c) / (b - a)\<close> by fastforce

    then have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
    by (smt (verit, del_insts) Q_def add_pCons mult.right_neutral one_poly_eq_simps(2)
        pcompose_assoc pcompose_const pcompose_pCons)
      
    then show ?thesis
      using Bernstein_changes_eq_rescale cb deg by force
  qed

  (* 7. Apply the [0,1] splitting lemma *)
  ultimately show ?thesis
    using Bernstein_changes_01_split[OF t_pos t_less degQ]
    by simp
qed


lemma reflect_linear_poly:
  fixes a b :: "'a::zero_neq_one"
  assumes "b \<noteq> 0"
  shows "reflect_poly [:a, b:] = [:b, a:]"
proof -
  (* Explicitly construct the coefficient list *)
  have "pCons b 0 \<noteq> 0" using assms by (simp )
  
  have "coeffs [:a, b:] = coeffs (pCons a (pCons b 0))" by simp
  also have "\<dots> = a # coeffs (pCons b 0)"
    using \<open>pCons b 0 \<noteq> 0\<close> by (simp )
  also have "\<dots> = a # b # coeffs 0"
    using assms by (simp )
  also have "\<dots> = [a, b]" by simp
  finally have coeffs_eq: "coeffs [:a, b:] = [a, b]"
    using \<open>a # coeffs [:b:] = a # b # coeffs 0\<close> coeffs_0_eq_Nil by force
  
  (* Reverse and rebuild *)
  have "rev (coeffs [:a, b:]) = [b, a]" using coeffs_eq by simp
  then have "Poly (rev (coeffs [:a, b:])) = Poly [b, a]" by simp
  also have "\<dots> = [:b, a:]" by simp
  finally show ?thesis unfolding reflect_poly_def .
qed



lemma Bernstein_boundary_invariance_left:
  assumes P_eq: "P = R * [:-t, 1:]" 
      and t_pos: "t > 0"
      and deg: "degree P \<le> p"
      and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:])"
proof -
  \<comment> \<open>1. Relate P_left and R_left\<close>
  let ?P_L = "P \<circ>\<^sub>p [:0, t:]"
  let ?R_L = "R \<circ>\<^sub>p [:0, t:]"
  
  have "[: -t, 1 :] \<circ>\<^sub>p [:0, t:] = [: -t, t :]"
    by (simp add: pcompose_pCons)
  also have "\<dots> = smult t [: -1, 1 :]"
    by simp
  finally have lin_trans: "[: -t, 1 :] \<circ>\<^sub>p [:0, t:] = smult t [: -1, 1 :]" .
  
  have P_L_eq: "?P_L = smult t (?R_L * [: -1, 1 :])"
    using P_eq 
    by (metis lin_trans mult_smult_right pcompose_mult)
  
  have deg_R: "degree R \<le> p - 1" 
    using deg P_eq 
    by (metis (no_types, lifting) ext Nat.le_diff_conv2 One_nat_def Suc_pred add_gr_0
        degree_0 degree_mult_eq degree_pCons_eq_if diff_is_0_eq' le_add_diff_inverse
        le_eq_less_or_eq linorder_not_less one_neq_zero one_pCons
        zero_less_one_class.zero_le_one)
  hence deg_R_L: "degree ?R_L \<le> p - 1"
    by simp
    

  let ?rec_P = "reciprocal_poly p ?P_L"
  let ?rec_R = "reciprocal_poly (p - 1) ?R_L"
  
  have rec_eq: "?rec_P = smult t (?rec_R * [: 1, -1 :])" 
  proof -
    have "reflect_poly [: (-1), 1 :] = [: 1, (-1)::real :]"
      by (simp add: reflect_linear_poly)
      
    have "reciprocal_poly p (?R_L * [: (-1)::real, 1 :]) = ?rec_R * [: 1, (-1)::real :]"
      by (smt (verit) One_nat_def P_L_eq \<open>reflect_poly [:- 1, 1:] = [:1, - 1:]\<close> deg
          deg_R_L degree_mult_eq degree_pCons_eq_if degree_pcompose degree_smult_eq
          diff_diff_left mult.assoc mult.commute mult.right_neutral mult_cancel_left
          pCons_eq_0_iff reciprocal_0_iff reciprocal_reflect_poly reflect_poly_mult
          t_pos)
    
    thus ?thesis using P_L_eq reciprocal_smult
      by (smt (verit, best) One_nat_def deg degree_pCons_eq_if degree_pcompose
          degree_smult_eq mult.right_neutral pCons_eq_0_iff t_pos)
  qed

  \<comment> \<open>3. Compose with [:1, 1:] to get to Monomial Basis\<close>
  let ?Q_P = "?rec_P \<circ>\<^sub>p [:1, 1:]"
  let ?Q_R = "?rec_R \<circ>\<^sub>p [:1, 1:]"
  
  have "?Q_P = smult t (?Q_R * ([: 1, (-1)::real :] \<circ>\<^sub>p [: 1, 1 :]))"
    unfolding rec_eq 
    by (metis pcompose_mult pcompose_smult)
    
  have "[: 1, (-1)::real :] \<circ>\<^sub>p [: 1, 1 :] = [: 0, (-1)::real :]"
    unfolding pcompose_pCons by simp
    
  have Q_P_eq: "?Q_P = smult (-t) (pCons 0 ?Q_R)"
    using \<open>[:1, - 1:] \<circ>\<^sub>p [:1, 1:] = [:0, - 1:]\<close>
      \<open>reciprocal_poly p (P \<circ>\<^sub>p [:0, t:]) \<circ>\<^sub>p [:1, 1:] = smult t (reciprocal_poly (p - 1) (R \<circ>\<^sub>p [:0, t:]) \<circ>\<^sub>p [:1, 1:] * [:1, - 1:] \<circ>\<^sub>p [:1, 1:])\<close>
      minus_pCons mult.commute mult_smult_right smult_minus_left by auto
  have "changes (coeffs ?Q_P) = changes (coeffs (smult (-t) (pCons 0 ?Q_R)))"
    using Q_P_eq by simp
  also have "\<dots> = changes (coeffs (pCons 0 ?Q_R))"
    using t_pos changes_scale_const[of "-t"] 
    by (smt (verit, ccfv_threshold) coeffs_smult)
  also have "\<dots> = changes (coeffs ?Q_R)"
    using changes_pCons by simp
  finally show ?thesis
    unfolding Bernstein_changes_01_def 
    by (smt (verit, del_insts) Bernstein_changes_01_def'
        Bernstein_changes_01_eq_changes Bernstein_coeffs_01_def One_nat_def deg deg_R_L
        degree_pCons_eq_if degree_pcompose mult.right_neutral pCons_eq_0_iff
        t_pos)
qed

lemma Bernstein_boundary_invariance_right:
  assumes P_eq: "P = R * [:-t, (1::real):]" 
      and t_less: "t < 1"
      and deg: "degree P \<le> p"
      and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:])"
proof -
  \<comment> \<open>1. Relate P_right and R_right\<close>
  let ?S = "1 - t"
  let ?P_R = "P \<circ>\<^sub>p [:t, ?S:]"
  let ?R_R = "R \<circ>\<^sub>p [:t, ?S:]"
  
  have S_pos: "?S > 0" using t_less by simp
  
  have "[: -t, 1 :] \<circ>\<^sub>p [:t, ?S:] = [: -t + t, ?S :]"
    by (simp add: pcompose_pCons)
  also have "\<dots> = smult ?S [: 0, 1 :]"
    by (simp)
  finally have lin_trans: "[: -t, 1 :] \<circ>\<^sub>p [:t, ?S:] = smult ?S [: 0, 1 :]" .
  
  have P_R_eq: "?P_R = smult ?S (?R_R * [: 0, 1 :])"
    using P_eq 
    by (metis lin_trans mult_smult_right pcompose_mult)

  have deg_R: "degree R \<le> p - 1" 
    using deg P_eq 
    by (metis (no_types, lifting) ext Nat.le_diff_conv2 One_nat_def Suc_pred add_gr_0 
        degree_0 degree_mult_eq degree_pCons_eq_if diff_is_0_eq' le_add_diff_inverse 
        le_eq_less_or_eq linorder_not_less one_neq_zero one_pCons 
        zero_less_one_class.zero_le_one)
  hence deg_R_R: "degree ?R_R \<le> p - 1"
    by simp

  let ?rec_P = "reciprocal_poly p ?P_R"
  let ?rec_R = "reciprocal_poly (p-1) ?R_R"
  
  have rec_eq: "?rec_P = smult ?S ?rec_R"
  proof -
    have "reflect_poly [: 0, (1::real) :] = [: 1, (0::real) :]"
      by (simp add: reflect_linear_poly)
      
    have "reciprocal_poly p (?R_R * [: 0, (1::real) :]) = ?rec_R * [: 1 :]"
      by (smt (verit) One_nat_def P_R_eq S_pos \<open>reflect_poly [:0, 1:] = [:1, 0:]\<close> deg 
          deg_R_R degree_mult_eq degree_pCons_eq_if degree_pcompose degree_smult_eq 
          diff_diff_left mult.assoc mult.commute mult.right_neutral mult_cancel_left 
          pCons_eq_0_iff reciprocal_0_iff reciprocal_reflect_poly reflect_poly_mult)
    
    also have "\<dots> = ?rec_R" by simp
    
    finally show ?thesis 
      using P_R_eq reciprocal_smult 
      by (smt (verit, ccfv_threshold) \<open>[:- t + t, 1 - t:] = smult (1 - t) [:0, 1:]\<close> deg
          degree_pCons_eq_if degree_pcompose degree_smult_eq pcompose_idR t_less)
  qed

  \<comment> \<open>3. Compose with [:1, 1:] to get to Monomial Basis\<close>
  let ?Q_P = "?rec_P \<circ>\<^sub>p [:1, 1:]"
  let ?Q_R = "?rec_R \<circ>\<^sub>p [:1, 1:]"
  
  have "?Q_P = smult ?S (?Q_R * ([: 1 :] \<circ>\<^sub>p [: 1, 1 :]))"
    unfolding rec_eq 
    by (simp add: pcompose_smult)
    
  have "[: 1 :] \<circ>\<^sub>p [: 1, 1 :] = [: 1 :]"
    by (simp add: pcompose_pCons)
    
  have Q_P_eq: "?Q_P = smult ?S ?Q_R"
    using \<open>[: 1 :] \<circ>\<^sub>p [: 1, 1 :] = ...\<close> 
      \<open>reciprocal_poly p (P \<circ>\<^sub>p [:t, 1 - t:]) \<circ>\<^sub>p [:1, 1:] = smult (1 - t) (reciprocal_poly (p - 1) (R \<circ>\<^sub>p [:t, 1 - t:]) \<circ>\<^sub>p [:1, 1:] * [:1:] \<circ>\<^sub>p [:1, 1:])\<close>
    by auto

  have "changes (coeffs ?Q_P) = changes (coeffs (smult ?S ?Q_R))"
    using Q_P_eq by simp
  also have "\<dots> = changes (coeffs ?Q_R)"
    using S_pos changes_scale_const[of "?S"] 
    by (smt (verit, ccfv_threshold) coeffs_smult)
  finally show ?thesis
    unfolding Bernstein_changes_01_def 
    by (smt (verit, del_insts) Bernstein_changes_01_def' 
        Bernstein_changes_01_eq_changes Bernstein_coeffs_01_def One_nat_def deg deg_R_R 
        degree_pCons_eq_if degree_pcompose mult.right_neutral pCons_eq_0_iff S_pos)
qed


lemma Bernstein_changes_01_split_root:
  assumes t_pos: "0 < t" and t_less: "t < 1" 
      and deg: "degree P \<le> p"
      and root: "poly P t = 0"
      and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) + 
         Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) + 1 \<le> Bernstein_changes_01 p P"
proof -
  \<comment> \<open>1. Factor out the root (x-t)\<close>
  obtain R where P_eq: "P = [:-t, 1:] * R"
    using root poly_eq_0_iff_dvd by (metis dvdE)
  
  have R_nz: "R \<noteq> 0" using P_nz P_eq by auto
  have deg_R: "degree R = degree P - 1" using P_eq R_nz 
    by (smt (verit, ccfv_SIG) add.right_neutral degree_synthetic_div mult_left_cancel
        pCons_0_0 pCons_eq_iff root synthetic_div_correct')
  
  let ?Trans = "\<lambda>f. reciprocal_poly (degree f) f \<circ>\<^sub>p [:1, 1:]"
  
  \<comment> \<open>Transforming the linear factor (x-t)\<close>
  \<comment> \<open>reciprocal of (x-t) is (1-tx). Compose with (x+1): 1 - t(x+1) = (1-t) - tx\<close>
  have lin_trans: "?Trans [:-t, 1:] = [:1 - t, -t:]"
    unfolding reciprocal_poly_def 
    by (auto simp: pcompose_pCons monom_altdef Poly_append)
  
  \<comment> \<open>The root of the transformed linear factor\<close>
  let ?a = "(1-t)/t"
  have a_pos: "?a > 0" using t_pos t_less by (simp add: field_simps)
  
  \<comment> \<open>Check that [:1-t, -t:] is proportional to [:a, -1:]\<close>
  have "[:1 - t, -t:] = smult t [:?a, -1:]"
    using t_pos by (simp add: field_simps)
    
  \<comment> \<open>Transforming the product P = (x-t)R\<close>
  \<comment> \<open>The transform ?Trans is multiplicative (modulo degree shifts)\<close>
  \<comment> \<open>Bernstein_changes_01 p P corresponds to changes(coeffs (?Trans P))\<close>
  
  define Q_R where "Q_R = reciprocal_poly (p-1) R \<circ>\<^sub>p [:1, 1:]"
  define Q_P where "Q_P = reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]"
  
  \<comment> \<open>Algebraic step: Q_P = (x + a_pos) * Q_R (roughly)\<close>
  \<comment> \<open>We use the property that V(P) >= V(R) + 1 via the Descartes lemma on Q_P and Q_R\<close>
  
  have "changes (coeffs Q_P) \<ge> changes (coeffs Q_R) + 1"
  proof -
    \<comment> \<open>This step formally connects the Bernstein polynomials P and R 
        to the Monomial polynomials Q_P and Q_R.
        Since P = (x-t)R, Q_P ends up being Q_R * (linear factor with root a).
        Applying sign_changes_poly_times_root_minus_x gives the result.
    \<close>
    have "reciprocal_poly p P = reciprocal_poly p ([:-t, 1:] * R)"
      using P_eq by simp

      have "changes (coeffs Q_P) \<ge> changes (coeffs Q_R) + 1"
  proof -
    \<comment> \<open>1. Decompose reciprocal_poly p P using the factorization P = (x-t)R\<close>
    
    have deg_lin: "degree [:-t, 1:] = 1" by simp
    have "degree P = 1 + degree R"
      using P_eq R_nz 
    by (metis deg_lin degree_0 degree_mult_eq one_neq_zero)
    have "reciprocal_poly p P = monom 1 (p - degree P) * reflect_poly P"
      using reciprocal_reflect_poly[OF deg] .
    also have "\<dots> = monom 1 (p - (1 + degree R)) * (reflect_poly [:-t, 1:] * reflect_poly R)"
      using P_eq \<open>degree P = 1 + degree R\<close> reflect_poly_mult
      by metis
    also have "\<dots> = (reflect_poly [:-t, 1:]) * (monom 1 ((p - 1) - degree R) * reflect_poly R)"
      by (simp add: mult.assoc mult.left_commute)
    also have "\<dots> = [:1, -t:] * reciprocal_poly (p - 1) R"
    proof -
      have "reciprocal_poly (p - 1) R = monom 1 ((p - 1) - degree R) * reflect_poly R"
        apply (rule reciprocal_reflect_poly)
        using deg \<open>degree P = 1 + degree R\<close> by simp
      moreover have "reflect_poly [:-t, 1:] = [:1, -t:]"
        unfolding reflect_poly_def by (simp add: coeffs_eq_iff)
      ultimately show ?thesis by simp
    qed
    finally have rec_eq: "reciprocal_poly p P = [:1, -t:] * reciprocal_poly (p - 1) R" .
    
    have "Q_P = ([:1, -t:] * reciprocal_poly (p - 1) R) \<circ>\<^sub>p [:1, 1:]"
      unfolding Q_P_def rec_eq ..
    also have "\<dots> = ([:1, -t:] \<circ>\<^sub>p [:1, 1:]) * (reciprocal_poly (p - 1) R \<circ>\<^sub>p [:1, 1:])"
    using pcompose_mult by blast
    also have "\<dots> = ([:1, -t:] \<circ>\<^sub>p [:1, 1:]) * Q_R"
      unfolding Q_R_def by simp
    finally have Q_P_factor: "Q_P = ([:1, -t:] \<circ>\<^sub>p [:1, 1:]) * Q_R" .

    \<comment> \<open>3. Simplify the linear factor transformation\<close>
    
    have "[:1, -t:] \<circ>\<^sub>p [:1, 1:] = [:1, -t:] \<circ>\<^sub>p ([:1:] + monom 1 1)"
      using pCons_one
      by (metis mult.right_neutral pcompose_idR pcompose_pCons x_as_monom)
    (* More direct evaluation of pcompose for linear poly *)
    have "[:1, -t:] \<circ>\<^sub>p [:1, 1:] = [:1:] + smult (-t) [:1, 1:]"
      unfolding pcompose_pCons by simp
    also have "\<dots> = [:1:] + [:-t, -t:]"
      by (simp add: smult_add_left)
    also have "\<dots> = [:1 - t, -t:]"
      by simp
    finally have lin_trans_eq: "[:1, -t:] \<circ>\<^sub>p [:1, 1:] = [:1 - t, -t:]" .

    \<comment> \<open>4. Relate to [:a, -1:] using the scalar t\<close>
    
    let ?a = "(1 - t) / t"
    have a_pos: "?a > 0" using t_pos t_less by (simp add: field_simps)
    
    have "[:1 - t, -t:] = smult t [:?a, -1:]"
      using t_pos by (simp add: field_simps)
      
    hence "Q_P = smult t ([:?a, -1:] * Q_R)"
      using Q_P_factor lin_trans_eq
      by (metis mult_smult_left)
    
    have "changes (coeffs Q_P) = changes (coeffs (smult t ([:?a, -1:] * Q_R)))"
      by (simp add: \<open>Q_P = ...\<close>)
    also have "\<dots> = changes (coeffs ([:?a, -1:] * Q_R))"
      using t_pos changes_scale_const 
      by (smt (verit) coeffs_smult)
    also have "changes (coeffs Q_P) \<ge> changes (coeffs Q_R) + 1"
    proof -
      \<comment> \<open>1. Establish non-zero preconditions\<close>
      have "Q_R \<noteq> 0" 
        unfolding Q_R_def using R_nz deg_R deg 
      by (metis (no_types, opaque_lifting) P_nz add.commute diff_add_cancel
          mult.right_neutral mult_zero_right one_poly_eq_simps(1) pcompose_0
          pcompose_assoc pcompose_idR pcompose_pCons rec_eq reciprocal_0_iff)
      
      have lemma_result: "changes (coeffs ([:?a, -1:] * Q_R)) - changes (coeffs Q_R) > 0"
        using sign_changes_poly_times_root_minus_x[OF \<open>Q_R \<noteq> 0\<close> a_pos] changes_eq_sign_changes
        by (metis (mono_tags, opaque_lifting) int_ops(6) less_numeral_extra(3)
            of_nat_0_less_iff)
      have "changes (coeffs ([:?a, -1:] * Q_R)) \<ge> changes (coeffs Q_R) + 1"
        using lemma_result by simp
        
      \<comment> \<open>4. Relate back to Q_P\<close>
      \<comment> \<open>Recall we proved Q_P = smult t ([:?a, -1:] * Q_R)\<close>
      have "coeffs Q_P = map ((*) t) (coeffs ([:?a, -1:] * Q_R))"
        using \<open>Q_P = smult t ([:?a, -1:] * Q_R)\<close> 
        by (metis coeffs_smult order_less_irrefl t_pos)
      
      hence "changes (coeffs Q_P) = changes (coeffs ([:?a, -1:] * Q_R))"
        using changes_scale_const[of t] t_pos by simp
        
      show ?thesis 
        using \<open>changes (coeffs ([:?a, -1:] * Q_R)) \<ge> changes (coeffs Q_R) + 1\<close> 
        using calculation by presburger
    qed
    finally show ?thesis 
      using \<open>changes (coeffs Q_R) + 1 \<le> changes (coeffs Q_P)\<close> by force
  qed
  show ?thesis
    by (simp add: \<open>changes (coeffs Q_R) + 1 \<le> changes (coeffs Q_P)\<close>)
qed
  
  hence V_diff: "Bernstein_changes_01 p P \<ge> Bernstein_changes_01 (p-1) R + 1"
    unfolding Bernstein_changes_01_eq_changes
    using Q_P_def Q_R_def
  by (simp add: Bernstein_changes_01_eq_changes deg deg_R diff_le_mono)
  have split_R: "Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:]) + 
                 Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:]) 
                 \<le> Bernstein_changes_01 (p-1) R"
    using Bernstein_changes_01_split[OF t_pos t_less] 
    using deg_R deg by simp

  \<comment> \<open>4. Boundary Invariance (Verify P_left/right matches R_left/right)\<close>
  \<comment> \<open>Because P(t)=0, P_left has root at 1, P_right has root at 0.\<close>
  \<comment> \<open>This effectively reduces their degree/coeffs to match R's components.\<close>
  
  have V_left: "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:])"
    using Bernstein_boundary_invariance_left P_eq P_nz deg t_pos by auto
    
  have V_right: "Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:])"
    using Bernstein_boundary_invariance_right P_eq P_nz deg t_pos t_less by auto

  have "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) + Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) + 1
        = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:]) + Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:]) + 1"
    using V_left V_right by simp
  also have "\<dots> \<le> Bernstein_changes_01 (p-1) R + 1"
    using split_R by simp
  also have "\<dots> \<le> Bernstein_changes_01 p P"
    using V_diff by simp
  finally show ?thesis .
qed

lemma Bernstein_changes_split_root:
  fixes P :: "real poly"
  assumes ac: "a < c" and cb: "c < b" and root : "poly P c = 0"
      and deg: "degree P \<le> p" and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes p a c P + Bernstein_changes p c b P + 
         1 \<le> Bernstein_changes p a b P"
proof -
  \<comment> \<open>1. Define the rescaling factor to map [a,b] to [0,1]\<close>
  let ?t = "(c - a) / (b - a)"
  
  \<comment> \<open>2. Verify t is in (0,1)\<close>
  from ac cb have ab: "a < b" by simp
  then have anb : "a \<noteq> b" by simp
  have t_pos: "0 < ?t" using ac ab by simp
  have t_less: "?t < 1" using cb ab by (simp add: field_simps)

  \<comment> \<open>3. Express the polynomial on [a,b] rescaled to [0,1]\<close>
  define Q where "Q = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]"
  have degQ: "degree Q \<le> p" 
    using deg Q_def by (simp)

  \<comment> \<open>4. Use the rescaling lemma to relate general Bernstein changes to [0,1]\<close>
  have term_total: "Bernstein_changes p a b P = Bernstein_changes_01 p Q"
    using Bernstein_changes_eq_rescale[OF \<open>a \<noteq> b\<close> deg] Q_def by simp
    
  \<comment> \<open>5. Relate the left sub-interval [a,c] to [0,t] on the reference interval\<close>
  have term_left: "Bernstein_changes p a c P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:0, ?t:])"
  proof -
    have "Q \<circ>\<^sub>p [:0, ?t:] = (P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]) \<circ>\<^sub>p [:0, (c - a) / (b - a):]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:0, (c - a) / (b - a):])"
      by (simp add: pcompose_assoc)
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]"
      using \<open>a < b\<close> by (simp add: pcompose_pCons)
    finally have "Q \<circ>\<^sub>p [:0, ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]" .
    
    then show ?thesis
      using Bernstein_changes_eq_rescale ac deg by force
  qed

  \<comment> \<open>6. Relate the right sub-interval [c,b] to [t,1] on the reference interval\<close>
  have term_right: "Bernstein_changes p c b P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:?t, 1 - ?t:])"
  proof -
    have "1 - ?t = (b - c) / (b - a)"
      using ab by (simp add: field_simps)
      
    have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:])"
      by (simp add: pcompose_assoc)
    
    have "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: (b-a)*?t, (b-a)*(1-?t) :]"
      by (simp add: pcompose_pCons)
    have "\<dots> = [: c - a, b - c :]"
      using ab \<open>1 - ?t = (b - c) / (b - a)\<close> by fastforce
    have composite: "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: c - a, b - c :]" 
      using
        \<open>[:(b - a) * ((c - a) / (b - a)), (b - a) * (1 - (c - a) / (b - a)):] = [:c - a, b - c:]\<close>
        \<open>[:0, b - a:] \<circ>\<^sub>p [:(c - a) / (b - a), 1 - (c - a) / (b - a):] = [:(b - a) * ((c - a) / (b - a)), (b - a) * (1 - (c - a) / (b - a)):]\<close>
      by presburger
    have "P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:c - a, b - c:] = P \<circ>\<^sub>p ([:a, 1:] \<circ>\<^sub>p [:c - a, b - c:])"
      by (simp add: pcompose_assoc)
    have "[:a, 1:] \<circ>\<^sub>p [:c - a, b - c:] = [:c, b - c:]"
      by (simp add: pcompose_pCons)
    have "\<dots> = [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
      by (simp add: pcompose_pCons)
    have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
      using composite
    by (metis Q_def \<open>[:a, 1:] \<circ>\<^sub>p [:c - a, b - c:] = [:c, b - c:]\<close>
        \<open>[:c, b - c:] = [:c, 1:] \<circ>\<^sub>p [:0, b - c:]\<close> pcompose_assoc)
      
    then show ?thesis
      using Bernstein_changes_eq_rescale cb deg by force
  qed

  \<comment> \<open>7. Relate the root condition P(c)=0 to Q(t)=0\<close>
  have root_eq: "(poly P c = 0) \<longleftrightarrow> (poly Q ?t = 0)"
  proof -
    have "poly Q ?t = poly (P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]) ?t"
      unfolding Q_def by simp
    also have "\<dots> = poly P (poly [:a, 1:] (poly [:0, b - a:] ?t))"
      by (simp add: poly_pcompose)
    also have "\<dots> = poly P (poly [:a, 1:] (?t * (b - a)))"
      by simp
    also have "\<dots> = poly P (a + (c - a))"
      using ab by simp
    also have "\<dots> = poly P c"
      by simp
    finally show ?thesis by simp
  qed

  then have rootQ:  "poly Q ?t = 0" 
    using root by blast

  have Qnz: "Q \<noteq> 0" using P_nz 
    by (metis Q_def Suc_eq_plus1 add_0 bot_nat_0.not_eq_extremum degree_pCons_eq_if
        divide_eq_0_iff less_irrefl one_neq_zero pCons_0_0 pCons_eq_iff pcompose_eq_0
        t_pos)

  show ?thesis
    using Bernstein_changes_01_split_root[OF t_pos t_less degQ rootQ Qnz]
    using term_left term_right term_total by presburger

qed

end