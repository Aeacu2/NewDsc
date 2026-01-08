theory Dsc
  imports
    Dsc_Misc

begin

function (sequential, domintros) dsc :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "dsc p a b P =
    (if a \<ge> b \<or> P = 0 then []
     else
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (let m = (a + b) / 2 in
             (if poly P m = 0 then [(m, m)] else []) @
             dsc p a m P @
             dsc p m b P)))"
  by pat_completeness auto

lemma dsc_domI_general:
  fixes \<delta> :: real and p :: nat and P :: "real poly"
  assumes \<delta>_pos: "\<delta> > 0"
      and small: "\<And>a b. a < b \<Longrightarrow> b - a \<le> \<delta> \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
  shows "\<And>a b. a < b \<Longrightarrow> dsc_dom (p,a,b,P)"
proof -
  define \<mu> where "\<mu> = (\<lambda> a b. mu \<delta> a b)"
  let ?Prop = "\<lambda>n::nat. \<forall>a b. \<mu> a b < n \<longrightarrow> a < b \<longrightarrow> dsc_dom (p,a,b,P)"

  have step: "\<And>n. (\<And>m. m < n \<Longrightarrow> ?Prop m) \<Longrightarrow> ?Prop n"
  proof -
    fix n assume IH: "\<And>m. m < n \<Longrightarrow> ?Prop m"
    show "?Prop n"
    proof (intro allI impI)
      fix a b :: real
      assume abn: "\<mu> a b < n" and ab: "a < b"
      show "dsc_dom (p,a,b,P)"
      proof (cases "a \<ge> b \<or> P = 0")
        case True
        then show ?thesis by (auto intro: dsc.domintros)
      next
        case False
        let ?v = "Bernstein_changes p a b P"
        show ?thesis
        proof (cases "?v = 0 \<or> ?v = 1")
          case True
          then show ?thesis using False by (auto intro: dsc.domintros)
        next
          case False
          have v_ge2: "2 \<le> ?v" using False Bernstein_changes_def by fastforce
          have \<delta>lt: "\<delta> < b - a"
          proof (rule ccontr)
            assume "\<not> \<delta> < b - a"
            then have "b - a \<le> \<delta>" by linarith
            then have "Bernstein_changes p a b P \<le> 1" using ab small by presburger
            with v_ge2 show False by linarith
          qed
          define m where "m = (a + b) / 2"
          have lessL: "\<mu> a m < \<mu> a b"
            by (simp add: \<delta>_pos \<delta>lt \<open>\<mu> \<equiv> mu \<delta>\<close> ab m_def
                mu_halve_strict(1))
          have lessR: "\<mu> m b < \<mu> a b" 
            by (simp add: \<delta>_pos \<delta>lt \<open>\<mu> \<equiv> mu \<delta>\<close> ab m_def
                mu_halve_strict(2))
          have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
          have IH_at: "?Prop (\<mu> a b)"
            using IH abn by simp
          have IH_L: "dsc_dom (p,a,m,P)"
            using IH_at lessL am by blast
          have IH_R: "dsc_dom (p,m,b,P)"
            using IH_at lessR mb by blast
          show ?thesis
            using dsc.domintros[of p a b P] False False IH_L IH_R using m_def by blast 
        qed
      qed
    qed
  qed
   have "\<And>n. ?Prop n" by (rule less_induct, rule step)
  then show "\<And>a b. a < b \<Longrightarrow> dsc_dom (p,a,b,P)"
  proof
    fix a b :: real
    assume ab: "a < b"
    have H: "?Prop (Suc (\<mu> a b))" by (rule \<open>\<And>n. ?Prop n\<close>)
    from H have H1:
      "\<forall>b. \<mu> a b < Suc (\<mu> a b) \<longrightarrow> a < b \<longrightarrow> dsc_dom (p,a,b,P)"
    using
      \<open>\<And>n. \<forall>a b. \<mu> a b < n \<longrightarrow> a < b \<longrightarrow> dsc_dom (p, a, b, P)\<close>
    by auto
    from H1 have H2:
      "\<mu> a b < Suc (\<mu> a b) \<longrightarrow> a < b \<longrightarrow> dsc_dom (p,a,b,P)"
      by (rule spec[of _ b])
    from H2 show "dsc_dom (p,a,b,P)"
      by (simp add: ab)
  qed
qed

lemma dsc_terminates_squarefree_real:
  fixes P :: "real poly"
  defines "Q \<equiv> map_poly (of_real :: real \<Rightarrow> complex) P"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0: "p \<noteq> 0"
      and rsf: "rsquarefree Q"
  shows "\<And>a b. a < b \<Longrightarrow> dsc_dom (p,a,b,P)"
proof -
  have \<delta>_pos: "delta_P P > 0"
    using P0 delta_P_pos by blast

  have small:
    "\<And>a b. a < b \<Longrightarrow> b - a \<le> delta_P P \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
  using Bernstein_changes_small_interval_le_1 P0 Q_def deg p0 rsf
  by blast

  show "\<And>a b. a < b \<Longrightarrow> dsc_dom (p,a,b,P)"
    using dsc_domI_general[OF \<delta>_pos small] .
qed

lemma dsc_correct:
  assumes dom: "dsc_dom (p,a,b,P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
  shows "\<forall>I \<in> set (dsc p a b P). dsc_pair_ok P I"
using dom deg P0
proof (induction p a b P rule: dsc.pinduct)
  case (1 p a b P)

  have dsc_eq:
    "dsc p a b P =
       (if a \<ge> b \<or> P = 0 then []
        else
          (let v = Bernstein_changes p a b P in
           if v = 0 then []
           else if v = 1 then [(a,b)]
           else
             (let m = (a + b) / 2 in
                (if poly P m = 0 then [(m,m)] else []) @
                dsc p a m P @
                dsc p m b P)))"
    using "1.hyps" dsc.psimps by blast

  show ?case
  proof (cases "a \<ge> b \<or> P = 0")
    case True
    then show ?thesis
      by (simp add: dsc_eq dsc_pair_ok_def)
  next
    case False
    hence ab: "a < b" and P0': "P \<noteq> 0"
      by auto
    from 1 have deg': "degree P \<le> p"
      by simp

    show ?thesis
    proof (subst dsc_eq, simp only: Let_def Ball_def)
      let ?v = "Bernstein_changes p a b P"

      have H0:
        "\<forall>I\<in> set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                   (let m = (a + b) / 2 in
                      (if poly P m = 0 then [(m, m)] else []) @
                      dsc p a m P @ dsc p m b P)).
           dsc_pair_ok P I"
      proof (cases "?v = 0")
        case True
        then show ?thesis by simp
      next
        case v0: False
        show ?thesis
        proof (cases "?v = 1")
          case True
          hence v1: "Bernstein_changes p a b P = 1"
            by simp
          have "roots_in P a b = 1"
            using Bernstein_changes_1_one_root[OF deg' P0' ab v1] .
          hence "dsc_pair_ok P (a,b)"
            by (simp add: dsc_pair_ok_def roots_in_def ab)
          with v0 True show ?thesis
            by simp
        next
          case v_ge2: False
          hence v2: "?v \<ge> 2"
            using v0
            by (smt (verit) Bernstein_changes_def int_nat_eq)
          let ?m = "(a + b) / 2"
          have am: "a < ?m" and mb: "?m < b"
            using ab by simp_all

          have IH_left:
            "\<forall>I\<in>set (dsc p a ?m P). dsc_pair_ok P I"
            using "1.IH"(1) False deg' v0 v_ge2 by blast

          have IH_right:
            "\<forall>I\<in>set (dsc p ?m b P). dsc_pair_ok P I"
            using "1.IH"(2) False deg' v0 v_ge2 by blast
          
          show ?thesis
          proof (simp add: v0 v_ge2 Let_def, intro ballI impI)
            fix I
            assume Ain:
              "I \<in> {x. x = (?m, ?m) \<and> poly P ?m = 0} \<union>
                   (set (dsc p a ?m P) \<union> set (dsc p ?m b P))"
            then have disj:
              "I = (?m,?m) \<and> poly P ?m = 0
               \<or> I \<in> set (dsc p a ?m P)
               \<or> I \<in> set (dsc p ?m b P)"
              by auto
            from disj show "dsc_pair_ok P I"
            proof
              assume "I = (?m,?m) \<and> poly P ?m = 0"
              then show "dsc_pair_ok P I"
                by (simp add: dsc_pair_ok_def)
            next
              assume alt:
                "I \<in> set (dsc p a ?m P) \<or> I \<in> set (dsc p ?m b P)"
              from alt show "dsc_pair_ok P I"
              proof
                assume "I \<in> set (dsc p a ?m P)"
                then show "dsc_pair_ok P I"
                  using IH_left by blast
              next
                assume "I \<in> set (dsc p ?m b P)"
                then show "dsc_pair_ok P I"
                  using IH_right by blast
              qed
            qed
          qed
        qed
      qed

      have H:
        "\<forall>I\<in>set (if Bernstein_changes p a b P = 0 then []
                 else if Bernstein_changes p a b P = 1 then [(a, b)]
                      else (if poly P ((a + b) / 2) = 0
                            then [((a + b) / 2, (a + b) / 2)]
                            else []) @
                           dsc p a ((a + b) / 2) P @
                           dsc p ((a + b) / 2) b P).
           dsc_pair_ok P I"
        using H0
        by (simp add: Let_def)

      show
        "\<forall>x. x \<in> set (if b \<le> a \<or> P = 0 then []
                      else if Bernstein_changes p a b P = 0 then []
                           else if Bernstein_changes p a b P = 1 then [(a, b)]
                                else (if poly P ((a + b) / 2) = 0
                                      then [((a + b) / 2, (a + b) / 2)]
                                      else []) @
                                     dsc p a ((a + b) / 2) P @
                                     dsc p ((a + b) / 2) b P) \<longrightarrow>
             dsc_pair_ok P x"
      proof (intro allI impI)
        fix x
        assume Xin:
          "x \<in> set (if b \<le> a \<or> P = 0 then []
                    else if Bernstein_changes p a b P = 0 then []
                         else if Bernstein_changes p a b P = 1 then [(a, b)]
                              else (if poly P ((a + b) / 2) = 0
                                    then [((a + b) / 2, (a + b) / 2)]
                                    else []) @
                                   dsc p a ((a + b) / 2) P @
                                   dsc p ((a + b) / 2) b P)"

        have guard: "\<not> (b \<le> a \<or> P = 0)"
          using ab P0' by auto

        from Xin guard
        have Xin':
          "x \<in> set (if Bernstein_changes p a b P = 0 then []
                    else if Bernstein_changes p a b P = 1 then [(a, b)]
                         else (if poly P ((a + b) / 2) = 0
                               then [((a + b) / 2, (a + b) / 2)]
                               else []) @
                              dsc p a ((a + b) / 2) P @
                              dsc p ((a + b) / 2) b P)"
          by simp

        from H have "dsc_pair_ok P x"
          using Xin' by blast
        thus "dsc_pair_ok P x" .
      qed
    qed
  qed
qed


lemma dsc_complete:
  assumes dom: "dsc_dom (p,a,b,P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (dsc p a b P). fst I \<le> x \<and> x \<le> snd I)"
using dom deg P0
proof (induction p a b P rule: dsc.pinduct)
  case (1 p a b P)
  find_theorems intro
  have dsc_eq:
    "dsc p a b P =
       (if a \<ge> b \<or> P = 0 then []
        else
          (let v = Bernstein_changes p a b P in
           if v = 0 then []
           else if v = 1 then [(a,b)]
           else
             (let m = (a + b) / 2 in
                (if poly P m = 0 then [(m,m)] else []) @
                dsc p a m P @
                dsc p m b P)))"
    using "1.hyps" dsc.psimps by blast

  show ?case
  proof (cases "a \<ge> b \<or> P = 0")
    case True
    then show ?thesis
      using "1.prems"(2,3,5) by argo
  next
    case False
    hence ab: "a < b" and P0': "P \<noteq> 0"
      using P0 by auto
    from 1 have deg': "degree P \<le> p"
      by simp

    have H:
      "\<And>x::real. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (dsc p a b P). fst I \<le> x \<and> x \<le> snd I)"
    proof -
      fix x :: real
      assume root: "poly P x = 0"
         and ax:   "a < x"
         and xb:   "x < b"

      let ?v = "Bernstein_changes p a b P"

      have v_nonzero: "?v \<noteq> 0"
        using Bernstein_changes_pos_of_root[OF deg' P0' ab root ax xb] .

      have Ex0:
        "\<exists>I\<in>set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                        (let m = (a + b) / 2 in
                           (if poly P m = 0 then [(m, m)] else []) @
                           dsc p a m P @ dsc p m b P)).
                 fst I \<le> x \<and> x \<le> snd I"
      proof (cases "?v = 1")
        case True
        hence v1: "?v = 1" by simp
        have cover: "fst (a,b) \<le> x \<and> x \<le> snd (a,b)"
          using ax xb by simp
        moreover have mem:
          "(a,b) \<in> set (if ?v = 0 then [] else if ?v = 1 then [(a,b)] else
                        (let m = (a + b) / 2 in
                           (if poly P m = 0 then [(m,m)] else []) @
                           dsc p a m P @ dsc p m b P))"
          using v1 v_nonzero by simp
        ultimately show ?thesis
          by blast
      next
        case v_ne1: False
        hence v_ge2: "?v \<ge> 2"
          using v_nonzero
          by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)

        let ?m = "(a + b) / 2"
        have am: "a < ?m" and mb: "?m < b"
          using ab by simp_all

        have IH_left:
          "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < ?m \<Longrightarrow>
               (\<exists>I\<in>set (dsc p a ?m P). fst I \<le> x \<and> x \<le> snd I)"
          using "1.IH"(1) False deg' v_ne1 v_nonzero by blast

        have IH_right:
          "\<And>x. poly P x = 0 \<Longrightarrow> ?m < x \<Longrightarrow> x < b \<Longrightarrow>
               (\<exists>I\<in>set (dsc p ?m b P). fst I \<le> x \<and> x \<le> snd I)"
          using "1.IH"(2) False deg' v_ne1 v_nonzero by blast

        show ?thesis
        proof (cases "x = ?m")
          case mid: True
          then have "poly P ?m = 0"
            using root by blast
          then have mem_root:
            "(?m,?m) \<in> set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                             (let m = (a + b) / 2 in
                                (if poly P m = 0 then [(m, m)] else []) @
                                dsc p a m P @
                                dsc p m b P))"
            using v_nonzero v_ne1 by (simp add: Let_def mid)
          moreover have cover_root:
            "fst (?m,?m) \<le> x \<and> x \<le> snd (?m,?m)"
            using mid by simp
          ultimately show ?thesis
            by blast
        next
          case mid_ne: False
          then have x_split: "x < ?m \<or> ?m < x"
            using ax xb by linarith

          show ?thesis
          proof (cases "x < ?m")
            case x_left: True
            then have ax': "a < x" and xm': "x < ?m"
              using ax by simp_all
            have ex_left:
              "\<exists>I\<in>set (dsc p a ?m P). fst I \<le> x \<and> x \<le> snd I"
              using IH_left root ax' xm' by blast
            then obtain I where I_in: "I \<in> set (dsc p a ?m P)"
                             and I_cov: "fst I \<le> x \<and> x \<le> snd I"
              by blast
            have mem_top:
              "I \<in> set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                         (let m = (a + b) / 2 in
                            (if poly P m = 0 then [(m, m)] else []) @
                            dsc p a m P @ dsc p m b P))"
              using v_nonzero v_ne1 I_in
              by (simp add: Let_def)
            from mem_top I_cov show ?thesis
              by blast
          next
            case not_left: False
            with x_split have x_right: "?m < x" by simp
            have mx': "?m < x" using x_right .
            have ex_right:
              "\<exists>I\<in>set (dsc p ?m b P). fst I \<le> x \<and> x \<le> snd I"
              using IH_right root mx' xb by blast
            then obtain I where I_in: "I \<in> set (dsc p ?m b P)"
                             and I_cov: "fst I \<le> x \<and> x \<le> snd I"
              by blast
            have mem_top:
              "I \<in> set (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
                         (let m = (a + b) / 2 in
                            (if poly P m = 0 then [(m, m)] else []) @
                            dsc p a m P @ dsc p m b P))"
              using v_nonzero v_ne1 I_in
              by (simp add: Let_def)
            from mem_top I_cov show ?thesis
              by blast
          qed
        qed
      qed

      have Ex:
        "\<exists>I\<in>set (if Bernstein_changes p a b P = 0 then []
                 else if Bernstein_changes p a b P = 1 then [(a, b)]
                      else let m = (a + b) / 2
                           in (if poly P m = 0 then [(m, m)] else []) @
                              dsc p a m P @ dsc p m b P).
           fst I \<le> x \<and> x \<le> snd I"
        using Ex0 by simp

      have Ex_dsc:
        "\<exists>I\<in>set (dsc p a b P). fst I \<le> x \<and> x \<le> snd I"
        using Ex
        by (simp add: dsc_eq False Let_def)

      show "\<exists>I\<in>set (dsc p a b P). fst I \<le> x \<and> x \<le> snd I"
        using Ex_dsc by simp
    qed

    show ?thesis
      using "1.prems"(1,2,3) H by blast

  qed
qed

end