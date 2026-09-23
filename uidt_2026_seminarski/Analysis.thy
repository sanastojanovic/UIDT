theory Analysis
  imports Complex_Main "HOL-Analysis.Finite_Cartesian_Product" "HOL-Library.Extended_Real"
begin

section \<open>3.1 Definicije\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
type_synonym 'a sequence = "nat \<Rightarrow> 'a"

(* mi22062_Nenad_Pesic_FORMULACIJA *)
definition tendsto :: "'a::metric_space sequence \<Rightarrow> 'a \<Rightarrow> bool" where
  "tendsto x a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (x n) a < \<epsilon>)"

(* mi22062_Nenad_Pesic_FORMULACIJA *)
definition bounded :: "'a::metric_space sequence \<Rightarrow> bool" where
  "bounded x \<longleftrightarrow> (\<exists>p M. \<forall>n. dist (x n) p \<le> M)"

section \<open>Rudin 3.2 (b) -- Jedinstvenost granicne vrednosti\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma tendsto_common_index:
  fixes x :: "'a::metric_space sequence"
  assumes "tendsto x a"
    and "tendsto x b"
    and "\<epsilon> > 0"
  shows "\<exists> n. dist (x n) a < \<epsilon> \<and> dist (x n) b < \<epsilon>"
(* mi22062_Nenad_Pesic_DOKAZ *)
proof -
  obtain K where K: "\<forall> n \<ge> K. dist (x n) a < \<epsilon>"
    using Analysis.tendsto_def assms(1,3) by blast
  obtain L where L: "\<forall> n \<ge> L. dist (x n) b < \<epsilon>"
    using Analysis.tendsto_def assms(2,3) by blast
  have leq1: "K \<le> max K L" by simp
  have leq2: "L \<le> max K L" by simp
  have "dist (x (max K L)) a < \<epsilon>"
    by (metis K leq1)
  moreover have "dist (x (max K L)) b < \<epsilon>"
    by (metis L leq2)
  ultimately show ?thesis by blast
qed

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma tendsto_dist_lt:
  fixes a b :: "'a::metric_space"
  assumes "\<forall> \<epsilon> > 0. dist a b < \<epsilon>"
  shows "a = b"
(* mi22062_Nenad_Pesic_DOKAZ *)
proof (rule ccontr)
  assume "a \<noteq> b"
  then have "0 < dist a b" by simp
  with assms have "dist a b < dist a b" by blast
  from this show False by simp
qed

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma tendsto_unique:
  fixes x :: "'a::metric_space sequence"
  assumes "tendsto x a" and "tendsto x b"
  shows "a = b"
(* mi22062_Nenad_Pesic_DOKAZ *)
proof (rule tendsto_dist_lt)
  show "\<forall> \<epsilon> > 0. dist a b < \<epsilon>"
  proof
    fix \<epsilon> :: "real"
    show "0 < \<epsilon> \<longrightarrow> dist a b < \<epsilon>"
    proof
      assume eps: "0 < \<epsilon>"
      have eps_pola: "0 < \<epsilon> / 2" using eps by simp
      obtain n where n_a: "dist (x n) a < \<epsilon> / 2"
        and n_b: "dist (x n) b < \<epsilon> / 2"
        using tendsto_common_index[OF assms(1) assms(2) eps_pola] by blast
      have "dist a b \<le> dist a (x n) + dist (x n) b"
        by (simp add: dist_triangle)
      also have "... = dist (x n) a + dist (x n) b"
        by (simp add: dist_commute)
      also have "... < \<epsilon> / 2 + \<epsilon> / 2"
        using n_a n_b
        by simp
      also have "... = \<epsilon>" by simp
      finally show "dist a b < \<epsilon>" by auto
    qed
  qed
qed

section \<open>Rudin 3.2 (c) -- Svaki konvergentan niz je ogranicen\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma finite_prefix_bounded:
  fixes x :: "'a::metric_space sequence"
    and a :: "'a"
    and N :: nat
  shows "\<exists> C. \<forall> n < N. dist (x n) a \<le> C"
(* mi22062_Nenad_Pesic_DOKAZ *)
proof -
  let ?S = "(\<lambda> n. dist (x n) a) ` {..<N}"
  have fin: "finite ?S"
    by simp
  have "\<forall> y \<in> ?S. y \<le> Max ?S"
    by simp
  from this have "\<forall> n < N. dist (x n) a \<le> Max ?S"
    by auto
  from this show ?thesis
    by blast
qed

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma tendsto_bounded:
  fixes x :: "'a::metric_space sequence"
  assumes "tendsto x a"
  shows "bounded x"
(* mi22062_Nenad_Pesic_DOKAZ *)
proof -
  have "\<forall> \<epsilon> > 0. \<exists> N. \<forall> n \<ge> N. dist (x n) a < \<epsilon>"
    using Analysis.tendsto_def assms by blast
  then obtain N :: "nat" where N: "\<forall> n \<ge> N. dist (x n) a < 1"
    by fastforce

  obtain C :: "real" where C: "\<forall> n < N. dist (x n) a \<le> C"
    using finite_prefix_bounded by blast

  have svi: "\<forall> n. dist (x n) a \<le> max 1 C"
  proof
    fix n :: nat
    show "dist (x n) a \<le> max 1 C"
    proof (cases "N \<le> n")
      case True
      then have "dist (x n) a \<le> 1"
        using N by (simp add: less_imp_le)
      moreover have "(1::real) \<le> max 1 C"
        by simp
      ultimately show ?thesis by auto
    next
      case False
      then have "n < N" by simp
      then have "dist (x n) a \<le> C"
        using C by blast
      moreover have "C \<le> max 1 C"
        by simp
      ultimately show ?thesis
        by auto
    qed
  qed

  have "\<exists> p M. \<forall> n. dist (x n) p \<le> M"
    using svi by blast
  from this show ?thesis
    by (simp add: bounded_def)
qed

section \<open>Nezavisnost ogranicenosti od izbora centra\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma bounded_any_center:
  fixes x :: "'a::metric_space sequence"
    and q :: "'a"
  assumes "bounded x"
  shows "\<exists> M. \<forall> n. dist (x n) q \<le> M"
(* mi22062_Nenad_Pesic_DOKAZ *)
proof -
  from assms obtain p M where pM: "\<forall> n. dist (x n) p \<le> M"
    using bounded_def by blast
  have "\<forall> n. dist (x n) q \<le> M + dist p q"
  proof
    fix n
    have h: "dist (x n) p \<le> M" using pM by blast
    have "dist (x n) q \<le> dist (x n) p + dist p q" 
      by (simp add: dist_triangle)
    also have "... \<le> M + dist p q"
      using h by simp
    finally show "dist (x n) q \<le> M + dist p q" .
  qed
  from this show ?thesis by blast
qed

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_add:
  fixes sn tn :: "complex sequence"
  assumes "tendsto sn s"
      and "tendsto tn t"
    shows "tendsto (\<lambda>n. sn n + tn n) (s + t)"
(* mi19011_Dimitrije_Jovanovic_DOKAZ *)
  unfolding tendsto_def
proof (intro allI impI)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  

  with assms(1) have sn_e: "\<exists>N. \<forall>n\<ge>N. dist (sn n) (s) < \<epsilon> / 2"
    using half_gt_zero unfolding tendsto_def by blast
  with assms(2) have tn_e: "\<exists>N. \<forall>n\<ge>N. dist (tn n) (t) < \<epsilon> / 2"
    using \<open>0 < \<epsilon>\<close> half_gt_zero using tendsto_def by blast

  from sn_e obtain N1 where N1: "\<forall>n\<ge>N1. dist (sn n) s < \<epsilon> / 2"
    by blast
  from tn_e obtain N2 where N2: "\<forall>n\<ge>N2. dist (tn n) t < \<epsilon> / 2"
    by blast

  have "\<forall>n\<ge>max N1 N2. dist (sn n + tn n) (s + t) < \<epsilon>"
  proof (intro allI impI)
    fix n
    assume "n \<ge> max N1 N2"
    then have "n \<ge> N1" and "n \<ge> N2"
      by auto
    have "dist (sn n + tn n) (s + t) = norm ((sn n + tn n) - (s + t))"
      using dist_norm by blast
    also have "... = norm ((sn n - s) + (tn n - t))"
      by (simp add: add_diff_add)
    also have "... \<le> norm (sn n - s) + norm (tn n - t)"
      using norm_triangle_ineq by blast
    also have "... = dist (sn n) s + dist (tn n) t"
      by (simp add: dist_norm)
    also have "... < \<epsilon> / 2 + \<epsilon> / 2"
      using N1 N2 \<open>N1 \<le> n\<close> \<open>N2 \<le> n\<close> by fastforce
    also have "... = \<epsilon>"
      using field_sum_of_halves by blast
    finally show "dist (sn n + tn n) (s + t) < \<epsilon>" .
  qed
  then show "\<exists>N. \<forall>n\<ge>N. dist (sn n + tn n) (s + t) < \<epsilon>"
    by blast
qed

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_scale:
  fixes sn :: "complex sequence"
    and c :: "complex"
  assumes "tendsto sn s"
  shows "tendsto (\<lambda>n. c * sn n) (c * s)"
(* mi19011_Dimitrije_Jovanovic_DOKAZ *)
  unfolding tendsto_def
proof (intro allI impI)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  show "\<exists>N. \<forall>n\<ge>N. dist (c * sn n) (c * s) < \<epsilon>"
  proof (cases "c = 0")
    case True
    then show ?thesis
      using \<open>0 < \<epsilon>\<close> by auto
  next
    case False
    with assms have sn_e: "\<exists>N. \<forall>n\<ge>N. dist (sn n) (s) < \<epsilon> / norm c"
      unfolding tendsto_def by (simp add: \<open>0 < \<epsilon>\<close>)
    then obtain N where N: "\<forall>n\<ge>N. dist (sn n) (s) < \<epsilon> / norm c"
      by blast

    have "\<forall>n\<ge>N. dist (c * sn n) (c * s) < \<epsilon>"
    proof (intro allI impI)
      fix n
      assume "n\<ge>N"

      have "dist (c * sn n) (c * s) = norm (c * sn n- c * s)"
        using dist_norm by blast
      also have "... = norm (c * (sn n - s))"
        by (simp add: right_diff_distrib)
      also have "... = norm c * norm (sn n - s)"
        using norm_mult by blast
      also have "... = norm c * dist (sn n) s"
        by (simp add: dist_norm)
      also have "... < norm c * (\<epsilon> / norm c)"
        using False N \<open>N \<le> n\<close> mult_strict_left_mono zero_less_norm_iff by blast
      also have "... = \<epsilon>"
        using False by auto
      finally show "dist (c * sn n) (c * s) < \<epsilon>" .
    qed
    then show ?thesis
      by blast
  qed
qed

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_inc:
  fixes sn :: "complex sequence"
    and c :: "complex"
  assumes "tendsto sn s" 
  shows"tendsto (\<lambda>n. c + sn n) (c + s)"
(* mi23026_Lola_Vukovic DOKAZ *)
  unfolding tendsto_def
proof (intro allI impI)
  fix ε :: real
  assume "ε > 0"
  
  with assms obtain N where N: "∀n≥N. dist (sn n) s < ε"
    unfolding tendsto_def by blast

  have "∀n≥N. dist (c + sn n) (c + s) < ε"
  proof (intro allI impI)
    fix n
    assume "n ≥ N"

    have "dist (c + sn n) (c + s) = norm ((c + sn n) - (c + s))"
      using dist_norm by blast
    also have "... = norm (sn n - s)"
      by simp
    also have "... = dist (sn n) s"
      by (simp add: dist_norm)
    also have "... < ε"
      using N `n ≥ N` by blast
    finally show "dist (c + sn n) (c + s) < ε" .
  qed
  thus "∃N. ∀n≥N. dist (c + sn n) (c + s) < ε"
    by blast
qed

(* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_mult_helper:
  fixes sn tn :: "complex sequence"
  assumes "tendsto sn s"
      and "tendsto tn t"
    shows "tendsto (\<lambda>n. (sn n - s)*( tn n - t)) 0"
(* mi22050_Lazar_Rajcic_DOKAZ *)
 unfolding tendsto_def
proof (intro allI impI)
 fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  have N1: "\<exists>N1. \<forall>n\<ge>N1. dist (sn n) (s) < sqrt \<epsilon>"
  using assms(1)
     unfolding tendsto_def  by (simp  add: \<open>0 < \<epsilon>\<close>)
    
  have  N2: "\<exists>N2. \<forall>n\<ge>N2. dist (tn n) (t) < sqrt \<epsilon>"
  using assms(2)
      unfolding tendsto_def  by (simp  add: \<open>0 < \<epsilon>\<close>)

  obtain N1 where hN1: "\<forall>n\<ge>N1. dist (sn n) s <sqrt \<epsilon>"
  using N1 by auto

  obtain N2 where hN2: "\<forall>n\<ge>N2. dist (tn n) t <sqrt \<epsilon>"
    using N2  by auto
  obtain N where hN: "N = max N1 N2"
    by simp

  have HN: "\<forall>n\<ge>N. (dist (sn n) s) * (dist (tn n) t) <  \<epsilon> "
  proof (intro allI impI)
    fix n :: nat
    assume nVn:"n\<ge>N"
    then have "n\<ge>N1" using hN  by auto
    then have nsn: "dist (sn n) s <sqrt \<epsilon>" using hN1 by simp

    have nVn2:"n\<ge>N2" using hN nVn by auto
    then have ntn:"dist (tn n) t <sqrt \<epsilon>" using hN2 by simp 

    have pomh1: "0 \<le> dist (sn n) s"
    by simp
     have pomh2: "0 \<le> dist (tn n) t"
    by simp

    have "(dist (sn n) s)*(dist (tn n) t)< sqrt \<epsilon> * sqrt \<epsilon>" using nsn ntn pomh1 pomh2 
      using mult_strict_mono' by blast
    then show "(dist (sn n) s)*(dist (tn n) t) <  \<epsilon>"  using  \<open>0 < \<epsilon>\<close> by auto
  qed
  have "\<forall>n\<ge>N. dist ((sn n - s) * (tn n - t)) 0
       = (dist (sn n) s) * (dist (tn n) t)"
    by (simp add: dist_norm norm_mult) 

  then have "\<forall>n\<ge>N. dist ((sn n - s) * (tn n - t)) 0 <  \<epsilon> "
    using HN by auto

  then show "\<exists>N. \<forall>n\<ge>N. dist ((sn n - s) * (tn n - t)) 0 < \<epsilon>"
    by auto

qed



(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_mult:
  fixes sn tn :: "complex sequence"
  assumes "tendsto sn s"
      and "tendsto tn t"
    shows "tendsto (\<lambda>n. sn n * tn n) (s * t)"
(* mi22050_Lazar_Rajcic_DOKAZ *)
proof -
  have hsntn:
    "tendsto (\<lambda>n. (sn n - s) * (tn n - t)) 0"
  using tendsto_mult_helper[OF assms(1) assms(2)]
  by simp

   have htn0:
    "tendsto (\<lambda>n. tn n - t) 0"
     using tendsto_inc[OF assms(2), of "-t"]
     by simp
   then have ht:
    "tendsto (\<lambda>n. s * (tn n - t)) 0"
  using tendsto_scale[OF htn0, of s]
  by simp

  have hsn0:
    "tendsto (\<lambda>n. sn n - s) 0"
  using tendsto_inc[OF assms(1), of "-s"]
  by simp
  then have hs:
    "tendsto (\<lambda>n. t * (sn n - s)) 0"
  using tendsto_scale[OF hsn0, of t]
  by simp

  have    hadd1: "tendsto
      (\<lambda>n. (sn n - s) * (tn n - t) + s * (tn n - t))
      0"
  using tendsto_add[OF hsntn ht]
  by simp
  have    hadd2:  "tendsto
      (\<lambda>n. ((sn n - s) * (tn n - t) + s * (tn n - t))
            + t * (sn n - s))    0"
  using tendsto_add[OF hadd1 hs]
  by simp

have hdiff:
    "tendsto (\<lambda>n. sn n * tn n - s * t) 0"
  using hadd2
  by (simp add: algebra_simps)

  then show "tendsto (\<lambda>n. sn n * tn n) (s * t)"
    using tendsto_inc[OF hdiff, of  "(s * t)"]
    by simp
  qed

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_inverse:
  fixes sn :: "complex sequence"
  assumes "tendsto sn s"
      and "\<forall>n. sn n \<noteq> 0"
      and "s \<noteq> 0"
    shows "tendsto (\<lambda>n. 1/sn n) (1/s)"
(* mi22050_Lazar_Rajcic_DOKAZ*)
unfolding tendsto_def
proof (intro allI impI)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  obtain m where " \<forall>n\<ge>m. dist (sn n) s < (1/2)* dist s 0"
    using assms(1)
    by (metis Analysis.tendsto_def assms(3) half_gt_zero_iff mult_numeral_1 numeral_One
      times_divide_eq_left zero_less_dist_iff) (* sledgehammer <3 *)

  then have m2:"\<forall>n\<ge>m.  dist (sn n) 0 > (1/2)*dist s 0"
  by (smt (verit) add_divide_distrib dist_triangle3 eq_divide_eq_1 mult_cancel_right1
      ring_class.ring_distribs(2))

  have hdist: "0 < dist s 0"
    using assms(3)
    by simp
  then have he:
    "0 < (1/2) * (dist s 0 ^ 2) * \<epsilon>"
    using \<open>\<epsilon> > 0\<close>
    by auto
  obtain N0 where hN0:
     "\<forall>n\<ge>N0. dist (sn n) s <
        (1/2) * (dist s 0 ^ 2) * \<epsilon>"
    using assms(1)
    unfolding tendsto_def
    using he
    by blast
  
  obtain N where hN: "N = max m N0"
    by simp
    then have "N\<ge>m" "N\<ge> N0" by auto

  show "\<exists>N. \<forall>n\<ge>N. dist (1 / sn n) (1 / s) < \<epsilon>"
   proof (rule exI)
    show " \<forall>n\<ge>N. dist (1 / sn n) (1 / s) < \<epsilon>"
    proof (intro allI impI)
      fix n :: nat
      assume "N\<le>n"
      show "dist (1 / sn n) (1 / s) < \<epsilon>"
      proof-
        have hs:
          "0 < (1/2)*dist s 0"using assms(3)
          by simp
        have hs2:
          "0< 2/((dist s 0)^2)" using assms(3)
          by simp
        have hsn:
          "0 < dist (sn n) 0" using assms(2)
          by simp

        have "n\<ge>m" using \<open>N\<le> n\<close> \<open>N\<ge>m\<close>  by auto
        then have m3:"dist (sn n) 0 > (1/2)*dist s 0"   using m2 by auto
        then have m4: "1/(dist (sn n) 0) < 1/((1/2)*dist s 0)" using hs hsn
        using frac_less2 less_eq_real_def zero_less_one by blast
        have "n\<ge>N0" using \<open>N\<le> n\<close> \<open>N\<ge> N0\<close> by auto
        then have n2:"dist (sn n) s <  (1/2) * (dist s 0 ^ 2) * \<epsilon>" using hN0 by auto

         have hnum:
              "0 \<le> ( dist (s - sn n) 0 )/(dist  s 0 )"
              using hs by simp

        have "dist (1/sn n) (1/s) = dist(1/sn n - 1/s) 0"
          by (simp add: dist_complex_def)
        also have "... = dist ( s/(sn n * s)- sn n/(sn n * s)) 0" 
          by (metis assms(3) assms(2) nonzero_divide_mult_cancel_left nonzero_divide_mult_cancel_right)
        also have "... = dist ((s - sn n)/(sn n * s)) 0"
          by (metis diff_divide_distrib)
        also have "...  = ( dist (s - sn n) 0 )/((dist (sn n) 0 )* (dist  s 0 ))"
           by (simp add: dist_complex_def norm_divide norm_mult)
         also have "... =  1/(dist (sn n) 0 ) * ( dist (s - sn n) 0 )/(dist  s 0 )" by simp
         also have "...\<le> 1/((1/2)*dist s 0)* ( dist (s - sn n) 0 )/(dist  s 0 )" using  m4 hnum
           by (smt (verit, best) dist_not_less_zero divide_right_mono mult_le_cancel_right)
         also have "... = 2/((dist s 0)^2)*(dist (s - sn n) 0)"
         by (simp add: power2_eq_square)
       also have "... = 2/((dist s 0)^2)* (dist s (sn n))" by (simp add: dist_complex_def)
       also have "... = 2/((dist s 0)^2)* (dist (sn n) s)" by (simp add: dist_commute)
       also have "... < 2/((dist s 0)^2)* ((1/2) * (dist s 0 ^ 2) * \<epsilon>)" using n2 hs2  by (rule mult_strict_left_mono)
       also have "... = \<epsilon>" using he by auto
       finally show "dist (1/sn n) (1/s) <  \<epsilon>" by simp
     qed
   qed
 qed
qed



(* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_real_vec:
  fixes xn :: "(real^'k) sequence"
    and x :: "real^'k"
  assumes "finite (UNIV :: 'k set)"
  assumes "CARD('k)>0"
    shows "tendsto xn x \<longleftrightarrow>
         (\<forall>j. tendsto (\<lambda>n. xn n $ j) (x $ j))"
(* mi22050_Lazar_Rajcic_DOKAZ*)
proof
  show "tendsto xn x \<Longrightarrow> \<forall>j. tendsto (\<lambda>n. xn n $ j) (x $ j)"
  proof-
    assume "tendsto xn x"
    show "\<forall>j. tendsto (\<lambda>n. xn n $ j) (x $ j)"
      unfolding tendsto_def
    proof
      fix j:: 'k
      show "\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (xn n $ j) (x $ j) < \<epsilon>"
      proof  (intro allI impI)
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        show "\<exists>N. \<forall>n\<ge>N. dist (xn n $ j) (x $ j) < \<epsilon>"
        proof-
          have h1:"\<exists>N0. \<forall>n\<ge>N0. dist (xn n) x < \<epsilon>" using \<open>tendsto xn x\<close> unfolding tendsto_def
          using \<open>0 < \<epsilon>\<close> by auto
          have h2:"\<forall>n. dist (xn n $ j) (x $ j) \<le>  dist (xn n) x"
            by (metis dist_vec_nth_le)
          show "\<exists>N0. \<forall>n\<ge>N0. dist (xn n $ j) (x $ j) < \<epsilon> " using h1 h2
          using dist_vec_nth_le order_le_less_trans by blast
      qed
    qed
  qed
qed
next
  show "\<forall>j. tendsto (\<lambda>n. xn n $ j) (x $ j) \<Longrightarrow> tendsto xn x"
  proof-
    assume "\<forall>j. tendsto (\<lambda>n. xn n $ j) (x $ j)"
    show "tendsto xn x"
      unfolding tendsto_def
    proof  (intro allI impI)
      fix \<epsilon>::real
      assume "\<epsilon>>0"
      show "\<exists>N. \<forall>n\<ge>N. dist (xn n) x < \<epsilon> "
      proof-
      have hsqrt: "0 < sqrt (real (CARD('k)))"
        by auto
      then have heps: "0 < \<epsilon> / sqrt (real (CARD('k)))"
        using \<open>\<epsilon> > 0\<close> 
        by auto
      then  have hcomp:"\<forall>j. \<exists>N. \<forall>n\<ge>N.
        dist (xn n $ j) (x $ j) <  \<epsilon> / sqrt (real (CARD('k)))"
        using \<open>\<forall>j. tendsto (\<lambda>n. xn n $ j) (x $ j)\<close>
        unfolding tendsto_def
        by simp

      obtain Nf where
        Nf: "\<forall>j. \<forall>n\<ge>Nf j.
          dist (xn n $ j) (x $ j) <
           \<epsilon> / sqrt (real (CARD('k)))"
        using hcomp
        by metis
      obtain N where "N = Max (Nf ` UNIV)" by auto
      then have a:"\<forall>j. \<forall>n\<ge>N.
              dist (xn n $ j) (x $ j) <
          \<epsilon> / sqrt (real (CARD('k)))" 
        using Nf by auto
        
      have "\<forall>n\<ge>N. dist (xn n) x < \<epsilon>"
      proof (intro allI impI)
        fix n
        assume "n\<ge>N"
        show "dist (xn n) x < \<epsilon>"
        proof-
          have 1: "dist (xn n) x = L2_set (\<lambda>j. dist (xn n $ j) (x $ j)) UNIV"
            by (simp only: dist_vec_def)
          have 2: "L2_set (\<lambda>j. dist (xn n $ j) (x $ j)) UNIV
                 < L2_set (\<lambda>j::'k. \<epsilon> / sqrt (real (CARD('k)))) UNIV"
          proof (rule L2_set_strict_mono[OF assms(1)])
            show "UNIV \<noteq> {}"
              using assms(2) by simp
          next
            show "\<And>i.  dist (xn n $ i) (x $ i) < \<epsilon> / sqrt (real (CARD('k)))"
              using a \<open>n \<ge> N\<close> by auto
          next
            show "\<And>i. 0 \<le> dist (xn n $ i) (x $ i)"
              by simp
          qed
          have 3: "L2_set (\<lambda>j::'k. \<epsilon> / sqrt (real (CARD('k)))) UNIV = \<epsilon>"
            using L2_set_constant[of "\<epsilon> / sqrt (real (CARD('k)))" "UNIV::'k set"]
            using abs_of_pos[OF heps] by simp
          show "dist (xn n) x < \<epsilon>"
            using 1 2 3 by simp
        qed
      qed
      then show "\<exists>N. \<forall>n\<ge>N. dist (xn n) x < \<epsilon> "
        by auto
    qed
  qed
qed
qed

 (* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_add_real:
  fixes xn yn ::"real sequence"
    and x y ::  "real"
  assumes "tendsto xn x" and "tendsto yn y"
  shows "tendsto (\<lambda>n. xn n + yn n)  (x+y)"
 (* mi22050_Lazar_Rajcic_DOKAZ *)
proof-
  define sn where "sn = (\<lambda>n. Complex (xn n) 0)"
  define tn where "tn = (\<lambda>n. Complex (yn n) 0)"
  define s where "s = Complex x 0"
  define t where "t = Complex y 0"

  have sn: "tendsto sn s"
    using assms(1) unfolding tendsto_def sn_def s_def dist_complex_def dist_real_def
    by (simp add: Complex.minus_cis cmod_def)

  have tn: "tendsto tn t"
    using  assms(2) unfolding tendsto_def tn_def t_def dist_complex_def dist_real_def
    by (simp add: Complex.minus_cis cmod_def)

  have hsum: "tendsto (\<lambda>n. sn n + tn n) (s + t)"
    using tendsto_add [OF sn tn] .

  show "tendsto (\<lambda>n. xn n + yn n) (x + y)"
    unfolding tendsto_def
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    
    then obtain N where N: "\<forall>n\<ge>N. dist (sn n + tn n) (s + t) < \<epsilon>"
      using hsum unfolding tendsto_def by blast
    have "\<forall>n\<ge>N. dist (xn n + yn n) (x + y) < \<epsilon>"
    proof (intro allI impI)
      fix n assume "n \<ge> N"
      then have "dist (sn n + tn n) (s + t) < \<epsilon>" using N by simp
      then show "dist (xn n + yn n) (x + y) < \<epsilon>"
        unfolding sn_def tn_def s_def t_def  
        by (simp add:  Complex.minus_cis cmod_def dist_real_def dist_complex_def)
    qed
    
    then show "\<exists>N. \<forall>n\<ge>N. dist (xn n + yn n) (x + y) < \<epsilon>" by (rule exI[of _ N])
  qed
qed
 (* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_add_real_vec:
  fixes xn yn ::"(real^'k) sequence"
    and x y ::  "real^'k"
  assumes "tendsto xn x" and "tendsto yn y"
  shows "tendsto (\<lambda>n. xn n + yn n)  (x+y)"
 (* mi22050_Lazar_Rajcic_DOKAZ*)
proof-
  have "(\<forall>j. tendsto (\<lambda>n. ( xn n + yn n) $ j) ( (x+y) $ j))"
  proof
    fix j
    have 1:"tendsto (\<lambda>n. xn n $ j) (x $ j)" using tendsto_real_vec assms(1) by auto
    have  2:"tendsto (\<lambda>n. yn n $ j) (y $ j)" using tendsto_real_vec assms(2) by auto
    have "tendsto (\<lambda>n. (xn n $ j) + (yn n $ j) ) ( (x $ j) + (y $ j))" using  1 2  tendsto_add_real
      by simp
    then show "tendsto (\<lambda>n. ( xn n + yn n) $ j) ( (x+y) $ j)" by auto
  qed
  then show "tendsto (\<lambda>n. xn n + yn n)  (x+y)"  using tendsto_real_vec
  by fastforce
qed

(* mi22059_Matija_Djordjevic POMOCNA FORMULACIJA_I_DOKAZ *)
lemma tendsto_mult_real:
  fixes xn yn :: "real sequence"
    and x y :: "real"
  assumes "tendsto xn x" and "tendsto yn y"
  shows "tendsto (\<lambda>n. xn n * yn n) (x * y)"
proof -
  define sn where "sn = (\<lambda>n. Complex (xn n) 0)"
  define tn where "tn = (\<lambda>n. Complex (yn n) 0)"
  define s where "s = Complex x 0"
  define t where "t = Complex y 0"

  have sn: "tendsto sn s"
    using assms(1) unfolding tendsto_def sn_def s_def dist_complex_def dist_real_def
    by (simp add: Complex.minus_cis cmod_def)

  have tn: "tendsto tn t"
    using assms(2) unfolding tendsto_def tn_def t_def dist_complex_def dist_real_def
    by (simp add: Complex.minus_cis cmod_def)

  have hprod: "tendsto (\<lambda>n. sn n * tn n) (s * t)"
    using tendsto_mult [OF sn tn] .

  show "tendsto (\<lambda>n. xn n * yn n) (x * y)"
    unfolding tendsto_def
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    then obtain N where N: "\<forall>n\<ge>N. dist (sn n * tn n) (s * t) < \<epsilon>"
      using hprod unfolding tendsto_def by blast
    have "\<forall>n\<ge>N. dist (xn n * yn n) (x * y) < \<epsilon>"
    proof (intro allI impI)
      fix n assume "n \<ge> N"
      then have "dist (sn n * tn n) (s * t) < \<epsilon>" using N by simp
      then show "dist (xn n * yn n) (x * y) < \<epsilon>"
        unfolding sn_def tn_def s_def t_def  
        by (simp add: Complex.minus_cis cmod_def dist_real_def dist_complex_def)
    qed
    then show "\<exists>N. \<forall>n\<ge>N. dist (xn n * yn n) (x * y) < \<epsilon>" by (rule exI[of _ N])
  qed
qed


 (* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_mult_real_vec:
  fixes xn yn :: "(real^'k) sequence"
    and x y :: "real^'k"
  assumes  "tendsto xn x" and "tendsto yn y"
  shows "tendsto (\<lambda>n. xn n * yn n)  (x*y)"
 (* mi22059_Matija_Djordjevic_DOKAZ *)
  proof-
    have "(\<forall>j. tendsto (\<lambda>n. ( xn n * yn n) $ j) ( (x*y) $ j))"
  proof
    fix j
    have 1:"tendsto (\<lambda>n. xn n $ j) (x $ j)" using tendsto_real_vec assms(1) by auto
    have  2:"tendsto (\<lambda>n. yn n $ j) (y $ j)" using tendsto_real_vec assms(2) by auto
    have "tendsto (\<lambda>n. (xn n $ j) * (yn n $ j) ) ( (x $ j) * (y $ j))" using  1 2  tendsto_mult_real
      by simp
    then show "tendsto (\<lambda>n. ( xn n * yn n) $ j) ( (x*y) $ j)" by auto
  qed
  then show "tendsto (\<lambda>n. xn n * yn n)  (x*y)"  using tendsto_real_vec
  by fastforce
qed


 (* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_scale_real_vec:
  fixes xn ::  "(real^'k) sequence"
    and x :: "real^'k"
    and bn :: "real sequence"
    and b :: real
  assumes "tendsto xn x" and "tendsto bn b"
  shows "tendsto (\<lambda>n. bn n *s xn n) (b *s x)"
 (* mi22059_Matija_Djordjevic_DOKAZ *)
proof -
  have "(\<forall>j. tendsto (\<lambda>n. (bn n *s xn n) $ j) ((b *s x) $ j))"
  proof
    fix j
    have h1: "tendsto bn b" using assms(2) .
    have h2: "tendsto (\<lambda>n. xn n $ j) (x $ j)"
      using tendsto_real_vec assms(1) by auto
    have "tendsto (\<lambda>n. bn n * (xn n $ j)) (b * (x $ j))"
      using h1 h2 tendsto_mult_real by simp
    then show "tendsto (\<lambda>n. (bn n *s xn n) $ j) ((b *s x) $ j)"
      by simp
  qed
  then show "tendsto (\<lambda>n. bn n *s xn n) (b *s x)"
    using tendsto_real_vec by fastforce
qed


(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
definition subseq :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "subseq pn nk pni \<longleftrightarrow> strict_mono nk \<and> pni = pn \<circ> nk"

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma sequence_tendsto_subseq:
    fixes pn pni :: "'a::metric_space sequence"
      and nk :: "nat \<Rightarrow> nat"
  assumes "subseq pn nk pni"
      and "tendsto pn p"
    shows "tendsto pni p"
(* mi19011_Dimitrije_Jovanovic_DOKAZ *)
  unfolding tendsto_def
proof (intro allI impI)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"

  with assms(2) have pn_e: "\<exists>N. \<forall>n\<ge>N. dist (pn n) p < \<epsilon>"
    unfolding tendsto_def by blast

  from pn_e obtain N where N:"\<forall>n\<ge>N. dist (pn n) p < \<epsilon>"
    by blast

  have nk_k: "\<forall>k. nk k \<ge> k"
    using assms(1) seq_suble subseq_def by blast

  have "\<forall>k\<ge>N. dist (pni k) p < \<epsilon>"
  proof (intro allI impI)
    fix k
    assume "k\<ge>N"

    from nk_k have "nk k \<ge> k"
      by blast

    with \<open>k\<ge>N\<close> have N1: "nk k \<ge> N"
       by linarith

    from assms(1) have "pni k = pn (nk k)"
     unfolding subseq_def
     by simp

    from N N1 have "dist (pn (nk k)) p < \<epsilon>"
      by blast

    then show "dist (pni k) p < \<epsilon>"
      by (simp add: \<open>pni k = pn (nk k)\<close>)
  qed
  then show "\<exists>N. \<forall>n\<ge>N. dist (pni n) p < \<epsilon>"
    by blast
qed

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma subseq_tendsto_sequence:
    fixes pn :: "'a::metric_space sequence"
  assumes "(\<forall>pni nk. subseq pn nk pni \<longrightarrow> tendsto pni p)"
    shows "tendsto pn p"
(* mi19011_Dimitrije_Jovanovic_DOKAZ *)
proof-
  have "subseq pn (\<lambda>k. k) pn"
    unfolding subseq_def strict_mono_def comp_def by auto
  then show ?thesis
    using assms by blast
qed


(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_sequence_subseq:
  fixes pn :: "'a::metric_space sequence"
  shows "tendsto pn p \<longleftrightarrow> (\<forall>pni nk. subseq pn nk pni \<longrightarrow> tendsto pni p)"
(* mi19011_Dimitrije_Jovanovic_DOKAZ *)
proof
  assume "tendsto pn p"
  show "\<forall>pni nk. subseq pn nk pni \<longrightarrow> tendsto pni p"
    using \<open>tendsto pn p\<close> sequence_tendsto_subseq by blast
next
  assume "\<forall>pni nk. subseq pn nk pni \<longrightarrow> tendsto pni p"
  then show "tendsto pn p"
    using subseq_tendsto_sequence by blast
qed



(* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma subseq_tendsto_compact:
  fixes pn :: "'a::metric_space sequence"
    and X :: "'a set"
  assumes "compact X"
        and "\<forall>n. pn n \<in> X"
  shows "\<exists> nk pni p.
           subseq pn nk pni \<and> p \<in> X \<and>  tendsto pni p"
sorry

(*mi22206 Anastasija Divjak FORMULACIJA*)
lemma tendsto_subseq_bounded:
  fixes pn :: "(real^'k) sequence"
  assumes "bounded pn"
  shows "\<exists>nk pni p. subseq pn nk pni \<and> tendsto pni p"
  sorry

(*mi22206 Anastasija Divjak FORMULACIJA*)
definition cauchy::"'a::metric_space sequence \<Rightarrow> bool" where
"cauchy p \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (p n)(p m) < \<epsilon>)"


(*mi22206 Anastasija Divjak FORMULACIJA*)
definition diam::"'a::metric_space set \<Rightarrow> real" where
"diam E = Sup {dist p q | p q. p \<in> E \<and> q \<in> E}"

(*mi22206 Anastasija Divjak FORMULACIJA*)
lemma cauchy_diam_nil:
  fixes pn :: "'a::metric_space sequence"
  defines "En \<equiv> (\<lambda>N. {pn n | n. n \<ge> N})"
  shows "cauchy pn \<longleftrightarrow> tendsto (\<lambda>N. diam (En N)) 0"
  sorry

(*mi22206 Anastasija Divjak FORMULACIJA*)
definition closure :: "'a::metric_space set \<Rightarrow> 'a set" where
  "closure E = {p. \<forall>\<epsilon>>0. \<exists>q \<in> E. dist p q < \<epsilon>}"

(*mi22206 Anastasija Divjak FORMULACIJA*)
lemma diam_closure:
  fixes E :: "'a::metric_space set"
  defines "Ec ≡ closure E"
  assumes "bounded_set Ec"
  shows "diam Ec = diam E"
(*mi22206 Anastasija Divjak DOKAZ*)
proof -
  have jedan_smer: "E ⊆ Ec"
  proof
    fix x
    assume "x ∈ E"
    have "∀ε>0. ∃q ∈ E. dist x q < ε"
    proof (intro allI impI)
      fix ε :: real assume "ε > 0"
      from `x ∈ E` and `ε > 0` have "dist x x < ε" by simp
      with `x ∈ E` show "∃q∈E. dist x q < ε" by blast
    qed
    from this show "x ∈ Ec" unfolding Ec_def closure_def by simp
  qed
  obtain c M where granica:
      "∀x∈Ec. dist x c ≤ M"
      using assms
      unfolding bounded_set_def
      by blast
  have ogranicen_Ec:"bdd_above {dist p q | p q. p ∈ Ec ∧ q ∈ Ec}"
  proof -
    have "∀x∈{dist p q | p q. p ∈ Ec ∧ q ∈ Ec}. x ≤ 2 * M"
    proof
      fix x
      assume "x ∈ {dist p q | p q. p ∈ Ec ∧ q ∈ Ec}"
      then obtain p q where
        "p ∈ Ec" "q ∈ Ec" "x = dist p q"
        by auto

      have "dist p q ≤ dist p c + dist c q"
        by (rule dist_triangle)
      also have "... = dist p c + dist q c"
        by (simp add: dist_commute)
     also have "... ≤ M + M"
      proof -
        have p_bound: "dist p c ≤ M"
          using granica `p ∈ Ec`
          by blast
      
        have q_bound: "dist q c ≤ M"
          using granica `q ∈ Ec`
          by blast
      
        show "dist p c + dist q c ≤ M + M"
          using p_bound q_bound
          by arith
      qed
      also have "... = 2 * M"
        by simp
      finally show "x ≤ 2 * M"
        using `x = dist p q`
        by simp
    qed
    then show ?thesis
      unfolding bdd_above_def
      by auto
  qed

have l1: "diam E ≤ diam Ec"
proof (cases "E = {}")
  case True

  have Ec_empty: "Ec = {}"
proof -
  have "closure E = {}"
  proof
    show "closure E ⊆ {}"
    proof
      fix x
      assume "x ∈ closure E"

      have "∀ε>0. ∃q∈E. dist x q < ε"
        using `x ∈ closure E`
        unfolding closure_def
        by auto

      then have "∃q∈E. dist x q < (1::real)"
        by auto

      then show "x ∈ {}"
        using True
        by auto
    qed

    show "{} ⊆ closure E"
      by auto
  qed

  then show ?thesis
    unfolding Ec_def
    by simp
qed

  then show ?thesis
    using True
    unfolding diam_def
    by simp

next
  case False

  have podskup:
    "{dist p q | p q. p ∈ E ∧ q ∈ E}
     ⊆
     {dist p q | p q. p ∈ Ec ∧ q ∈ Ec}"
  proof
    fix x
    assume "x ∈ {dist p q | p q. p ∈ E ∧ q ∈ E}"
    then obtain p q where
      "p ∈ E" "q ∈ E" "x = dist p q"
      by auto

    have "p ∈ Ec"
      using jedan_smer `p ∈ E`
      by auto

    have "q ∈ Ec"
      using jedan_smer `q ∈ E`
      by auto

    show "x ∈ {dist p q | p q. p ∈ Ec ∧ q ∈ Ec}"
      using `x = dist p q` `p ∈ Ec` `q ∈ Ec`
      by auto
  qed

  have neprazan:
    "{dist p q | p q. p ∈ E ∧ q ∈ E} ≠ {}"
  proof -
    obtain p where "p ∈ E"
      using False
      by auto

    have "dist p p ∈ {dist p q | p q. p ∈ E ∧ q ∈ E}"
      using `p ∈ E`
      by auto

    then show ?thesis
      by auto
  qed

  show ?thesis
    unfolding diam_def
  proof (rule cSup_least)
    show "{dist p q |p q. p ∈ E ∧ q ∈ E} ≠ {}"
      using neprazan .

    fix x
    assume xE:
      "x ∈ {dist p q |p q. p ∈ E ∧ q ∈ E}"

    have xEc:
      "x ∈ {dist p q |p q. p ∈ Ec ∧ q ∈ Ec}"
      using podskup xE
      by blast

    show "x ≤ Sup {dist p q |p q. p ∈ Ec ∧ q ∈ Ec}"
      using xEc ogranicen_Ec
      by (rule cSup_upper)
  qed
qed
  have l2: "diam Ec ≤ diam E"
  proof -
    have ogranicen_E:
      "bdd_above {dist x y | x y. x ∈ E ∧ y ∈ E}"
    proof -
      have "{dist x y | x y. x ∈ E ∧ y ∈ E}
            ⊆
            {dist x y | x y. x ∈ Ec ∧ y ∈ Ec}"
        using jedan_smer
        by auto
      then show ?thesis
        using ogranicen_Ec
        by (meson bdd_above_mono)
    qed

    have dist_le: "dist p q ≤ diam E"
      if "p ∈ Ec" "q ∈ Ec" for p q
    proof (rule field_le_epsilon)
      fix eps :: real
      assume "eps > 0"

      have "eps / 2 > 0"
        using `eps > 0`
        by simp

      from `p ∈ Ec` `eps / 2 > 0`
      obtain p1 where
        "p1 ∈ E" "dist p p1 < eps / 2"
        unfolding Ec_def closure_def
        by blast

      from `q ∈ Ec` `eps / 2 > 0`
      obtain q1 where
        "q1 ∈ E" "dist q q1 < eps / 2"
        unfolding Ec_def closure_def
        by blast

      have 0:
        "dist p1 q1 ∈ {dist x y | x y. x ∈ E ∧ y ∈ E}"
        using `p1 ∈ E` `q1 ∈ E`
        by auto

      have 1: "dist p q ≤ dist p p1 + dist p1 q"
        by (rule dist_triangle)

      have 2: "dist p1 q ≤ dist p1 q1 + dist q1 q"
        by (rule dist_triangle)

      have 3:
        "dist p q ≤ dist p p1 + dist p1 q1 + dist q1 q"
        using 1 2
        by arith

      have 4:
        "dist p q ≤ eps / 2 + dist p1 q1 + eps / 2"
      proof -
        have "dist q1 q = dist q q1"
          by (rule dist_commute)
        with 3
             `dist p p1 < eps / 2`
             `dist q q1 < eps / 2`
        show ?thesis
          by linarith
      qed

      have 5: "dist p1 q1 ≤ diam E"
        unfolding diam_def
        using 0 ogranicen_E 
        by (rule cSup_upper)

      show "dist p q ≤ diam E + eps"
        using 4 5
        by linarith
    qed

        show "diam Ec ≤ diam E"
    proof (cases "Ec = {}")
      case True

      have "E = {}"
        using jedan_smer True
        by auto

      then show ?thesis
        using True
        unfolding diam_def
        by simp

    next
      case False

      have neprazan:
        "{dist x y | x y. x ∈ Ec ∧ y ∈ Ec} ≠ {}"
      proof -
        obtain x where "x ∈ Ec"
          using False
          by auto

        then have
          "dist x x ∈ {dist x y | x y. x ∈ Ec ∧ y ∈ Ec}"
          by auto

        then show ?thesis
          by auto
      qed

      show ?thesis
        unfolding diam_def
      proof (rule cSup_least)
        show "{dist x y | x y. x ∈ Ec ∧ y ∈ Ec} ≠ {}"
          using neprazan .

        fix x
        assume
          "x ∈ {dist p q | p q. p ∈ Ec ∧ q ∈ Ec}"

        then obtain p q where
          "p ∈ Ec" "q ∈ Ec" "x = dist p q"
          by auto

        have "dist p q ≤ diam E"
          using `p ∈ Ec` `q ∈ Ec`
          by (rule dist_le)

        then show
          "x ≤ Sup {dist p q | p q. p ∈ E ∧ q ∈ E}"
          using `x = dist p q`
          unfolding diam_def
          by simp
      qed
    qed
  qed

  show "diam Ec = diam E"
    using l1 l2
    by auto
qed


(*mi20174_Nikola_Krstajic_FORMULACIJA*)
lemma diam_compact:
  fixes K :: "('a::metric_space set) sequence"
  assumes "\<forall> n. compact (K n)"
      and "\<forall> n. K n \<noteq> {}"
      and "\<forall> n. K (Suc n) \<subseteq> K n"
      and "tendsto (\<lambda> n. diam (K n)) 0"
    shows "\<exists>! p. p \<in> (\<Inter>n. K n)"
  sorry


(*mi20174_Nikola_Krstajic_FORMULACIJA*)
lemma tendsto_cauchy:
  fixes xn :: "'a::metric_space sequence"
   and x :: "'a"
  assumes "tendsto xn x"
  shows "cauchy xn"
(*mi20174_Nikola_Krstajic_DOKAZ*)
  unfolding cauchy_def
proof(intro allI impI)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  then have eps_pola : "\<epsilon> /2 > 0"by simp
   obtain N where N: "\<forall>n\<ge>N. dist (xn n) x < \<epsilon> / 2"
 using assms eps_pola unfolding tendsto_def by blast
  have "\<forall>n\<ge>N. \<forall>m\<ge>N. dist (xn n) (xn m) < \<epsilon>"
  proof (intro allI impI)
    fix n m
    assume "n \<ge> N" and "m \<ge> N"
    have h1: "dist (xn n) x < \<epsilon> / 2"
      using N \<open>n \<ge> N\<close> by blast
    have h2: "dist (xn m) x < \<epsilon> / 2"
      using N \<open>m \<ge> N\<close> by blast
    have "dist (xn n) (xn m) \<le> dist (xn n) x + dist (xn m) x"
      by (metis dist_commute dist_triangle)
    also have "... < \<epsilon> / 2 + \<epsilon> / 2"
      using h1 h2 by simp
    also have "... = \<epsilon>" by simp
    finally show "dist (xn n) (xn m) < \<epsilon>" .
  qed
  then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (xn n) (xn m) < \<epsilon>" by blast
qed


(*mi20174_Nikola_Krstajic_FORMULACIJA* pomocna lema*)
lemma closure_subset_closed:
  fixes X E :: "'a::metric_space set"
  assumes "closed X" and "E \<subseteq> X"
  shows "closure E \<subseteq> X"
proof
  fix p assume "p \<in> closure E"
  show "p \<in> X"
  proof (rule ccontr)
    assume "p \<notin> X"
    then have "p \<in> -X" by simp
    then obtain e where e: "e > 0" "\<forall>y. dist y p < e \<longrightarrow> y \<in> -X"
      using \<open>closed X\<close> unfolding closed_def open_dist by blast
    from \<open>p \<in> closure E\<close> have "\<forall>\<epsilon>>0. \<exists> q \<in> E. dist p q < \<epsilon>"
      unfolding closure_def by simp
    then obtain q where q: "q \<in> E" "dist p q < e"
      using e(1) by blast
    have "dist q p < e" using q(2) by (simp add: dist_commute)
    then have "q \<in> -X" using e(2) by blast
    moreover have "q \<in> X" using q(1) \<open>E \<subseteq> X\<close> by blast
    ultimately show False by simp
  qed
qed

(*mi20174_Nikola_Krstajic_FORMULACIJA* pomocna lema*)
lemma closed_closure:
  fixes E :: "'a::metric_space set"
  shows "closed (closure E)"
  unfolding closed_def open_dist
proof (intro ballI)
  fix p assume "p \<in> - closure E"
  then have "p \<notin> closure E" by simp
  have "\<exists> e0 >0. \<forall> q \<in> E. dist p q \<ge> e0"
    using \<open>p \<notin> closure E\<close> unfolding closure_def by (auto simp: not_less)
  then obtain e0 where e0: "e0 > 0" "\<forall> q \<in> E. dist p q \<ge> e0"
    by blast
  show "\<exists> e > 0. \<forall>y. dist y p < e \<longrightarrow> y \<in> - closure E"
  proof (rule exI[of _ "e0/2"])
    show "0 < e0 / 2 \<and> (\<forall>y. dist y p < e0 / 2 \<longrightarrow> y \<in> - closure E)"
    proof (intro conjI allI impI)
      show "0 < e0 / 2" using e0(1) by auto
    next
      fix y assume dyp: "dist y p < e0 / 2"
      show "y \<in> - closure E"
      proof
        assume "y \<in> closure E"
        then have "\<forall> \<epsilon> > 0. \<exists> q \<in> E. dist y q < \<epsilon>"
          unfolding closure_def by simp
        then obtain q where q: "q \<in> E" "dist y q < e0 / 2"
          using half_gt_zero[OF e0(1)] by blast  
        have "dist p q \<le> dist p y + dist y q"
          by (simp add: dist_triangle)
        also have "... = dist y p + dist y q"
          by (simp add: dist_commute)
        also have "... < e0 / 2 + e0 / 2"
          using dyp q(2) by (simp add: dist_commute)
        also have "... = e0" by simp
        finally have "dist p q < e0" .
        
        moreover have "dist p q \<ge> e0" using e0(2) q(1) by blast
        ultimately show False by auto
      qed
    qed
  qed
qed


(*mi20174_Nikola_Krstajic_FORMULACIJA* pomocna lema treba dokazati za sad sorry*)
lemma dist_le_diam:
  fixes x y :: "'a::metric_space"
    and K :: "'a set"
  assumes "x \<in> K" "y \<in> K"
  shows "dist x y \<le> diam K"
  sorry

(*mi20174_Nikola_Krstajic_FORMULACIJA*)
lemma compact_cauchy_tendsto:
  fixes pn :: "'a::metric_space sequence"
    and X :: "'a set"
  assumes "compact X"
    and "\<forall> n. pn n \<in> X"
    and "cauchy pn"
  shows "\<exists> p \<in> X. tendsto pn p"
(*mi20174_Nikola_Krstajic_DOKAZ*)
proof -
  define En where "En = (\<lambda> N. {pn n | n. n \<ge> N})"
  define Kn where "Kn = (\<lambda> N. closure(En N))"

  have "tendsto (\<lambda> N. diam(En N)) 0"
    using assms(3) cauchy_diam_nil En_def by blast
  have lim_diam_Kn: "tendsto (\<lambda>N. diam (Kn N)) 0"
  proof -
    have "\<forall>N. diam (Kn N) = diam (En N)"
      unfolding Kn_def using diam_closure by blast
    hence "(\<lambda>N. diam (Kn N)) = (\<lambda>N. diam (En N))"
      by auto
    thus ?thesis
      using \<open>tendsto (\<lambda>N. diam (En N)) 0\<close> by simp
  qed
 have Kn_compact: "\<forall>N. compact (Kn N)"
proof
  fix N
  have podksup_En: "En N \<subseteq> X"
    unfolding En_def using assms(2) by auto
  have zatvoren_X: "closed X" 
    using assms(1) by (rule compact_imp_closed)
  have "Kn N \<subseteq> X"
    unfolding Kn_def 
    by (rule closure_subset_closed[OF zatvoren_X podksup_En])
  have "closed (Kn N)"
    unfolding Kn_def by (rule closed_closure)
  have "Kn N = X \<inter> Kn N"
    using \<open>Kn N \<subseteq> X\<close> by auto
  thus "compact (Kn N)"
    using assms(1) \<open>closed (Kn N)\<close> compact_Int_closed by metis
qed
  have Kn_ugnjezden: "\<forall>N. Kn (Suc N) \<subseteq> Kn N"
  proof
    fix N
    have podksup_E: "En (Suc N) \<subseteq> En N" unfolding En_def by auto
    show "Kn (Suc N) \<subseteq> Kn N"
      unfolding Kn_def
    proof
      fix x assume "x \<in> closure (En (Suc N))"
      then have "\<forall>\<epsilon>>0. \<exists>q \<in> En (Suc N). dist x q < \<epsilon>"
        unfolding closure_def by simp
      hence "\<forall>\<epsilon>>0. \<exists>q \<in> En N. dist x q < \<epsilon>"
        using podksup_E by blast
      thus "x \<in> closure (En N)"
        unfolding closure_def by simp
    qed
  qed

  have Kn_neprazan: "\<forall>N. Kn N \<noteq> {}"
  proof
    fix N
    have "pn N \<in> En N"
      unfolding En_def by auto
    hence "En N \<noteq> {}"
      by blast
    have "En N \<subseteq> Kn N"
       unfolding Kn_def
  proof
    fix y
    assume "y \<in> En N"
    show "y \<in> closure (En N)"
      unfolding closure_def
    proof (intro CollectI allI impI)
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      have "y \<in> En N" using \<open>y \<in> En N\<close> .
      moreover
      have "dist y y < \<epsilon>" using \<open>\<epsilon> > 0\<close> by simp
      ultimately 
      show "\<exists>q \<in> En N. dist y q < \<epsilon>" by blast
    qed
  qed
    thus "Kn N \<noteq> {}"
      using `En N \<noteq> {}` by blast
  qed
  have "\<exists>! p. p \<in> (\<Inter>N. Kn N)"
    apply (rule diam_compact)
    using Kn_compact Kn_neprazan Kn_ugnjezden lim_diam_Kn by auto
  then obtain p where p_inter: "p \<in> (\<Inter>N. Kn N)" by blast

have "tendsto pn p"
  proof (unfold tendsto_def, intro allI impI)
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    obtain N0 where hN0: "diam (Kn N0) < \<epsilon>"
    proof -
      have "\<exists>N0. \<forall>N \<ge> N0. dist (diam (Kn N)) 0 < \<epsilon>"
        using lim_diam_Kn `\<epsilon> > 0` unfolding tendsto_def by auto
      then obtain N0 where "\<forall>N \<ge> N0. dist (diam (Kn N)) 0 < \<epsilon>" by blast
      hence "diam (Kn N0) < \<epsilon>"
        unfolding dist_real_def by auto
      thus thesis using that by blast
    qed
    show "\<exists>N. \<forall>n \<ge> N. dist (pn n) p < \<epsilon>"
    proof (rule exI[of _ N0], intro allI impI)
      fix n :: nat
      assume "n \<ge> N0"
     have pK: "p \<in> Kn N0"
        using p_inter by blast
      have pnn_K: "pn n \<in> Kn N0"
        unfolding En_def Kn_def closure_def using `n \<ge> N0` by auto
   have "dist p (pn n) < \<epsilon>"
      proof -
        have "dist p (pn n) \<le> diam (Kn N0)"
          using pK pnn_K by (rule dist_le_diam)
        thus "dist p (pn n) < \<epsilon>"
          using hN0 by auto
      qed
      thus "dist (pn n) p < \<epsilon>"
        by (simp add: dist_commute)
    qed
  qed
 have "p \<in> X"
   proof-
    have "p \<in> Kn 0"
      using p_inter by blast
    have "En 0 \<subseteq> X"
      unfolding En_def using assms(2) by auto
    have "closed X"
      using assms(1) compact_imp_closed by blast
    have "Kn 0 \<subseteq> X"
      unfolding Kn_def using closure_subset_closed[OF `closed X` `En 0 \<subseteq> X`] .
    thus "p \<in> X"
      using `p \<in> Kn 0` by auto
  qed
  thus "\<exists>p \<in> X. tendsto pn p"
    using `tendsto pn p` by blast
qed

(* mi20174_Nikola_Krstajic_FORMULACIJA * pomocna lema*)
definition bounded_set :: "(real^'k) set \<Rightarrow> bool" where
  "bounded_set S \<equiv> \<exists> p M. \<forall> x \<in> S. dist x p \<le> M"

(*pomocna lema 2.41 u knjizi  Nikola Krstajic* sorry za sad treba dokazati*)
lemma bounded_closure_compact:
  fixes E :: "(real^'k) set"
  assumes "bounded_set E"
    and "closed E"
  shows "compact E"    
  sorry


(*mi20174_Nikola_Krstajic_FORMULACIJA*)
lemma cauchy_tendsto_real_vec:
  fixes xn :: "(real^'k)  sequence"
  assumes "cauchy xn"
  shows "\<exists> x. tendsto xn x "
(*mi20174_Nikola_Krstajic_DOKAZ*)
  proof -
  define En where "En = (\<lambda> N. {xn n | n. n \<ge> N})"
 have hdiam: "tendsto (\<lambda>N. diam (En N)) 0"
  using assms cauchy_diam_nil En_def by blast
have "\<exists>N. diam (En N) < 1"
proof -
  have h: "\<exists>N. \<forall>n \<ge> N. \<bar>diam (En n)\<bar> < 1"
    using hdiam unfolding tendsto_def
    by auto
  obtain N where hN: "\<forall>n \<ge> N. \<bar>diam (En n)\<bar> < 1"
    using h by blast
  have hN1: "\<bar>diam (En N)\<bar> < 1"
    using hN by simp
  have "diam (En N) < 1"
    using hN1
    by linarith
  thus ?thesis by blast
qed

obtain N where hN: "diam (En N) < 1"
  using \<open>\<exists>N. diam (En N) < 1\<close> by blast
  define E where "E = range xn"

have "E = En N \<union> {xn n | n. n < N}"
proof
  show "E \<subseteq> En N \<union> {xn n | n. n < N}"
  proof
    fix x
    assume "x \<in> E"
    then obtain n where "x = xn n"
      unfolding E_def by blast
    show "x \<in> En N \<union> {xn n | n. n < N}"
    proof (cases "n < N")
      case True
      then show ?thesis
        using \<open>x = xn n\<close> by blast
    next
      case False
      then have "n \<ge> N" by simp
      then show ?thesis
        using \<open>x = xn n\<close> unfolding En_def by blast
    qed
  qed
next
  show "En N \<union> {xn n | n. n < N} \<subseteq> E"
  proof
    fix x
    assume "x \<in> En N \<union> {xn n | n. n < N}"
    then show "x \<in> E"
    proof
      assume "x \<in> En N"
      then obtain n where "x = xn n" "n \<ge> N"
        unfolding En_def by blast
      then show "x \<in> E"
        unfolding E_def by blast
    next
      assume "x \<in> {xn n | n. n < N}"
      then obtain n where "x = xn n" "n < N"
        by blast
      then show "x \<in> E"
        unfolding E_def by blast
    qed
  qed
qed

  have E_bounded: "bounded_set E"
   unfolding bounded_set_def
    proof -
      obtain N1 where N1: "\<forall>n\<ge>N1. \<forall>m\<ge>N1. dist (xn n) (xn m) < 1"
        using assms unfolding cauchy_def by (metis zero_less_one)
      obtain C where C: "\<forall>n<N1. dist (xn n) (xn N1) \<le> C"
        using finite_prefix_bounded by blast
      have "\<forall>x \<in> E. dist x (xn N1) \<le> max 1 C"
      proof
        fix x assume "x \<in> E"
        then obtain n where "x = xn n"
          unfolding E_def by blast
        show "dist x (xn N1) \<le> max 1 C"
        proof (cases "n \<ge> N1")
          case True
          then have "dist (xn n) (xn N1) < 1" using N1 by blast
          then show ?thesis using \<open>x = xn n\<close> by simp
        next
          case False
          then have "n < N1" by simp
          then have "dist (xn n) (xn N1) \<le> C" using C by blast
          then show ?thesis using \<open>x = xn n\<close> by simp
        qed
      qed
      then show "\<exists>p M. \<forall>x\<in>E. dist x p \<le> M"
        by blast
    qed

 have compact_closure_E: "compact (closure E)"
    proof -
      have closure_bounded: "bounded_set (closure E)"
      proof -
        from E_bounded obtain p M where pM: "\<forall>x\<in>E. dist x p \<le> M"
          unfolding bounded_set_def by blast
        have "\<forall>y \<in> closure E. dist y p \<le> M + 1"
        proof
          fix y assume "y \<in> closure E"
          then have "\<forall>\<epsilon>>0. \<exists>q\<in>E. dist y q < \<epsilon>"
            unfolding closure_def by simp
          then obtain q where hq: "q \<in> E" "dist y q < 1"
            using zero_less_one by blast
         have "dist y p \<le> dist y q + dist q p"
      by (simp add: dist_triangle)
    also have "... < 1 + M"
    proof -
      have "dist y q < 1" using hq(2) by simp
      have "dist q p \<le> M"
        using hq(1) pM by metis 
      show "dist y q + dist q p < 1 + M"
        using \<open>dist y q < 1\<close> \<open>dist q p \<le> M\<close> by simp
    qed
    finally show "dist y p \<le> M + 1" by simp
        qed
        then show ?thesis unfolding bounded_set_def by blast
      qed
      show ?thesis
       using bounded_closure_compact[OF closure_bounded closed_closure[of E]] by blast
   qed
   have in_E: "\<forall>n. xn n \<in> E"
     unfolding E_def by simp

 have in_closure_E: "\<forall>n. xn n \<in> closure E"
  proof
    fix n
    have "xn n \<in> E"
      unfolding E_def by blast
    then show "xn n \<in> closure E"
      unfolding closure_def
    proof (intro CollectI allI impI)
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      have "xn n \<in> E" unfolding E_def by blast
      moreover have "dist (xn n) (xn n) < \<epsilon>"
        using \<open>\<epsilon> > 0\<close> by simp
      ultimately show "\<exists>q\<in>E. dist (xn n) q < \<epsilon>"
        by blast
    qed
  qed
    have "\<exists>p \<in> closure E. tendsto xn p"
    using compact_cauchy_tendsto[OF compact_closure_E in_closure_E assms]
    by blast
  thus ?thesis
    by blast
qed




(* mi20174_Nikola_Krstajic_FORMULACIJA *)
definition complete :: "'a::metric_space set \<Rightarrow> bool" where
  "complete X \<longleftrightarrow> (\<forall> pn. (\<forall>n. pn n \<in> X ) \<and> cauchy pn \<longrightarrow> (\<exists> p \<in> X. tendsto pn p))"


(* mi20174_Nikola_Krstajic_FORMULACIJA *)
lemma compact_metric_space_complete:
  fixes X :: "'a::metric_space set"
  assumes "compact X"
  shows "complete X"
(*mi20174 Nikola_Krstajic DOKAZ*)
    unfolding complete_def
proof (intro allI impI)
  fix pn
  assume "(\<forall>n. pn n \<in> X) \<and> cauchy pn"
  then show "\<exists>p \<in> X. tendsto pn p"
    using compact_cauchy_tendsto[OF assms] by blast
qed

(* mi18306 Stefanija Markovic FORMULACIJA *)
lemma euclidean_space_complete:
  fixes x :: "(real^'k) sequence"
  assumes "cauchy x"
  shows "\<exists> l. tendsto x l"
  using assms
  by (rule cauchy_tendsto_real_vec)
  

(* mi18306 Stefanija_Markovic FORMULACIJA *)
lemma closed_limit_in_set:
  fixes E :: "'a::metric_space set"
    and pn :: "'a sequence"
  assumes "closed E" and "\<forall>n. pn n \<in> E" and "tendsto pn p"
  shows "p \<in> E"
proof (rule ccontr)
  assume "p \<notin> E"
  then have "p \<in> -E" by simp
  with \<open>closed E\<close> obtain e where e: "e > 0" "\<forall>y. dist y p < e \<longrightarrow> y \<in> -E"
    unfolding closed_def open_dist by auto
  with \<open>tendsto pn p\<close>  obtain N where N: "\<forall>n \<ge> N. dist (pn n) p < e"
    unfolding tendsto_def by auto
  then have "dist (pn N) p < e" by simp
  with e(2) have "pn N \<in> -E"  by simp
  with assms(2) show False by simp
qed

lemma closed_subset_complete:
  fixes X E :: "'a::metric_space set"
  assumes "complete X" and "closed E" and "E \<subseteq> X"
  shows "complete E"
  unfolding complete_def
proof (intro allI impI)
  fix pn
  assume "(\<forall>n. pn n \<in> E) \<and> cauchy pn"
  then have inE: "\<forall>n. pn n \<in> E" and cau: "cauchy pn" by auto
  with \<open>E \<subseteq> X\<close> have inX: "\<forall>n. pn n \<in> X" by auto
  with \<open>complete X\<close> cau obtain p where pX: "p \<in> X" and ptend: "tendsto pn p"
    unfolding complete_def by auto
  have "p \<in> E"
    using closed_limit_in_set[OF \<open>closed E\<close> inE ptend] .
  with ptend show "\<exists>p \<in> E. tendsto pn p" by auto
qed

(* mi18306 Stefanija_Markovic FORMULACIJA *)
definition mono_seq :: "real sequence \<Rightarrow> bool" where
  "mono_seq s \<longleftrightarrow> (\<forall>n. s n \<le> s (Suc n))"

(* mi18306 Stefanija_Markovic FORMULACIJA *)
definition antimono_seq :: "real sequence \<Rightarrow> bool" where
  "antimono_seq s \<longleftrightarrow> (\<forall>n. s n \<ge> s (Suc n))"

(* mi18306 Stefanija_Markovic FORMULACIJA *)
lemma mono_seq_le:
  fixes s :: "real sequence"
    and m n :: nat
  assumes "mono_seq s" and "m \<le> n"
  shows "s m \<le> s n"
  using \<open>m \<le> n\<close>
proof (induction rule: dec_induct)
  case base
  show ?case by simp
next
  case (step n)
  have "s m \<le> s n" by (rule step.IH)
  also have "s n \<le> s (Suc n)"
    using \<open>mono_seq s\<close> unfolding mono_seq_def by auto
  finally show ?case .
qed

(* mi18306 Stefanija_Markovic FORMULACIJA *)
lemma antimono_seq_le:
  fixes s :: "real sequence"
    and m n :: nat
  assumes "antimono_seq s" and "m \<le> n"
  shows "s n \<le> s m"
  using \<open>m \<le> n\<close>
proof (induction rule: dec_induct)
  case base
  show ?case by simp
next
  case (step n)
  have "s (Suc n) \<le> s n"
    using \<open>antimono_seq s\<close> unfolding antimono_seq_def by auto
  also have "s n \<le> s m" by (rule step.IH)
  finally show ?case .
qed

(* mi18306 Stefanija_Markovic POMOCNA *)
lemma mono_seq_uminus:
  fixes s :: "real sequence"
  shows "antimono_seq s \<longleftrightarrow> mono_seq (\<lambda>n. - s n)"
  unfolding antimono_seq_def mono_seq_def by simp

(* mi18306 Stefanija_Markovic POMOCNA *)
lemma bounded_uminus_real:
  fixes s :: "real sequence"
  shows "bounded s \<longleftrightarrow> bounded (\<lambda>n. - s n)"
  unfolding bounded_def
proof
  assume "\<exists>p M. \<forall>n. dist (s n) p \<le> M"
  then obtain p M where dispM: "\<forall>n. dist (s n) p \<le> M" by auto
  have "\<forall>n. dist (- s n) (- p) \<le> M"
  proof
    fix n
    have "dist (- s n) (- p) = dist (s n) p" by (simp add: dist_real_def)
    with dispM show "dist (- s n) (- p) \<le> M" by simp
  qed
  then show "\<exists>p M. \<forall>n. dist (- s n) p \<le> M" by auto
next
  assume "\<exists>p M. \<forall>n. dist (- s n) p \<le> M"
  then obtain p M where dispM: "\<forall>n. dist (- s n) p \<le> M" by auto
  have "\<forall>n. dist (s n) (- p) \<le> M"
  proof
    fix n
    have "dist (s n) (- p) = dist (- s n) p" by (simp add: dist_real_def)
    with dispM show "dist (s n) (- p) \<le> M" by simp
  qed
  then show "\<exists>p M. \<forall>n. dist (s n) p \<le> M" by auto
qed

(* mi18306 Stefanija_Markovic POMOCNA *)
lemma tendsto_uminus_real:
  fixes s :: "real sequence"
  shows "tendsto s l \<longleftrightarrow> tendsto (\<lambda>n. - s n) (- l)"
  unfolding tendsto_def
proof -
  have "\<And>n. dist (- s n) (- l) = dist (s n) l" by (simp add: dist_real_def)
  then show "(\<forall>\<epsilon> > 0. \<exists>N. \<forall>n \<ge> N. dist (s n) l < \<epsilon>) \<longleftrightarrow> (\<forall>\<epsilon> > 0. \<exists>N. \<forall>n \<ge> N. dist (- s n) (- l) < \<epsilon>)" 
    by simp
qed

(* mi18306 Stefanija Markovic POMOCNA *)
lemma mono_bounded_convergent:
  fixes s :: "real sequence"
  assumes "mono_seq s" and "bounded s"
  shows "\<exists>l. tendsto s l"
proof -
  from \<open>bounded s\<close> obtain p M where pM: "\<forall>n. dist (s n) p \<le> M"
    unfolding bounded_def by auto
  have upper: "\<And>x. x \<in> range s \<Longrightarrow> x \<le> p + M"
  proof -
    fix x assume "x \<in> range s"
    then obtain n where n: "x = s n" by auto
    have "s n - p \<le> dist (s n) p" by (simp add: dist_real_def)
    also have "... \<le> M" using pM by simp
    finally show "x \<le> p + M" using n by simp
  qed
  then have bdd_above_s: "bdd_above (range s)"
    unfolding bdd_above_def by auto
  have s_le_l: "\<And>n. s n \<le> Sup (range s)"
  proof -
    fix n
    have "s n \<in> range s" by simp
    with bdd_above_s show "s n \<le> Sup (range s)" by (auto simp add: cSup_upper)
  qed
  have find_close: "\<exists>n. Sup (range s) - \<epsilon> < s n" if "\<epsilon> > 0" for \<epsilon> :: real
  proof (rule ccontr)
    assume contra: "\<not> (\<exists>n. Sup (range s) - \<epsilon> < s n)"
    have all_le: "\<forall>n. s n \<le> Sup (range s) - \<epsilon>"
    proof
      fix n
      from contra have "\<not> (Sup (range s) - \<epsilon> < s n)" by simp
      then show "s n \<le> Sup (range s) - \<epsilon>" by simp
    qed
    have upper2: "\<And>x. x \<in> range s \<Longrightarrow> x \<le> Sup (range s) - \<epsilon>"
    proof -
      fix x assume "x \<in> range s"
      then obtain n where "x = s n" by auto
      with all_le show "x \<le> Sup (range s) - \<epsilon>" by simp
    qed
    have sup_le: "Sup (range s) \<le> Sup (range s) - \<epsilon>"
    proof (rule cSup_least)
      show "range s \<noteq> {}" by simp
    next
      fix x assume "x \<in> range s"
      then show "x \<le> Sup (range s) - \<epsilon>" using upper2 by simp
    qed
    from sup_le that show False by auto
  qed
  have "tendsto s (Sup (range s))"
    unfolding tendsto_def
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    then obtain N where N: "Sup (range s) - \<epsilon> < s N" using find_close by auto
    have "\<forall>n \<ge> N. dist (s n) (Sup (range s)) < \<epsilon>"
    proof (intro allI impI)
      fix n assume "n \<ge> N"
      have "s N \<le> s n" using mono_seq_le[OF \<open>mono_seq s\<close> \<open>N \<le> n\<close>] .
      with N have lower: "Sup (range s) - \<epsilon> < s n" by simp
      have "s n \<le> Sup (range s)" using s_le_l by simp
      with lower show "dist (s n) (Sup (range s)) < \<epsilon>" by (simp add: dist_real_def)
    qed
    then show "\<exists>N. \<forall>n \<ge> N. dist (s n) (Sup (range s)) < \<epsilon>" by auto
  qed
  then show ?thesis by auto
qed

(* mi18306 Stefanija_Markovic FORMULACIJA *)
lemma bounded_mono_convergent:
  fixes s :: "real sequence"
  assumes mono_assm: "mono_seq s \<or> antimono_seq s"
  shows "(\<exists>l. tendsto s l) \<longleftrightarrow> bounded s"
proof
  assume "\<exists>l. tendsto s l"
  then obtain l where "tendsto s l" by auto
  then show "bounded s" by (rule tendsto_bounded)
next
  assume bdd: "bounded s"
  show "\<exists>l. tendsto s l"
  proof (cases "mono_seq s")
    case True
    with bdd show ?thesis by (auto simp add: mono_bounded_convergent)
  next
    case False
    with mono_assm have "antimono_seq s" by auto
    then have mono_neg: "mono_seq (\<lambda>n. - s n)" by (simp add: mono_seq_uminus)
    with bdd bounded_uminus_real[of s] have bdd_neg: "bounded (\<lambda>n. - s n)" by auto
    with mono_bounded_convergent[OF mono_neg bdd_neg] 
      obtain l where hl: "tendsto (\<lambda>n. - s n) l" by auto
    with tendsto_uminus_real[of s "- l"] hl have "tendsto s (- l)" by simp
    then show ?thesis by auto
  qed
qed

(* mi23026_Lola_Vukovic FORMULACIJA *)
definition tendsto_top :: "real sequence \<Rightarrow> bool" where
  "tendsto_top s \<longleftrightarrow> (\<forall>M. \<exists>N. \<forall>n \<ge> N. s n \<ge> M)"

(* mi23026_Lola_Vukovic FORMULACIJA *)
definition tendsto_bot :: "real sequence \<Rightarrow> bool" where
  "tendsto_bot s \<longleftrightarrow> (\<forall>M. \<exists>N. \<forall>n \<ge> N. s n \<le> M)" 

(* mi23026_Lola_Vukovic FORMULACIJA pomocna *)
definition subsequential_limits :: "(nat ⇒ 'a::metric_space) ⇒ 'a set" where
  "subsequential_limits p = {q. ∃nk sk. subseq p nk sk ∧ sk ⇢ q}"

(* mi23026_Lola_Vukovic FORMULACIJA *)
lemma subsequential_limits_closed:
  fixes p :: "'a::metric_space sequence"
  shows "closed (subsequential_limits p)"
  sorry

(*mi23026_Lola_Vukovic FORMULACIJA pomocna*)
definition tendsto_ereal :: "(real sequence) \<Rightarrow> ereal \<Rightarrow> bool" where
  "tendsto_ereal s x \<longleftrightarrow> 
    (if x = \<infinity> then (\<forall>M. \<exists>N. \<forall>n \<ge> N. s n \<ge> M)
     else if x = -\<infinity> then (\<forall>M. \<exists>N. \<forall>n \<ge> N. s n \<le> M)
     else (\<exists>l. x = ereal l \<and> (\<forall>e > 0. \<exists>N. \<forall>n \<ge> N. dist (s n) l < e)))"

(*mi23026_Lola_Vukovic FORMULACIJA pomocna*)
definition E :: "(real sequence) \<Rightarrow> ereal set" where
  "E s = {x. \<exists>nk sk. subseq s nk sk \<and> tendsto_ereal sk x}"

(*mi23026_Lola_Vukovic FORMULACIJA*)
definition limsup :: "(real sequence) \<Rightarrow> ereal" where
  "limsup s = Sup (E s)"

(*mi23026_Lola_Vukovic FORMULACIJA*)
definition liminf:: "(real sequence) \<Rightarrow> ereal" where
  "liminf s = Inf (E s)"

(*mi23026_Lola_Vukovic FORMULACIJA*)
theorem limsup_alt:
  fixes s :: "real sequence"
    and y :: ereal
  assumes "y \<in> E s"
      and "\<forall>x > y. \<exists>N. \<forall>n \<ge> N. ereal (s n) < x"
  shows "limsup s \<in> E s" 
    and "\<forall>x > limsup s. \<exists>N. \<forall>n \<ge> N. ereal (s n) < x"
    and "y = limsup s"
  (*mi23026 Lola Vukovic DOKAZ*)
  proof -
  define L where "L = E s"
  have y_eq: "y = limsup s"
  proof (rule order_antisym)
    show "y ≤ limsup s"
      unfolding L_def limsup_def
      using `y ∈ E s` 
      by (simp add: Sup_upper)
  next
    show "limsup s ≤ y"
    proof (rule ccontr)
      assume "¬ limsup s ≤ y"
      hence "y < limsup s" by simp

      define p where "p = y"
      define q where "q = limsup s"
      have "p < q" using `y < limsup s` unfolding p_def q_def by simp

      obtain x where "p < x" "x < q"
        using dense `p<q`
        by auto

      obtain N where N_bound: "∀n ≥ N. ereal (s n) < x"
        using assms(2) `p < x` unfolding p_def by blast

      have "∃z ∈ E s. x < z"
        using `x < q` unfolding q_def limsup_def
        using less_Sup_iff by blast
      then obtain z where "z ∈ E s" and "x < z" by auto

      obtain nk sk where nk_sub: "subseq s nk sk"
        and sk_tend: "tendsto_ereal sk z"
        using `z ∈ E s` unfolding E_def by blast

      have sk_bound: "∀k ≥ N. ereal (sk k) ≤ x"
      proof (rule allI, rule impI)
        fix k assume "k ≥ N"
        have "nk k ≥ N"
          using `k ≥ N` nk_sub
          by (metis seq_suble subseq_def order_trans)
        thus "ereal (sk k) ≤ x"
          using N_bound subseq_def nk_sub less_imp_le 
          by (metis comp_apply)
      qed

      have "z ≤ x"
        proof (rule ccontr)
        assume "¬ z ≤ x"
        hence "x < z" by simp

        show False
        proof (cases z)
          case PInf
          hence "z = ∞" by simp
          obtain M where "x < ereal M"
            using `x < z`  ereal_dense2 by blast
          obtain N1 where "∀n ≥ N1. M ≤ sk n"
            using sk_tend `z=∞`  unfolding tendsto_ereal_def 
            by auto
          
          define k where "k = max N N1"
          have "ereal (sk k) ≤ x" using sk_bound k_def by simp
          moreover have "x < ereal (sk k)" 
            using  `x < ereal M` k_def 
            by (metis ‹x < ereal M› max.cobounded2 ‹∀n≥N1. M ≤ sk n› less_ereal_le k_def)
          ultimately show False by simp
        next
          case MInf
          hence False using `x<z` by simp
          thus ?thesis ..
        next
          case (real l)
          obtain r where "x < ereal r" "r < l"
            using `x < z` real ereal_dense2 
            by force
          
          obtain N2 where N2_def: "∀n ≥ N2. dist (sk n) l < l - r"
            using sk_tend real `r < l` unfolding tendsto_ereal_def 
            by fastforce

          define k where "k = max N N2"
          have "sk k > r" 
            using N2_def k_def unfolding dist_real_def 
            by (smt (verit, best) max.cobounded2)
          hence "x < ereal (sk k)" 
            using `x < ereal r` 
            by (metis ‹r < sk k› ‹x < ereal r› order_le_less less_ereal_le)
          moreover have "ereal (sk k) ≤ x" 
            using sk_bound k_def by simp
          ultimately show False by simp
        qed
      qed

      thus False
        using `x < z` by simp
    qed
  qed

  have "limsup s ∈ E s"
    using `y ∈ E s` y_eq by simp

  have "∀x > limsup s. ∃N. ∀n ≥ N. ereal (s n) < x"
    using assms(2) y_eq by simp

  show "limsup s ∈ E s" by (rule `limsup s ∈ E s`)
  show "∀x > limsup s. ∃N. ∀n ≥ N. ereal (s n) < x" by (rule `∀x > limsup s. ∃N. ∀n ≥ N. ereal (s n) < x`)
  show "y = limsup s" by (rule y_eq)
qed

(*mi23026 Lola Vukovic FORMULACIJA*)
theorem liminf_alt:
  fixes s :: "real sequence"
    and y :: ereal
  assumes "y \<in> E s"
      and "\<forall>x < y. \<exists>N. \<forall>n \<ge> N. ereal (s n) > x"
  shows "liminf s \<in> E s" 
    and "\<forall>x < liminf s. \<exists>N. \<forall>n \<ge> N. ereal (s n) > x"
    and "y = liminf s"
 (*mi23026 Lola Vukovic DOKAZ*)
proof -
  define L where "L = E s"
  show y_eq: "y = liminf s"
  proof (rule order_antisym)
    show "liminf s ≤ y"
      unfolding L_def liminf_def
      using `y ∈ E s` 
      by (simp add: Inf_lower)
  next
    show "y ≤ liminf s"
    proof (rule ccontr)
      assume "¬ y ≤ liminf s"
      hence "liminf s < y" by simp

      define p where "p = liminf s"
      define q where "q = y"
      have "p < q" using `liminf s < y` unfolding p_def q_def by simp

      obtain x where "p < x" "x < q"
        using dense `p < q`
        by auto

      obtain N where N_bound: "∀n ≥ N. ereal (s n) > x"
        using assms(2) `x < q` unfolding q_def by blast

      have "∃z ∈ E s. z < x"
        using `p < x` unfolding p_def liminf_def
        using Inf_less_iff by blast
      then obtain z where "z ∈ E s" and "z < x" by auto

      obtain nk sk where nk_sub: "subseq s nk sk"
        and sk_tend: "tendsto_ereal sk z"
        using `z ∈ E s` unfolding E_def by blast

      have sk_bound: "∀k ≥ N. x ≤ ereal (sk k)"
      proof (rule allI, rule impI)
        fix k assume "k ≥ N"
        have "nk k ≥ N"
          using `k ≥ N` nk_sub
          by (metis seq_suble subseq_def order_trans)
        thus "x ≤ ereal (sk k)"
          using N_bound subseq_def nk_sub less_imp_le 
          by (metis comp_apply)
      qed

      have "x ≤ z"
      proof (rule ccontr)
        assume "¬ x ≤ z"
        hence "z < x" by simp

        show False
        proof (cases z)
          case PInf
          hence False using `z < x` by simp
          thus ?thesis ..
        next
          case MInf
          hence "z = -∞" by simp
          obtain M where "ereal M < x"
            using `z < x` ereal_dense2 by blast
          obtain N1 where "∀n ≥ N1. sk n ≤ M"
            using sk_tend `z = -∞` unfolding tendsto_ereal_def 
            by auto

          define k where "k = max N N1"
          have "x ≤ ereal (sk k)" using sk_bound k_def by simp
          moreover have "ereal (sk k) < x"
            using `ereal M < x` k_def
            by (metis ‹ereal M < x› k_def order_trans less_ereal.simps(1) max.cobounded2 linorder_not_less ‹∀n≥N1. sk n ≤ M›)
          ultimately show False by simp
        next
          case (real l)
          obtain r where "l < r" "ereal r < x"
            using `z < x` real ereal_dense2 
            by force

          obtain N2 where N2_def: "∀n ≥ N2. dist (sk n) l < r - l"
            using sk_tend real `l < r` unfolding tendsto_ereal_def 
            by fastforce

          define k where "k = max N N2"
          have "sk k < r" 
            using N2_def k_def unfolding dist_real_def 
            by (smt (verit, best) max.cobounded2)
          hence "ereal (sk k) < x" 
            using `ereal r < x` 
            by (metis ‹sk k < r› ‹ereal r < x› order_le_less ereal_less_le)
          moreover have "x ≤ ereal (sk k)" 
            using sk_bound k_def by simp
          ultimately show False by simp
        qed
      qed

      thus False
        using `z < x` by simp
    qed
  qed

  show "liminf s ∈ E s"
    using `y ∈ E s` y_eq by simp

  show "∀x < liminf s. ∃N. ∀n ≥ N. ereal (s n) > x"
    using assms(2) y_eq by simp
qed

(* mi22059_Matija_Djordjevic POMOCNA FORMULACIJA I DOKAZ*)
lemma ereal_subseq_limit:
  fixes s :: "real sequence"
  shows "\<exists>nk zf.
    strict_mono nk \<and> ((ereal \<circ> s) \<circ> nk)  \<longlonglongrightarrow>  zf"
proof -
  obtain zf nk where
    "strict_mono nk"
    and "((ereal \<circ> s) \<circ> nk) \<longlonglongrightarrow> zf"
    using Liminf_Limsup.compact_complete_linorder[of "ereal \<circ> s"]
    by blast

  then show ?thesis
    by blast
qed

(* mi22059_Matija_Djordjevic POMOCNA FORMULACIJA I DOKAZ *)
lemma E_nonempty:
  fixes s :: "real sequence"
  shows "E s \<noteq> {}"
proof -
  obtain nk zf where
    nk_mono: "strict_mono nk"
    and hlim: "((ereal \<circ> s) \<circ> nk) \<longlonglongrightarrow> zf"
    using ereal_subseq_limit
    by blast

  define sk where
    "sk = s \<circ> nk"

  have hsub: "subseq s nk sk"
  unfolding subseq_def sk_def
  using nk_mono
  by simp

  have htend: "tendsto_ereal sk zf"
  proof (cases zf)
    case PInf

    have h:
        "\<forall>M. \<exists>N. \<forall>n \<ge> N. sk n \<ge> M"
      using hlim
      unfolding PInf
      by (simp add: Lim_PInfty sk_def)

    show ?thesis
      unfolding tendsto_ereal_def PInf
      using h
      by simp


next
    case MInf

    have h:
        "\<forall>M. \<exists>N. \<forall>n \<ge> N. sk n \<le> M"
      using hlim
      unfolding MInf
      by (simp add: Lim_MInfty sk_def)

    show ?thesis
      unfolding tendsto_ereal_def MInf
      using h
      by simp

  next
    case (real l)

    have h:
        "sk \<longlonglongrightarrow> l"
      using hlim
      unfolding real
      by (simp add: comp_assoc ereal_tendsto_simps2(1) sk_def)

    show ?thesis
      unfolding tendsto_ereal_def real
      using h
    by (metis LIMSEQ_iff_nz PInfty_neq_ereal(1) ereal_less_eq(2,3) ereal_top
        le_minus_iff)
  qed

  have "zf \<in> E s"
    unfolding E_def
    using hsub htend
    by blast

  thus "E s \<noteq> {}"
    by blast
qed

(* mi22059_Matija_Djordjevic POMOCNA FORMULACIJA I DOKAZ*)
lemma ereal_lim_imp_tendsto_ereal:
  fixes s :: "real sequence"
    and z :: ereal
  assumes "((ereal \<circ> s) \<longlonglongrightarrow> z)"
  shows "tendsto_ereal s z"
proof (cases z)
  case PInf

  have h:
      "\<forall>M. \<exists>N. \<forall>n \<ge> N. s n \<ge> M"
    using assms
    unfolding PInf
    by (simp add: Lim_PInfty)

  show ?thesis
    unfolding tendsto_ereal_def PInf
    using h
    by simp

next
  case MInf

  have h:
      "\<forall>M. \<exists>N. \<forall>n \<ge> N. s n \<le> M"
    using assms
    unfolding MInf
    by (simp add: Lim_MInfty)

  show ?thesis
    unfolding tendsto_ereal_def MInf
    using h
    by simp

next
  case (real l)

  have h:
      "s \<longlonglongrightarrow> l"
    using assms
    unfolding real
    by (simp add: ereal_tendsto_simps2(1))

  show ?thesis
    unfolding tendsto_ereal_def real
    using h
    by (simp add: lim_sequentially dist_real_def)
qed

(* mi22059_Matija_Djordjevic POMOCNA FORMULACIJA I DOKAZ*)
lemma E_eq_ereal_l:
  fixes s :: "real sequence"
    and l :: real
  assumes h1: "limsup s = liminf s"
    and h2: "limsup s = ereal l"
    and hy: "y \<in> E s"
  shows "y = ereal l"
proof -
  have hy_sup: "y \<le> limsup s"
    unfolding limsup_def
    using hy
    by (simp add: Sup_upper)

  have hy_inf: "liminf s \<le> y"
    unfolding liminf_def
    using hy
    by (simp add: Inf_lower)

  have "y \<le> ereal l"
    using hy_sup h2
    by simp

  moreover have "ereal l \<le> y"
    using hy_inf h1 h2
    by simp

  ultimately show "y = ereal l"
    by simp
qed

(* mi22059_Matija_Djordjevic_FORMULACIJA *)
lemma limsup_eq_liminf:
  fixes s :: "real sequence"
  and l :: real
shows "tendsto s l \<longleftrightarrow> limsup s = liminf s \<and> limsup s = ereal l"
(* mi22059_Matija_Djordjevic_DOKAZ *)
proof -
  have h1: "tendsto s l \<Longrightarrow> limsup s = ereal l"
  proof -
    assume hs: "tendsto s l"
    have hsub: "subseq s (\<lambda>n. n) s" unfolding subseq_def 
      by (simp add: comp_def strict_mono_on_ident)
    have hE: "ereal l \<in> E s" unfolding E_def
      using Analysis.tendsto_def hs hsub tendsto_ereal_def by fastforce
    have hbound: "\<forall>x > ereal l. \<exists> N. \<forall> n \<ge> N. ereal (s n) < x"
    proof (intro allI impI)
    fix x
    assume "x > ereal l"

    obtain r where "l < r" "ereal r < x"
      by (metis ‹ereal l < x› less_ereal.simps(1) ereal_dense2)

    obtain N where N_def: "\<forall>n \<ge> N. dist (s n) l < r - l"
      using hs
      unfolding Analysis.tendsto_def
      using `l < r`
      by fastforce

    have hN: "\<forall>n \<ge> N. ereal (s n) < x"
      using N_def ‹ereal r < x› dist_real_def ereal_less_le
      by fastforce

    then show "\<exists>N. \<forall>n \<ge> N. ereal (s n) < x"
      by blast
  qed

  have "limsup s \<le> ereal l"
    using limsup_alt hbound
    by (metis ereal_le_real hE)

  have "ereal l \<le> limsup s"
    unfolding E_def
    using hE hbound limsup_alt(3) by force

    then show ?thesis
      by (simp add: ‹Analysis.limsup s ≤ ereal l› dual_order.eq_iff) 
      
  qed

  have h2: "tendsto s l \<Longrightarrow> liminf s = ereal l" (*slicno kao h1*)
  proof -
     assume hs: "tendsto s l"
    have hsub: "subseq s (\<lambda>n. n) s" unfolding subseq_def 
      by (simp add: comp_def strict_mono_on_ident)
    have hE: "ereal l \<in> E s" unfolding E_def
      using Analysis.tendsto_def hs hsub tendsto_ereal_def by fastforce

    have hbound: "\<forall>x < ereal l. \<exists> N. \<forall> n \<ge> N. x < ereal (s n)"
    proof (intro allI impI)
    fix x
    assume "x < ereal l"

    obtain r where "x < ereal r" "r < l"
      by (metis ‹x < ereal l› less_ereal.simps(1) ereal_dense2)

    obtain N where N_def: "\<forall>n \<ge> N. dist (s n) l < l - r"
      using hs
      unfolding Analysis.tendsto_def
      using `r < l`
      by fastforce

    have hN: "\<forall>n \<ge> N. x < ereal (s n)"
      using N_def ‹x < ereal r› dist_real_def less_ereal_le by auto

    then show "\<exists>N. \<forall>n \<ge> N. x < ereal (s n)"
      by blast
  qed  


  have "ereal l \<le> liminf s"
    using hE hbound liminf_alt(3) by fastforce

  have "liminf s \<le> ereal l"
    using liminf_alt hbound
    by (metis ereal_le_real hE)

   then show ?thesis
     using ‹ereal l \<le> Analysis.liminf s› by force
 qed


  have h3: "limsup s = liminf s \<and> limsup s = ereal l \<Longrightarrow> tendsto s l"
   proof -
    assume h:
      "limsup s = liminf s \<and> limsup s = ereal l"

    show "tendsto s l"
      unfolding Analysis.tendsto_def
    proof (intro allI impI)
      fix e :: real
      assume he: "e > 0"

      show "\<exists>N. \<forall>n \<ge> N. dist (s n) l < e"
      proof (rule ccontr)
        assume hnot:
          "\<not> (\<exists>N. \<forall>n \<ge> N. dist (s n) l < e)"

        have hnot_eventually:
            "\<not> eventually (\<lambda>n. dist (s n) l < e) sequentially"
          using hnot
          by (simp add: eventually_sequentially)

        obtain nk :: "nat ⇒ nat" where
          nk_prop: "strict_mono nk \<and> (\<forall>n. \<not> dist (s (nk n)) l < e)"
          using not_eventually_sequentiallyD[OF hnot_eventually]
          by blast

        have nk_mono: "strict_mono nk"
          using nk_prop by blast

        have hnk: "\<forall>n. \<not> dist (s (nk n)) l < e"
          using nk_prop by blast


        define t where
          "t = s \<circ> nk"

        obtain nk' zf where
          nk'_mono: "strict_mono nk'"
          and hlim:
            "((ereal \<circ> t) \<circ> nk') \<longlonglongrightarrow> zf"
          using ereal_subseq_limit[of t]
          by blast

        define nk'' where
          "nk'' = nk \<circ> nk'"

        define sk where
          "sk = s \<circ> nk''"

        have nk''_mono:
            "strict_mono nk''"
          unfolding nk''_def
          using nk_mono nk'_mono
          by (simp add: strict_mono_o)

        have hsub:
            "subseq s nk'' sk"
        unfolding subseq_def
        using nk''_mono
        by (simp add: sk_def nk''_def)

        have hlim':
            "((ereal \<circ> sk) \<longlonglongrightarrow> zf)"
        proof -
          have
            "((ereal \<circ> t) \<circ> nk') \<longlonglongrightarrow> zf"
            using hlim .

          then show
            "((ereal \<circ> sk) \<longlonglongrightarrow> zf)"
            unfolding sk_def nk''_def t_def
            by (simp add: comp_assoc)
        qed

        have htend:
            "tendsto_ereal sk zf"
          using ereal_lim_imp_tendsto_ereal[OF hlim']
          by simp

        have hzE:
            "zf \<in> E s"
          unfolding E_def
          using hsub htend
          by blast

        have h_limsup: "limsup s = liminf s"
          using h by blast

        have h_limsup_l: "limsup s = ereal l"
          using h by blast

        have hz:
            "zf = ereal l"
          using E_eq_ereal_l[OF h_limsup h_limsup_l hzE]
          by simp


          have hconv:
            "tendsto_ereal sk (ereal l)"
          using htend hz
          by simp

        have hN:
            "\<exists>N. \<forall>n \<ge> N. dist (sk n) l < e"
          using hconv he
          unfolding tendsto_ereal_def
          by fastforce

        obtain N where
          hN':
            "\<forall>n \<ge> N. dist (sk n) l < e"
          using hN
          by blast


      have hbad:
        "\<not> dist (s (nk (nk' N))) l < e"
        using hnk
        by blast


        show False
          using hbad hN
          by (metis hnk nk''_def sk_def comp_apply strict_mono_imp_increasing nk'_mono)
      qed
    qed
  qed


  show ?thesis by (metis h1 h2 h3)
qed

(* mi22059_Matija_Djordjevic_FORMULACIJA *)
lemma limsup_mono:
  fixes s t  :: "real sequence"
    and N :: nat
  assumes "\<forall>n \<ge> N. s n \<le> t n"
  shows "limsup s \<le> limsup t"
(* mi22059_Matija_Djordjevic_DOKAZ *)
  proof (rule ccontr)

  assume h: "\<not> limsup s \<le> limsup t"

  hence hst: "limsup t < limsup s"
    by simp

  obtain x where
    xt: "limsup t < x"
    and xs: "x < limsup s"
    using ereal_dense2 hst
    by blast

  have "\<exists>y \<in> E s. x < y"
    unfolding limsup_def
    using xs less_Sup_iff
    using limsup_def by auto


  then obtain y where
    yE: "y \<in> E s"
    and xy: "x < y"
    by blast

  obtain ns ss where
    ns_sub: "subseq s ns ss"
    and ss_lim: "tendsto_ereal ss y"
    using yE unfolding E_def
    by blast

  have ss_eventually:
      "\<exists>K. \<forall>k \<ge> K. x < ereal (ss k)"

  proof -
    show ?thesis

    proof (cases y)
      case PInf

      obtain K where K: "\<forall>k \<ge> K. x < ereal (ss k)"
        using ss_lim PInf xy
        unfolding tendsto_ereal_def
        by (meson ereal_dense3 less_ereal_le)
      
      then show ?thesis by blast

    next
      case MInf

      have False
        using xy MInf
        by simp
      then show ?thesis by blast

    next
      case (real l)

      have hlx: "x < ereal l"
        using xy real
        by simp

      obtain r where
        "x < ereal r"
        and "r < l"
        using hlx ereal_dense2
        by fastforce

      have hpos: "0 < l - r"
        using ‹r < l›
        by linarith

      obtain K where K:"\<forall>k \<ge> K. dist (ss k) l < l - r"
        using ss_lim real hpos
        unfolding tendsto_ereal_def
        by fastforce

      show ?thesis
      proof (rule exI[of _ K])

        show "\<forall>k \<ge> K. x < ereal (ss k)"
        proof (intro allI impI)

          fix k
          assume hk: "k \<ge> K"

          have hdist: "dist (ss k) l < l - r"
            using K hk
            by blast

          have hssr: "r < ss k"
            using hdist
            unfolding dist_real_def
            by linarith

          have "ereal r < ereal (ss k)"
            using hssr
            by simp

          then show "x < ereal (ss k)"
            using ‹x < ereal r›
            by order

        qed
      qed
    qed
  qed

  define u where "u k = t (ns k)"

  have u_bound: "\<exists>K. \<forall>k \<ge> K. ss k \<le> u k"
  proof -

    obtain K where K:"\<forall>k \<ge> K. x < ereal (ss k)"
      using ss_eventually
      by blast

    show "\<exists>K. \<forall>k \<ge> K. ss k \<le> u k"
    proof (rule exI[of _ "max K N"])

      show "\<forall>k \<ge> max K N. ss k \<le> u k"
      proof (intro allI impI)

        fix k

        assume hk: "k \<ge> max K N"

        have hkN: "k \<ge> N"
          using hk
          by simp

        have hnkN: "N \<le> ns k"
          using hkN ns_sub
          by (metis seq_suble subseq_def order_trans)

        have hst: "s (ns k) \<le> t (ns k)"
          using assms hnkN
          by blast

        have hss: "ss k = s (ns k)"
          using ns_sub
          unfolding subseq_def
          by simp


        have hu: "u k = t (ns k)"
          unfolding u_def
        using ‹u \<equiv> \<lambda>k. t (ns k)› by simp

        show "ss k \<le> u k"
          using hst hss hu
          by simp

      qed
    qed
  qed


  have u_eventually: "\<exists>K. \<forall>k \<ge> K. x < ereal (u k)"
  proof -

    obtain K1 where K1: "\<forall>k \<ge> K1. x < ereal (ss k)"
      using ss_eventually
      by blast

    obtain K2 where K2: "\<forall>k \<ge> K2. ss k \<le> u k"
      using u_bound
      by blast


    show "\<exists>K. \<forall>k \<ge> K. x < ereal (u k)"
    proof (rule exI[of _ "max K1 K2"])

      show "\<forall>k \<ge> max K1 K2. x < ereal (u k)"
      proof (intro allI impI)

        fix k

        assume hk: "k \<ge> max K1 K2"

        have hk1: "k \<ge> K1"
          using hk
          by simp

        have hk2: "k \<ge> K2"
          using hk
          by simp

        have hsx: "x < ereal (ss k)"
          using K1 hk1
          by blast

        have hsu: "ss k \<le> u k"
          using K2 hk2
          by blast

        have "ereal (ss k) \<le> ereal (u k)"
          using hsu
          by simp

        thus "x < ereal (u k)"
          using hsx
          by order

      qed
    qed
  qed


  obtain nk uk zf where
    nk_sub: "subseq u nk uk"
    and uk_lim: "tendsto_ereal uk zf"
    using E_nonempty E_def by fastforce 


  have zfE: "zf \<in> E t"
  proof -
    have hcomp: "subseq t (ns \<circ> nk) uk"

    proof -
      have hmono:"strict_mono (ns \<circ> nk)"
        using ns_sub nk_sub
        unfolding subseq_def
        by (simp add: strict_mono_def comp_def)

      have huk: "uk = t \<circ> (ns \<circ> nk)"
        using nk_sub
        unfolding subseq_def
      by (simp add: ‹u \<equiv> \<lambda>k. t (ns k)› comp_def)


      show "subseq t (ns \<circ> nk) uk"
        unfolding subseq_def
        using hmono huk
        by simp
    qed

    show "zf \<in> E t"
      unfolding E_def
      using hcomp uk_lim
      by blast

  qed

  have zf_le: "zf \<le> limsup t"
    unfolding limsup_def
    using zfE
    by (rule Sup_upper)


  have zf_lt_x: "zf < x"
    using zf_le xt
    by order


  have uk_eventually: "\<exists>K. \<forall>k \<ge> K. x < ereal (uk k)"
  proof -
    obtain K where K: "\<forall>k \<ge> K. x < ereal (u k)"
      using u_eventually
      by blast


    show "\<exists>K. \<forall>k \<ge> K. x < ereal (uk k)"
    proof (rule exI[of _ K])

      show "\<forall>k \<ge> K. x < ereal (uk k)"
      proof (intro allI impI)

        fix k

        assume hk: "k \<ge> K"

        have hnk: "k \<le> nk k"
          using nk_sub
          by (metis seq_suble subseq_def)

        have hnK: "nk k \<ge> K"
          using hk hnk
          by simp

        have hu: "x < ereal (u (nk k))"
          using K hnK
          by blast

        have huk: "uk k = u (nk k)"
          using nk_sub
          unfolding subseq_def
          by simp

        show "x < ereal (uk k)"
          using hu huk
          by simp

      qed
    qed
  qed

  have x_le_zf: "x \<le> zf"
  proof (rule ccontr)

    assume hnot: "\<not> x \<le> zf"

    hence hzx: "zf < x"
      by simp

    obtain K where K: "\<forall>k \<ge> K. x < ereal (uk k)"
      using uk_eventually
      by blast

    show False
    proof (cases zf)
      case PInf

      have False
        using hzx
      by (simp add: PInf)
      thus ?thesis ..

    next
      case MInf

      obtain M where "ereal M < x"
        using ereal_dense2 hzx
        by blast

      obtain N1 where N1: "\<forall>n \<ge> N1. uk n \<le> M"
        using uk_lim MInf
        unfolding tendsto_ereal_def
        by auto

      define k where "k = max K N1"

      have hkK: "k \<ge> K"
        unfolding k_def
        by simp

      have hkN1: "k \<ge> N1"
        unfolding k_def
        by simp

      have hxu: "x < ereal (uk k)"
        using K hkK
        by blast

      have hukM: "uk k \<le> M"
        using N1 hkN1
        by blast


      have "ereal (uk k) \<le> ereal M"
        using hukM
        by simp

      have "ereal M < x"
        using `ereal M < x`
        by simp

      have "ereal (uk k) < x"
        using `ereal (uk k) \<le> ereal M` `ereal M < x`
        by order

      show False
        using hxu `ereal (uk k) < x`
        by simp

    next
      case (real l)

      have hlx: "l < x"
        using hzx zf_lt_x real
        by simp


      obtain r where "l < r" "ereal r < x"
        using hlx ereal_dense2
        by fastforce

      have hrx: "r < x"
        using ‹ereal r < x›
        by simp

      have hconv:"\<forall>e > 0. \<exists>K. \<forall>k \<ge> K. dist (uk k) l < e"
        using uk_lim ‹zf = ereal l›
        unfolding tendsto_ereal_def
        by simp

      have hpos: "0 < r - l"
        using ‹l < r›
        by linarith


      have h_eps:"\<exists>K. \<forall>k \<ge> K. dist (uk k) l < r - l"
        using hconv hpos
        by blast


      obtain N1 where N1: "\<forall>k \<ge> N1. dist (uk k) l < r - l"
        using h_eps
        by blast

      define k where "k = max K N1"

      have hkK: "k \<ge> K"
        unfolding k_def
        by simp

      have hkN: "k \<ge> N1"
        unfolding k_def
        by simp

      have hxuk: "x < ereal (uk k)"
        using K hkK
        by blast

      have hdist: "dist (uk k) l < r - l"
        using N1 hkN
        by blast

      have hukx: "uk k < r"
        using hdist
        unfolding dist_real_def
        by linarith

      have "ereal (uk k) < x"
      using hukx hrx ereal_less_le by simp

      thus False
        using hxuk
        by simp
    qed
  qed


  show False
    using zf_lt_x x_le_zf
    by simp
qed

(* mi22059_Matija_Djordjevic_FORMULACIJA *)
lemma liminf_mono:
  fixes s t :: "real sequence"
    and N :: nat
  assumes "\<forall>n \<ge> N. s n \<le> t n"
  shows "liminf s \<le> liminf t"
 (* mi22059_Matija_Djordjevic_DOKAZ *)
proof (rule ccontr)

  assume h: "\<not> liminf s \<le> liminf t"

  hence hst: "liminf t < liminf s"
    by simp

  obtain x where
    xt: "liminf t < x"
    and xs: "x < liminf s"
    using ereal_dense2 hst
    by blast

  have "\<exists>y \<in> E t. y < x"
    unfolding liminf_def
    using xt Inf_less_iff
    using liminf_def by auto

  then obtain y where
    yE: "y \<in> E t"
    and yx: "y < x"
    by blast

  obtain nt tt where
    nt_sub: "subseq t nt tt"
    and tt_lim: "tendsto_ereal tt y"
    using yE unfolding E_def
    by blast

  have tt_eventually:
      "\<exists>K. \<forall>k \<ge> K. ereal (tt k) < x"
  proof -
    show ?thesis
    proof (cases y)
      case PInf
      have False
        using yx PInf
        by simp
      then show ?thesis by blast

    next
     case MInf
      obtain m :: real where hm: "ereal m < x"
        using yx MInf ereal_dense2 by blast

      obtain K where K: "\<forall>k \<ge> K. tt k \<le> m"
        using tt_lim MInf unfolding tendsto_ereal_def by auto

      have "\<forall>k \<ge> K. ereal (tt k) < x"
      proof (intro allI impI)
        fix k
        assume "k \<ge> K"
        hence "tt k \<le> m"
          using K by simp
        hence "ereal (tt k) \<le> ereal m"
          by simp
        thus "ereal (tt k) < x"
          using hm by (rule order_le_less_trans)
      qed
      thus ?thesis by blast

    next
      case (real l)
      have hlx: "ereal l < x"
        using yx real
        by simp

      obtain r where
        "l < r"
        and "ereal r < x"
        using hlx ereal_dense2
        by fastforce

      have hpos: "0 < r - l"
        using ‹l < r›
        by linarith

      obtain K where K: "\<forall>k \<ge> K. dist (tt k) l < r - l"
        using tt_lim real hpos
        unfolding tendsto_ereal_def
        by fastforce

      show ?thesis
      proof (rule exI[of _ K])
        show "\<forall>k \<ge> K. ereal (tt k) < x"
        proof (intro allI impI)
          fix k
          assume hk: "k \<ge> K"

          have hdist: "dist (tt k) l < r - l"
            using K hk
            by blast

          have httr: "tt k < r"
            using hdist
            unfolding dist_real_def
            by linarith

          have "ereal (tt k) < ereal r"
            using httr
            by simp

          then show "ereal (tt k) < x"
            using ‹ereal r < x›
            by order
        qed
      qed
    qed
  qed

  define v where "v k = s (nt k)"

  have v_bound: "\<exists>K. \<forall>k \<ge> K. v k \<le> tt k"
  proof -
    obtain K where K: "\<forall>k \<ge> K. ereal (tt k) < x"
      using tt_eventually
      by blast

    show "\<exists>K. \<forall>k \<ge> K. v k \<le> tt k"
    proof (rule exI[of _ "max K N"])
      show "\<forall>k \<ge> max K N. v k \<le> tt k"
      proof (intro allI impI)
        fix k
        assume hk: "k \<ge> max K N"

        have hkN: "k \<ge> N"
          using hk
          by simp

        have hntN: "N \<le> nt k"
          using hkN nt_sub
          by (metis seq_suble subseq_def order_trans)

        have hst: "s (nt k) \<le> t (nt k)"
          using assms hntN
          by blast

        have htt: "tt k = t (nt k)"
          using nt_sub
          unfolding subseq_def
          by simp

        have hv: "v k = s (nt k)"
          unfolding v_def
          using ‹v  \<equiv> \<lambda>k. s (nt k)› by simp

        show "v k \<le> tt k"
          using hst htt hv
          by simp
      qed
    qed
  qed

  have v_eventually: "\<exists>K. \<forall>k \<ge> K. ereal (v k) < x"
  proof -
    obtain K1 where K1: "\<forall>k \<ge> K1. ereal (tt k) < x"
      using tt_eventually
      by blast

    obtain K2 where K2: "\<forall>k \<ge> K2. v k \<le> tt k"
      using v_bound
      by blast

    show "\<exists>K. \<forall>k \<ge> K. ereal (v k) < x"
    proof (rule exI[of _ "max K1 K2"])
      show "\<forall>k \<ge> max K1 K2. ereal (v k) < x"
      proof (intro allI impI)
        fix k
        assume hk: "k \<ge> max K1 K2"

        have hk1: "k \<ge> K1"
          using hk
          by simp

        have hk2: "k \<ge> K2"
          using hk
          by simp

        have htx: "ereal (tt k) < x"
          using K1 hk1
          by blast

        have hvt: "v k \<le> tt k"
          using K2 hk2
          by blast

        have "ereal (v k) \<le> ereal (tt k)"
          using hvt
          by simp

        thus "ereal (v k) < x"
          using htx
          by order
      qed
    qed
  qed

  obtain nk vk zf where
    nk_sub: "subseq v nk vk"
    and vk_lim: "tendsto_ereal vk zf"
    using E_nonempty E_def by fastforce

  have zfE: "zf \<in> E s"
  proof -
    have hcomp: "subseq s (nt \<circ> nk) vk"
    proof -
      have hmono: "strict_mono (nt \<circ> nk)"
        using nt_sub nk_sub
        unfolding subseq_def
        by (simp add: strict_mono_def comp_def)

      have hvk: "vk = s \<circ> (nt \<circ> nk)"
        using nk_sub
        unfolding subseq_def
        by (simp add: ‹v \<equiv> \<lambda>k. s (nt k)› comp_def)

      show "subseq s (nt \<circ> nk) vk"
        unfolding subseq_def
        using hmono hvk
        by simp
    qed

    show "zf \<in> E s"
      unfolding E_def
      using hcomp vk_lim
      by blast
  qed

  have le_zf: "liminf s \<le> zf"
    unfolding liminf_def
    using zfE
    by (rule Inf_lower)

  have x_lt_zf: "x < zf"
    using le_zf xs
    by order

  have vk_eventually: "\<exists>K. \<forall>k \<ge> K. ereal (vk k) < x"
  proof -
    obtain K where K: "\<forall>k \<ge> K. ereal (v k) < x"
      using v_eventually
      by blast

    show "\<exists>K. \<forall>k \<ge> K. ereal (vk k) < x"
    proof (rule exI[of _ K])
      show "\<forall>k \<ge> K. ereal (vk k) < x"
      proof (intro allI impI)
        fix k
        assume hk: "k \<ge> K"

        have hnk: "k \<le> nk k"
          using nk_sub
          by (metis seq_suble subseq_def)

        have hnK: "nk k \<ge> K"
          using hk hnk
          by simp

        have hv: "ereal (v (nk k)) < x"
          using K hnK
          by blast

        have hvk: "vk k = v (nk k)"
          using nk_sub
          unfolding subseq_def
          by simp

        show "ereal (vk k) < x"
          using hv hvk
          by simp
      qed
    qed
  qed

  have zf_le_x: "zf \<le> x"
  proof (rule ccontr)
    assume hnot: "\<not> zf \<le> x"
    hence hxz: "x < zf"
      by simp

    obtain K where K: "\<forall>k \<ge> K. ereal (vk k) < x"
      using vk_eventually
      by blast

    show False
    proof (cases zf)
      case MInf
      have False
        using hxz
        by (simp add: MInf)
      thus ?thesis ..

    next
      case PInf
      obtain M where "x < ereal M"
        using ereal_dense2 hxz
        by blast

      obtain N1 where N1: "\<forall>n \<ge> N1. M \<le> vk n"
        using vk_lim PInf
        unfolding tendsto_ereal_def
        by auto

      define k where "k = max K N1"

      have hkK: "k \<ge> K"
        unfolding k_def
        by simp

      have hkN1: "k \<ge> N1"
        unfolding k_def
        by simp

      have hvx: "ereal (vk k) < x"
        using K hkK
        by blast

      have hMvk: "M \<le> vk k"
        using N1 hkN1
        by blast

      have "ereal M \<le> ereal (vk k)"
        using hMvk
        by simp

      have "x < ereal M"
        using ‹x < ereal M›
        by simp

      have "x < ereal (vk k)"
        using ‹x < ereal M› ‹ereal M \<le> ereal (vk k)›
        by order

      show False
        using hvx ‹x < ereal (vk k)›
        by simp

    next
      case (real l)
      have hxl: "x < l"
        using hxz x_lt_zf real
        by simp

      obtain r where "x < ereal r" "r < l"
        using hxl ereal_dense2
        by fastforce

      have hrx: "x < r"
        using ‹x < ereal r›
        by simp

      have hconv: "\<forall>e > 0. \<exists>K. \<forall>k \<ge> K. dist (vk k) l < e"
        using vk_lim ‹zf = ereal l›
        unfolding tendsto_ereal_def
        by simp

      have hpos: "0 < l - r"
        using ‹r < l›
        by linarith

      have h_eps: "\<exists>K. \<forall>k \<ge> K. dist (vk k) l < l - r"
        using hconv hpos
        by blast

      obtain N1 where N1: "\<forall>k \<ge> N1. dist (vk k) l < l - r"
        using h_eps
        by blast

      define k where "k = max K N1"

      have hkK: "k \<ge> K"
        unfolding k_def
        by simp

      have hkN: "k \<ge> N1"
        unfolding k_def
        by simp

      have hxvk: "ereal (vk k) < x"
        using K hkK
        by blast

      have hdist: "dist (vk k) l < l - r"
        using N1 hkN
        by blast

      have hukx: "r < vk k"
        using hdist
        unfolding dist_real_def
        by linarith

      have "x < ereal (vk k)"
        using hukx hrx ereal_less_le 
      by (simp add: less_ereal_le)

      thus False
        using hxvk
        by simp
    qed
  qed

  show False
    using x_lt_zf zf_le_x
    by simp
qed


(* mi22059_Matija_Djordjevic_FORMULACIJA *)
lemma tendsto_npow_neg:
  fixes p :: "real"
  assumes "p>0"
  shows "(λn. 1 / ((real n) powr p)) ⇢ 0"
(* mi23026_Lola_Vukovic DOKAZ *)
 proof (rule metric_LIMSEQ_I)
  fix e :: real
  assume "e > 0"

  define K where "K = (1 / e) powr (1 / p)"

  obtain N where N_prop: "real N > K"
    using reals_Archimedean2 by blast

  have "∀n ≥ max 1 N. dist (1 / ((real n) powr p)) 0 < e"
  proof (rule allI, rule impI)
    fix n :: nat
    assume hn: "n ≥ max 1 N"
    hence n_pos: "real n > 0" by simp
    hence "real n ≥ real N" using hn by simp
    hence "real n > K" using N_prop by linarith
    hence "(real n) powr p > K powr p"
      using n_pos `p > 0` powr_less_mono2 K_def by auto
    also have "K powr p = ((1 / e) powr (1 / p)) powr p"
      by (simp add: K_def)
    also have "… = (1 / e) powr ((1 / p) * p)"
      using `e > 0` by (simp add: powr_powr)
    also have "… = (1 / e) powr 1"
      using `p > 0` by simp
    also have "… = 1 / e"
      using ‹0 < e› by simp
    finally have npow_gt: "(real n) powr p > 1 / e" .

    have "1 / ((real n) powr p) < e"
      using npow_gt `e > 0` n_pos
      by (metis ‹0 < e› n_pos npow_gt powr_gt_zero mult.commute order_less_irrefl divide_less_eq)

    thus "dist (1 / ((real n) powr p)) 0 < e"
      using n_pos `p > 0` by simp
  qed

  thus "∃N. ∀n≥N. dist (1 / ((real n) powr p)) 0 < e"
    by blast
qed 


(* mi22164_Lazar_Nikolic_POMOCNA *)
lemma tendsto_zero_aux:
  fixes s :: "real sequence"
  fixes x :: "real sequence"
  assumes "∃N. ∀n≥N. 0 ≤ x n ∧ x n ≤ s n"
  shows "tendsto s 0 ⟶ tendsto x 0"
(* mi22164_Lazar_Nikolic_DOKAZ *)
  unfolding tendsto_def
proof
  assume tendsto_s_0:"∀ε>0. ∃N. ∀n≥N. dist (s n) 0 < ε"
  show "∀ε>0. ∃N. ∀n≥N. dist (x n) 0 < ε"
  proof
    fix ε
    show "0 < ε ⟶ (∃N. ∀n≥N. dist (x n) 0 < ε)"
    proof
      assume "0 < ε"
      with tendsto_s_0 have "∃N. ∀n≥N. dist (s n) 0 < ε" by auto
      then obtain N1 where N1_prop:"∀n≥N1. dist (s n) 0 < ε" by auto

      from assms obtain N2 where N2_prop: "∀n≥N2. 0 ≤ x n ∧ x n ≤ s n" by auto

      define N where "N = max N1 N2"

      from N1_prop N_def have N_prop1:"∀n≥N. dist (s n) 0 < ε" by auto
      from N2_prop N_def have N_prop2:"∀n≥N. 0 ≤ x n ∧ x n ≤ s n" by auto

      show "∃N. ∀n≥N. dist (x n) 0 < ε"
      proof (rule_tac x=N in exI)
        show "∀n≥N. dist (x n) 0 < ε"
        proof
          fix n
          show "N ≤ n ⟶ dist (x n) 0 < ε"
          proof
            assume "N ≤ n"
            
            from N_prop1 ‹N ≤ n› have 1: "dist (s n) 0 < ε" by auto
            from N_prop2 ‹N ≤ n› have "0 ≤ x n ∧ x n ≤ s n" by auto
            then have 2: "dist (x n) 0 ≤ dist (s n) 0" by (auto simp add: dist_norm)

            from 1 2 show "dist (x n) 0 < ε" by auto
          qed
        qed
      qed
    qed
  qed
qed

(* mi22164_Lazar_Nikolic_POMOCNA *)
lemma tendsto_root_one:
  fixes p :: "real"
  assumes "p > 1"
  shows "tendsto (λn. p powr (1/(real n))) 1"
(* mi22164_Lazar_Nikolic_DOKAZ *)
proof -
  define x :: "real sequence" 
    where "x = (λn. p powr (1/(real n))-1)"

  define s :: "real sequence"
    where "s = (λn. (p - 1) / n)"

  have 1:"∃N. ∀n≥N. 0 ≤ x n ∧ x n ≤ s n"
  proof (rule_tac x=1 in exI)
    show "∀n≥1. 0 ≤ x n ∧ x n ≤ s n"
    proof
      fix n
      show "1 ≤ n ⟶ 0 ≤ x n ∧ x n ≤ s n"
      proof
        assume n1: "1 ≤ n"
        then have n0: "n > 0" by simp

        from powr_powr[of p "1/n" "n"] have pomocna:"(p powr (1 / real n)) powr real n = p"
          using assms n0 by auto
      
        have "x n = p powr (1/n) - 1" using x_def by simp
        then have rx:"1 + x n = p powr (1/n)" by simp
        
        have l:"0 < x n" (* sledgehammer *)
          by (smt (verit) assms powr_powr[of p "1/n" "n"] rx
              mult_eq_0_iff of_nat_less_0_iff pomocna powr01_less_one powr_eq_one_iff powr_gt_zero)
        
        from rx have "(1 + x n) powr n = (p powr (1/real n)) powr real n" by simp
        then have "(1 + x n) powr n = p" using pomocna by auto
        then have "(1 + x n) ^ n = p" using l powr_realpow by auto
        then have "1 + n * x n ≤ p" by (smt (verit) l linear_plus_1_le_power)
        then have "n * x n ≤ p - 1" by simp
        then have "x n ≤ (p - 1) / n" by (simp add: mult.commute mult_imp_le_div_pos n0)
        then have r:"x n ≤ s n" by (simp add: s_def)

        from l r show "0 ≤ x n ∧ x n ≤ s n" by simp
      qed
    qed
  qed

  have 2:"tendsto s 0"
  unfolding s_def tendsto_def
  proof
    fix ε
    show "0 < ε ⟶ (∃N. ∀n≥N. dist ((p - 1) / real n) 0 < ε)"
    proof
      assume "0 < ε"

      define K where "K = p * 1 / ε"
    
      obtain N where N_prop: "real N > K"
        using reals_Archimedean2 by blast

      show "∃N. ∀n≥N. dist ((p - 1) / real n) 0 < ε"
      proof (rule_tac x="N" in exI)
        show "∀n≥N. dist ((p - 1) / real n) 0 < ε"
        proof
          fix n
          show "N ≤ n ⟶ dist ((p - 1) / real n) 0 < ε"
          proof
            assume "N ≤ n"
            with N_prop K_def have n0:"0 < n" (* sledgehammer *)
              by (smt (verit, ccfv_SIG) ‹0 < ε› assms bot_nat_0.not_eq_extremum divide_le_0_iff le_zero_eq of_nat_0)
            from ‹N ≤ n› N_prop have "K < n" by simp
            then have "p * 1 / ε < n" by (auto simp add: K_def)
            then have "p < n * ε" by (simp add: ‹0 < ε› pos_divide_less_eq)
            then have "p - 1 < n * ε" by simp
            then have "(p - 1) / n < ε" using n0 (* sledgehammer *)
              by (smt (verit, ccfv_SIG) mult_imp_div_pos_less nonzero_mult_div_cancel_left of_nat_0_less_iff pos_divide_le_eq)
            then show "dist ((p - 1) / real n) 0 < ε" using assms n0 by auto
          qed
        qed
      qed
    qed
  qed

  have "tendsto x 0" using 1 2 by (auto simp add: tendsto_zero_aux)
  then have "tendsto (λn. p powr (1 / n) - 1) 0" by (simp add: x_def)
  then have "tendsto (λn. complex_of_real (p powr (1 / n) - 1)) 0"
    unfolding tendsto_def by (metis dist_of_real of_real_0)
  then have "tendsto (λn. 1 + complex_of_real (p powr (1 / real n) - 1)) (1 + 0)"
    using tendsto_inc[of "(λn. p powr (1 / real n) - 1)" 0 1] by auto
  then have "tendsto (λn. 1 + (p powr (1 / real n) - 1)) (1 + 0)"
    unfolding tendsto_def by (metis dist_add_cancel dist_of_real of_real_0)
  then show ?thesis by simp
qed

(* mi22059_Matija_Djordjevic_FORMULACIJA *)
lemma tendsto_root:
  fixes p :: "real"
  assumes "p>0"
  shows "tendsto (λn. p powr (1/(real n))) 1"
(* mi22164_Lazar_Nikolic_DOKAZ *)
proof (cases "p < 1")
  case True
  define q where "q = 1/p"
  have "q > 1" using True q_def by (simp add: assms)
  then have q_tendsto_1:"tendsto (λn. q powr (1/n)) 1" by (simp add: tendsto_root_one)

  have "tendsto (λn. 1 / (p powr (1/ real n))) 1"
    using q_tendsto_1 unfolding tendsto_def by (simp add: powr_divide q_def)
  then have 1:"tendsto (λn. 1 / complex_of_real (p powr (1/ real n))) 1"
    unfolding tendsto_def by (metis dist_of_real of_real_divide of_real_eq_1_iff)

  have 2:"∀n. 1 / p powr (1 / real n) ≠ 0" using assms by simp

  from 1 2 have "tendsto (λn. complex_of_real (p powr (1/real n))) 1" 
    using tendsto_inverse[of "(λn. 1 / (p powr (1/ real n)))" 1] by simp

  then show "tendsto (λn. p powr (1/real n)) 1"
    unfolding tendsto_def by (metis dist_of_real of_real_eq_1_iff)
next
  case False
  show ?thesis
  proof (cases "p > 1")
    case True
    then show ?thesis by (simp add: tendsto_root_one)
  next
    case False
    have "p = 1" using ‹¬ p < 1› ‹¬ p > 1› by simp
    then show ?thesis unfolding tendsto_def by simp
  qed
qed

(* mi22164_Lazar_Nikolic_FORMULACIJA *)
lemma tendsto_nth_root:
  shows "tendsto (λ n. n powr (1/n)) 1"
(* mi22164_Lazar_Nikolic_DOKAZ *)
proof -
  define x :: "real sequence"
    where "x = (λn. n powr (1 / n) - 1)"

  define s :: "real sequence"
    where "s = (λn. (2 / (n - 1)) powr (1/2))"

  have 1:"∃N. ∀n≥N. 0 ≤ x n ∧ x n ≤ s n"
  proof (rule_tac x=2 in exI)
    show "∀n≥2. 0 ≤ x n ∧ x n ≤ s n"
    proof
      fix n
      show "2 ≤ n ⟶ 0 ≤ x n ∧ x n ≤ s n"
      proof
        assume "2 ≤ n"

        have l: "0 ≤ x n" using x_def ‹2 ≤ n› ge_one_powr_ge_zero by force

        from x_def have "x n = n powr (1/n) - 1" by simp
        then have "x n + 1 = n powr (1/n)" by simp
        then have "(x n + 1) powr n = (n powr (1/n)) powr n" by simp
        then have "(x n + 1) powr n = n powr (1/n * n)"
          using powr_powr[of n "1/n" n] by simp
        then have 1:"(x n + 1) powr n = n" by simp

        have 2: "(x n + 1) powr n ≥ ((n * (n - 1)) / 2) * (x n) powr 2"
        proof -
          have 1:"(x n + 1) powr n = (1 + x n) ^ n"
            using ‹2 ≤ n› (* sledgehammer *)
            by (metis ‹x n + 1 = real n powr (1 / real n)› add.commute bot_nat_0.extremum 
                le_antisym numeral_le_one_iff powr_ge_zero powr_realpow' semiring_norm(69))

          have "(1 + x n) ^ n = (x n + 1) ^ n" by argo
          also have "... = (∑k≤n. real (n choose k) * x n ^ k)" 
            using binomial_ring[of "x n" 1 n] by simp
          finally have 2:"(1 + x n) ^ n ≥ n * (n - 1) / 2 * (x n) ^ 2"
            using ‹2 ≤ n› ‹0 ≤ x n› sorry (* potrebna pomoc *)

          from 1 2 have "(x n + 1) powr n ≥ n * (n - 1) / 2 * (x n) ^ 2" by simp
          then have "(x n + 1) powr n ≥ n * (n - 1) / 2 * (x n) powr 2" (* sledgehammer *)
            by (metis abs_mult_self_eq one_add_one power2_eq_square powr_mult_base' powr_one')
          then show ?thesis by simp
        qed

        from 1 2 have "((n * (n - 1)) / 2) * (x n) powr 2 ≤ n" by simp
        then have "(n - 1) * (x n) powr 2 ≤ 2" using ‹2 ≤ n› by simp
        then have "(x n) powr 2 ≤ 2 / (n - 1)" 
          using ‹2 ≤ n› divide_right_mono[of "(n - 1) * (x n) powr 2" 2 "n - 1"] by simp
        then have "((x n) powr 2) powr (1 / 2) ≤ (2 / (n - 1)) powr (1 / 2)"
          using powr_mono2[of "1/2" "(x n) powr 2" "2 / (n - 1)"] by simp
        then have "x n ≤ (2 / (n - 1)) powr (1 / 2)"
          using powr_powr[of "x n" 2 "1/2"] by simp
        then have r:"x n ≤ s n" using s_def ‹2 ≤ n› by simp

        from l r show "0 ≤ x n ∧ x n ≤ s n" by simp
      qed
    qed
  qed

  have 2:"tendsto s 0"
    unfolding tendsto_def s_def
  proof
    fix ε
    show "0 < ε ⟶ (∃N. ∀n≥N. dist ((2 / (real n - 1)) powr (1 / 2)) 0 < ε)"
    proof
      assume "0 < ε"

      define K where "K = 2 / ε powr 2 + 1"
    
      obtain N where N_prop: "real N > K"
        using reals_Archimedean2 by blast

      show "∃N. ∀n≥N. dist ((2 / (real n - 1)) powr (1 / 2)) 0 < ε"
      proof (rule_tac x=N in exI)
        show "∀n≥N. dist ((2 / (real n - 1)) powr (1 / 2)) 0 < ε"
        proof
          fix n
          show "N ≤ n ⟶ dist ((2 / (real n - 1)) powr (1 / 2)) 0 < ε"
          proof
            assume "N ≤ n"

            with N_prop K_def have "n > 2 / ε powr 2 + 1" by simp
            then have "n - 1 > 2 / ε powr 2" by simp
            then have "(n - 1) / 2 > 1 / ε powr 2" by simp
            then have "1 / ε powr 2 < (n - 1) / 2" by simp
            then have "((n - 1) / 2) powr -1 < (1 / ε powr 2) powr -1"
              using powr_less_mono2_neg[of "-1" "1 / ε powr 2" "(n - 1) / 2"] ‹0 < ε› by auto
            then have "2 / (n - 1) < ε powr 2" by auto
            then have "(2 / (n - 1)) powr (1/2) < (ε powr 2) powr (1/2)"
              using powr_less_mono2[of "1/2" "2 / (n - 1)" "ε powr 2"] by auto
            then have "(2 / (n - 1)) powr (1/2) < ε" 
              using powr_powr[of ε 2 "1/2"] (* sledgehammer *)
              using ‹(ε powr 2) powr (1 / 2) = ε powr (2 * (1 / 2))›
              ‹(2 / real (n - 1)) powr (1 / 2) < (ε powr 2) powr (1 / 2)› ‹0 < ε› by auto
            then have "(2 / (real n - 1)) powr (1 / 2) < ε" (* sledgehammer *)
              by (smt (verit) ‹2 / ε powr 2 < real (n - 1)› divide_less_0_iff of_nat_1 of_nat_diff_if powr_ge_zero)
            then show "dist ((2 / (real n - 1)) powr (1 / 2)) 0 < ε" by auto
          qed
        qed
      qed
    qed
  qed

  have "tendsto x 0" using 1 2 by (auto simp add: tendsto_zero_aux)
  then have "tendsto (λn. n powr (1 / n) - 1) 0" using x_def by auto
  then have "tendsto (λn. complex_of_real (n powr (1 / n)) - 1) 0"
    unfolding tendsto_def (* sledgehammer *)
    by (metis (no_types, opaque_lifting) dist_of_real of_real_diff of_real_eq_0_iff of_real_eq_1_iff)
  then have "tendsto (λn. complex_of_real (n powr (1 / n))) 1"
    using tendsto_inc[of "(λn. complex_of_real (n powr (1 / n)) - 1)" 0 1] by auto
  then have "tendsto (λn. (n powr (1 / n))) 1"
    unfolding tendsto_def (* sledgehammer *)
    by (metis dist_of_real of_real_eq_1_iff)
  then show ?thesis by simp
qed

(* mi22164_Lazar_Nikolic_FORMULACIJA *)
lemma tendsto_npow_div_geom:
  fixes α :: real
  assumes "p > 0"
  shows "tendsto (λ n. (n powr α) / ((1 + p) powr n)) 0"
(* mi22164_Lazar_Nikolic_DOKAZ *)
proof -
  obtain k'::"nat" where k'_prop:"k' > α"
    using reals_Archimedean2 by blast

  define k :: "nat" where "k = max k' 1"

  from k'_prop k_def have "k > α" by simp
  from k'_prop k_def have "k > 0" by simp

  define N where "N = 2*k + 1"
  then have "N > 2*k" by simp
  with ‹0 < k› have "0 < N" by simp
  then have "0 < N powr α" by simp

  define x :: "real sequence" 
    where "x = (λ n. (n powr α) / ((1 + p) powr n))"

  define s :: "real sequence"
    where "s = (λ n. n powr (α - k) * ((2 powr k) * fact k) / (p powr k))"

  have 1:"∃N. ∀n≥N. 0 ≤ x n ∧ x n ≤ s n"
  proof (rule_tac x=N in exI)
    show "∀n≥N. 0 ≤ x n ∧ x n ≤ s n"
    proof (intro allI impI)
      fix n
      assume "N ≤ n"

      with ‹2*k < N› have "2*k < n" by simp
      with ‹0 < k› have "0 < n" by simp
      then have "0 < n powr α" by simp

      have l: "0 ≤ x n" using x_def by simp

      have r: "x n ≤ s n"
      proof -
        have powr_exp: "(1 + p) powr n = (1 + p) ^ n"
          using assms powr_realpow by auto
      
        have "(1 + p) ^ n = (p + 1) ^ n" by argo
        also have "... = (∑k≤n. real (n choose k) * p ^ k)"
          using binomial_ring[of p 1 n] by simp
        finally have binomial_eq:"(1 + p) ^ n = (∑k≤n. real (n choose k) * p ^ k)" .
      
        (* potrebna pomoc *)
        have binomial_le: "real (n choose k) * p ^ k < (∑k≤n. real (n choose k) * p ^ k)"
          using ‹2*k < n› ‹0 < p› sorry
      
        (* potrebna pomoc, ne razumem ovaj korak *)
        have 222:"(n^k * p^k) / (2^k * fact k) < real (n choose k) * p ^ k" sorry
      
        have "0 < (n^k * p^k) / (2^k * fact k)" using assms ‹2*k < n› ‹0 < p› ‹0 < k› by auto
      
        have "n ^ k = n powr k" by (simp add: ‹0 < n› powr_realpow)
        have alpha_div: "n powr α * ((2^k * fact k) / (n powr k * p^k)) = n powr (α - k) * (2^k * fact k) / p^k"
          by (simp add: powr_diff)

        from binomial_eq binomial_le have "real (n choose k) * p ^ k < (1 + p) ^ n" by simp
        with 222 have "(n^k * p^k) / (2^k * fact k) < (1 + p) ^ n" by simp
        then have "((1 + p) ^ n) powr -1 < ((n^k * p^k) / (2^k * fact k)) powr -1"
          using powr_less_mono2_neg[of "-1" "(n^k * p^k) / (2^k * fact k)" "(1 + p) ^ n"]
          ‹0 < (n^k * p^k) / (2^k * fact k)› by simp
        then have "1 / ((1 + p) ^ n) < 1 / ((n^k * p^k) / (2^k * fact k))" (* sledgehammer *)
          using ‹0 < real (n ^ k) * p ^ k / (2 ^ k * fact k)› ‹real (n ^ k) * p ^ k / (2 ^ k * fact k) < (1 + p) ^ n› powr_neg_one
          by fastforce
        then have "1 / ((1 + p) ^ n) < (2^k * fact k) / (n^k * p^k)" by simp
        then have "n powr α * (1 / ((1 + p) ^ n)) < n powr α * ((2^k * fact k) / (n^k * p^k))" 
          using ‹0 < n powr α› mult_strict_left_mono[of "1 / ((1 + p) ^ n)" "(2^k * fact k) / (n^k * p^k)" "n powr α"]
          by simp
        then have "n powr α / ((1 + p) ^ n) < (n powr α * (2^k * fact k)) / (n powr k * p^k)"
          using ‹n^k = n powr k› by simp
        with alpha_div have "n powr α / ((1 + p) ^ n) < n powr (α - k) * (2^k * fact k) / p^k"
          by simp
        then have "n powr α / ((1 + p) powr n) < n powr (α - k) * (2 powr k * fact k) / p powr k"
          using powr_exp by (simp add: assms powr_realpow)
        then show ?thesis using x_def s_def by simp
      qed

      from l r show "0 ≤ x n ∧ x n ≤ s n" by simp
    qed
  qed

  then have 2: "tendsto s 0"
  proof - 
    define sn :: "real sequence"
      where "sn = (λ n. n powr (α - k))"
  
    define c where "c = ((2 powr k) * fact k) / (p powr k)"

    define sn_complex :: "complex sequence"
      where "sn_complex = (λ n. n powr (α - k))"

    have "tendsto sn 0"
    proof -
      define q where "q = - (α - k)"
      then have "0 < q"
        using ‹α < k› by simp
      then have "tendsto (λn. 1 / (n powr q)) 0"
 (* ovo bi radilo kad bi tendsto_npow_neg bio definisan preko tendsto ali iz nekog razloga nije *)
        using tendsto_npow_neg[of q] sorry

      have "sn = (λ n. n powr (α - k))" using sn_def .
      also have "... = (λn. inverse (n powr -(α - k)))"
        by (metis minus_diff_eq powr_minus)
      also have "... = (λn. 1 / (n powr - (α - k)))" by (auto simp add: inverse_eq_divide)
      also have "... = (λn. 1 / (n powr q))" using q_def by simp
      finally show ?thesis using ‹tendsto (λn. 1 / (n powr q)) 0› by simp
    qed
  
    have scale_eq: "(λn. c * sn n) = (λn. s n)"
      using s_def sn_def c_def by auto
    
    have sn_compl_eq: "sn = sn_complex" using sn_def sn_complex_def by auto
    have c_compl_eq: "c = complex_of_real c" using c_def by auto

    have scale_compl_eq:"(λn. complex_of_real c * sn_complex n) = (λn. c * sn n)"
      using sn_compl_eq c_compl_eq by auto

    from ‹tendsto sn 0› sn_compl_eq have "tendsto sn_complex 0" unfolding tendsto_def by auto

    have "tendsto (λn. complex_of_real c * sn_complex n) 0"
      using tendsto_scale[of sn_complex 0 c] ‹tendsto sn_complex 0› by simp
    have "tendsto (λn. c * sn n) 0" unfolding tendsto_def
    proof (intro allI impI)
      fix ε :: "real"
      assume "0 < ε"

      from ‹tendsto (λn. complex_of_real c * sn_complex n) 0›
      have "∀ε>0. ∃N. ∀n≥N. dist (complex_of_real c * sn_complex n) 0 < ε"
        unfolding tendsto_def by simp
      then have "∃N. ∀n≥N. dist (complex_of_real c * sn_complex n) 0 < ε"
        using ‹0 < ε› by simp
      then obtain N where N_prop:"∀n≥N. dist (complex_of_real c * sn_complex n) 0 < ε" by auto

      show "∃N. ∀n≥N. dist (c * sn n) 0 < ε"
      proof (rule_tac x=N in exI)
        show "∀n≥N. dist (c * sn n) 0 < ε"
        proof (intro allI impI)
          fix n
          assume "N ≤ n"

          with N_prop have "dist (complex_of_real c * sn_complex n) 0 < ε" by simp
          then show "dist (c * sn n) 0 < ε" (* sledgehammer *)
            by (metis dist_of_real of_real_0 scale_compl_eq)
        qed
      qed
    qed
    then show ?thesis using scale_eq by simp
  qed

  have "tendsto x 0" using 1 2 by (auto simp add: tendsto_zero_aux)
  then show ?thesis using x_def by auto
qed

(* mi22164_Lazar_Nikolic_POMOCNA *)
lemma tendsto_pow_lt_one_positive_aux:
  assumes "0 < x"
  assumes "(abs x) < 1"
  shows "tendsto (λ n. x powr n) 0"
(* mi22164_Lazar_Nikolic_DOKAZ *)
proof -

  thm tendsto_npow_div_geom[of "1 / x - 1" 0]
  from assms have "1 / x > 1" by simp
  then have 1:"tendsto (λn. real n powr 0 / (1 + (1 / x - 1)) powr real n) 0"
    using tendsto_npow_div_geom[of "1 / x - 1" 0] by simp

  have 2:"(λn. real n powr 0 / (1 + (1 / x - 1)) powr real n) = (λn. real n powr 0 / (1/x) powr real n)"
    by simp

  from 1 2 have pomoc:"tendsto (λn. real n powr 0 / (1/x) powr real n) 0" by simp
  show ?thesis
    unfolding tendsto_def
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"

    from pomoc have "∀ε>0. ∃N. ∀n≥N. dist (real n powr 0 / (1/x) powr real n) 0 < ε"
      unfolding tendsto_def by simp
    with ‹0 < ε› have "∃N. ∀n≥N. dist (real n powr 0 / (1/x) powr real n) 0 < ε" by simp
    then obtain N' where N'_prop:"∀n≥N'. dist (real n powr 0 / (1/x) powr real n) 0 < ε" by auto
    define N where "N = N' + 1"
    
    show "∃N. ∀n≥N. dist (x powr real n) 0 < ε"
    proof (rule_tac x=N in exI)
      show "∀n≥N. dist (x powr real n) 0 < ε"
      proof (intro allI impI)
        fix n
        assume n_def:"N ≤ n"

        from N_def n_def have ‹0 < n› by auto
        from N_def n_def have "N' ≤ n" by auto
        then have "dist (real n powr 0 / (1/x) powr real n) 0 < ε" using N'_prop by auto
        with ‹0 < n› have "dist (1 / (1/x) powr real n) 0 < ε" by simp
        then have "dist (1 / (1 / (x powr real n))) 0 < ε"
          by (simp add: powr_divide)
        with ‹0 < x› ‹0 < n› show "dist (x powr real n) 0 < ε" by auto
      qed
    qed
  qed
qed

(* mi22164_Lazar_Nikolic_FORMULACIJA *)
lemma tendsto_pow_lt_one:
  assumes "(abs x) < 1"
  shows "tendsto (λ n. x powr n) 0"
(* mislim da dokaz iz knjige ne moze da se primeni direktno u slucaju x < 0 *)
(* mozda nesto sa subseq_tendsto_sequence i moj gornji dokaz za x > 0 - lazar *)
  sorry

(* mi22164_Lazar_Nikolic_FORMULACIJA *)
definition partial_sums :: "'a::{metric_space, comm_monoid_add} sequence \<Rightarrow> 'a sequence" 
  where "partial_sums s = (\<lambda>n. (∑i<n. s i))"

(* mi22164_Lazar_Nikolic_FORMULACIJA *)
definition sums_to :: "'a::{metric_space, comm_monoid_add} sequence \<Rightarrow> 'a \<Rightarrow> bool" 
  where "sums_to s a \<longleftrightarrow> tendsto (partial_sums s) a"

(* mi22164_Lazar_Nikolic_FORMULACIJA *)
definition summable :: "'a::{metric_space, comm_monoid_add} sequence \<Rightarrow> bool"
  where "summable s \<longleftrightarrow> (\<exists>a. sums_to s a)"


(* mi23106_Jana_Nenic_POMOCNA *)
definition partial_sum :: "'a::{metric_space, comm_monoid_add} sequence 
    \<Rightarrow> nat \<Rightarrow> nat
     \<Rightarrow> 'a"
  where "partial_sum s n m = (∑i=n..<m. s i)"


(* mi23106_Jana_Nenic_FORMULACIJA *)
lemma summable_cauchy:  
  fixes s :: "'a::{metric_space, comm_monoid_add, ord,abs} sequence"
  assumes  "summable ( partial_sums s)"
  shows "\<forall> \<epsilon> > 0 .\<exists> N :: nat .
         \<forall> m \<ge> N. \<forall> n \<ge> m.
        (abs(partial_sum s n m) \<le> \<epsilon>)"
  sorry

(* mi23106_Jana_Nenic_FORMULACIJA *)
lemma summable_tendsto_zero:
  fixes  s :: "'a::{metric_space, comm_monoid_add, ord,abs} sequence"
  assumes  "summable (partial_sums s)"
  shows " tendsto s 0"
  sorry

(* mi23106_Jana_Nenic_FORMULACIJA *)
lemma summable_def_with_mono:
  fixes l :: "real sequence"
  assumes "\<forall> n. l n > 0"
  shows "summable (partial_sums l)\<longleftrightarrow> bounded (partial_sums l)" 
  sorry

(* mi23106_Jana_Nenic_FORMULACIJA *)
lemma summable_comparison_test1:
  fixes a :: "'a:: {metric_space, comm_monoid_add,zero,ord, abs} sequence"
  fixes c :: "'a::{metric_space, comm_monoid_add,zero,ord, abs} sequence"
  assumes "∃N. ∀n≥N. abs( a n) ≤ c n"
  and "summable (partial_sums c)"
shows "summable (partial_sums a)"
  sorry

(* mi23106_Jana_Nenic_FORMULACIJA *)
lemma summable_comparison_test2:
  fixes a :: "'a:: {metric_space, comm_monoid_add,zero,ord} sequence"
  fixes d :: "'a::{metric_space, comm_monoid_add,zero,ord} sequence"
  assumes "∃N. ∀n≥N. a n \<ge> d n \<and> d n \<ge> 0"
  and "\<not>(summable (partial_sums (d)))"
shows "\<not>(summable (partial_sums (a)))"
  sorry

(* mi23106_Jana_Nenic_FORMULACIJA *)
lemma summable_geometric:
 fixes p :: "real"
 shows " (p > 1 \<longrightarrow>
       summable (partial_sums (λn. 1/((real n) powr p))))
      \<and>
      (p < 1 \<longrightarrow> \<not> summable (partial_sums  (λn. 1/((real n) powr p))))"
  sorry

end
