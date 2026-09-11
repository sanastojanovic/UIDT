theory Analysis
  imports Complex_Main "HOL-Analysis.Finite_Cartesian_Product"
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
  sorry

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

 (* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_mult_real_vec:
  fixes xn yn :: "(real^'k) sequence"
    and x y :: "real^'k"
  assumes  "tendsto xn x" and "tendsto yn y"
  shows "tendsto (\<lambda>n. xn n * yn n)  (x*y)"
sorry


 (* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_scale_real_vec:
  fixes xn ::  "(real^'k) sequence"
    and x :: "real^'k"
    and bn :: "real sequence"
    and b :: real
  assumes "tendsto xn x" and "tendsto bn b"
    shows "tendsto (\<lambda>n. bn n *s xn n) (b *s x)"
sorry



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
  defines "Ec \<equiv> closure E"
  shows "diam Ec = diam E"
  sorry


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
      unfolding Kn_def using closure_subset_closed (* by blast *)
      sorry
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

end