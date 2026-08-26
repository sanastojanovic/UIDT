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
          have h2:"dist (xn n $ j) (x $ j) \<le>  dist (xn n) x"
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
  fixes pn :: "real_vector sequence"
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



(*mi20174_Nikola_Krstajic_FORMULACIJA*)
lemma compact_cauchy_tendsto:
  fixes pn :: "'a::metric_space sequence"
    and X :: "'a set"
  assumes "compact X"
    and "\<forall> n. pn n \<in> X"
    and "cauchy pn"
  shows "\<exists> p \<in> X. tendsto pn p"
(*mi20174_Nikola_Krstajic_DOKAZ*)
define En where "En = (\<lambda> N. {pn n | n. n \<ge>N})"
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
  (*Kn podskup od prostora  X*)

  (*prvo pokusavam da mi je En podskup od X*)
  have "En N \<subseteq> X"
    unfolding En_def using assms(2) by auto
  (*Kn podskup od prostora  X*)
  have "Kn N \<subseteq> X"
    sorry

  (*Kn zatvoren skup*)
  have "closed (Kn N)"
    sorry  
 (*svaki kompaktan*)
  show "compact (Kn N)"
    sorry
qed


(*mi20174_Nikola_Krstajic_FORMULACIJA*)
lemma cauchy_tendsto_real_vec:
  fixes xn :: "(real^'k)  sequence"
  assumes "cauchy xn"
  shows "\<exists> x. tendsto xn x " 
  sorry


(* mi20174_Nikola_Krstajic_FORMULACIJA *)
definition complete :: "'a::metric_space set \<Rightarrow> bool" where
  "complete X \<longleftrightarrow> (\<forall> pn. (\<forall>n. pn n \<in> X ) \<and> cauchy pn \<longrightarrow> (\<exists> p \<in> X. tendsto pn p))"


(* mi20174_Nikola_Krstajic_FORMULACIJA *)
lemma compact_metric_space_complete:
  fixes X :: "'a::metric_space set"
  assumes "compact X"
  shows "complete X"
  sorry

end
