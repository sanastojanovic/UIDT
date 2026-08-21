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

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_mult:
  fixes sn tn :: "complex sequence"
  assumes "tendsto sn s"
      and "tendsto tn t"
    shows "tendsto (\<lambda>n. sn n * tn n) (s * t)"
  sorry

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_inverse:
  fixes sn :: "complex sequence"
  assumes "tendsto sn s"
      and "\<forall>n. sn n \<noteq> 0"
      and "s \<noteq> 0"
    shows "tendsto (\<lambda>n. 1/sn n) (1/s)"
  sorry


(* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_real_vec:
  fixes xn :: "(real^'k) sequence"
    and x :: "real^'k"
    shows "tendsto xn x \<longleftrightarrow>
         (\<forall>j. tendsto (\<lambda>n. xn n $ j) (x $ j))"
  sorry

 (* mi22050_Lazar_Rajcic_FORMULACIJA *)
lemma tendsto_add_real_vec:
  fixes xn yn ::"(real^'k) sequence"
    and x y ::  "real^'k"
  assumes "tendsto xn x" and "tendsto yn y"
  shows "tendsto (\<lambda>n. xn n + yn n)  (x+y)"
  sorry

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

end
