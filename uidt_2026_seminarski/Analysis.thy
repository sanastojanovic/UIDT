theory Analysis
  imports Complex_Main
begin

section \<open>3.1 Definicije\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
type_synonym 'a sequence = "nat \<Rightarrow> 'a"

(* mi22062_Nenad_Pesic_FORMULACIJA *)
definition tendsto :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> 'a \<Rightarrow> bool" where
  "tendsto x a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (x n) a < \<epsilon>)"

(* mi22062_Nenad_Pesic_FORMULACIJA *)
definition bounded :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> bool" where
  "bounded x \<longleftrightarrow> (\<exists>p M. \<forall>n. dist (x n) p \<le> M)"

section \<open>Rudin 3.2 (b) -- Jedinstvenost granicne vrednosti\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma tendsto_common_index:
  fixes x :: "nat \<Rightarrow> 'a::metric_space"
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
  fixes x :: "nat \<Rightarrow> 'a::metric_space"
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
  fixes x :: "nat \<Rightarrow> 'a::metric_space"
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
  fixes x :: "nat \<Rightarrow> 'a::metric_space"
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
  fixes x :: "nat \<Rightarrow> 'a::metric_space"
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
  sorry

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_scale:
  fixes sn :: "complex sequence"
    and c :: "complex"
  assumes "tendsto sn s"
  shows "tendsto (\<lambda>n. c * sn n) (c * s)"
  sorry

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
  sorry

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma subseq_tendsto_sequence:
    fixes pn :: "'a::metric_space sequence"
  assumes "(\<forall>pni nk. subseq pn nk pni \<longrightarrow> tendsto pni p)"
    shows "tendsto pn p"
  sorry

(* mi19011_Dimitrije_Jovanovic_FORMULACIJA *)
lemma tendsto_sequence_subseq:
  fixes pn :: "'a::metric_space sequence"
  shows "tendsto pn p \<longleftrightarrow> (\<forall>pni nk. subseq pn nk pni \<longrightarrow> tendsto pni p)"
  sorry


end
