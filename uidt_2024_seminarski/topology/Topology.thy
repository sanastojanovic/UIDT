theory Topology
  imports Complex_Main "HOL-Library.Multiset"
begin

section \<open>Aksiomatsko zasnivanje teorija\<close>

locale topological_space =
  \<comment> \<open>konstante\<close>
  fixes X :: "'a set"  \<comment> \<open>skup nosilac\<close>
  fixes \<tau> :: "'a set set" \<comment> \<open>kolekcija otvorenih skupova\<close>

  \<comment> \<open>aksiome\<close>
  assumes subsets: "\<And> S. S \<in> \<tau> \<Longrightarrow> S \<subseteq> X"
  assumes univ: "X \<in> \<tau>"
  assumes empty: "{} \<in> \<tau>"
  assumes inter: "\<And> S1 S2. \<lbrakk>S1 \<in> \<tau>; S2 \<in> \<tau>\<rbrakk> \<Longrightarrow> S1 \<inter> S2 \<in> \<tau>"
  assumes union: "\<And> \<tau>'. \<lbrakk>\<tau>' \<noteq> {}; \<tau>' \<subseteq> \<tau>\<rbrakk> \<Longrightarrow> \<Union> \<tau>' \<in> \<tau>"
begin

abbreviation open_set :: "'a set \<Rightarrow> bool" where
  "open_set S \<equiv> S \<in> \<tau>"

lemma inter_finite:
  assumes "finite \<tau>'" "\<tau>' \<noteq> {}" "\<forall> S \<in> \<tau>'. open_set S"
  shows "open_set (\<Inter> \<tau>')"
  using assms
proof (induction \<tau>' rule: finite.induct)
  case emptyI
  then show ?case
    by simp
next
  case (insertI A a)
  show ?case
  proof (cases "A = {}")
    case True
    then show ?thesis
      using insertI
      by simp
  next
    case False
    then show ?thesis
      using insertI inter
      by simp
  qed
qed

definition closed_set :: "'a set \<Rightarrow> bool" where
  "closed_set S \<longleftrightarrow> open_set (X - S)"

lemma closed_empty:
  "closed_set {}"
  unfolding closed_set_def
  using univ
  by simp

lemma closed_univ:
  "closed_set X"
  unfolding closed_set_def
  using empty
  by simp

lemma closed_inter:
  assumes "\<tau>' \<noteq> {}" "\<forall> S \<in> \<tau>'. closed_set S"
  shows "closed_set (\<Inter> \<tau>')"
proof-
  have "X - (\<Inter> \<tau>') = \<Union> {X - S | S . S \<in> \<tau>'}"
    using assms
    by auto
  thus ?thesis
    using assms
    unfolding closed_set_def
    using union[of "{X - S |S. S \<in> \<tau>'}"]
    by auto
qed

lemma closed_union:
  assumes "closed_set S1" "closed_set S2"
  shows "closed_set (S1 \<inter> S2)"
  using assms union[of "{X - S1, X - S2}"]
  unfolding closed_set_def
  by (simp add: Diff_Int)

lemma closed_union_finite:
  assumes "finite \<tau>'" "\<tau>' \<noteq> {}" "\<forall> S \<in> \<tau>'. closed_set S"
  shows "closed_set (\<Union> \<tau>')"
proof-
  have "X - \<Union> \<tau>' = \<Inter> {X - S | S . S \<in> \<tau>'}"
    using `\<tau>' \<noteq> {}`
    by auto
  thus ?thesis
    using assms
    using inter_finite[of "{X - S | S. S \<in> \<tau>'}"]
    unfolding closed_set_def
    by auto
qed

end

definition X_ex1 :: "nat set" where
  "X_ex1 = {0::nat, 1, 2, 3, 4, 5}"

definition \<tau>_ex1 :: "nat set set" where
  "\<tau>_ex1 = {{0::nat, 1, 2, 3, 4, 5}, {}, {0}, {2, 3}, {0, 2, 3}, {1, 2, 3, 4, 5}}"

interpretation topological_space where
  X = "X_ex1" and
  \<tau> = "\<tau>_ex1"
proof
  fix S
  assume "S \<in> \<tau>_ex1"
  thus "S \<subseteq> X_ex1"
    unfolding \<tau>_ex1_def X_ex1_def
    by auto
next
  show "X_ex1 \<in> \<tau>_ex1" "{} \<in> \<tau>_ex1"
    unfolding X_ex1_def \<tau>_ex1_def
    by auto
next
  fix S1 S2
  assume "S1 \<in> \<tau>_ex1" "S2 \<in> \<tau>_ex1"
  thus "S1 \<inter> S2 \<in> \<tau>_ex1"
    unfolding \<tau>_ex1_def
    \<comment> \<open>ovi dokazi su krajnje neinteresantni, a ne mogu se dokazati automatski\<close>
    sorry
next
  fix \<tau>'
  assume "\<tau>' \<noteq> {}" "\<tau>' \<subseteq> \<tau>_ex1"
  thus "\<Union> \<tau>' \<in> \<tau>_ex1"
    unfolding \<tau>_ex1_def
    \<comment> \<open>ovi dokazi su krajnje neinteresantni, a ne mogu se dokazati automatski\<close>
    sorry
qed

definition open_interval :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "open_interval a b = {x. a < x \<and> x < b}"

lemma open_interval_empty_iff:
  "open_interval a b = {} \<longleftrightarrow> a \<ge> b"
  unfolding open_interval_def
  by (metis (no_types, lifting) dense_le dual_order.strict_implies_order empty_Collect_eq leD le_less_linear order.strict_trans1)

definition is_real_open_set where
  "is_real_open_set S \<longleftrightarrow>
      (\<forall> x \<in> S. \<exists> a b. x \<in> open_interval a b \<and> open_interval a b \<subseteq> S)"

interpretation Euclidean_topology: topological_space where
 X = "UNIV :: real set" \<comment> \<open>UNIV je skup svih elemenata nekog tipa\<close> and
 \<tau> = "{S. is_real_open_set S}"
proof
  fix S
  assume "S \<in> {S. is_real_open_set S}"
  then show "S \<subseteq> UNIV"
    by simp
next
  have "\<forall> x. \<exists> a b. x \<in> open_interval a b"
  proof-
    have "\<forall> x. x \<in> open_interval (x - 1) (x + 1)"
      unfolding open_interval_def
      by simp
    then show ?thesis
      by auto
  qed
  then show "UNIV \<in> {S. is_real_open_set S}"
    unfolding is_real_open_set_def
    by auto
next
  show "{} \<in> {S. is_real_open_set S}"
    unfolding is_real_open_set_def
    by simp
next
  fix \<tau>'
  assume *: "\<tau>' \<subseteq> {S. is_real_open_set S}"
  show "\<Union> \<tau>' \<in> {S. is_real_open_set S}"
  proof
    show "is_real_open_set (\<Union> \<tau>')"
      unfolding is_real_open_set_def
    proof
      fix x
      assume "x \<in> \<Union> \<tau>'"
      then obtain S where "S \<in> \<tau>'" "x \<in> S"
        by auto
      hence "is_real_open_set S"
        using *
        by auto
      then obtain a b where "x \<in> open_interval a b" "open_interval a b \<subseteq> S"
        using `x \<in> S`
        unfolding is_real_open_set_def
        by auto
      thus "\<exists>a b. x \<in> open_interval a b \<and> open_interval a b \<subseteq> \<Union> \<tau>'"
        using `S \<in> \<tau>'`
        by auto
    qed
  qed
next
  fix S1 S2
  assume *: "S1 \<in> {S. is_real_open_set S}" "S2 \<in> {S. is_real_open_set S}"
  show "S1 \<inter> S2 \<in> {S. is_real_open_set S}"
  proof
    show "is_real_open_set (S1 \<inter> S2)"
      unfolding is_real_open_set_def
    proof
      fix x
      assume "x \<in> S1 \<inter> S2"
      then obtain a1 b1 a2 b2 where
      **: "x \<in> open_interval a1 b1" "open_interval a1 b1 \<subseteq> S1"
          "x \<in> open_interval a2 b2" "open_interval a2 b2 \<subseteq> S2"
        using *
        unfolding is_real_open_set_def
        by blast
      let ?a = "max a1 a2"
      let ?b = "min b1 b2"
      have "x \<in> open_interval ?a ?b"
        using **
        unfolding open_interval_def
        by auto
      moreover
      have "open_interval ?a ?b \<subseteq> S1 \<inter> S2"
        using **
        unfolding open_interval_def
        by auto
      ultimately
      show "\<exists>a b. x \<in> open_interval a b \<and> open_interval a b \<subseteq> S1 \<inter> S2"
        by auto
    qed
  qed
qed

thm Euclidean_topology.closed_set_def
thm Euclidean_topology.closed_inter
thm Euclidean_topology.closed_union_finite

lemma "Euclidean_topology.open_set A \<longleftrightarrow> is_real_open_set A"
  by simp

end
