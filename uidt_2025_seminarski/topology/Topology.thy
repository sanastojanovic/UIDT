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

(* mi19439_Marko_Vuceljic_FORMULACIJA *)
abbreviation clopen :: "'a set \<Rightarrow> bool" where
  "clopen S \<equiv> open_set S \<and> closed_set S"

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

(* mi21207 Matija Stankovic FORMULACIJA*)
definition open_rectangle :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<times> real) set" where
  "open_rectangle a b c d = {(x, y). a < x \<and> x < b \<and> c < y \<and> y < d}"

(* mi21207 Matija Stankovic FORMULACIJA *)
definition open_n_dimensional_interval :: "('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) set" where
  "open_n_dimensional_interval a b = {x. \<forall>i. a i < x i \<and> x i < b i}"

(* mi21207 Matija Stankovic FORMULACIJA *)
definition left_half_open_interval :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "left_half_open_interval a b = {x. a < x \<and> x \<le> b}"


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

(* mi21061_Marko_Koprivica_FORMULACIJA *)
locale discrete_topological_space =
  fixes X :: "'a set" 
  fixes Pow_X :: "'a set set"
  assumes discrete_topology: "Pow_X = {Y. Y \<subseteq> X}"
begin

(* mi21061_Marko_Koprivica_FORMULACIJA *)
(* mi21061_Marko_Koprivica_DOKAZ *)
lemma is_topological_space: "topological_space X Pow_X"
proof
  show "\<And>S. S \<in> Pow_X \<Longrightarrow> S \<subseteq> X"
    by (simp add: discrete_topology)
next
  show "X \<in> Pow_X"
    by (simp add: discrete_topology)
next
  show "{} \<in> Pow_X"
    by (simp add: discrete_topology)
next
  fix S1 S2
  assume "S1 \<in> Pow_X" "S2 \<in> Pow_X"
  then have "S1 \<subseteq> X \<and> S2 \<subseteq> X"
    using discrete_topology
    by auto
  then have "S1 \<inter> S2 \<subseteq> X"
    by auto
  then show "S1 \<inter> S2 \<in> Pow_X"
    using discrete_topology
    by simp
next
  fix "\<tau>'"
  assume "\<tau>' \<noteq> {}" "\<tau>' \<subseteq> Pow_X"
  then have "\<Union> \<tau>' \<subseteq> X"
    using discrete_topology
    by auto
  then show "\<Union> \<tau>' \<in> Pow_X"
    by (simp add: discrete_topology)
qed

end

(* mi21061_Marko_Koprivica_FORMULACIJA *)
locale indiscrete_topological_space = 
  fixes X :: "'a set"
  fixes \<tau> :: "'a set set"
  assumes indiscrete_topology: "\<tau> = {X, {}}"
begin

(* mi21061_Marko_Koprivica_FORMULACIJA *)
(* mi21061_Marko_Koprivica_DOKAZ *)
lemma is_topological_space: "topological_space X \<tau>"
proof
  show "\<And>S. S \<in> \<tau> \<Longrightarrow> S \<subseteq> X"
    by (auto simp add: indiscrete_topology)
next
  show "X \<in> \<tau>"
    by (simp add: indiscrete_topology)
next
  show "{} \<in> \<tau>"
    by (simp add: indiscrete_topology)
next
  fix S1 S2
  assume "S1 \<in> \<tau>" "S2 \<in> \<tau>"
  then have "(S1 = X \<or> S1 = {}) \<and> (S2 = {} \<or> S2 \<subseteq> X)"
    using indiscrete_topology
    by auto
  then have "(S1 = X \<and> S2 = {}) \<or> (S1 = X \<and> S2 = X) \<or> (S1 = {} \<and> S2 = {}) \<or> (S1 = {} \<and> S2 = X)"
    using \<open>S2 \<in> \<tau>\<close> indiscrete_topology 
    by auto
  then have "(S1 \<inter> S2 = {}) \<or> (S1 \<inter> S2 = X)"
    by auto
  then show "S1 \<inter> S2 \<in> \<tau>"
    using indiscrete_topology
    by auto
next
  fix "\<tau>'"
  assume "\<tau>' \<noteq> {}" "\<tau>' \<subseteq> \<tau>"
  then have "\<tau>' = {X} \<or> \<tau>' = {X, {}} \<or> \<tau>' = {{}}"
    using indiscrete_topology subset_insert_iff 
    by auto
  then have "\<Union> \<tau>' = X \<or> \<Union> \<tau>' = {}"
    by auto
  then show "\<Union> \<tau>' \<in> \<tau>"
    by (simp add: indiscrete_topology)
qed
sublocale topological_space
  by (rule is_topological_space)
end

(* mi21061_Marko_Koprivica_FORMULACIJA *)
(* mi21061_Marko_Koprivica_DOKAZ *)
lemma Ex_1_1_8:
  assumes "topological_space {a, b, c} \<tau>"
  and "{a} \<in> \<tau>" 
  and "{b} \<in> \<tau>" 
  and "{c} \<in> \<tau>"
shows "discrete_topological_space {a, b, c} \<tau>"
  using assms
proof-
  have "\<tau> = {x. x \<subseteq> {a, b, c}}"
  proof
    show "\<tau> \<subseteq> {x. x \<subseteq> {a, b, c}}"
      by (metis assms(1) mem_Collect_eq subsetI topological_space_def)
  next
    show "{x. x \<subseteq> {a, b, c}} \<subseteq> \<tau>"
    proof
      fix x
      assume "x \<in> {x. x \<subseteq> {a, b, c}}"
      then have "x \<subseteq> {a, b, c}"
        by simp
      then have "x = {} \<or> x = {a} \<or> x = {b} \<or> x = {c} \<or> x = {a, b} \<or> x = {a, c} \<or> 
                x = {b, c} \<or> x = {a, b, c}"
        by (smt (verit, best) empty_subsetI insert_absorb insert_commute insert_mono subset_antisym subset_insert subset_singletonD)
      then show "x \<in> \<tau>"
      proof-
        have "x = {} \<Longrightarrow> x \<in> \<tau>"
          using assms(1) topological_space.empty 
          by auto
        moreover have "x = {a} \<Longrightarrow> x \<in> \<tau>"
          using assms(2)
          by simp
        moreover have "x = {b} \<Longrightarrow> x \<in> \<tau>"
          using assms(3)
          by simp
        moreover have "x = {c} \<Longrightarrow> x \<in> \<tau>"
          using assms(4)
          by simp
        moreover have "x = {a, b} \<Longrightarrow> x \<in> \<tau>"
        proof-
          assume "x = {a, b}"
          then have "x = {a} \<union> {b}"
            by auto
          moreover have "{a} \<union> {b} \<in> \<tau>"
            using assms(1) assms(2) assms(3) topological_space.union[of "{a, b, c}" "\<tau>" "{{a}, {b}}"]
            by simp
          ultimately show ?thesis
            by auto
        qed
        moreover have "x = {a, c} \<Longrightarrow> x \<in> \<tau>"
        proof-
          assume "x = {a, c}"
          then have "x = {a} \<union> {c}"
            by auto
          moreover have "{a} \<union> {c} \<in> \<tau>"
            using assms(1) assms(2) assms(4) topological_space.union[of "{a, b, c}" "\<tau>" "{{a}, {c}}"]
            by simp
          ultimately show ?thesis
            by auto
        qed
        moreover have "x = {b, c} \<Longrightarrow> x \<in> \<tau>"
        proof-
          assume "x = {b, c}"
          then have "x = {b} \<union> {c}"
            by auto
          moreover have "{b} \<union> {c} \<in> \<tau>"
            using assms(1) assms(3) assms(4) topological_space.union[of "{a, b, c}" "\<tau>" "{{b}, {c}}"]
            by simp
          ultimately show ?thesis
            by auto
        qed
        moreover have "x = {a, b, c} \<Longrightarrow> x \<in> \<tau>"
          using assms(1) topological_space.univ 
          by auto
        ultimately show ?thesis
          using \<open>x = {} \<or> x = {a} \<or> x = {b} \<or> x = {c} \<or> x = {a, b} \<or> x = {a, c} \<or> x = {b, c} \<or> x = {a, b, c}\<close> 
          by fastforce
      qed
    qed
  qed
  then show ?thesis
    by (simp add: discrete_topological_space_def)
qed

(* mi21061_Marko_Koprivica_FORMULACIJA *)
(* mi21061_Marko_Koprivica_DOKAZ *)
lemma Prop_1_1_9:
  assumes "topological_space X \<tau>"
    and "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> \<tau>"
  shows "discrete_topological_space X \<tau>"
proof-
  have "\<tau> = {Y. Y \<subseteq> X}"
  proof
    show "\<tau> \<subseteq> {Y. Y \<subseteq> X}"
      by (metis CollectI assms(1) subsetI topological_space_def)
  next
    show "{Y. Y \<subseteq> X} \<subseteq> \<tau>"
    proof
      fix Z
      assume "Z \<in> {Y. Y \<subseteq> X}"
      then have "Z \<subseteq> X"
        by simp
      then have "Z = \<Union> {{x} | x. x \<in> Z}"
        by (simp add: Setcompr_eq_image)
      then show "Z \<in> \<tau>"
      proof-
        assume "Z = \<Union> {{x} |x. x \<in> Z}"
        then have "Z = \<Union> {{x} | x. x \<in> Z \<and> x \<in> X}"
          using \<open>Z \<subseteq> X\<close>
          by auto
        have " {{x} | x. x \<in> Z \<and> x \<in> X} \<subseteq> \<tau>"
          using assms(2)
          by auto
        have "\<Union> {{x} | x. x \<in> Z \<and> x \<in> X} \<in> \<tau>"
          using assms(1) topological_space.union[of "X" "\<tau>" "{Z}"] 
                \<open>{{x} | x. x \<in> Z \<and> x \<in> X} \<subseteq> \<tau>\<close>
          by (metis (no_types, lifting) Union_empty topological_space.empty topological_space.union)
        then show ?thesis
          using \<open>Z = \<Union> {{x} | x. x \<in> Z \<and> x \<in> X}\<close>
          by simp
      qed
    qed
  qed
  then show ?thesis
    by (simp add: discrete_topological_space_def)
qed


(* mi19439_Marko_Vuceljic_FORMULACIJA *)
context topological_space
begin

(* mi19439_Marko_Vuceljic_FORMULACIJA *)
(* mi19439_Marko_Vuceljic_DOKAZ *)
lemma open_set_X:
  shows "open_set X"
  by (simp add: local.univ)

(* mi19439_Marko_Vuceljic_FORMULACIJA *)
(* mi19439_Marko_Vuceljic_DOKAZ *)
lemma open_set_empty:
  shows "open_set {}"
  by (simp add: local.empty)


(* mi19439_Marko_Vuceljic_FORMULACIJA *)
(* mi19439_Marko_Vuceljic_DOKAZ *)
lemma clopen_X:
  shows "clopen X"
  by (simp add: local.closed_univ local.univ)

(* mi19439_Marko_Vuceljic_FORMULACIJA *)
(* mi19439_Marko_Vuceljic_DOKAZ *)
lemma clopen_empty:
  shows "clopen {}"
  by (simp add: local.closed_empty open_set_empty)

(*mi21207 Matija Stankovic FORMULACIJA*)
definition is_basis :: "'a set set \<Rightarrow> bool" where 
  "is_basis B \<longleftrightarrow> (\<forall>B' \<in> B. open_set B') \<and> (\<forall>U. open_set U \<longrightarrow> (\<exists>C \<subseteq> B. U = \<Union>C) )"

end

(* mi21207 Matija Stankovic FORMULACIJA *)
lemma Prop_2_2_8:
  fixes X :: "'a set" and B :: "'a set set"
  assumes "X \<noteq> {}"
  shows
    "((\<Union> B = X) \<and>
      (\<forall>B1\<in>B. \<forall>B2\<in>B. \<exists>C \<subseteq> B. B1 \<inter> B2 = \<Union> C))
     \<longleftrightarrow>
     (\<exists>\<tau>. topological_space X \<tau> \<and>
          (\<forall>U\<in>\<tau>. \<exists>C \<subseteq> B. U = \<Union> C))"
  sorry




context discrete_topological_space
begin
sublocale topological_space X Pow_X
  by (auto intro!: topological_space.intro simp: discrete_topology)

(* mi19439_Marko_Vuceljic_FORMULACIJA *)
(* mi19439_Marko_Vuceljic_DOKAZ *)

lemma all_subsets_clopen_discrete:
  assumes "S \<subseteq> X"
  shows "clopen S"
  using assms discrete_topology local.closed_set_def by auto
end



(* mi19439_Marko_Vuceljic_FORMULACIJA *)
(* mi19439_Marko_Vuceljic_DOKAZ *)

lemma Ex_1_2_3:
  assumes "X = {n::nat. n > 0}"
      and "\<tau> = {{}} \<union> {S. S \<subseteq> X \<and> finite (X - S)}"
  shows "topological_space X \<tau>"
proof
  show " \<And>S. S \<in> \<tau> \<Longrightarrow> S \<subseteq> X"
  using assms(2) by blast
next
  show"X \<in> \<tau>" 
  using assms(2) by auto
next 
  show" {} \<in> \<tau>"
    using assms(2) by simp
next
  fix S1 S2 assume "S1 \<in> \<tau>" "S2 \<in> \<tau>"
  then show "S1 \<inter> S2 \<in> \<tau>"
    by (cases "S1 = {}"; cases "S2 = {}")
       (auto simp: assms(2) Diff_Int)
next
  show "\<And>\<tau>'. \<lbrakk>\<tau>' \<noteq> {}; \<tau>' \<subseteq> \<tau>\<rbrakk> \<Longrightarrow> \<Union> \<tau>' \<in> \<tau>"
  proof -
    fix \<tau>' assume nz: "\<tau>' \<noteq> {}" and sub: "\<tau>' \<subseteq> \<tau>"
    show "\<Union> \<tau>' \<in> \<tau>"
    proof (cases "\<Union> \<tau>' = {}")
      case True
      then show ?thesis by (simp add: assms(2))
    next
      case False
      then obtain x U where "U \<in> \<tau>'" and "x \<in> U"
        by auto
      hence "U \<in> \<tau>" and "U \<noteq> {}"
        using sub by auto
      then have "U \<subseteq> X" and "finite (X - U)"
        by (simp_all add: assms(2))
      have "X - \<Union> \<tau>' \<subseteq> X - U"
        using \<open>U \<in> \<tau>'\<close> by auto
      hence "finite (X - \<Union> \<tau>')"
        using \<open>finite (X - U)\<close> finite_subset by blast
      moreover have "\<Union> \<tau>' \<subseteq> X"
        using sub by (auto simp: assms(2))
      ultimately show ?thesis
        by (simp add: assms(2))
    qed
  qed
qed

(* mi19201_Aleksandar_Urosevic_FORMULACIJA *)
(* mi21002_Stasa_Djordjevic_DOKAZ *)
context indiscrete_topological_space
begin
lemma subsets_clopen_indiscrete:
  assumes "S \<subseteq> X"
  shows "clopen S \<longleftrightarrow> (S = X \<or> S = {})"
  proof
  assume "clopen S" 
    then have "open_set S \<and> closed_set S"  by simp
    then have "open_set S" by simp
    then have "S \<in> \<tau>" by simp
    then show "S = X \<or> S = {}" by (auto simp add: indiscrete_topology)
  next
    assume "S = X \<or> S = {}" 
    then show "clopen S"
    proof
      assume "S=X"
      then show "clopen S" using clopen_X by simp 
    next
      assume "S = {}" 
      then have "S \<in> \<tau>" by (auto simp add: indiscrete_topology)
      then have "open_set S" by simp
      moreover
      from `S = {}` have "closed_set S" by (auto simp add: closed_empty)
      ultimately 
      show "clopen S" by simp
    qed
qed
end

(* mi19201_Aleksandar_Urosevic_FORMULACIJA *)
locale cofinite_topological_space =
  fixes X :: "'a set"
  fixes \<tau> :: "'a set set"
  assumes x_is_nonempty: "X \<noteq> {}"
  assumes cofinite_topology: "\<tau> = { U. U \<subseteq> X \<and> (U = {} \<or> finite (X - U)) }"
begin
lemma x_in_cofinite_topology:
  "X \<in> \<tau>" by (simp add: cofinite_topology)

(* mi21002_Stasa_Djordjevic_DOKAZ *)
lemma is_topological_space: "topological_space X \<tau>"
proof
  show " \<And>S. S \<in> \<tau> \<Longrightarrow> S \<subseteq> X" 
    by (simp add:cofinite_topology)
next
  show " X \<in> \<tau>"
    by (simp add:cofinite_topology)
next
  show "{} \<in> \<tau>" 
    by (simp add:cofinite_topology)
next
  fix S1 S2
  assume "S1 \<in> \<tau>" "S2 \<in> \<tau>"
  then have "S1 \<subseteq> X \<and> S2 \<subseteq> X" by (simp add:cofinite_topology)
  then have "S1 \<inter> S2 \<subseteq> X" by (auto simp add:cofinite_topology)
  with \<open>S1 \<in> \<tau>\<close> have a1:"S1 = {} \<or> finite (X-S1)" by (simp add:cofinite_topology)
  with \<open>S2 \<in> \<tau>\<close> have a2:"S2 = {} \<or> finite (X-S2)" by (simp add:cofinite_topology)
  then show "S1 \<inter> S2 \<in> \<tau>" 
  proof (cases "S1 = {} \<or> S2 = {}")
    case True
    then show ?thesis by (auto simp add:cofinite_topology)
  next
    case False
    then have "finite (X-S1)" "finite (X-S2)" using a1 a2 by  (auto simp add:cofinite_topology)
    then have *:"finite ((X-S1) \<union> (X-S2))" by (auto simp add:cofinite_topology)
    have "(X-S1) \<union> (X-S2) = X-(S1 \<inter> S2)" by auto
    with * have "finite (X-(S1\<inter>S2))" by auto
    then show ?thesis using \<open>S1 \<inter> S2 \<subseteq> X\<close> by (auto simp add:cofinite_topology)
  qed
next
  fix "\<tau>'" 
  assume "\<tau>' \<noteq> {}" "\<tau>' \<subseteq> \<tau>" 
  show "( \<Union> \<tau>') \<in> \<tau> "
  proof (cases "\<Union> \<tau>' = {}")
    case True
    then show ?thesis by (auto simp add:cofinite_topology)
  next
    case False
    then obtain A where "A \<in> \<tau>'" "A \<noteq> {}" by auto 
    with \<open>\<tau>' \<subseteq> \<tau>\<close>  have "A \<in> \<tau>" "finite (X-A)" by (auto simp add:cofinite_topology)
    then have "X - (\<Union> \<tau>') \<subseteq> (X - A)" using \<open>A \<in> \<tau>'\<close> by blast
    then have f1:"finite (X - (\<Union> \<tau>'))"  by (simp add: \<open>finite (X - A)\<close> finite_subset)
    with \<open>\<tau>' \<subseteq> \<tau>\<close> have "\<Union> \<tau>' \<subseteq> X"  by (auto simp add:cofinite_topology)
    with f1 show ?thesis by (auto simp add:cofinite_topology)
  qed
qed
sublocale topological_space
  by (rule is_topological_space)
end

(* mi19201_Aleksandar_Urosevic_FORMULACIJA *)
(* mi21002_Stasa_Djordjevic_DOKAZ *)
context cofinite_topological_space
begin
lemma Ex_1_3_3:
  fixes A B C :: "'a set"
  assumes "A \<subseteq> X"
  assumes "B \<subseteq> X"
  assumes "C \<subseteq> X"
  assumes "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> clopen A \<and> clopen B \<and> clopen C"
  shows "finite X"
proof-
  have "clopen A" "clopen B" "clopen C" using assms(4) by auto
  have "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" using assms(4) by auto
  then have "(A \<noteq> {} \<and> A \<noteq> X) \<or> (B \<noteq> {} \<and> B \<noteq> X) \<or> (C \<noteq> {} \<and> C \<noteq> X)"  by auto
  then have "\<exists> S . S \<subseteq> X \<and> S \<noteq> {} \<and> S \<noteq> X \<and> clopen S" using \<open>local.clopen C\<close> assms(3) by blast
  then obtain S where " S \<subseteq> X" "S \<noteq> {}" "S \<noteq> X" "clopen S" by auto
  with \<open>clopen S\<close> have "closed_set S" by auto
  then have "open_set (X-S)" unfolding closed_set_def by auto
  then have "(X-S) \<in> \<tau> " by auto
  from \<open>clopen S\<close> have "open_set S" by auto
  then have "S \<in> \<tau>" by auto
  then have "S={} \<or> finite (X-S)" by (simp add:cofinite_topology)
  with \<open>S\<noteq>{}\<close> have f1:"finite (X-S)" by simp
  with \<open>(X-S) \<in> \<tau>\<close> have *:"X-S = {} \<or> finite (X-(X-S))" by (simp add:cofinite_topology)
  with \<open>S\<noteq>X\<close> \<open>S\<subseteq>X\<close> have "X-S \<noteq> {}" by (simp add:cofinite_topology)
  with * have "finite (X-(X-S))" by simp 
  moreover
  have "X-(X-S) = S" using \<open>S\<subseteq>X\<close> by auto
  ultimately have "finite S" by auto
  with f1 have "finite (S \<union> (X-S))"  by auto
  then show "finite X" by auto
qed


end

(* mi19201_Aleksandar_Urosevic_FORMULACIJA *)
definition closed_interval :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "closed_interval a b = { x. a \<le> x \<and> x \<le> b }"

(* mi19201_Aleksandar_Urosevic_FORMULACIJA *)
(* mi21002_Stasa_Djordjevic_DOKAZ *)
lemma closed_interval_empty_iff:
  "closed_interval a b = {} \<longleftrightarrow> a > b"
  unfolding closed_interval_def by auto

  
(* mi21002_Stasa_Djordjevic_FORMULACIJA *)
(* mi21002_Stasa_Djordjevic_DOKAZ *)
lemma open_interval_is_open:
  assumes "r<s"
  shows "is_real_open_set (open_interval r s)" 
  unfolding is_real_open_set_def open_interval_def
by auto

(* mi21002_Stasa_Djordjevic_FORMULACIJA *)
lemma inf_intervals_are_open:
  shows "is_real_open_set {x::real . r<x}" and "is_real_open_set {x::real . x<r}" 
  sorry

(* mi21002_Stasa_Djordjevic_FORMULACIJA *)
lemma not_all_open_sets_are_intervals:
  shows "\<exists> S . is_real_open_set S \<and> (\<forall> a b . S \<noteq> (open_interval a b))"
  sorry 

(* mi21002_Stasa_Djordjevic_FORMULACIJA *)
lemma closed_interval_is_not_open:
  assumes "c<d"
  shows "is_real_open_set (closed_interval c d) \<longleftrightarrow> False"
  sorry


(* mi21002 Stasa Djordjevic FORMULACIJA *)
lemma closed_interval_is_closed: 
  assumes "a<b"
  shows "Euclidean_topology.closed_set (closed_interval a b)"
  sorry

(* mi22229 Ivana Milenkovic FORMULACIJA *)
lemma singleton_is_closed:
  fixes a :: real
  shows "Euclidean_topology.closed_set {a}"
  sorry

(* mi22229 Ivana Milenkovic FORMULACIJA *)
lemma singleton_as_degenerate_closed_interval:
  fixes a :: real
  shows "{a} = closed_interval a a"
  sorry

(* mi22229 Ivana Milenkovic FORMULACIJA *)
lemma integers_are_closed:
 shows "Euclidean_topology.closed_set {x \<in> \<real>. x \<in> \<int>}"
  sorry 

(* mi22229 Ivana Milenkovic FORMULACIJA *)
lemma rationals_not_open_nor_closed:
  shows "\<not> is_real_open_set (\<rat>) \<and> \<not> Euclidean_topology.closed_set (\<rat>)"
  sorry
(* mi22229 Ivana Milenkovic FORMULACIJA *)
lemma open_set_iff_union_of_open_intervals:
  "is_real_open_set S \<longleftrightarrow> (\<exists>J. (\<forall>j \<in> J. \<exists>r s. r < s \<and> j = open_interval r s) \<and> S = \<Union> J)"
  sorry

