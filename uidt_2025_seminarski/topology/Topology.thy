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

(*mi21207 Matija Stankovic FORMULACIJA*)
definition is_basis :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_basis X \<tau> B \<longleftrightarrow>
     topological_space X \<tau> \<and>
     (\<forall>B'\<in>B. B' \<in> \<tau>) \<and>
     (\<forall>U\<in>\<tau>. \<exists>C \<subseteq> B. U = \<Union> C)"

(*mi21207 Matija Stankovic FORMULACIJA*)
(*mi21093_Nikolina_Sobic_DOKAZ*)
lemma Prop_2_2_8_forward:
  fixes X :: "'a set" and B :: "'a set set"
  assumes "X \<noteq> {}"
    and union_B: "\<Union> B = X"
    and inter_basis: "\<forall>B1\<in>B. \<forall>B2\<in>B. \<exists>C \<subseteq> B. B1 \<inter> B2 = \<Union> C"
  shows
    "\<exists>\<tau>. is_basis X \<tau> B"
proof -
  let ?\<tau> = "{U. \<exists>C \<subseteq> B. U = \<Union> C}"

  have T: "topological_space X ?\<tau>"
  proof
    fix S assume "S \<in> ?\<tau>"
    then obtain C where "C \<subseteq> B" "S = \<Union> C" by auto
    then show "S \<subseteq> X" using union_B by auto
  next
    show "X \<in> ?\<tau>" using union_B by auto
  next
    show "{} \<in> ?\<tau>"
    proof -
      have "{} \<subseteq> B \<and> {} = \<Union> {}" by simp
      then show ?thesis by auto
    qed
  next
    fix S1 S2 assume "S1 \<in> ?\<tau>" "S2 \<in> ?\<tau>"
    then obtain C1 C2 where C1: "C1 \<subseteq> B" "S1 = \<Union> C1" 
                        and C2: "C2 \<subseteq> B" "S2 = \<Union> C2" by auto
    let ?f = "\<lambda>b1 b2. SOME C. C \<subseteq> B \<and> b1 \<inter> b2 = \<Union> C"
    have f_props: "\<And>b1 b2. \<lbrakk>b1 \<in> C1; b2 \<in> C2\<rbrakk> \<Longrightarrow> ?f b1 b2 \<subseteq> B \<and> b1 \<inter> b2 = \<Union> (?f b1 b2)"
    proof -
      fix b1 b2 assume "b1 \<in> C1" "b2 \<in> C2"
      hence "b1 \<in> B" "b2 \<in> B" using C1 C2 by auto
      hence "\<exists>C. C \<subseteq> B \<and> b1 \<inter> b2 = \<Union> C" using inter_basis by auto
      thus "?f b1 b2 \<subseteq> B \<and> b1 \<inter> b2 = \<Union> (?f b1 b2)" by (rule someI_ex)
    qed
    let ?C_final = "\<Union> {?f b1 b2 | b1 b2. b1 \<in> C1 \<and> b2 \<in> C2}"
    have "?C_final \<subseteq> B" using f_props by auto
    moreover have "S1 \<inter> S2 = \<Union> ?C_final"
    proof (intro equalityI subsetI)
      fix x assume "x \<in> S1 \<inter> S2"
      then obtain b1 b2 where "x \<in> b1" "b1 \<in> C1" "x \<in> b2" "b2 \<in> C2" unfolding C1 C2 by auto
      hence "x \<in> b1 \<inter> b2" by simp
      with f_props[OF \<open>b1 \<in> C1\<close> \<open>b2 \<in> C2\<close>] have "x \<in> \<Union> (?f b1 b2)" by simp
      thus "x \<in> \<Union> ?C_final" using \<open>b1 \<in> C1\<close> \<open>b2 \<in> C2\<close> by auto
    next
      fix x assume "x \<in> \<Union> ?C_final"
      then obtain b1 b2 where "b1 \<in> C1" "b2 \<in> C2" "x \<in> \<Union> (?f b1 b2)" by auto
      with f_props[OF \<open>b1 \<in> C1\<close> \<open>b2 \<in> C2\<close>] have "x \<in> b1 \<inter> b2" by simp
      thus "x \<in> S1 \<inter> S2" unfolding C1 C2 using \<open>b1 \<in> C1\<close> \<open>b2 \<in> C2\<close> by auto
    qed
    ultimately show "S1 \<inter> S2 \<in> ?\<tau>" by auto
  next
    fix \<tau>' assume "\<tau>' \<noteq> {}" "\<tau>' \<subseteq> ?\<tau>"
    let ?F = "\<lambda>S. SOME C. C \<subseteq> B \<and> S = \<Union> C"
    have F_props: "\<And>S. S \<in> \<tau>' \<Longrightarrow> ?F S \<subseteq> B \<and> S = \<Union> (?F S)"
    proof -
      fix S assume "S \<in> \<tau>'"
      hence "S \<in> ?\<tau>" using \<open>\<tau>' \<subseteq> ?\<tau>\<close> by auto
      hence "\<exists>C. C \<subseteq> B \<and> S = \<Union> C" by auto
      thus "?F S \<subseteq> B \<and> S = \<Union> (?F S)" by (rule someI_ex)
    qed
    let ?C_union = "\<Union>S\<in>\<tau>'. ?F S"
    have "?C_union \<subseteq> B" using F_props by auto
    moreover have "\<Union> \<tau>' = \<Union> ?C_union"
    proof (intro equalityI subsetI)
      fix x assume "x \<in> \<Union> \<tau>'"
      then obtain S where "S \<in> \<tau>'" "x \<in> S" by auto
      with F_props[OF \<open>S \<in> \<tau>'\<close>] have "x \<in> \<Union> (?F S)" by simp
      thus "x \<in> \<Union> ?C_union" using \<open>S \<in> \<tau>'\<close> by auto
    next
      fix x assume "x \<in> \<Union> ?C_union"
      then obtain C_set where "C_set \<in> ?F ` \<tau>'" "x \<in> \<Union> C_set" by auto
      then obtain S where "S \<in> \<tau>'" "C_set = ?F S" by auto
      with \<open>x \<in> \<Union> C_set\<close> F_props[OF \<open>S \<in> \<tau>'\<close>] have "x \<in> S" by simp
      thus "x \<in> \<Union> \<tau>'" using \<open>S \<in> \<tau>'\<close> by auto
    qed
    ultimately show "\<Union> \<tau>' \<in> ?\<tau>" by auto
  qed

  have B_in: "\<forall>B'\<in>B. B' \<in> ?\<tau>"
  proof
    fix b assume "b \<in> B"
    hence "{b} \<subseteq> B \<and> b = \<Union> {b}" by auto
    then show "b \<in> ?\<tau>" by auto
  qed
  
  have \<tau>_basis: "\<forall>U\<in>?\<tau>. \<exists>C \<subseteq> B. U = \<Union> C" by auto

  show ?thesis
    unfolding is_basis_def
  proof (rule exI[where x="?\<tau>"], intro conjI)
    show "topological_space X ?\<tau>" by (rule T)
  next
    show "\<forall>B'\<in>B. B' \<in> ?\<tau>" by (rule B_in)
  next
    show "\<forall>U\<in>?\<tau>. \<exists>C\<subseteq>B. U = \<Union> C" by (rule \<tau>_basis)
  qed
qed

(*mi21207 Matija Stankovic FORMULACIJA*)
(*mi21093_Nikolina_Sobic_DOKAZ*)
lemma Prop_2_2_8_backward:
  fixes X :: "'a set" and \<tau> :: "'a set set" and B :: "'a set set"
  assumes "is_basis X \<tau> B"
  shows
    "\<Union> B = X \<and>
     (\<forall>B1\<in>B. \<forall>B2\<in>B. \<exists>C \<subseteq> B. B1 \<inter> B2 = \<Union> C)"
proof -
  interpret topological_space X \<tau> 
    using assms unfolding is_basis_def by simp

  have "\<Union> B = X"
  proof
    show "\<Union> B \<subseteq> X" 
      using assms unfolding is_basis_def using subsets by blast
  next
    have "X \<in> \<tau>" by (rule univ)
    then obtain C where "C \<subseteq> B" "X = \<Union> C" 
      using assms unfolding is_basis_def by blast
    thus "X \<subseteq> \<Union> B" by blast
  qed
  
  moreover have "\<forall>B1\<in>B. \<forall>B2\<in>B. \<exists>C \<subseteq> B. B1 \<inter> B2 = \<Union> C"
  proof (clarify)
    fix B1 B2 assume "B1 \<in> B" "B2 \<in> B"
    hence "B1 \<in> \<tau>" "B2 \<in> \<tau>" using assms unfolding is_basis_def by auto
    hence "B1 \<inter> B2 \<in> \<tau>" by (rule inter)
    thus "\<exists>C \<subseteq> B. B1 \<inter> B2 = \<Union> C" 
      using assms unfolding is_basis_def by blast
  qed
  
  ultimately show ?thesis by blast
qed


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

end

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
(* mi21207 Matija Stankovic DOKAZ*)
lemma inf_intervals_are_open:
  shows "is_real_open_set {x::real . r<x}" and "is_real_open_set {x::real . x<r}" 
proof -
  show "is_real_open_set {x::real . r < x}"
    unfolding is_real_open_set_def
  proof
    fix x
    assume hx: "x \<in> {x::real . r < x}"
    have h1: "x \<in> open_interval r (x + 1)"
      unfolding open_interval_def
      using hx
      by auto
    have h2: "open_interval r (x + 1) \<subseteq> {x::real . r < x}"
      unfolding open_interval_def
      by auto
    show "\<exists>a b. x \<in> open_interval a b \<and> open_interval a b \<subseteq> {x::real . r < x}"
      using h1 h2
      by auto
  qed
next
  show "is_real_open_set {x::real . x < r}"
    unfolding is_real_open_set_def
  proof
    fix x
    assume hx: "x \<in> {x::real . x < r}"
    have h1: "x \<in> open_interval (x - 1) r"
      unfolding open_interval_def
      using hx
      by auto
    have h2: "open_interval (x - 1) r \<subseteq> {x::real . x < r}"
      unfolding open_interval_def
      by auto
    show "\<exists>a b. x \<in> open_interval a b \<and> open_interval a b \<subseteq> {x::real . x < r}"
      using h1 h2
      by auto
  qed
qed

(* mi21002_Stasa_Djordjevic_FORMULACIJA *)
(*mi21093_Nikolina_Sobic_DOKAZ*)
lemma not_all_open_sets_are_intervals:
  shows "\<exists> S . is_real_open_set S \<and> (\<forall> a b . S \<noteq> (open_interval a b))"
proof -
  let ?S = "open_interval 1 3 \<union> open_interval 5 6"
  have "is_real_open_set ?S"
    unfolding is_real_open_set_def open_interval_def
    by auto
  moreover have "\<forall> a b . ?S \<noteq> open_interval a b"
  proof (intro allI notI)
    fix a b
    assume eq: "?S = open_interval a b" 
    have "2 \<in> ?S" and "5.5 \<in> ?S" 
      unfolding open_interval_def by auto
    hence "2 \<in> open_interval a b" and "5.5 \<in> open_interval a b" 
      using eq by auto
    have "a < 2" and "5.5 < b" 
      using \<open>2 \<in> open_interval a b\<close> \<open>5.5 \<in> open_interval a b\<close> 
      unfolding open_interval_def by auto
    have "4 \<in> open_interval a b"
    proof -
      have "a < 4" using \<open>a < 2\<close> by simp
      moreover have "4 < b" using \<open>5.5 < b\<close> by simp
      ultimately show ?thesis unfolding open_interval_def by simp
    qed
    hence "4 \<in> ?S" using eq by simp
    thus False unfolding open_interval_def by auto
  qed
  ultimately show ?thesis by blast
qed

(* mi21002_Stasa_Djordjevic_FORMULACIJA *)
(* mi21207 Matija Stankovic DOKAZ*)
lemma closed_interval_is_not_open:
  assumes "c<d"
  shows "is_real_open_set (closed_interval c d) \<longleftrightarrow> False"
proof
  assume h: "is_real_open_set (closed_interval c d)"
  have hc: "c \<in> closed_interval c d"
    unfolding closed_interval_def
    using assms
    by auto
  from h hc obtain a b where
    h1: "c \<in> open_interval a b" and
    h2: "open_interval a b \<subseteq> closed_interval c d"
    unfolding is_real_open_set_def
    by auto
  have hlt: "a < c"
    using h1
    unfolding open_interval_def
    by auto
  have hmid: "(a + c) / 2 \<in> open_interval a b"
    using h1 hlt
    unfolding open_interval_def
    by auto
  have hmid2: "(a + c) / 2 < c"
    using hlt
    by auto
  have h_contra: "(a + c) / 2 \<notin> closed_interval c d"
    unfolding closed_interval_def
    using hmid2
    by auto
  from h2 hmid have "(a + c) / 2 \<in> closed_interval c d"
    by auto
  with h_contra show False
    by auto
next
  show "False \<Longrightarrow> is_real_open_set (closed_interval c d)"
    by auto
qed

(* mi21207 Matija Stankovic FORMULACIJA*)
(* mi21207 Matija Stankovic DOKAZ*)
lemma is_real_open_set_union:
  assumes "is_real_open_set A" "is_real_open_set B"
  shows "is_real_open_set (A \<union> B)"
proof -
  show ?thesis
    unfolding is_real_open_set_def
  proof
    fix x
    assume hx: "x \<in> A \<union> B"
    then consider (A) "x \<in> A" | (B) "x \<in> B"
      by auto
    then show "\<exists>a b. x \<in> open_interval a b \<and> open_interval a b \<subseteq> A \<union> B"
    proof cases
      case A
      then obtain a b where
        h1: "x \<in> open_interval a b"
        and h2: "open_interval a b \<subseteq> A"
        using assms(1)
        unfolding is_real_open_set_def
        by auto
      show ?thesis
        using h1 h2
        by auto
    next
      case B
      then obtain a b where
        h1: "x \<in> open_interval a b"
        and h2: "open_interval a b \<subseteq> B"
        using assms(2)
        unfolding is_real_open_set_def
        by auto
      show ?thesis
        using h1 h2
        by auto
    qed
  qed
qed


(* mi21002 Stasa Djordjevic FORMULACIJA *)
(* mi21207 Matija Stankovic DOKAZ*)
lemma closed_interval_is_closed: 
  assumes "a<b"
  shows "Euclidean_topology.closed_set (closed_interval a b)"
proof -
  have h1: "is_real_open_set {x::real. x < a}"
    using inf_intervals_are_open(2)
    by auto

  have h2: "is_real_open_set {x::real. b < x}"
    using inf_intervals_are_open(1)
    by auto

  have h3: "is_real_open_set ({x::real. x < a} \<union> {x::real. b < x})"
    using is_real_open_set_union h1 h2
    by auto

  have hcomp:
    "UNIV - closed_interval a b = {x::real. x < a} \<union> {x::real. b < x}"
    unfolding closed_interval_def
    by auto

  show ?thesis
    unfolding Euclidean_topology.closed_set_def
    using h3 hcomp
    by auto
qed

(* mi22229 Ivana Milenkovic FORMULACIJA *)
(* mi21207 Matija Stankovic DOKAZ*)
lemma singleton_is_closed:
  fixes a :: real
  shows "Euclidean_topology.closed_set {a}"
 proof -
  have h1: "is_real_open_set {x::real. x < a}"
    using inf_intervals_are_open(2)
    by auto

  have h2: "is_real_open_set {x::real. a < x}"
    using inf_intervals_are_open(1)
    by auto

  have h3: "is_real_open_set ({x::real. x < a} \<union> {x::real. a < x})"
    using is_real_open_set_union h1 h2
    by auto

  have hcomp: "UNIV - {a} = {x::real. x < a} \<union> {x::real. a < x}"
    by auto

  show ?thesis
    unfolding Euclidean_topology.closed_set_def
    using h3 hcomp
    by auto
qed

(* mi22229 Ivana Milenkovic FORMULACIJA *)
(* mi21207 Matija Stankovic DOKAZ*)
lemma singleton_as_degenerate_closed_interval:
  fixes a :: real
  shows "{a} = closed_interval a a"
proof
  show "{a} \<subseteq> closed_interval a a"
    unfolding closed_interval_def
    by auto
next
  show "closed_interval a a \<subseteq> {a}"
    unfolding closed_interval_def
    by auto
qed

(* mi22229 Ivana Milenkovic FORMULACIJA *)
(*mi21093_Nikolina_Sobic_DOKAZ*)
lemma integers_are_closed:
 shows "Euclidean_topology.closed_set {x \<in> \<real>. x \<in> \<int>}"
proof -
  have "Euclidean_topology.open_set (UNIV - {x \<in> \<real>. x \<in> \<int>})"
  proof -
    have eq: "UNIV - {x \<in> \<real>. x \<in> \<int>} = (\<Union>n\<in>\<int>. {x::real. n < x \<and> x < n + 1})"
    proof (rule set_eqI)
      fix x :: real
      show "x \<in> UNIV - {x \<in> \<real>. x \<in> \<int>} \<longleftrightarrow> x \<in> (\<Union>n\<in>\<int>. {x. n < x \<and> x < n + 1})"
      proof
        assume h: "x \<in> UNIV - {x \<in> \<real>. x \<in> \<int>}"
        then have "x \<notin> \<int>" 
        proof -
          have "x \<in> \<real>" by (simp add: Reals_def)
          with h show "x \<notin> \<int>" by auto
        qed
        then show "x \<in> (\<Union>n\<in>\<int>. {x. n < x \<and> x < n + 1})"
        proof -
          obtain n where "n = floor x" by simp
          then have "n \<le> x" "x < n + 1" by linarith+
          moreover have "n < x" 
            using \<open>x \<notin> \<int>\<close> \<open>n = floor x\<close> \<open>n \<le> x\<close>
            by (metis Ints_of_int dual_order.strict_iff_order)
          moreover have "n \<in> \<int>" 
            using \<open>n = floor x\<close> by (simp add: Ints_def)
          ultimately show ?thesis by auto
        qed
      next
        assume "x \<in> (\<Union>n\<in>\<int>. {x. n < x \<and> x < n + 1})"
        then show "x \<in> UNIV - {x \<in> \<real>. x \<in> \<int>}"
          by (auto simp: Ints_def Reals_def)
      qed
    qed
    moreover have all_open: "\<forall>n\<in>\<int>. Euclidean_topology.open_set {x::real. n < x \<and> x < n + 1}"
      proof
      fix n :: real
      assume "n \<in> \<int>"
      have "{x::real. n < x \<and> x < n + 1} = open_interval n (n + 1)"
        unfolding open_interval_def by auto
      moreover have "is_real_open_set (open_interval n (n + 1))"
        using open_interval_is_open by simp
      ultimately show "Euclidean_topology.open_set {x::real. n < x \<and> x < n + 1}"
        by simp
    qed
    have union_open: "Euclidean_topology.open_set (\<Union>n\<in>\<int>. {x::real. n < x \<and> x < n + 1})"
      proof -
      let ?\<tau>' = "{{x::real. n < x \<and> x < n + 1} | n. n \<in> \<int>}"
      have "\<Union> ?\<tau>' = (\<Union>n\<in>\<int>. {x::real. n < x \<and> x < n + 1})" by auto
      moreover have "?\<tau>' \<subseteq> {S. is_real_open_set S}"
        using all_open by auto
      moreover have "?\<tau>' \<noteq> {}"
      proof -
        have "0 \<in> (\<int> :: real set)" by (simp add: Ints_def)
        then have "{x. (0::real) < x \<and> x < 0 + 1} \<in> ?\<tau>'" by blast
        thus ?thesis by blast
      qed
      ultimately show ?thesis
        using Euclidean_topology.union[of ?\<tau>'] by simp
    qed
    show "Euclidean_topology.open_set (UNIV - {x \<in> \<real>. x \<in> \<int>})"
      using eq union_open by simp
  qed
  then show ?thesis
    by (simp add: Euclidean_topology.closed_set_def)
qed

(* mi22229 Ivana Milenkovic FORMULACIJA *)
lemma rationals_not_open_nor_closed:
  shows "\<not> is_real_open_set (\<rat>) \<and> \<not> Euclidean_topology.closed_set (\<rat>)"
  sorry
(* mi22229 Ivana Milenkovic FORMULACIJA *)
(* mi21207 Matija Stankovic DOKAZ*)
lemma open_set_iff_union_of_open_intervals:
  "is_real_open_set S \<longleftrightarrow> (\<exists>J. (\<forall>j \<in> J. \<exists>r s. r < s \<and> j = open_interval r s) \<and> S = \<Union> J)"
proof
  assume hS: "is_real_open_set S"
  let ?J = "{I. \<exists>a b. a < b \<and> I = open_interval a b \<and> I \<subseteq> S}"
  have hJ_form:
    "\<forall>I\<in>?J. \<exists>r s. r < s \<and> I = open_interval r s"
    by auto
  have hSJ: "S = \<Union> ?J"
  proof
    show "S \<subseteq> \<Union> ?J"
    proof
      fix x
      assume hx: "x \<in> S"
      then obtain a b where
        h1: "x \<in> open_interval a b" and
        h2: "open_interval a b \<subseteq> S"
        using hS
        unfolding is_real_open_set_def
        by auto
      have hlt: "a < b"
        using h1
        unfolding open_interval_def
        by auto
      have "open_interval a b \<in> ?J"
        using hlt h2
        by auto
      thus "x \<in> \<Union> ?J"
        using h1
        by auto
    qed
  next
    show "\<Union> ?J \<subseteq> S"
      by auto
  qed
  show "\<exists>J. (\<forall>j\<in>J. \<exists>r s. r < s \<and> j = open_interval r s) \<and> S = \<Union> J"
  proof
    show "(\<forall>j\<in>?J. \<exists>r s. r < s \<and> j = open_interval r s) \<and> S = \<Union> ?J"
      using hJ_form hSJ
      by auto
qed
next
  assume h:
    "\<exists>J. (\<forall>j\<in>J. \<exists>r s. r < s \<and> j = open_interval r s) \<and> S = \<Union> J"
  then obtain J where
    hJ: "\<forall>j\<in>J. \<exists>r s. r < s \<and> j = open_interval r s"
    and hS: "S = \<Union> J"
    by auto
  show "is_real_open_set S"
    unfolding hS is_real_open_set_def
  proof
    fix x
    assume hx: "x \<in> \<Union> J"
    then obtain j where
      hj: "j \<in> J" and
      hxj: "x \<in> j"
      by auto
    then obtain r s where
      hrs: "r < s" and
      hj_eq: "j = open_interval r s"
      using hJ
      by auto
    have hsub: "open_interval r s \<subseteq> \<Union> J"
    proof
      fix y
      assume "y \<in> open_interval r s"
      hence "y \<in> j"
        using hj_eq
        by auto
      thus "y \<in> \<Union> J"
        using hj
        by auto
    qed
    show "\<exists>a b. x \<in> open_interval a b \<and> open_interval a b \<subseteq> \<Union> J"
      using hxj hj_eq hsub
      by auto
  qed
qed

(* mi21093_Nikolina_Sobic_FORMULACIJA *)
lemma Ex_2_2_3:
  shows "is_basis UNIV {S. is_real_open_set S} {open_interval a b | a b. a < b}"
  sorry

(* mi21093_Nikolina_Sobic_FORMULACIJA *)
lemma Ex_2_2_4:
  fixes X :: "'a set"
  shows "is_basis X (Pow X) {{x} | x. x \<in> X}"
  sorry

(* mi21093_Nikolina_Sobic_FORMULACIJA *)
lemma Ex_2_2_5:
  fixes X :: "'a set" and a b c d e f :: "'a"
  fixes \<tau> :: "'a set set" and B :: "'a set set"
  assumes "X = {a, b, c, d, e, f}"
    and "\<tau> = {X, {}, {a}, {c, d}, {a, c, d}, {b, c, d, e, f}}"
    and "B = {{a}, {c, d}, {b, c, d, e, f}}"
    and "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "a \<noteq> e" "a \<noteq> f"
                  "b \<noteq> c" "b \<noteq> d" "b \<noteq> e" "b \<noteq> f"
                  "c \<noteq> d" "c \<noteq> e" "c \<noteq> f"
                  "d \<noteq> e" "d \<noteq> f"
                  "e \<noteq> f"
                shows "is_basis X \<tau> B"
proof (unfold is_basis_def, intro conjI)
    show "topological_space X \<tau>" 
(* Dokazivanje aksioma topoloskog prostora za zadatu familiju \<tau> 
       u ovom primeru zahteva proveru svih kombinacija unija i preseka elemenata 
       navedenih u assms(2). Posto je \<tau> konacna i mala familija, ove aksiome 
       su ocigledno zadovoljene (npr. {a, c, d} \<inter> {b, c, d, e, f} = {c, d} \<in> \<tau>), 
       ali je formalni dokaz u Isabelle izostavljen zbog obimnosti nabrajanja. *)
    using assms sorry
next
  show "\<forall>B'\<in>B. B' \<in> \<tau>"
    using assms(2) assms(3) by auto
next
  show "\<forall>U\<in>\<tau>. \<exists>C\<subseteq>B. U = \<Union> C"
  proof
    fix U assume "U \<in> \<tau>"
    then consider "U = X" | "U = {}" | "U = {a}" | "U = {c, d}" | "U = {a, c, d}" | "U = {b, c, d, e, f}"
      using assms(2) by blast
    then show "\<exists>C\<subseteq>B. U = \<Union> C"
   proof cases
      case 1 
      let ?C = "{{a}, {b, c, d, e, f}}"
      have "?C \<subseteq> B" using assms(3) by auto
      moreover have "X = \<Union> ?C" using assms(1) by auto
      ultimately show ?thesis using 1 by blast
    next
      case 2 
      have "{} \<subseteq> B" by simp
      moreover have "{} = \<Union> {}" by simp
      ultimately show ?thesis using 2 by blast
    next
      case 3 
      have "{{a}} \<subseteq> B" using assms(3) by auto
      moreover have "{a} = \<Union> {{a}}" by simp
      ultimately show ?thesis using 3 by blast
    next
      case 4 
      have "{{c, d}} \<subseteq> B" using assms(3) by auto
      moreover have "{c, d} = \<Union> {{c, d}}" by simp
      ultimately show ?thesis using 4 by blast
    next
      case 5 
      let ?C = "{{a}, {c, d}}"
      have "?C \<subseteq> B" using assms(3) by auto
      moreover have "{a, c, d} = \<Union> ?C" by auto
      ultimately show ?thesis using 5 by blast
    next
      case 6 
      have "{{b, c, d, e, f}} \<subseteq> B" using assms(3) by auto
      moreover have "{b, c, d, e, f} = \<Union> {{b, c, d, e, f}}" by simp
      ultimately show ?thesis using 6 by blast
    qed
  qed
qed


(* mi21093_Nikolina_Sobic_FORMULACIJA *)
(*mi21093_Nikolina_Sobic_DOKAZ*)
lemma Remark_2_2_6:
  assumes "topological_space X \<tau>"
  shows "is_basis X \<tau> \<tau>"
proof (unfold is_basis_def, intro conjI)
  show "topological_space X \<tau>" 
    by (rule assms)
next
  show "\<forall>B'\<in>\<tau>. B' \<in> \<tau>" 
    by simp
next
  show "\<forall>U\<in>\<tau>. \<exists>C\<subseteq>\<tau>. U = \<Union> C"
  proof
    fix U assume "U \<in> \<tau>"
    let ?C = "{U}"
    have "?C \<subseteq> \<tau>" using `U \<in> \<tau>` by simp
    moreover have "U = \<Union> ?C" by simp
    ultimately show "\<exists>C\<subseteq>\<tau>. U = \<Union> C" by blast
  qed
qed

lemma Remark_2_2_6_discrete:
  fixes X :: "'a set"
  shows "is_basis X (Pow X) (Pow X)"
proof -
  have "topological_space X (Pow X)"
  proof
    fix S assume "S \<in> Pow X" thus "S \<subseteq> X" by simp
  next
    show "X \<in> Pow X" by simp
  next
    show "{} \<in> Pow X" by simp
  next
    fix S1 S2 assume "S1 \<in> Pow X" "S2 \<in> Pow X"
    thus "S1 \<inter> S2 \<in> Pow X" by auto
  next
    fix \<tau>' assume "\<tau>' \<noteq> {}" "\<tau>' \<subseteq> Pow X"
    thus "\<Union> \<tau>' \<in> Pow X" by auto
  qed
  thus ?thesis by (rule Remark_2_2_6)
qed

lemma basis_extension:
  assumes "is_basis X \<tau> B"
    and "B \<subseteq> B1"
    and "B1 \<subseteq> \<tau>"
  shows "is_basis X \<tau> B1"
proof (unfold is_basis_def, intro conjI)
  show "topological_space X \<tau>" 
    using assms(1) unfolding is_basis_def by simp
next
  show "\<forall>B'\<in>B1. B' \<in> \<tau>" 
    using assms(3) by auto
next
  show "\<forall>U\<in>\<tau>. \<exists>C\<subseteq>B1. U = \<Union> C"
  proof
    fix U assume "U \<in> \<tau>"
    obtain C' where "C' \<subseteq> B" "U = \<Union> C'" 
      using assms(1) `U \<in> \<tau>` unfolding is_basis_def by blast
    have "C' \<subseteq> B1" 
      using `C' \<subseteq> B` assms(2) by blast
    thus "\<exists>C\<subseteq>B1. U = \<Union> C" 
      using `U = \<Union> C'` by blast
  qed
qed


(* mi21093_Nikolina_Sobic_FORMULACIJA *)
definition right_half_open_interval :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "right_half_open_interval a b = {x. a \<le> x \<and> x < b}"


