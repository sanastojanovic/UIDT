theory Topology
  imports Complex_Main "HOL-Library.Multiset"
begin

section ‹Aksiomatsko zasnivanje teorija›

locale topological_space =
  ― ‹konstante›
  fixes X :: "'a set"  ― ‹skup nosilac›
  fixes τ :: "'a set set" ― ‹kolekcija otvorenih skupova›

  ― ‹aksiome›
  assumes subsets: "⋀ S. S ∈ τ ⟹ S ⊆ X"
  assumes univ: "X ∈ τ"
  assumes empty: "{} ∈ τ"
  assumes inter: "⋀ S1 S2. ⟦S1 ∈ τ; S2 ∈ τ⟧ ⟹ S1 ∩ S2 ∈ τ"
  assumes union: "⋀ τ'. ⟦τ' ≠ {}; τ' ⊆ τ⟧ ⟹ ⋃ τ' ∈ τ"
begin

abbreviation open_set :: "'a set ⇒ bool" where
  "open_set S ≡ S ∈ τ"

lemma inter_finite:
  assumes "finite τ'" "τ' ≠ {}" "∀ S ∈ τ'. open_set S"
  shows "open_set (⋂ τ')"
  using assms
proof (induction τ' rule: finite.induct)
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

definition closed_set :: "'a set ⇒ bool" where
  "closed_set S ⟷ open_set (X - S)"

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
  assumes "τ' ≠ {}" "∀ S ∈ τ'. closed_set S"
  shows "closed_set (⋂ τ')"
proof-
  have "X - (⋂ τ') = ⋃ {X - S | S . S ∈ τ'}"
    using assms
    by auto
  thus ?thesis
    using assms
    unfolding closed_set_def
    using union[of "{X - S |S. S ∈ τ'}"]
    by auto
qed

lemma closed_union:
  assumes "closed_set S1" "closed_set S2"
  shows "closed_set (S1 ∩ S2)"
  using assms union[of "{X - S1, X - S2}"]
  unfolding closed_set_def
  by (simp add: Diff_Int)

lemma closed_union_finite:
  assumes "finite τ'" "τ' ≠ {}" "∀ S ∈ τ'. closed_set S"
  shows "closed_set (⋃ τ')"
proof-
  have "X - ⋃ τ' = ⋂ {X - S | S . S ∈ τ'}"
    using `τ' ≠ {}`
    by auto
  thus ?thesis
    using assms
    using inter_finite[of "{X - S | S. S ∈ τ'}"]
    unfolding closed_set_def
    by auto
qed

end

definition X_ex1 :: "nat set" where
  "X_ex1 = {0::nat, 1, 2, 3, 4, 5}"

definition τ_ex1 :: "nat set set" where
  "τ_ex1 = {{0::nat, 1, 2, 3, 4, 5}, {}, {0}, {2, 3}, {0, 2, 3}, {1, 2, 3, 4, 5}}"

interpretation topological_space where
  X = "X_ex1" and
  τ = "τ_ex1"
proof
  fix S
  assume "S ∈ τ_ex1"
  thus "S ⊆ X_ex1"
    unfolding τ_ex1_def X_ex1_def
    by auto
next
  show "X_ex1 ∈ τ_ex1" "{} ∈ τ_ex1"
    unfolding X_ex1_def τ_ex1_def
    by auto
next
  fix S1 S2
  assume "S1 ∈ τ_ex1" "S2 ∈ τ_ex1"
  thus "S1 ∩ S2 ∈ τ_ex1"
    unfolding τ_ex1_def
    ― ‹ovi dokazi su krajnje neinteresantni, a ne mogu se dokazati automatski›
    sorry
next
  fix τ'
  assume "τ' ≠ {}" "τ' ⊆ τ_ex1"
  thus "⋃ τ' ∈ τ_ex1"
    unfolding τ_ex1_def
    ― ‹ovi dokazi su krajnje neinteresantni, a ne mogu se dokazati automatski›
    sorry
qed

definition open_interval :: "real ⇒ real ⇒ real set" where
  "open_interval a b = {x. a < x ∧ x < b}"

lemma open_interval_empty_iff:
  "open_interval a b = {} ⟷ a ≥ b"
  unfolding open_interval_def
  by (metis (no_types, lifting) dense_le dual_order.strict_implies_order empty_Collect_eq leD le_less_linear order.strict_trans1)

definition is_real_open_set where
  "is_real_open_set S ⟷
      (∀ x ∈ S. ∃ a b. x ∈ open_interval a b ∧ open_interval a b ⊆ S)"

interpretation Euclidean_topology: topological_space where
 X = "UNIV :: real set" ― ‹UNIV je skup svih elemenata nekog tipa› and
 τ = "{S. is_real_open_set S}"
proof
  fix S
  assume "S ∈ {S. is_real_open_set S}"
  then show "S ⊆ UNIV"
    by simp
next
  have "∀ x. ∃ a b. x ∈ open_interval a b"
  proof-
    have "∀ x. x ∈ open_interval (x - 1) (x + 1)"
      unfolding open_interval_def
      by simp
    then show ?thesis
      by auto
  qed
  then show "UNIV ∈ {S. is_real_open_set S}"
    unfolding is_real_open_set_def
    by auto
next
  show "{} ∈ {S. is_real_open_set S}"
    unfolding is_real_open_set_def
    by simp
next
  fix τ'
  assume *: "τ' ⊆ {S. is_real_open_set S}"
  show "⋃ τ' ∈ {S. is_real_open_set S}"
  proof
    show "is_real_open_set (⋃ τ')"
      unfolding is_real_open_set_def
    proof
      fix x
      assume "x ∈ ⋃ τ'"
      then obtain S where "S ∈ τ'" "x ∈ S"
        by auto
      hence "is_real_open_set S"
        using *
        by auto
      then obtain a b where "x ∈ open_interval a b" "open_interval a b ⊆ S"
        using `x ∈ S`
        unfolding is_real_open_set_def
        by auto
      thus "∃a b. x ∈ open_interval a b ∧ open_interval a b ⊆ ⋃ τ'"
        using `S ∈ τ'`
        by auto
    qed
  qed
next
  fix S1 S2
  assume *: "S1 ∈ {S. is_real_open_set S}" "S2 ∈ {S. is_real_open_set S}"
  show "S1 ∩ S2 ∈ {S. is_real_open_set S}"
  proof
    show "is_real_open_set (S1 ∩ S2)"
      unfolding is_real_open_set_def
    proof
      fix x
      assume "x ∈ S1 ∩ S2"
      then obtain a1 b1 a2 b2 where
      **: "x ∈ open_interval a1 b1" "open_interval a1 b1 ⊆ S1"
          "x ∈ open_interval a2 b2" "open_interval a2 b2 ⊆ S2"
        using *
        unfolding is_real_open_set_def
        by blast
      let ?a = "max a1 a2"
      let ?b = "min b1 b2"
      have "x ∈ open_interval ?a ?b"
        using **
        unfolding open_interval_def
        by auto
      moreover
      have "open_interval ?a ?b ⊆ S1 ∩ S2"
        using **
        unfolding open_interval_def
        by auto
      ultimately
      show "∃a b. x ∈ open_interval a b ∧ open_interval a b ⊆ S1 ∩ S2"
        by auto
    qed
  qed
qed

thm Euclidean_topology.closed_set_def
thm Euclidean_topology.closed_inter
thm Euclidean_topology.closed_union_finite

lemma "Euclidean_topology.open_set A ⟷ is_real_open_set A"
  by simp

(* mi21061_Marko_Koprivica_FORMULACIJA *)
locale discrete_topological_space =
  fixes X :: "'a set" 
  fixes Pow_X :: "'a set set"
  assumes discrete_topology: "Pow_X = {Y. Y ⊆ X}"
begin

(* mi21061_Marko_Koprivica_FORMULACIJA *)
(* mi21061_Marko_Koprivica_DOKAZ *)
lemma is_topological_space: "topological_space X Pow_X"
proof
  show "⋀S. S ∈ Pow_X ⟹ S ⊆ X"
    by (simp add: discrete_topology)
next
  show "X ∈ Pow_X"
    by (simp add: discrete_topology)
next
  show "{} ∈ Pow_X"
    by (simp add: discrete_topology)
next
  fix S1 S2
  assume "S1 ∈ Pow_X" "S2 ∈ Pow_X"
  then have "S1 ⊆ X ∧ S2 ⊆ X"
    using discrete_topology
    by auto
  then have "S1 ∩ S2 ⊆ X"
    by auto
  then show "S1 ∩ S2 ∈ Pow_X"
    using discrete_topology
    by simp
next
  fix "τ'"
  assume "τ' ≠ {}" "τ' ⊆ Pow_X"
  then have "⋃ τ' ⊆ X"
    using discrete_topology
    by auto
  then show "⋃ τ' ∈ Pow_X"
    by (simp add: discrete_topology)
qed

end

(* mi21061_Marko_Koprivica_FORMULACIJA *)
locale indiscrete_topological_space = 
  fixes X :: "'a set"
  fixes τ :: "'a set set"
  assumes indiscrete_topology: "τ = {X, {}}"
begin

(* mi21061_Marko_Koprivica_FORMULACIJA *)
(* mi21061_Marko_Koprivica_DOKAZ *)
lemma is_topological_space: "topological_space X τ"
proof
  show "⋀S. S ∈ τ ⟹ S ⊆ X"
    by (auto simp add: indiscrete_topology)
next
  show "X ∈ τ"
    by (simp add: indiscrete_topology)
next
  show "{} ∈ τ"
    by (simp add: indiscrete_topology)
next
  fix S1 S2
  assume "S1 ∈ τ" "S2 ∈ τ"
  then have "(S1 = X ∨ S1 = {}) ∧ (S2 = {} ∨ S2 ⊆ X)"
    using indiscrete_topology
    by auto
  then have "(S1 = X ∧ S2 = {}) ∨ (S1 = X ∧ S2 = X) ∨ (S1 = {} ∧ S2 = {}) ∨ (S1 = {} ∧ S2 = X)"
    using ‹S2 ∈ τ› indiscrete_topology 
    by auto
  then have "(S1 ∩ S2 = {}) ∨ (S1 ∩ S2 = X)"
    by auto
  then show "S1 ∩ S2 ∈ τ"
    using indiscrete_topology
    by auto
next
  fix "τ'"
  assume "τ' ≠ {}" "τ' ⊆ τ"
  then have "τ' = {X} ∨ τ' = {X, {}} ∨ τ' = {{}}"
    using indiscrete_topology subset_insert_iff 
    by auto
  then have "⋃ τ' = X ∨ ⋃ τ' = {}"
    by auto
  then show "⋃ τ' ∈ τ"
    by (simp add: indiscrete_topology)
qed

end

(* mi21061_Marko_Koprivica_FORMULACIJA *)
(* mi21061_Marko_Koprivica_DOKAZ *)
lemma Ex_1_1_8:
  assumes "topological_space {a, b, c} τ"
  and "{a} ∈ τ" 
  and "{b} ∈ τ" 
  and "{c} ∈ τ"
shows "discrete_topological_space {a, b, c} τ"
  using assms
proof-
  have "τ = {x. x ⊆ {a, b, c}}"
  proof
    show "τ ⊆ {x. x ⊆ {a, b, c}}"
      by (metis assms(1) mem_Collect_eq subsetI topological_space_def)
  next
    show "{x. x ⊆ {a, b, c}} ⊆ τ"
    proof
      fix x
      assume "x ∈ {x. x ⊆ {a, b, c}}"
      then have "x ⊆ {a, b, c}"
        by simp
      then have "x = {} ∨ x = {a} ∨ x = {b} ∨ x = {c} ∨ x = {a, b} ∨ x = {a, c} ∨ 
                x = {b, c} ∨ x = {a, b, c}"
        by (smt (verit, best) empty_subsetI insert_absorb insert_commute insert_mono subset_antisym subset_insert subset_singletonD)
      then show "x ∈ τ"
      proof-
        have "x = {} ⟹ x ∈ τ"
          using assms(1) topological_space.empty 
          by auto
        moreover have "x = {a} ⟹ x ∈ τ"
          using assms(2)
          by simp
        moreover have "x = {b} ⟹ x ∈ τ"
          using assms(3)
          by simp
        moreover have "x = {c} ⟹ x ∈ τ"
          using assms(4)
          by simp
        moreover have "x = {a, b} ⟹ x ∈ τ"
        proof-
          assume "x = {a, b}"
          then have "x = {a} ∪ {b}"
            by auto
          moreover have "{a} ∪ {b} ∈ τ"
            using assms(1) assms(2) assms(3) topological_space.union[of "{a, b, c}" "τ" "{{a}, {b}}"]
            by simp
          ultimately show ?thesis
            by auto
        qed
        moreover have "x = {a, c} ⟹ x ∈ τ"
        proof-
          assume "x = {a, c}"
          then have "x = {a} ∪ {c}"
            by auto
          moreover have "{a} ∪ {c} ∈ τ"
            using assms(1) assms(2) assms(4) topological_space.union[of "{a, b, c}" "τ" "{{a}, {c}}"]
            by simp
          ultimately show ?thesis
            by auto
        qed
        moreover have "x = {b, c} ⟹ x ∈ τ"
        proof-
          assume "x = {b, c}"
          then have "x = {b} ∪ {c}"
            by auto
          moreover have "{b} ∪ {c} ∈ τ"
            using assms(1) assms(3) assms(4) topological_space.union[of "{a, b, c}" "τ" "{{b}, {c}}"]
            by simp
          ultimately show ?thesis
            by auto
        qed
        moreover have "x = {a, b, c} ⟹ x ∈ τ"
          using assms(1) topological_space.univ 
          by auto
        ultimately show ?thesis
          using ‹x = {} ∨ x = {a} ∨ x = {b} ∨ x = {c} ∨ x = {a, b} ∨ x = {a, c} ∨ x = {b, c} ∨ x = {a, b, c}› 
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
  assumes "topological_space X τ"
    and "⋀x. x ∈ X ⟹ {x} ∈ τ"
  shows "discrete_topological_space X τ"
proof-
  have "τ = {Y. Y ⊆ X}"
  proof
    show "τ ⊆ {Y. Y ⊆ X}"
      by (metis CollectI assms(1) subsetI topological_space_def)
  next
    show "{Y. Y ⊆ X} ⊆ τ"
    proof
      fix Z
      assume "Z ∈ {Y. Y ⊆ X}"
      then have "Z ⊆ X"
        by simp
      then have "Z = ⋃ {{x} | x. x ∈ Z}"
        by (simp add: Setcompr_eq_image)
      then show "Z ∈ τ"
      proof-
        assume "Z = ⋃ {{x} |x. x ∈ Z}"
        then have "Z = ⋃ {{x} | x. x ∈ Z ∧ x ∈ X}"
          using ‹Z ⊆ X›
          by auto
        have " {{x} | x. x ∈ Z ∧ x ∈ X} ⊆ τ"
          using assms(2)
          by auto
        have "⋃ {{x} | x. x ∈ Z ∧ x ∈ X} ∈ τ"
          using assms(1) topological_space.union[of "X" "τ" "{Z}"] 
                ‹{{x} | x. x ∈ Z ∧ x ∈ X} ⊆ τ›
          by (metis (no_types, lifting) Union_empty topological_space.empty topological_space.union)
        then show ?thesis
          using ‹Z = ⋃ {{x} | x. x ∈ Z ∧ x ∈ X}›
          by simp
      qed
    qed
  qed
  then show ?thesis
    by (simp add: discrete_topological_space_def)
qed
