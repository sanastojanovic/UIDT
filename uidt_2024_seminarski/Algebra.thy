theory Algebra
  imports Main

begin

locale Semigroup =
  fixes A and op (infixl "\<cdot>" 100)
  assumes closed [intro, simp]: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A"
      and associative [intro]: "\<lbrakk> a \<in> A; b \<in> A; c \<in> A \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"

locale Semilattice = Semigroup A "(\<sqinter>)" for A and meet (infixl "\<sqinter>" 100) +
  assumes commutative [intro]: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> b = b \<sqinter> a"
      and idempotent [intro, simp]: "a \<in> A \<Longrightarrow> a \<sqinter> a = a"

locale Lattice = meet_semilattice: Semilattice A "(\<sqinter>)" 
               + join_semilattice: Semilattice A "(\<squnion>)"
  for A and meet (infixl "\<sqinter>" 100) and join (infixl "\<squnion>" 100) +
  assumes absorption_law [intro, simp]: 
    "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> (a \<squnion> b) = a"
    "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<squnion> (a \<sqinter> b) = a"
begin

definition leq (infixl "\<sqsubseteq>" 95) where "a \<sqsubseteq> b \<equiv> a \<squnion> b = b"
definition le (infixl "\<sqsubset>" 95) where "a \<sqsubset> b \<equiv> a \<sqsubseteq> b \<and> a \<noteq> b"

definition ub where "ub u H \<equiv> H \<subseteq> A \<and> (\<forall> h \<in> H. h \<sqsubseteq> u)"
definition lb where "lb l H \<equiv> H \<subseteq> A \<and> (\<forall> h \<in> H. l \<sqsubseteq> h)"

definition lub where "lub u H \<equiv> ub u H \<and> (\<forall> h \<in> H. ub h H \<longrightarrow> u \<sqsubseteq> h)"
definition glb where "glb l H \<equiv> lb l H \<and> (\<forall> h \<in> H. lb h H \<longrightarrow> h \<sqsubseteq> l)"

lemma leq_relf [simp]: "a \<in> A \<Longrightarrow> a \<sqsubseteq> a"
  unfolding leq_def by simp

lemma leq_antisymm [simp]: "\<lbrakk> a \<in> A; b \<in> A; a \<sqsubseteq> b; b \<sqsubseteq> a \<rbrakk> \<Longrightarrow> a = b"
  unfolding leq_def
proof -
  assume "a \<in> A" "b \<in> A" "a \<squnion> b = b" "b \<squnion> a = a"
  have "a = b \<squnion> a" 
    using \<open>b \<squnion> a = a\<close> by simp
  also have "... = a \<squnion> b" using \<open>a \<in> A\<close> \<open>b \<in> A\<close>
    using join_semilattice.commutative[OF \<open>a \<in> A\<close> \<open>b \<in> A\<close>] by simp
  also have "... = b" 
    using \<open>a \<squnion> b = b\<close> by simp
  finally show "a = b" .
qed

lemma leq_trans [simp]: "\<lbrakk> a \<in> A; b \<in> A; c \<in> A; a \<sqsubseteq> b; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> a \<sqsubseteq> c"
  unfolding leq_def
proof -
  assume "a \<in> A" "b \<in> A" "c \<in> A" "a \<squnion> b = b" "b \<squnion> c = c"
  have "a \<squnion> c = a \<squnion> (b \<squnion> c)" 
    using \<open>b \<squnion> c = c\<close> by simp
  also have "... = (a \<squnion> b) \<squnion> c" 
    using join_semilattice.associative[OF \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>c \<in> A\<close>] by simp
  also have "... = b \<squnion> c" 
    using \<open>a \<squnion> b = b\<close> by simp
  also have "... = c" 
    using \<open>b \<squnion> c = c\<close> by simp
  finally show "a \<squnion> c = c" .
qed

lemma leq_leq_join: "\<lbrakk> a \<in> A; b \<in> A; c \<in> A; a \<sqsubseteq> c; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> a \<squnion> b \<sqsubseteq> c"
  unfolding leq_def
proof -
  assume "a \<in> A" "b \<in> A" "c \<in> A" "a \<squnion> c = c" "b \<squnion> c = c"
  have "a \<squnion> b \<squnion> c = a \<squnion> (b \<squnion> c)"
    using join_semilattice.associative[OF \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>c \<in> A\<close>] by simp
  also have "... = a \<squnion> c" 
    using \<open>b \<squnion> c = c\<close> by simp
  also have "... = c" 
    using \<open>a \<squnion> c = c\<close> by simp
  finally show "a \<squnion> b \<squnion> c = c" .
qed

lemma join_ub_left: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqsubseteq> a \<squnion> b"
  unfolding leq_def
proof -
  assume "a \<in> A" "b \<in> A"
  have "a \<squnion> (a \<squnion> b) = a \<squnion> a \<squnion> b" 
    using join_semilattice.associative[OF \<open>a \<in> A\<close> \<open>a \<in> A\<close> \<open>b \<in> A\<close>] by simp
  also have "... = a \<squnion> b" 
    using \<open>a \<in> A\<close> by simp
  finally show "a \<squnion> (a \<squnion> b) = a \<squnion> b" .
qed

lemma join_ub_right: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> b \<sqsubseteq> a \<squnion> b"
  unfolding leq_def
proof -
  assume "a \<in> A" "b \<in> A"
  have "b \<squnion> (a \<squnion> b) = b \<squnion> (b \<squnion> a)"
    using join_semilattice.commutative[OF \<open>b \<in> A\<close> \<open>a \<in> A\<close>] by simp
  also have "... = b \<squnion> b \<squnion> a" 
    using join_semilattice.associative[OF \<open>b \<in> A\<close> \<open>b \<in> A\<close> \<open>a \<in> A\<close>] by simp
  also have "... = b \<squnion> a" 
    using \<open>b \<in> A\<close> by simp
  also have "... = a \<squnion> b"
    using join_semilattice.commutative[OF \<open>a \<in> A\<close> \<open>b \<in> A\<close>] by simp
  finally show " b \<squnion> (a \<squnion> b) = a \<squnion> b" .
qed

lemma join_ub: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> ub (a \<squnion> b) {a, b}"
  unfolding ub_def
  using join_ub_left[of a b] join_ub_right[of a b]
  by blast

lemma pair_ub: "\<lbrakk> a \<in> A; b \<in> A; ub c {a, b} \<rbrakk> \<Longrightarrow> a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
  unfolding ub_def
  by blast

lemma join_sup: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> lub (a \<squnion> b) {a, b}"
  unfolding lub_def
  using join_ub[of a b] pair_ub leq_leq_join[of a b]
  by blast

lemma join_iff_meet: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> b = a \<squnion> b \<longleftrightarrow> a = a \<sqinter> b"
proof
  assume "a \<in> A" "b \<in> A" "b = a \<squnion> b"
  have "a = a \<sqinter> (a \<squnion> b)" 
    using \<open>a \<in> A\<close> \<open>b \<in> A\<close> by simp
  also have "... = a \<sqinter> b" 
    using \<open>b = a \<squnion> b\<close> by simp
  finally show "a = a \<sqinter> b" .
next
  assume "a \<in> A" "b \<in> A" "a = a \<sqinter> b"
  have "b = b \<squnion> (b \<sqinter> a)" 
    using \<open>a \<in> A\<close> \<open>b \<in> A\<close> by simp
  also have "... = b \<squnion> (a \<sqinter> b)" 
    using meet_semilattice.commutative[OF \<open>a \<in> A\<close> \<open>b \<in> A\<close>] by simp 
  also have "... = b \<squnion> a" 
    using \<open>a = a \<sqinter> b\<close> by simp
  also have "... = a \<squnion> b"
    using join_semilattice.commutative[OF \<open>b \<in> A\<close> \<open>a \<in> A\<close>] by simp
  finally show "b = a \<squnion> b" .
qed

lemma le_not_refl: "x \<in> A \<Longrightarrow> \<not> x \<sqsubset> x"
  unfolding le_def by simp

end

locale Boolean_Algebra = Lattice A "(\<sqinter>)" "(\<squnion>)" 
  for A and conj (infixl "\<sqinter>" 100) and disj (infixl "\<squnion>" 100) + 
  fixes neg ("\<Zcat>")
  assumes distributive_law: 
        "\<lbrakk> a \<in> A; b \<in> A; c \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> (b \<squnion> c) = (a \<sqinter> b) \<squnion> (a \<sqinter> c)"
        "\<lbrakk> a \<in> A; b \<in> A; c \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> (b \<squnion> c) = (a \<sqinter> b) \<squnion> (a \<sqinter> c)"
      and de_morgan_law:
        "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> \<Zcat> (a \<sqinter> b) = \<Zcat> a \<squnion> \<Zcat> b"
        "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> \<Zcat> (a \<squnion> b) = \<Zcat> a \<sqinter> \<Zcat> b"
      and double_neg [intro, simp]: "a \<in> A \<Longrightarrow> \<Zcat> (\<Zcat> a) = a"
      and complementation_law [intro, simp]:
        "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> (\<Zcat> a \<sqinter> a) \<squnion> b = b"
        "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> (\<Zcat> a \<squnion> a) \<sqinter> b = b"

locale Monoid = Semigroup M "(\<cdot>)" for M and op (infixl "\<cdot>" 100) + 
  fixes unit ("\<e>")
  assumes unit_law [intro, simp]: 
        "a \<in> M \<Longrightarrow> a \<cdot> \<e> = a"
        "a \<in> M \<Longrightarrow> \<e> \<cdot> a = a"
begin

definition invertable where "invertable a = (\<exists> b \<in> M. a \<cdot> b = \<e> \<and> b \<cdot> a = \<e>)"
definition inverse where "inverse a = (THE b. b \<in> M \<and> a \<cdot> b = \<e> \<and> b \<cdot> a = \<e>)"

end

locale Group = Monoid G "(\<cdot>)" \<e> for G and op (infixl "\<cdot>" 100) and unit ("\<e>") +
  assumes inverse_law [intro]: "a \<in> G \<Longrightarrow> invertable a"

locale Abelian_Group = Group G "(\<cdot>)" \<e> for G and op (infixl "\<cdot>" 100) and unit ("\<e>") +
  assumes commutative [intro]: "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"

locale Ring = Abelian_Group R "(\<oplus>)" \<zero> + Semigroup R "(\<cdot>)" 
  for R and add (infixl "\<oplus>" 100) and mul (infixl "\<cdot>" 110) and zero ("\<zero>")  +
  assumes distributive_law: 
        "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> (b \<oplus> c) = a \<cdot> c \<oplus> b \<cdot> c"
        "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> (a \<oplus> b) \<cdot> c = a \<cdot> c \<oplus> b \<cdot> c"

end