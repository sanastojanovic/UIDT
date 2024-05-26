theory Algebra
  imports Main

begin

locale Semigroup =
  fixes A and op (infixl "\<cdot>" 100)
  assumes closed [intro, simp]: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A"
      and associative [intro]: "\<lbrakk> a \<in> A; b \<in> A; c \<in> A \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"
begin
end

locale Semilattice = Semigroup A "(\<sqinter>)" for A and meet (infixl "\<sqinter>" 100) +
  assumes commutative [intro]: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> b = b \<sqinter> a"
      and idempotent [intro, simp]: "a \<in> A \<Longrightarrow> a \<sqinter> a = a"
begin
end

locale Lattice = meet_semilattice: Semilattice A "(\<sqinter>)" 
               + join_semilattice: Semilattice A "(\<squnion>)"
  for A and meet (infixl "\<sqinter>" 100) and join (infixl "\<squnion>" 100) +
  assumes absorption_law [intro, simp]: 
    "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> (a \<squnion> b) = a"
    "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<squnion> (a \<sqinter> b) = a"
begin

definition leq (infixl "\<sqsubseteq>" 95) where "a \<sqsubseteq> b \<equiv> a \<squnion> b = b"

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

lemma leq_join_left: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqsubseteq> a \<squnion> b"
  unfolding leq_def
proof -
  assume "a \<in> A" "b \<in> A"
  have "a \<squnion> (a \<squnion> b) = a \<squnion> a \<squnion> b" 
    using join_semilattice.associative[OF \<open>a \<in> A\<close> \<open>a \<in> A\<close> \<open>b \<in> A\<close>] by simp
  also have "... = a \<squnion> b" 
    using \<open>a \<in> A\<close> by simp
  finally show "a \<squnion> (a \<squnion> b) = a \<squnion> b" .
qed

lemma leq_join_right: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> b \<sqsubseteq> a \<squnion> b"
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

definition le (infixl "\<sqsubset>" 95) where "a \<sqsubset> b \<equiv> a \<sqsubseteq> b \<and> a \<noteq> b"

lemma le_not_refl: "x \<in> A \<Longrightarrow> \<not> x \<sqsubset> x"
  unfolding le_def by simp

definition ub where "\<lbrakk> u \<in> A; H \<subseteq> A \<rbrakk> \<Longrightarrow> ub u H \<equiv> \<forall> h \<in> H. h \<sqsubseteq> u"

lemma ubI [intro]: "\<lbrakk> u \<in> A; H \<subseteq> A; \<forall> h \<in> H. h \<sqsubseteq> u \<rbrakk> \<Longrightarrow> ub u H"
  unfolding ub_def by simp

lemma ubE [elim]: "\<lbrakk> u \<in> A; H \<subseteq> A; ub u H; \<And>u. \<lbrakk> \<forall> h \<in> H. h \<sqsubseteq> u \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding ub_def by simp

lemma ub_join: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> ub (a \<squnion> b) {a, b}"
proof
  assume "a \<in> A" "b \<in> A" 
  then show "a \<squnion> b \<in> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "{a, b} \<subseteq> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "\<forall>h\<in>{a, b}. h \<sqsubseteq> a \<squnion> b"
    by (metis empty_iff insert_iff leq_join_left leq_join_right)
qed

lemma ub_leq: "\<lbrakk> u \<in> A; H \<subseteq> A; ub u H; a \<in> H \<rbrakk> \<Longrightarrow> a \<sqsubseteq> u"
  unfolding ub_def by auto

definition lub where "lub u H \<equiv> ub u H \<and> (\<forall> h \<in> A. ub h H \<longrightarrow> u \<sqsubseteq> h)"

lemma lubI [intro]: "\<lbrakk> u \<in> A; H \<subseteq> A; ub u H; \<forall> h \<in> A. ub h H \<longrightarrow> u \<sqsubseteq> h \<rbrakk> \<Longrightarrow> lub u H"
  unfolding lub_def
  by (rule conjI) assumption

lemma lubE [elim]: "\<lbrakk> l \<in> A; H \<subseteq> A; lub u H; \<And>u. \<lbrakk> ub u H \<and> (\<forall> h \<in> A. ub h H \<longrightarrow> u \<sqsubseteq> h) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding lub_def by simp

lemma lub_unique: "\<lbrakk> u \<in> A; u' \<in> A; H \<subseteq> A; ub u H \<and> (\<forall> h \<in> A. ub h H \<longrightarrow> u \<sqsubseteq> h); ub u' H \<and> (\<forall> h \<in> A. ub h H \<longrightarrow> u' \<sqsubseteq> h) \<rbrakk> \<Longrightarrow> u = u'"
  by (metis Semilattice.commutative join_semilattice.Semilattice_axioms leq_def)

lemma lub_join: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> lub (a \<squnion> b) {a, b}"
proof
  assume "a \<in> A" "b \<in> A"
  then show "a \<squnion> b \<in> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "{a, b} \<subseteq> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "ub (a \<squnion> b) {a, b}" by (rule ub_join)
next
  assume "a \<in> A" "b \<in> A"
  then have 1: "\<forall>h\<in>A. ub h {a, b} \<longrightarrow> a \<sqsubseteq> h" 
    by (meson ub_leq Lattice_axioms bot.extremum insertI1 insert_subsetI)
  from \<open>a \<in> A\<close> \<open>b \<in> A\<close> have 2: "\<forall>h\<in>A. ub h {a, b} \<longrightarrow> b \<sqsubseteq> h"
    by (meson empty_subsetI insertCI insert_subsetI ub_leq)
  from \<open>a \<in> A\<close> \<open>b \<in> A\<close> 1 2 show "\<forall>h\<in>A. ub h {a, b} \<longrightarrow> a \<squnion> b \<sqsubseteq> h"
    by (meson leq_leq_join)
qed

definition sup where "sup H \<equiv> THE s. s \<in> A \<and> ub s H \<and> (\<forall> h \<in> A. ub h H \<longrightarrow> s \<sqsubseteq> h)"

lemma sup_equality: "\<lbrakk> s \<in> A; H \<subseteq> A; ub s H \<and> (\<forall> h \<in> A. ub h H \<longrightarrow> s \<sqsubseteq> h)\<rbrakk> \<Longrightarrow> sup H = s"
  unfolding sup_def
proof
  show " \<lbrakk>s \<in> A; H \<subseteq> A; ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h)\<rbrakk>
      \<Longrightarrow> s \<in> A \<and> ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h)"
    by (rule conjI, assumption)
next
  fix sa
  show " \<lbrakk>s \<in> A; H \<subseteq> A; ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h);
           sa \<in> A \<and> ub sa H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> sa \<sqsubseteq> h)\<rbrakk>
          \<Longrightarrow> sa = s"
(* sredi ovo *)
    apply (erule conjE) back
    apply (rule lub_unique)
        apply assumption +
    done
qed

lemma sup_join: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> sup {a, b} = a \<squnion> b"
proof (rule sup_equality)
  assume "a \<in> A" "b \<in> A"
  then show "a \<squnion> b \<in> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "{a, b} \<subseteq> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "ub (a \<squnion> b) {a, b} \<and> (\<forall>h\<in>A. ub h {a, b} \<longrightarrow> a \<squnion> b \<sqsubseteq> h)"
    using lub_join[of a b]
    unfolding lub_def
    by - assumption
qed

definition lb where "\<lbrakk> u \<in> A; H \<subseteq> A \<rbrakk> \<Longrightarrow> lb l H \<equiv> \<forall> h \<in> H. l \<sqsubseteq> h"

lemma lbI [intro]: "\<lbrakk> l \<in> A; H \<subseteq> A; \<forall> h \<in> H. l \<sqsubseteq> h \<rbrakk> \<Longrightarrow> lb l H"
  unfolding lb_def by simp

lemma lbE [elim]: "\<lbrakk> l \<in> A; H \<subseteq> A; lb l H; \<And>l. \<lbrakk> \<forall> h \<in> H. l \<sqsubseteq> h \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding lb_def by simp

definition glb where "glb l H \<equiv> lb l H \<and> (\<forall> h \<in> A. lb h H \<longrightarrow> h \<sqsubseteq> l)"

definition inf where "inf H \<equiv> THE i. lb i H \<and> (\<forall> h \<in> A. glb h H \<longrightarrow> h \<sqsubseteq> i)"

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
begin
end

locale Monoid = Semigroup M "(\<cdot>)" for M and op (infixl "\<cdot>" 100) + 
  fixes unit ("\<e>")
  assumes unit_law [intro, simp]: 
        "a \<in> M \<Longrightarrow> a \<cdot> \<e> = a"
        "a \<in> M \<Longrightarrow> \<e> \<cdot> a = a"
begin
end

locale Group = Monoid G "(\<cdot>)" \<e> for G and op (infixl "\<cdot>" 100) and unit ("\<e>") +
  assumes inverse_law [intro]: "a \<in> G \<Longrightarrow> invertable a"
begin
end

locale Abelian_Group = Group G "(\<cdot>)" \<e> for G and op (infixl "\<cdot>" 100) and unit ("\<e>") +
  assumes commutative [intro]: "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"
begin
end

locale Ring = Abelian_Group R "(\<oplus>)" \<zero> + Semigroup R "(\<cdot>)" 
  for R and add (infixl "\<oplus>" 100) and mul (infixl "\<cdot>" 110) and zero ("\<zero>")  +
  assumes distributive_law: 
        "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> (b \<oplus> c) = a \<cdot> c \<oplus> b \<cdot> c"
        "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> (a \<oplus> b) \<cdot> c = a \<cdot> c \<oplus> b \<cdot> c"
begin
end

end