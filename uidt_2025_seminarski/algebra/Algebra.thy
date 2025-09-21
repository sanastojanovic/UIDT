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

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma meet_leq_left: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> b \<sqsubseteq> a"
  unfolding leq_def
proof-
  assume "a \<in> A" "b \<in> A"
  have "a \<sqinter> b \<in> A"
    using  \<open>a \<in> A\<close> \<open>b \<in> A\<close>
    by simp
  have "(a \<sqinter> b) \<squnion> a = a \<squnion> (a \<sqinter> b)"
    using join_semilattice.commutative[OF \<open>a \<in> A\<close> \<open>a \<sqinter> b \<in> A\<close>] by simp
  also have "... = a"
    using \<open>a \<in> A\<close> \<open>b \<in> A\<close>
    by simp
  finally show "a \<sqinter> b \<squnion> a = a"
    .
qed

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma meet_leq_right: "\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a \<sqinter> b \<sqsubseteq> b"
   unfolding leq_def
proof-
  assume "a \<in> A" "b \<in> A"
  have "a \<sqinter> b \<in> A"
    using  \<open>a \<in> A\<close> \<open>b \<in> A\<close>
    by simp
  have "(a \<sqinter> b) \<squnion> b = b \<squnion> (a \<sqinter> b)"
    using join_semilattice.commutative[OF \<open>b \<in> A\<close> \<open>a \<sqinter> b \<in> A\<close>] by simp
  also have "... = b \<squnion> (b \<sqinter> a)"
    using meet_semilattice.commutative[OF \<open>b \<in> A\<close> \<open>a \<in> A\<close>] by simp
  also have "... = b"
    using \<open>a \<in> A\<close> \<open>b \<in> A\<close>
    by simp
  finally show "a \<sqinter> b \<squnion> b = b"
    .
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

(* mi21098_Marko_Lazarević_DOKAZ *)
lemma sup_equality: "\<lbrakk> s \<in> A; H \<subseteq> A; ub s H \<and> (\<forall> h \<in> A. ub h H \<longrightarrow> s \<sqsubseteq> h)\<rbrakk> \<Longrightarrow> sup H = s"
  unfolding sup_def
proof
  show " \<lbrakk>s \<in> A; H \<subseteq> A; ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h)\<rbrakk>
      \<Longrightarrow> s \<in> A \<and> ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h)"
    by (rule conjI, assumption)
next
  fix sa
  assume "s \<in> A" "H \<subseteq> A" "ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h)" "sa \<in> A \<and> ub sa H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> sa \<sqsubseteq> h)"
  have l1:"lub s H"
    using \<open>H \<subseteq> A\<close> \<open>s \<in> A\<close> \<open>ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h)\<close> by blast
  have l2:"lub sa H"
    using \<open>H \<subseteq> A\<close> \<open>sa \<in> A \<and> ub sa H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> sa \<sqsubseteq> h)\<close> lubI by presburger
  show "sa = s"
    using l1 l2 lub_unique 
       \<open>s \<in> A\<close> \<open>sa \<in> A \<and> ub sa H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> sa \<sqsubseteq> h)\<close> \<open>ub s H \<and> (\<forall>h\<in>A. ub h H \<longrightarrow> s \<sqsubseteq> h)\<close>
  by (metis Lattice.leq_antisymm Lattice_axioms)
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

definition lb where "\<lbrakk> l \<in> A; H \<subseteq> A \<rbrakk> \<Longrightarrow> lb l H \<equiv> \<forall> h \<in> H. l \<sqsubseteq> h"

lemma lbI [intro]: "\<lbrakk> l \<in> A; H \<subseteq> A; \<forall> h \<in> H. l \<sqsubseteq> h \<rbrakk> \<Longrightarrow> lb l H"
  unfolding lb_def by simp

lemma lbE [elim]: "\<lbrakk> l \<in> A; H \<subseteq> A; lb l H; \<And>l. \<lbrakk> \<forall> h \<in> H. l \<sqsubseteq> h \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding lb_def by simp

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma lb_meet:"\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> lb (a \<sqinter> b) {a, b}"
proof
  assume "a \<in> A" "b \<in> A" 
  then show "a \<sqinter> b \<in> A" by simp
next 
  assume "a \<in> A" "b \<in> A" 
  then show "{a, b} \<subseteq> A" by simp
next
  assume "a \<in> A" "b \<in> A" 
  then show " \<forall>h\<in>{a, b}. a \<sqinter> b \<sqsubseteq> h "
  by (metis insert_iff meet_leq_left meet_leq_right singletonD)
qed

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma lb_leq:"\<lbrakk> l \<in> A; H \<subseteq> A; lb l H; a \<in> H \<rbrakk> \<Longrightarrow> l \<sqsubseteq> a"
 unfolding lb_def by simp

definition glb where "glb l H \<equiv> lb l H \<and> (\<forall> h \<in> A. lb h H \<longrightarrow> h \<sqsubseteq> l)"

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma glbI [intro]:"\<lbrakk> l \<in> A; H \<subseteq> A; lb l H; \<forall> h \<in> A. lb h H \<longrightarrow> h \<sqsubseteq> l \<rbrakk> \<Longrightarrow> glb l H"
  unfolding glb_def
  by (rule conjI) assumption

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma glbE [elim]:"\<lbrakk> g \<in> A; H \<subseteq> A; glb g H; \<And>l. \<lbrakk> lb l H \<and> (\<forall> h \<in> A. lb h H \<longrightarrow> h \<sqsubseteq> l) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding glb_def by metis

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma glb_unique:"\<lbrakk> l \<in> A; l' \<in> A; H \<subseteq> A; lb l H \<and> (\<forall> h \<in> A. lb h H \<longrightarrow> h \<sqsubseteq> l); lb l' H \<and> (\<forall> h \<in> A. lb h H \<longrightarrow> h \<sqsubseteq> l')\<rbrakk> \<Longrightarrow> l = l'"
  by (meson Lattice.leq_antisymm Lattice_axioms)

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma glb_meet:"\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> glb (a \<sqinter> b) {a, b}"
proof
  assume "a \<in> A" "b \<in> A"
  then show "a \<sqinter> b \<in> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "{a, b} \<subseteq> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "lb (a \<sqinter> b) {a, b}"
    by (rule lb_meet)
next 
  assume "a \<in> A" "b \<in> A"
  then have 1:"\<forall>h\<in>A. lb h {a, b} \<longrightarrow> h \<sqsubseteq> a"
    by (meson bot.extremum insertI1 insert_subset lb_leq)
  from \<open>a \<in> A\<close> \<open>b \<in> A\<close> have 2:"\<forall>h\<in>A. lb h {a, b} \<longrightarrow> h \<sqsubseteq> b"
    by (metis bot.extremum insertI1 insert_commute insert_subsetI lb_leq)
  from \<open>a \<in> A\<close> \<open>b \<in> A\<close> 1 2 show "\<forall>h\<in>A. lb h {a, b} \<longrightarrow> h \<sqsubseteq> a \<sqinter> b"
    by (metis absorption_law(1) leq_def meet_leq_right meet_semilattice.associative meet_semilattice.closed)
qed

definition inf where "inf H \<equiv> THE i. i \<in> A \<and> lb i H \<and> (\<forall> h \<in> A. glb h H \<longrightarrow> h \<sqsubseteq> i)"

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma inf_equality:"\<lbrakk> i \<in> A; H \<subseteq> A; lb i H \<and> (\<forall> h \<in> A. lb h H \<longrightarrow> h \<sqsubseteq> i)\<rbrakk> \<Longrightarrow> inf H = i"
  unfolding inf_def
proof
  show "\<lbrakk>i \<in> A; H \<subseteq> A; lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)\<rbrakk> \<Longrightarrow> i \<in> A \<and> lb i H \<and> (\<forall>h\<in>A. glb h H \<longrightarrow> h \<sqsubseteq> i)"
    unfolding glb_def
  proof
    assume "i \<in> A" "H \<subseteq> A" "lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)"
    show "i \<in> A"
      using \<open>i \<in> A\<close>
      by simp
  next
    assume "i \<in> A" "H \<subseteq> A" "lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)"
    show "lb i H \<and> (\<forall>h\<in>A. lb h H \<and> (\<forall>ha\<in>A. lb ha H \<longrightarrow> ha \<sqsubseteq> h) \<longrightarrow> h \<sqsubseteq> i)"
    proof
      show "lb i H"
        using \<open>lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)\<close>
        by simp
    next
      show "\<forall>h\<in>A. lb h H \<and> (\<forall>ha\<in>A. lb ha H \<longrightarrow> ha \<sqsubseteq> h) \<longrightarrow> h \<sqsubseteq> i"
        using \<open>lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)\<close> by blast
    qed
  qed
next
  fix ia
  assume "i \<in> A" "H \<subseteq> A" "lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)" "ia \<in> A \<and> lb ia H \<and> (\<forall>h\<in>A. glb h H \<longrightarrow> h \<sqsubseteq> ia)"
  have l1:"ia \<sqsubseteq> i"
    by (simp add: \<open>ia \<in> A \<and> lb ia H \<and> (\<forall>h\<in>A. glb h H \<longrightarrow> h \<sqsubseteq> ia)\<close> \<open>lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)\<close>)
  have l2:"i \<sqsubseteq> ia"
    by (simp add: \<open>i \<in> A\<close> \<open>ia \<in> A \<and> lb ia H \<and> (\<forall>h\<in>A. glb h H \<longrightarrow> h \<sqsubseteq> ia)\<close> \<open>lb i H \<and> (\<forall>h\<in>A. lb h H \<longrightarrow> h \<sqsubseteq> i)\<close> glb_def)
  show "ia = i"
    using l1 l2
    by (simp add: \<open>i \<in> A\<close> \<open>ia \<in> A \<and> lb ia H \<and> (\<forall>h\<in>A. glb h H \<longrightarrow> h \<sqsubseteq> ia)\<close>)
qed

(* mi21098_Marko_Lazarević_FORMULACIJA *)
(* mi21098_Marko_Lazarević_DOKAZ *)
lemma inf_meet:"\<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> inf {a, b} = a \<sqinter> b" 
proof (rule inf_equality)
  assume "a \<in> A" "b \<in> A"
  then show "a \<sqinter> b \<in> A" by simp
next 
  assume "a \<in> A" "b \<in> A"
  then show "{a, b} \<subseteq> A" by simp
next
  assume "a \<in> A" "b \<in> A"
  then show "lb (a \<sqinter> b) {a, b} \<and> (\<forall>h\<in>A. lb h {a, b} \<longrightarrow> h \<sqsubseteq> a \<sqinter> b)"
    using glb_meet[of a b]
    unfolding glb_def
    by - assumption
qed

(*mi20191 Uros Milasinovic FORMULACIJA*)
definition geq (infixl "⊒ " 95) where "a ⊒ b ≡ a ⊔ b = a"

(*mi20191 Uros Milasinovic FORMULACIJA*)
(*mi20191 Uros Milasinovic DOKAZ*)
lemma geq_refl[simp]: "a ∈ A ⟹ a ⊒ a"
  unfolding geq_def by simp


(*mi20191 Uros Milasinovic FORMULACIJA*)
(*mi20191 Uros Milasinovic DOKAZ*)
lemma geq_antisymm [simp]: "⟦ a ∈ A; b ∈ A; a ⊒ b; b ⊒a ⟧ ⟹ a = b"
  unfolding geq_def
proof -
  assume  "a ∈ A" "b ∈ A" "a ⊔ b = a" "b ⊔ a = b"
  have "a = a ⊔ b" using ‹a ⊔ b = a› by simp
  also have "... = b ⊔ a" using ‹a ∈ A› ‹b ∈ A› by (simp add: join_semilattice.commutative)
  also have "... = b" using ‹b ⊔ a = b› by simp
  finally show "a = b".
  qed



(*mi20191 Uros Milasinovic FORMULACIJA*)
(*mi20191 Uros Milasinovic DOKAZ*)
lemma geq_trans [simp]: "⟦ a ∈ A; b ∈ A; c ∈ A; a ⊒ b ; b ⊒ c⟧ ⟹ a ⊒ c"
  unfolding geq_def
proof -
  assume "a ∈ A" " b ∈ A " " c ∈ A " " a ⊔ b = a " " b ⊔ c = b" 
  have "a ⊔ c = (a ⊔ b) ⊔ c" using ‹a ⊔ b = a› by simp
  also have "... = a ⊔ (b ⊔ c)" using join_semilattice.associative[OF ‹a ∈ A› ‹b ∈ A› ‹c ∈ A›] by simp
  also have "... = a ⊔ b" using ‹b ⊔ c = b› by simp
  also have "... = a" using ‹a ⊔ b = a› by simp
  finally show "a ⊔ c = a".
qed


(*mi20191 Uros Milasinovic FORMULACIJA*)
definition ge (infixl "⊐" 95) where "a ⊐ b ≡ a ⊒ b ∧ a ≠ b"

(*mi20191 Uros Milasinovic FORMULACIJA*)
(*mi20191 Uros Milasinovic DOKAZ*)
lemma ge_not_refl: "a ∈ A ⟹ ¬ a ⊐ a"
  unfolding ge_def by simp


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
  assumes unit_closed [intro, simp]: "\<e> \<in> M"
  assumes unit_law [intro, simp]: 
        "a \<in> M \<Longrightarrow> a \<cdot> \<e> = a"
        "a \<in> M \<Longrightarrow> \<e> \<cdot> a = a"
begin

(*mi21227_Jelena_Djuric_FORMULACIJA*)
definition invertable where "a \<in> M \<Longrightarrow> invertable a \<equiv> \<exists>b \<in> M. a \<cdot> b = \<e> \<and> b \<cdot> a = \<e>"


(*mi21227_Jelena_Djuric_FORMULACIJA*)
lemma invertable_intro:
  shows "\<lbrakk> a \<in> M; b \<in> M; a \<cdot> b = \<e>; b \<cdot> a = \<e> \<rbrakk> \<Longrightarrow> invertable a"
  using invertable_def by blast


(*mi21227_Jelena_Djuric_FORMULACIJA*)
lemma invertable_elim :
  shows "\<lbrakk>a \<in> M;  invertable a; \<And>a. \<lbrakk> \<exists>b \<in> M. a \<cdot> b = \<e> \<and> b \<cdot> a = \<e> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
   by (simp add: invertable_def)

(*mi21227_Jelena_Djuric_FORMULACIJA*)

(*mi21227_Jelena_Djuric_FORMULACIJA*)
lemma invertable_unit[simp]:
  shows "invertable \<e>"
proof -
  have "\<e> \<in> M" by simp
  moreover have "\<e> \<cdot> \<e> = \<e>" by simp
  ultimately show ?thesis
  using invertable_def by blast
qed 




(*mi21227_Jelena_Djuric_FORMULACIJA*)
lemma invertable_op[simp]:
  shows "\<lbrakk> a \<in> M; b \<in> M; invertable a; invertable b \<rbrakk> \<Longrightarrow> invertable (a \<cdot> b)"
  proof -
  assume "a \<in> M" "b \<in> M" "invertable a" "invertable b"
  then obtain a_inv b_inv where
    "a_inv \<in> M" "a \<cdot> a_inv = \<e>" "a_inv \<cdot> a = \<e>"
    "b_inv \<in> M" "b \<cdot> b_inv = \<e>" "b_inv \<cdot> b = \<e>"
    by (auto simp: invertable_def)
  moreover have "(a \<cdot> b) \<cdot> (b_inv \<cdot> a_inv) = a \<cdot> (b \<cdot> b_inv) \<cdot> a_inv"
  by (simp add: \<open>a \<in> M\<close> \<open>b \<in> M\<close> associative calculation(1) calculation(4))
  moreover have "(b_inv \<cdot> a_inv) \<cdot> (a \<cdot> b) = b_inv \<cdot> (a_inv \<cdot> a) \<cdot> b"
  by (simp add: \<open>a \<in> M\<close> \<open>b \<in> M\<close> associative calculation(1) calculation(4))
  ultimately show "invertable (a \<cdot> b)"
    unfolding invertable_def
  by (metis \<open>a \<in> M\<close> \<open>b \<in> M\<close> closed invertable_intro unit_law(1))
qed


(*mi20191 Uros Milasinovic FORMULACIJA*)
(*mi20191 Uros Milasinovic DOKAZ*)
lemma inverse_unique: "⟦a ∈ M; g1 ∈ M; g2 ∈ M; a ⋅ g1 = 𝖾; g1 ⋅ a = 𝖾; a ⋅ g2 = 𝖾; g2 ⋅ a = 𝖾⟧ ⟹ g1 = g2 "
proof -
  assume "a ∈ M" "g1 ∈ M" "g2 ∈ M" "a ⋅ g1 = 𝖾" "g1 ⋅ a = 𝖾" "a ⋅ g2 = 𝖾" "g2 ⋅ a = 𝖾"
  have "𝖾 = a ⋅ g2" using ‹a ⋅ g2 = 𝖾› by simp
  have "g1 = g1 ⋅ 𝖾" using ‹g1 ∈ M› by simp
  also  have "... = g1 ⋅ a ⋅ g2" using  ‹𝖾 = a ⋅ g2› ‹a ∈ M›‹g1 ∈ M›‹g2 ∈ M› by (simp add: associative)
  also have "... = 𝖾 ⋅ g2" using ‹g1 ⋅ a = 𝖾› by simp
  also have "... = g2" using ‹g2 ∈ M› by simp
  finally show "g1 = g2" by simp
qed

(*mi20191 Uros Milasinovic FORMULACIJA*)
definition inverse where "a ∈ M ⟹ inverse a ≡ THE a_inv. a_inv ∈ M  ∧ a ⋅ a_inv = 𝖾 ∧ a_inv ⋅ a = 𝖾"


(*mi20191 Uros Milasinovic FORMULACIJA*)
(*mi20191 Uros Milasinovic DOKAZ*)
lemma inverse_equality: "⟦a ∈ M; a_inv ∈ M  ; a ⋅ a_inv = 𝖾 ; a_inv ⋅ a = 𝖾⟧ ⟹ inverse a = a_inv"
  unfolding inverse_def
proof 
  show " ⟦a ∈ M ; a_inv ∈ M ; a ⋅ a_inv = 𝖾 ; a_inv ⋅ a = 𝖾⟧
      ⟹ a_inv ∈ M ∧ a ⋅ a_inv = 𝖾 ∧ a_inv ⋅ a = 𝖾"
  proof
    assume "a ∈ M "" a_inv ∈ M"" a ⋅ a_inv = 𝖾"" a_inv ⋅ a = 𝖾"
    show "a_inv ∈ M"
      using ‹a_inv ∈ M› by simp
  next
    assume "a ∈ M "" a_inv ∈ M"" a ⋅ a_inv = 𝖾"" a_inv ⋅ a = 𝖾"
    show " a ⋅ a_inv = 𝖾 ∧ a_inv ⋅ a = 𝖾"
    proof
      show "a ⋅ a_inv = 𝖾"
        using ‹a ⋅ a_inv = 𝖾› by simp
    next
      show "a_inv ⋅ a = 𝖾"
        using ‹a_inv ⋅ a = 𝖾› by simp
    qed
  qed
  fix a_inva
  assume "a ∈ M "" a_inv ∈ M"" a ⋅ a_inv = 𝖾"" a_inv ⋅ a = 𝖾" "a_inva ∈ M ∧ a ⋅ a_inva = 𝖾 ∧ a_inva ⋅ a = 𝖾"
  have "a_inva ∈ M"    using ‹a_inva ∈ M ∧ a ⋅ a_inva = 𝖾 ∧ a_inva ⋅ a = 𝖾› by simp
  have "a ⋅ a_inva = 𝖾" using ‹a_inva ∈ M ∧ a ⋅ a_inva = 𝖾 ∧ a_inva ⋅ a = 𝖾› by simp
  have "a_inva ⋅ a = 𝖾" using ‹a_inva ∈ M ∧ a ⋅ a_inva = 𝖾 ∧ a_inva ⋅ a = 𝖾› by simp
  show "a_inva = a_inv" using ‹a ∈ M› ‹a_inva ∈ M› ‹a_inv ∈ M›
      ‹a ⋅ a_inva = 𝖾› ‹a_inva ⋅ a = 𝖾› ‹a ⋅ a_inv = 𝖾› ‹a_inv ⋅ a = 𝖾›
    inverse_unique by blast
qed

(*mi20191 Uros Milasinovic FORMULACIJA*)
lemma inverse_closed: "⟦a ∈ M;  invertable a ⟧ ⟹ inverse a ∈ M"
(*<*) sorry (*>*)


(*mi20191 Uros Milasinovic FORMULACIJA*)
(*mi20191 Uros Milasinovic DOKAZ*)
lemma inverse_unit: "inverse 𝖾 = 𝖾"
  by (simp add: inverse_equality)


(*mi19089_Ivana_Ivaneza_FORMULACIJA*)
(*mi21061_Marko_Koprivica DOKAZ*)
lemma inverse_left: "⟦ a ∈ M; invertable a ⟧ ⟹ (inverse a) ⋅ a = 𝖾"
proof-
  assume "a ∈ M" "invertable a"
  then obtain a_inv where "a_inv ∈ M" "a ⋅ a_inv = 𝖾" "a_inv ⋅ a = 𝖾"
    by (auto simp: invertable_def)
  then have "inverse a = a_inv"
    using ‹a ∈ M›
    by (simp add: Monoid.inverse_equality Monoid_axioms)
  then show ?thesis
    using ‹a_inv ⋅ a = 𝖾›
    by simp
qed


(*mi19089_Ivana_Ivaneza_FORMULACJIJA*)
(*mi21061_Marko_Koprivica DOKAZ*)
lemma inverse_right: "⟦ a ∈ M; invertable a ⟧ ⟹ a ⋅ (inverse a) = 𝖾"
proof-
  assume "a ∈ M" "invertable a"
  then obtain a_inv where "a_inv ∈ M" "a ⋅ a_inv = 𝖾" "a_inv ⋅ a = 𝖾"
    by (auto simp: invertable_def)
  then have "inverse a = a_inv"
    using ‹a ∈ M›
    by (simp add: Monoid.inverse_equality Monoid_axioms)
  then show ?thesis
    using ‹a ⋅ a_inv = 𝖾›
    by simp
qed

(*mi19089_Ivana_Ivaneza_FORMULACJIJA*)
(*mi21061_Marko_Koprivica DOKAZ*)
lemma inverse_invertable:  "⟦ a ∈ M; invertable a ⟧ ⟹ invertable (inverse a)"
  by (simp add: inverse_closed inverse_left inverse_right invertable_intro)

(*mi19089_Ivana_Ivaneza_FORMULACIJA*)
(*mi21061_Marko_Koprivica DOKAZ*)
lemma inverse_inverse_id: "⟦ a ∈ M; invertable a ⟧ ⟹ inverse (inverse a) = a"
  by (simp add: inverse_closed inverse_equality inverse_left inverse_right)

(*mi19089_Ivana_Ivaneza_FORMULACIJA*)
(*mi21061_Marko_Koprivica DOKAZ*)
lemma inverse_op: "⟦ a ∈ M; b ∈ M; invertable a; invertable b ⟧ ⟹
          inverse (a ⋅ b) = (inverse b) ⋅ (inverse a)"
proof-
  assume "a ∈ M" "b ∈ M" "invertable a" "invertable b"
  obtain a_inv b_inv
    where "a_inv ∈ M" "a_inv ⋅ a = 𝖾" "a ⋅ a_inv = 𝖾"
          "b_inv ∈ M" "b_inv ⋅ b = 𝖾" "b ⋅ b_inv = 𝖾"
    using ‹a ∈ M› ‹invertable a› ‹b ∈ M› ‹invertable b›
    by (auto simp: invertable_def)

  have "a_inv = inverse a"
    using ‹a ∈ M› ‹a_inv ∈ M› ‹a_inv ⋅ a = 𝖾› ‹a ⋅ a_inv = 𝖾›
    by (simp add: Monoid.inverse_equality Monoid_axioms)
  have "b_inv = inverse b"
    using ‹b ∈ M› ‹b_inv ∈ M› ‹b_inv ⋅ b = 𝖾› ‹b ⋅ b_inv = 𝖾›
    by (simp add: Monoid.inverse_equality Monoid_axioms)

  have "(a ⋅ b) ⋅ (inverse b ⋅ inverse a) = 𝖾"
  proof-
    have "(a ⋅ b) ⋅ (inverse b ⋅ inverse a) = (a ⋅ b) ⋅ (b_inv ⋅ a_inv)"
      using ‹a_inv = inverse a› ‹b_inv = inverse b›
      by simp
    also have "... = a ⋅ b ⋅ b_inv ⋅ a_inv"
      by (simp add: ‹a ∈ M› ‹a_inv ∈ M› ‹b ∈ M› ‹b_inv ∈ M› associative)
    also have "... = 𝖾"
      by (simp add: ‹a ⋅ a_inv = 𝖾› ‹a ∈ M› ‹b ⋅ b_inv = 𝖾› ‹b ∈ M› ‹b_inv ∈ M› associative)
    finally show ?thesis
      .
  qed
  moreover have "(inverse b ⋅ inverse a) ⋅ (a ⋅ b) = 𝖾"
  proof-
    have "(inverse b ⋅ inverse a) ⋅ (a ⋅ b) = (b_inv ⋅ a_inv) ⋅ (a ⋅ b)"
      using ‹a_inv = inverse a› ‹b_inv = inverse b›
      by simp
    also have "... = b_inv ⋅ a_inv ⋅ a ⋅ b "
      by (simp add: ‹a ∈ M› ‹a_inv ∈ M› ‹b ∈ M› ‹b_inv ∈ M› associative)
    also have "... = 𝖾"
      by (simp add: ‹a ∈ M› ‹a_inv ⋅ a = 𝖾› ‹a_inv ∈ M› ‹b_inv ⋅ b = 𝖾› ‹b_inv ∈ M› associative)
    finally show ?thesis
      .
  qed
  moreover have "inverse b ⋅ inverse a ∈ M"
    by (simp add: ‹a ∈ M› ‹b ∈ M› ‹invertable a› ‹invertable b› inverse_closed)
  ultimately show ?thesis
    by (meson ‹a ∈ M› ‹b ∈ M› closed inverse_equality)
qed

end

locale Group = Monoid G "(\<cdot>)" \<e> for G and op (infixl "\<cdot>" 100) and unit ("\<e>") +
  assumes inverse_law [intro]: "a \<in> G \<Longrightarrow> invertable a"
begin


(*mi19172_Nikolina_Pejovic_FORMULACIJA*)
lemma right_cancel: "⟦a \<cdot> x = b \<cdot> x; a ∈ G; b ∈ G; x ∈ G⟧ \<Longrightarrow> a = b"
  sorry

(*mi19172_Nikolina_Pejovic_FORMULACIJA*)
lemma left_cancel: "⟦x \<cdot> a = x \<cdot> b; x ∈ G; a ∈ G; b ∈ G⟧ \<Longrightarrow> a = b"
  sorry


(*mi19172_Nikolina_Pejovic_FORMULACIJA*)
primrec pow_pos :: "'a ⇒ nat ⇒ 'a" where
  "pow_pos g 0 = \<e>"
| "pow_pos g (Suc n) = g \<cdot> pow_pos g n"

(*mi19172_Nikolina_Pejovic_FORMULACIJA*)
primrec pow_neg :: "'a ⇒ nat ⇒ 'a" where
  "pow_neg g 0 = \<e>"
| "pow_neg g (Suc n) = inverse g \<cdot> pow_neg g n"

(*mi19172_Nikolina_Pejovic_FORMULACIJA*)
fun pow :: "'a \<Rightarrow> int \<Rightarrow> 'a" where
"pow g n = (if n \<le> 0 then pow_neg g (nat (n)) else pow_pos g (nat (n)))"

(*mi19172_Nikolina_Pejovic_FORMULACIJA*)
lemma pow_sum: "⟦g ∈ G⟧ \<Longrightarrow> pow g n \<cdot> pow g m = pow g (n + m)"
  sorry

(*mi18044_Aleksa_Kostur_FORMULACIJA*)
lemma pow_pow:  "⟦g ∈ G⟧ ⟹ pow (pow g  n) m = pow g (n * m)"
(*<*) sorry (*>*)

(*mi18044_Aleksa_Kostur_FORMULACIJA*)
lemma pow_op: "⟦g ∈ G⟧ ⟹ pow (g \<cdot> h) n = pow (inverse h \<cdot> inverse g) (-n)"
(*<*) sorry (*>*)


(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma pow_center:
  fixes a b :: 'a and n :: int
  assumes "a \<in> G" "b \<in> G"
  shows "(a \<cdot> pow b n) \<cdot> inverse a = pow (a \<cdot> b \<cdot> inverse a) n"
  sorry

(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma squared_unit_compute:
  fixes a b :: 'a
  assumes "a \<in> G" "b \<in> G" "a \<cdot> a = e" "a \<cdot> b \<cdot> a = b"
  shows "a \<cdot> b = b \<cdot> a"
  sorry

(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma squared_comp_compute:
  fixes a b :: 'a
  assumes "a \<in> G" "b \<in> G"
      and "(a \<cdot> b) \<cdot> (a \<cdot> b) = (a \<cdot> a) \<cdot> (b \<cdot> b)"
  shows "a \<cdot> b = b \<cdot> a"
  sorry

end

(*mi18044_Aleksa_Kostur_FORMULACIJA*)
locale Submonoid = Monoid M "(\<cdot>)" \<e> for M and op (infixl "\<cdot>" 100) and unit ("\<e>") +
  fixes H :: "'a set"
  assumes submonoid_subset: "H ⊆ M"
  and submonoid_closed: "⟦ x ∈ H; y ∈ H ⟧ ⟹ x \<cdot> y ∈ H"
  and submonoid_unit: "\<e> ∈ H"
begin

(*mi18044_Aleksa_Kostur_FORMULACIJA*)
lemma invertable_closed: "⟦x ∈ H; invertable x⟧ ⟹ inverse x ∈ H"
(*<*) sorry (*>*)

(*mi18044_Aleksa_Kostur_FORMULACIJA*)
lemma inverse_closed: "⟦x ∈ H; invertable x⟧ ⟹ inverse (inverse x) = x"
(*<*) sorry (*>*)

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

(*mi21061_Marko_Koprivica_FORMULACIJA*)
locale Subgroup = Group G "(⋅)" 𝖾 + Submonoid G "(⋅)" 𝖾 H
  for G and op (infixl "⋅" 100) and unit ("𝖾") and H
begin
end

context Monoid 
begin
(*mi21061_Marko_Koprivica_FORMULACIJA*)
lemma subgroup_intro:
  shows "⟦H ⊆ G; Group G op 𝖾; 𝖾 ∈ H; ⋀ x. x ∈ H ⟹ invertable x ∧ inverse x ∈ H;⋀ x y. x ∈ H ∧ y ∈ H ⟹ op x y ∈ H⟧ 
        ⟹ Subgroup G op 𝖾 H"
  sorry

(*mi21061_Marko_Koprivica_FORMULACIJA*)
lemma subgroup_alt:
  shows "⟦H ⊆ G; H ≠ {}; Group G op 𝖾; ⋀ g h. g ∈ H ∧ h ∈ H ⟹ op g (inverse h) ∈ H⟧ 
        ⟹ Subgroup G op 𝖾 H"
  sorry
end

(*mi21061_Marko_Koprivica_FORMULACIJA*)
lemma subgroup_intersect:
  assumes "Subgroup G op 𝖾 H"
  and "Subgroup G op 𝖾 T"
shows "Subgroup G op 𝖾 (H ∩ T)"
  sorry

(*mi21061_Marko_Koprivica_FORMULACIJA*)
lemma subgroup_transitive:
  assumes "Subgroup G op 𝖾 H"
  and "Subgroup H op 𝖾 T"
shows "Subgroup G op 𝖾 T"
  sorry

consts ipow :: "'a ⇒ int ⇒ 'a" (infixr "[^]" 80)

(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma subgroup_of_cyclic_is_cyclic:
  fixes H :: "'a set"
  assumes "\<exists> a \<in> G. {x. x \<in> G ∧ (\<exists>k::int. x = a [^] k)} = G"
  assumes "Subgroup G op e H"
  shows   "\<exists>  b \<in> H. H = {x. x ∈ G ∧ (\<exists> k::int. x = b [^] k)}"
  sorry 

(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma pow_eq_e_iff_dvd:
  fixes a :: 'a and n :: nat and k :: int
  assumes "finite G"
      and "card G = n"
      and "a \<in> G"
      and "{x. x \<in> G ∧ (\<exists>t::int. x = a [^] t)} = G"
  shows "a [^] k = e \<longleftrightarrow> n dvd nat (abs k)"
  sorry

(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma order_of_power_in_cyclic:
  fixes a b :: 'a and n :: nat and k :: int
  assumes "finite G"
      and "card G = n"
      and "a \<in> G"
      and "{x. x \<in> G ∧ (\<exists>t::int. x = a [^] t)} = G"
      and "b = a [^] k"
  shows "(LEAST m. m>0 ∧ b [^] (int m) = e) = n div gcd (nat (abs k)) n"
  sorry

(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma generators_in_cyclic_by_gcd:
  fixes a :: 'a and r :: int and n :: nat
  assumes "finite G"
      and "card G = n"
      and "a \<in> G"
      and "{x. x \<in> G ∧ (\<exists>t::int. x = a [^] t)} = G"
  shows "{x. x \<in> G ∧ (\<exists>t::int. x = (a [^] r) [^] t)} = G \<longleftrightarrow> gcd (nat (abs r)) n = 1"
  sorry

(*mi20159_Natasa_Blagojevic_FORMULACIJA*)
lemma subgroups_of_int_are_nZ:
  fixes H :: "int set"
  shows "((0 \<in> H) \<and> (\<forall>x\<in>H. -x \<in> H) \<and> (\<forall>x\<in>H. \<forall>y\<in>H. x + y \<in> H))
         \<longleftrightarrow> (\<exists>n::nat. H = { x. \<exists>k::int. x = int n * k })"
  sorry










end
