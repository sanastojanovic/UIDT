theory GeoOrder
imports GeoIncidence
begin

chapter \<open>Order\<close>

section \<open>Axioms of Order\<close>

locale GeometryOrder = GeometryIncidence +
    fixes bet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* Given points a, b, and c, if b between a and c then \<open>bet a b c\<close>.*)
  assumes ax_ord_1: "\<And> a b c. bet a b c \<Longrightarrow> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> colinear a b c"
      and ax_ord_2: "\<And> a b c. bet a b c \<Longrightarrow> bet c b a"
      and ax_ord_3: "\<And> a b c. bet a b c \<Longrightarrow> \<not> bet a c b"
      and ax_ord_4: "\<And> a b. a \<noteq> b \<Longrightarrow> (\<exists> c. bet a b c)"
      and ax_ord_5: "\<And> a b c. \<lbrakk>a \<noteq> b; b \<noteq> c; a \<noteq> c; colinear a b c\<rbrakk> \<Longrightarrow> bet a b c \<or> bet b c a \<or> bet c a b"
      and ax_Pasch: "\<And> a b c l. \<lbrakk>\<not> colinear a b c; inc_l_pl l (plane a b c); \<not> inc_p_l a l; 
                                 bet b (intersection_l_l l (line b c)) c\<rbrakk> \<Longrightarrow> 
                                 (bet c (intersection_l_l l (line c a)) a) \<or> 
                                 (bet a (intersection_l_l l (line a b)) b)"
begin

section \<open>Consequences of axioms of order\<close>

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>one_of_two a b\<close> is true if exactly one of a b is true - this is XOR operation *)
definition one_of_two :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "one_of_two P1 P2 \<longleftrightarrow> (P1 \<and> \<not>P2) \<or> (\<not>P1 \<and> P2)"

lemma "one_of_two P1 P2 \<longleftrightarrow> P1 \<noteq> P2"
  by (auto simp add: one_of_two_def)

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* \<open>one_of_tree\<close> \<rightarrow> exatly one of three propositions is true*)
definition one_of_three where
  "one_of_three P1 P2 P3 \<equiv> (P1 \<and> \<not> P2 \<and> \<not> P3) \<or> (\<not> P1 \<and> P2 \<and> \<not> P3) \<or> (\<not> P1 \<and> \<not> P2 \<and> P3)"

(* one of the three points is between the other two *)
definition bet' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "bet' a b c \<equiv> one_of_three (bet a b c) (bet b c a) (bet c a b)"

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* mi20357_Jelena_Mitrovic_DOKAZ *)
theorem t2_1:
  assumes "colinear a b c" and "distinct [a, b, c]"
  shows "bet' a b c"
proof -
  have "a \<noteq> b" and "b \<noteq> c" and "a \<noteq> c"
    using assms by auto
  consider "bet a b c" | "bet b c a" | "bet c a b"
    using assms ax_ord_5[of a b c] by auto
  then show ?thesis
  proof cases
    assume "bet a b c"
    then have "one_of_three (bet a b c) (bet b c a) (bet c a b)"
      unfolding one_of_three_def 
      using ax_ord_2 ax_ord_3 by blast
    then show ?thesis
      unfolding bet'_def by auto
  next
    assume "bet b c a"
    then have "one_of_three (bet a b c) (bet b c a) (bet c a b)"
      unfolding one_of_three_def 
      using ax_ord_2 ax_ord_3 by blast
    then show ?thesis
      unfolding bet'_def by auto
  next
    assume "bet c a b"
    then have "one_of_three (bet a b c) (bet b c a) (bet c a b)"
      unfolding one_of_three_def 
      using ax_ord_2 ax_ord_3 by blast
    then show ?thesis
      unfolding bet'_def by auto
  qed
qed


(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* mi20357_Jelena_Mitrovic_DOKAZ *)
theorem t2_2:
  assumes "a \<noteq> b"
  shows "inc_p_l x (line a b) \<longleftrightarrow> x = a \<or> x = b \<or> (bet' a b x)"
proof
  assume "inc_p_l x (line a b)"
  consider "x = a" | "x = b" | "bet a x b" | "bet a b x"| "bet b a x "
    using assms
    by (meson \<open>inc_p_l x (line a b)\<close> ax_ord_2 ax_ord_5 colinear_def line)
  thus "x = a \<or> x = b \<or> bet' a b x"
    by (metis ax_ord_2 ax_ord_3 bet'_def one_of_three_def)
next
  assume "x = a \<or> x = b \<or> bet' a b x"
  thus "inc_p_l x (line a b)"
  proof (elim disjE)
    assume "x = a"
    hence "inc_p_l x (line a b)"
      using assms line by auto
    thus ?thesis .
  next
    assume "x = b"
    hence "inc_p_l x (line a b)"
      using assms line by auto
    thus ?thesis .
  next
    assume "bet' a b x"
    thus "inc_p_l x (line a b)"
      by (smt (verit, del_insts) ax_inc_3 ax_ord_1 bet'_def colinear_def line one_of_three_def)
  qed
qed

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* mi19096_Vladimir_Jovanovic_DOKAZ *)
theorem t2_3:
  assumes "\<not> colinear a b c" and 
          "bet b p c" and "bet c q a" and "bet a r b"
  shows "\<not> colinear p q r"
proof
  assume "colinear p q r"
  then show False
  proof-
    from assms and ax_ord_1 have "q \<noteq> a \<and> r \<noteq> a" by auto
    obtain l_a where a:"l_a = line b c" by simp
    from this assms have "inc_p_l p l_a" by (metis GeometryOrder.ax_ord_1 GeometryOrder_axioms ax_ord_2 ax_ord_3 bet'_def one_of_three_def t2_2)
    obtain l_b where b:"l_b = line a c" by simp
    from this assms have "inc_p_l q l_b" by (metis GeometryOrder.ax_ord_1 GeometryOrder_axioms ax_ord_2 ax_ord_3 bet'_def one_of_three_def t2_2)
    obtain l_c where c:"l_c = line a b" by simp
    from this assms have "inc_p_l r l_c" by (metis GeometryOrder.ax_ord_1 GeometryOrder_axioms ax_ord_2 ax_ord_3 bet'_def one_of_three_def t2_2)
    also have diff:"l_b \<noteq> l_c \<and> l_a \<noteq> l_b \<and> l_a \<noteq> l_c" by (smt (verit, best) GeometryOrder.ax_ord_1 GeometryOrder_axioms a b c assms(1) assms(3) colinear_def line)
    from diff `inc_p_l q l_b` `inc_p_l r l_c` have "q \<noteq> r" by (metis b c assms(3) assms(4) ax_inc_3 ax_ord_1 line)
    from diff `inc_p_l q l_b` `inc_p_l p l_a` have "q \<noteq> p" by (metis a b assms(2) assms(3) ax_inc_3 ax_ord_1 line)
    from diff `inc_p_l p l_a` `inc_p_l r l_c` have "r \<noteq> p" by (metis a c assms(2) assms(4) ax_inc_3 ax_ord_1 line)
    from `q \<noteq> r` `q \<noteq> p` `r \<noteq> p` have "distinct [p, q, r]" by simp
    from this `colinear p q r` and t2_1 have "bet' p q r" by simp
    then show False
    proof-
      consider (bet1) "bet r p q" | (bet2) "bet p q r" | (bet3) "bet p r q"
        by (metis \<open>colinear p q r\<close> \<open>q \<noteq> p\<close> \<open>q \<noteq> r\<close> \<open>r \<noteq> p\<close> ax_ord_2 ax_ord_5)
      then show ?thesis
      proof cases
        case bet1
        have "\<not> colinear a r q" by (smt (verit, best) Geometry.colinear_def assms(3) assms(4) ax_inc_3 ax_ord_1 b c diff line)
        then have "\<exists> P. inc_p_pl a P \<and> inc_p_pl r P \<and> inc_p_pl q P" by (auto simp add: ax_inc_5)
        then obtain P where "inc_p_pl a P \<and> inc_p_pl r P \<and> inc_p_pl q P" by auto
        then have "inc_l_pl l_a P" by (metis (mono_tags, lifting) GeometryIncidence.ax_inc_7 GeometryIncidence_axioms \<open>inc_p_l q l_b\<close> \<open>q \<noteq> a \<and> r \<noteq> a\<close> a b c calculation diff inc_trans line)
        then have "\<not> inc_p_l a l_a" by (metis a b c diff line t1_11)
        have "p = intersection_l_l l_a (line r q)"
        proof-
          have "inc_p_l p (line r q)" using \<open>bet r p q\<close> ax_ord_1 colinear_def line_equality by blast
          from this `inc_p_l p l_a` show "p = intersection_l_l l_a (line r q)"
            by (metis \<open>q \<noteq> r\<close> a assms(4) ax_ord_1 b c calculation diff intersection_l_l_equality line)
        qed 
        have "b = intersection_l_l l_a (line a r)"
        proof-
          have "inc_p_l b (line a r)" using assms(4) ax_ord_1 colinear_def line_equality by blast
          also have "inc_p_l b l_a" by (metis a b c diff t2_2)
          from this `inc_p_l b (line a r)` show "b = intersection_l_l l_a (line a r)"
            by (metis \<open>\<not> inc_p_l a l_a\<close> \<open>q \<noteq> a \<and> r \<noteq> a\<close> intersection_l_l_equality line)
        qed 
        have "c = intersection_l_l l_a (line q a)"
        proof-
          have "inc_p_l c (line q a)" using assms(3) ax_ord_1 colinear_def line_equality by blast
          also have "inc_p_l c l_a" by (metis a b c diff t2_2)
          from this `inc_p_l c (line q a)` show "c = intersection_l_l l_a (line q a)"
            by (metis \<open>\<not> inc_p_l a l_a\<close> \<open>q \<noteq> a \<and> r \<noteq> a\<close> intersection_l_l_equality line)
        qed 
        from this `\<not> colinear a r q` `inc_l_pl l_a P` `\<not> inc_p_l a l_a` `bet r p q` have "(bet q (intersection_l_l l_a (line q a)) a) \<or> (bet a (intersection_l_l l_a (line a r)) r)"
          using \<open>inc_p_pl a P \<and> inc_p_pl r P \<and> inc_p_pl q P\<close> \<open>p = intersection_l_l l_a (line r q)\<close> ax_Pasch plane_equality by blast
        then have "(bet q c a) \<or> (bet a b r)" using \<open>b = intersection_l_l l_a (line a r)\<close> \<open>c = intersection_l_l l_a (line q a)\<close> by fastforce
        then show False using assms ax_ord_2 ax_ord_3 by blast
      next
        case bet2
        have "\<not> colinear b r p" by (smt (verit, ccfv_SIG) Geometry.colinear_def GeometryOrder.ax_ord_1 GeometryOrder_axioms a assms(2) assms(4) ax_inc_3 c diff line)
        then have "\<exists> P. inc_p_pl b P \<and> inc_p_pl r P \<and> inc_p_pl p P" by (auto simp add: ax_inc_5)
        then obtain P where "inc_p_pl b P \<and> inc_p_pl r P \<and> inc_p_pl p P" by auto
        then have "inc_l_pl l_b P"  by (smt (verit, best) GeometryIncidence.t1_12 GeometryIncidence_axioms GeometryOrder.ax_ord_1 GeometryOrder_axioms \<open>inc_p_l p l_a\<close> a assms(2) assms(3) assms(4) b c calculation inc_trans line)
        then have "\<not> inc_p_l b l_b" by (metis a b c diff line t1_11)
        have "q = intersection_l_l l_b (line r p)"
        proof-
          have "inc_p_l q (line r p)" using bet2 ax_ord_1 colinear_def line_equality \<open>r \<noteq> p\<close> by blast
          from this `inc_p_l q l_b` show "q = intersection_l_l l_b (line r p)"
            by (metis \<open>r \<noteq> p\<close> assms(3) assms(4) ax_ord_1 b c calculation diff intersection_l_l_equality line)
        qed
        have "c = intersection_l_l l_b (line b p)"
        proof-
          have "inc_p_l c (line b p)" by (metis \<open>inc_p_l p l_a\<close> a assms(2) ax_ord_1 line line_equality)
          also have "inc_p_l c l_b" by (metis assms(3) ax_ord_1 b t2_2)
          from this `inc_p_l c (line b p)` show "c = intersection_l_l l_b (line b p)"
            by (metis \<open>\<not> inc_p_l b l_b\<close> assms(2) ax_ord_1 intersection_l_l_equality line)
        qed 
        have "a = intersection_l_l l_b (line b r)"
        proof-
          have "inc_p_l a (line b r)" by (metis assms(4) ax_ord_1 c calculation line line_equality)
          also have "inc_p_l a l_b" by (metis assms(3) ax_ord_1 b t2_2)
          from this `inc_p_l a (line b r)` show "a = intersection_l_l l_b (line b r)"
            by (metis \<open>\<not> inc_p_l b l_b\<close> assms(4) ax_ord_1 intersection_l_l_equality line)
        qed 
        from this `\<not> colinear b r p` `inc_l_pl l_b P` `\<not> inc_p_l b l_b` `bet p q r` have "(bet r (intersection_l_l l_b (line b r)) b) \<or> (bet b (intersection_l_l l_b (line b p)) p)"
          by (smt (verit, ccfv_threshold) \<open>inc_p_pl b P \<and> inc_p_pl r P \<and> inc_p_pl p P\<close> \<open>q = intersection_l_l l_b (line r p)\<close> ax_Pasch ax_ord_2 line line_equality plane_equality)
        then have "(bet r a b) \<or> (bet b c p)" using \<open>a = intersection_l_l l_b (line b r)\<close> \<open>c = intersection_l_l l_b (line b p)\<close> by fastforce
        then show False using assms ax_ord_2 ax_ord_3 by blast
      next
        case bet3
        have "\<not> colinear c p q" by (smt (verit, best) GeometryOrder.ax_ord_1 GeometryOrder_axioms a assms(2) assms(3) ax_inc_3 b colinear_def diff line)
        then have "\<exists> P. inc_p_pl c P \<and> inc_p_pl q P \<and> inc_p_pl p P" by (auto simp add: ax_inc_5)
        then obtain P where "inc_p_pl c P \<and> inc_p_pl q P \<and> inc_p_pl p P" by auto
        then have "inc_l_pl l_c P" by (smt (verit) Geometry.inc_l_pl_def GeometryIncidence.line GeometryIncidence_axioms GeometryIncidence_def \<open>inc_p_l p l_a\<close> \<open>inc_p_l q l_b\<close> a assms(2) assms(3) assms(4) ax_ord_1 b c)
        then have "\<not> inc_p_l c l_c" by (metis a b c diff line t1_11)
        have "r = intersection_l_l l_c (line p q)"
        proof-
          have "inc_p_l r (line p q)" using bet3 ax_ord_1 colinear_def line_equality by blast
          from this `inc_p_l r l_c` show "r = intersection_l_l l_c (line p q)"
            by (metis \<open>inc_p_l p l_a\<close> \<open>q \<noteq> p\<close> a assms(2) assms(4) ax_ord_1 c diff intersection_l_l_equality line)
        qed 
        have "a = intersection_l_l l_c (line c q)"
        proof-
          have "inc_p_l a (line c q)" by (metis \<open>inc_p_l q l_b\<close> assms(3) ax_ord_1 b line line_equality)
          also have "inc_p_l a l_c" by (metis a b c diff t2_2)
          from this `inc_p_l a (line c q)` show "a = intersection_l_l l_c (line c q)"
            by (metis \<open>\<not> inc_p_l c l_c\<close> assms(3) ax_ord_1 intersection_l_l_equality line)
        qed 
        have "b = intersection_l_l l_c (line c p)"
        proof-
          have "inc_p_l b (line c p)" using assms(2) ax_ord_1 ax_ord_2 colinear_def line_equality by blast
          also have "inc_p_l b l_c" by (metis a b c diff t2_2)
          from this `inc_p_l b (line c p)` show "b = intersection_l_l l_c (line c p)"
            by (metis \<open>\<not> inc_p_l c l_c\<close> assms(2) ax_ord_1 intersection_l_l_equality line)
        qed 
        from this `\<not> colinear c p q` `inc_l_pl l_c P` `\<not> inc_p_l c l_c` `bet p r q` have "(bet p (intersection_l_l l_c (line c p)) c) \<or> (bet c (intersection_l_l l_c (line c q)) q)"
          by (smt (verit, best) \<open>inc_p_pl c P \<and> inc_p_pl q P \<and> inc_p_pl p P\<close> \<open>r = intersection_l_l l_c (line p q)\<close> ax_Pasch ax_ord_2 line line_equality plane_equality)
        then have "(bet p b c) \<or> (bet c a q)" by (simp add: \<open>a = intersection_l_l l_c (line c q)\<close> \<open>b = intersection_l_l l_c (line c p)\<close>)
        then show False using assms ax_ord_2 ax_ord_3 by blast
      qed
    qed
  qed
qed

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* mi19432_Marko_Bekonja_DOKAZ *)
theorem t2_4:
  assumes "a \<noteq> b"
  shows "\<exists>c. bet a c b"
  proof-
  obtain p where "\<not> colinear a p b" by (metis assms ax_inc_4 colinear_def t1_6)
  from this have *:"a \<noteq> p \<and> p \<noteq> b \<and> b \<noteq> a" by (metis assms distinct_length_2_or_more t1_1)
  from this and ax_ord_4 have "\<exists>q. bet b p q" by auto
  from this obtain q where "bet b p q" by auto
  from this and \<open>\<not> colinear a p b\<close> * and ax_ord_4 have "\<exists>r. bet a q r" by (metis ax_ord_1 ax_ord_2)
  from this obtain r where "bet a q r" by auto
  from this and \<open>bet b p q\<close> and \<open>\<not> colinear a p b\<close> have "\<not> colinear a b q" by (smt (verit) ax_inc_3 ax_ord_1 colinear_def)
  obtain l where "l = line r p" by auto
  from this and \<open>bet a q r\<close> and \<open>\<not> colinear a b q\<close> \<open>bet b p q\<close> have "\<not> inc_p_l a l" 
    using colinear_def by (smt (verit, ccfv_threshold) ax_ord_1 line t1_11)
  from \<open>l = line r p\<close> and \<open>\<not>colinear a b q\<close> have "inc_l_pl l (plane a b q)"
    by (smt (verit, best) Geometry.colinear_def GeometryOrder.ax_ord_1 GeometryOrder_axioms \<open>bet a q r\<close> \<open>bet b p q\<close> ax_inc_3 ax_inc_7 inc_trans line plane_a plane_b plane_c)
  from \<open>bet b p q\<close> have *:"inc_p_l p (line b q)" using ax_ord_1 colinear_def line_equality by blast
  from this and \<open>\<not> colinear a p b\<close> and \<open>bet a q r\<close>and \<open>l = line r p\<close> have "inc_p_l p (line b q) \<and> inc_p_l p l"
    using colinear_def by (smt (verit, ccfv_SIG) GeometryIncidence.line_equality GeometryIncidence_axioms GeometryOrder.ax_ord_1 GeometryOrder.t2_2 GeometryOrder_axioms)
  from \<open>\<not> inc_p_l a l\<close> \<open>bet a q r\<close> \<open>bet b p q\<close> \<open>l = line r p\<close> have "l \<noteq> line b q" 
    by (smt (verit, ccfv_SIG) GeometryOrder.ax_ord_1 GeometryOrder_axioms ax_inc_3 colinear_def line)
  from \<open>\<not> colinear a b q\<close> \<open>bet a q r\<close> \<open>bet b p q\<close> \<open>inc_l_pl l (plane a b q)\<close> \<open>inc_p_l p (line b q) \<and> inc_p_l p l\<close> have "inc_l_pl (line b q) (plane a b q)" 
  using assms by (metis ax_inc_7 ax_ord_1 inc_trans line plane_c)
  from this and \<open>inc_l_pl l (plane a b q)\<close> and \<open>l \<noteq> line b q\<close> and \<open>inc_p_l p (line b q) \<and> inc_p_l p l\<close>
  have tacka_p:"p = intersection_l_l l (line b q)" by (smt (z3) intersection_l_l_def t1_6 the_equality)
  from this and \<open>bet b p q\<close> have "bet b (intersection_l_l l (line b q)) q" by auto 
  from \<open>bet a q r\<close> and \<open>inc_p_l p (line b q) \<and> inc_p_l p l\<close> and \<open>l = line r p\<close> have "inc_p_l r (line q a) \<and> inc_p_l r l" 
  using colinear_def by (smt (verit) GeometryIncidence.line_equality GeometryIncidence_axioms GeometryOrder.ax_ord_1 GeometryOrder_axioms line)
  from \<open>\<not> inc_p_l a l\<close> \<open>bet a q r\<close> have "l \<noteq> line q a" by (metis GeometryOrder.ax_ord_1 GeometryOrder_axioms t2_2)
  from \<open>\<not> colinear a b q\<close> have "inc_l_pl (line q a) (plane a b q)"
    using assms by (metis (mono_tags, opaque_lifting) Geometry.colinear_def ax_inc_7 line plane_a plane_c)
  from this and \<open>inc_l_pl l (plane a b q)\<close> and \<open>l \<noteq> line q a\<close> and \<open>inc_p_l r (line q a) \<and> inc_p_l r l\<close>
  have tacka_r:"r = intersection_l_l l (line q a)" by (smt (z3) intersection_l_l_def t1_6 the_equality)
  obtain c where tacka_c:"c = intersection_l_l l (line a b)" by auto
  from \<open>\<not> colinear a b q\<close> and \<open>inc_l_pl l (plane a b q)\<close> and \<open>\<not> inc_p_l a l\<close> and \<open>bet b (intersection_l_l l (line b q)) q\<close>
  and ax_Pasch have "(bet q (intersection_l_l l (line q a)) a) \<or> (bet a (intersection_l_l l (line a b)) b)" by auto
  from this and tacka_r tacka_c have "bet q r a \<or> bet a c b" by auto
  from \<open>bet a q r\<close> have "\<not>bet q r a" using ax_ord_2 ax_ord_3 by blast
  from this and \<open>bet q r a \<or> bet a c b\<close> have "bet a c b" by auto
  from this show "\<exists>c. bet a c b" by auto
qed

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* \<open> bet4 \<close> \<longrightarrow> Given points a, b, c and d. If b and c between a and d, in the way that b between a and c, and c between b and d, then \<open> bet4 a b c d \<close> *)
definition bet4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "bet4 a b c d \<equiv> bet a b c \<and> bet b c d"

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* mi19087_Andrijana_Bosiljcic_DOKAZ *)
theorem t2_5:
  assumes "bet a b c" and "bet b c d"
  shows "bet4 a b c d"
  using assms
  unfolding bet4_def 
  by meson

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* mi19087_Andrijana_Bosiljcic_DOKAZ *)
theorem t2_6:
  assumes "bet a b c" and "bet a c d"
  shows "bet4 a b c d"
proof-
  obtain l :: 'b where "inc_p_l a l" "inc_p_l b l" "inc_p_l c l" "inc_p_l d l"
    by (smt (verit, ccfv_SIG) Geometry.colinear_def assms(1) assms(2) ax_inc_3 ax_ord_1)
  obtain P :: 'a where "\<not> (inc_p_l P l)" using ax_inc_4 colinear_def by blast
  obtain Q :: 'a where "bet d P Q"
    by (metis \<open>\<not> inc_p_l P l\<close> \<open>inc_p_l d l\<close> ax_ord_4)
  then have p1: "\<not> (colinear P a d)"
    by (smt (verit) GeometryIncidence.t1_11 GeometryIncidence_axioms GeometryOrder.ax_ord_1 GeometryOrder_axioms \<open>\<not> inc_p_l P l\<close> \<open>inc_p_l a l\<close> \<open>inc_p_l d l\<close> assms(2) colinear_def)
  then have p2: "inc_l_pl (line Q c) (plane P a d)"
    by (smt (verit) GeometryIncidence.ax_inc_3 GeometryIncidence_axioms GeometryOrder.ax_ord_1 GeometryOrder_axioms \<open>bet d P Q\<close> assms(2) ax_inc_7 colinear_def inc_trans line plane_a plane_b plane_c)
  then have p3: "\<not> (inc_p_l P (line Q c))"
    by (smt (verit) GeometryIncidence.t1_11 GeometryIncidence_axioms \<open>\<not> inc_p_l P l\<close> \<open>bet d P Q\<close> \<open>inc_p_l c l\<close> \<open>inc_p_l d l\<close> assms(2) ax_ord_1 colinear_def line)
  then have pb: "bet a c d" and "bet d P Q" using assms(2) by (blast, simp add: \<open>bet d P Q\<close>)
  have "l = line a d"
    using \<open>inc_p_l a l\<close> \<open>inc_p_l d l\<close> ax_ord_1 line_equality pb by blast
  then have *:"inc_p_l c (line a d)"
    using \<open>inc_p_l c l\<close> by blast
  have "Q \<noteq> c"
    by (smt (verit, best) GeometryOrder.ax_ord_1 GeometryOrder_axioms \<open>bet d P Q\<close> \<open>inc_p_l a l\<close> \<open>inc_p_l c l\<close> \<open>inc_p_l d l\<close> ax_inc_3 colinear_def p1)
  then have **:"inc_p_l c (line Q c)" using line[of Q c] by simp
  from * ** have "intersection_l_l (line Q c) (line a d) = c" 
    by (smt (verit) \<open>\<not> inc_p_l P l\<close> \<open>bet d P Q\<close> \<open>inc_p_l d l\<close> \<open>l = line a d\<close> ax_ord_1 colinear_def intersection_l_l_equality line)  
  then have *:"bet a (intersection_l_l (line Q c) (line a d)) d" using pb by auto
  from ax_Pasch[OF p1 p2 p3 *] have "bet d (intersection_l_l (line Q c) (line d P)) P \<or> bet P (intersection_l_l (line Q c) (line P a)) a" by simp
  then have s: "bet P (intersection_l_l (line Q c) (line P a)) a"
    by (smt (verit, ccfv_SIG) Geometry.colinear_def \<open>\<not> inc_p_l P l\<close> \<open>bet d P Q\<close> \<open>inc_p_l c l\<close> \<open>inc_p_l d l\<close> ax_ord_1 ax_ord_3 intersection_l_l_equality line pb)
  then have "bet a b c"  by (simp add: assms(1))
  then have p11: "\<not> (colinear b a P)"
    by (metis (mono_tags, opaque_lifting) \<open>\<not> inc_p_l P l\<close> \<open>inc_p_l a l\<close> \<open>inc_p_l b l\<close> assms(1) ax_ord_1 colinear_def t1_6)
  then have p22: "inc_l_pl (line Q c) (plane b a P)" 
    by (smt (z3) GeometryIncidence.ax_inc_7 GeometryIncidence_axioms assms(1) ax_inc_3 ax_ord_1 colinear_def p2 pb plane_a plane_b plane_c plane_p_l_equality) 
  then have p33: "\<not> (inc_p_l b (line Q c))" 
    by (metis (no_types, opaque_lifting) "**" \<open>\<And>thesis. (\<And>l. \<lbrakk>inc_p_l a l; inc_p_l b l; inc_p_l c l; inc_p_l d l\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1) ax_ord_1 intersection_l_l_equality line p3 s)
  have "l = line a b"
    using \<open>inc_p_l a l\<close> \<open>inc_p_l b l\<close> assms(1) ax_ord_1 line_equality by presburger
  then have cab:"inc_p_l c (line a b)" using \<open>inc_p_l c l\<close> by blast
  from cab ** have "intersection_l_l (line Q c) (line a b) = c"
    using \<open>intersection_l_l (line Q c) (line a d) = c\<close> \<open>l = line a b\<close> \<open>l = line a d\<close> by presburger
  then have "bet b (intersection_l_l (line Q c) (line b P)) P \<or> bet b (intersection_l_l (line Q c) (line b a)) a"
    by (smt (verit, ccfv_threshold) GeometryIncidence.line_equality GeometryIncidence_axioms ax_Pasch ax_ord_2 line p11 p22 p33 s)
  then have r: "bet b (intersection_l_l (line Q c) (line b P)) P" 
    by (metis \<open>intersection_l_l (line Q c) (line a b) = c\<close> assms(1) ax_ord_2 ax_ord_3 line line_equality)
  then have p111: "\<not> (colinear d P b)"
    by (smt (z3) \<open>\<And>thesis. (\<And>l. \<lbrakk>inc_p_l a l; inc_p_l b l; inc_p_l c l; inc_p_l d l\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1) ax_ord_3 colinear_def p1 pb t1_6)
  then have p222: "inc_l_pl (line Q c) (plane d P b)"
    by (smt (verit) ax_inc_6 p1 p11 p2 p22 p3 plane_a plane_b plane_c plane_p_l_unique)
  then have p333: "\<not> (inc_p_l d (line Q c))"
    by (metis "**" GeometryIncidence.t1_11 GeometryIncidence_axioms GeometryOrder.ax_ord_1 GeometryOrder_axioms \<open>inc_p_l b l\<close> \<open>inc_p_l c l\<close> \<open>inc_p_l d l\<close> p33 pb)   
  have bd: "l = line b d" 
    by (metis \<open>inc_p_l b l\<close> \<open>inc_p_l d l\<close> assms(1) ax_ord_3 line_equality pb)
  then have cbd:"inc_p_l c (line b d)" using \<open>inc_p_l c l\<close> by auto
  from cbd ** have "intersection_l_l (line Q c) (line b d) = c" 
    using \<open>intersection_l_l (line Q c) (line a b) = c\<close> \<open>l = line a b\<close> bd by force
  then have p444: "bet P (intersection_l_l (line Q c) (line P b)) b"
    by (metis ax_ord_2 line line_equality r)
  then have "bet b (intersection_l_l (line Q c) (line b d)) d \<or> bet d (intersection_l_l (line Q c) (line d P)) P"
    using ax_Pasch p111 p222 p333 p444 by blast
  then have "bet b (intersection_l_l (line Q c) (line b d)) d" 
    by (smt (verit, ccfv_SIG) Geometry.colinear_def \<open>Q \<noteq> c\<close> \<open>bet d P Q\<close> ax_ord_1 ax_ord_3 intersection_l_l_equality p333 t2_2)
  then have ll: "bet b c d"  
    by (simp add: \<open>intersection_l_l (line Q c) (line b d) = c\<close>)
  then have "bet a b c" and "bet b c d"
    using assms(1) by blast (simp add: ll)
  then have "bet4 a b c d" using bet4_def by blast
  then show ?thesis by blast
qed

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* mi19087_Andrijana_Bosiljcic_DOKAZ *)
theorem t2_7:
  assumes "bet a b c" and "bet a b d" and "c \<noteq> d"
  shows "(bet4 a b c d) \<or> (bet4 a b d c)"
  proof-
  have *: "colinear a c d \<and> a \<noteq> c \<and> a \<noteq> d \<and> c \<noteq> d" 
    by (smt (verit) Geometry.colinear_def assms(1) assms(2) assms(3) ax_ord_1 t1_6)
  consider "bet a c d" | "bet c d a" | "bet d a c" 
    using "*" ax_ord_5 by blast 
  then show ?thesis
  proof cases
    assume "bet a c d"
    then have "bet4 a b c d" by (simp add: assms(1) t2_6)
    then show ?thesis by blast
  next
    assume "bet c d a"
    then have "bet a d c" using ax_ord_2 by blast
    then have "bet4 a b d c" by (simp add: assms(2) t2_6)
    then show ?thesis by auto
  next 
    assume "bet d a c"
    then have "bet4 d b a c" using assms(2) ax_ord_2 t2_6 by blast
    then have "bet b a c" using bet4_def by auto
    then show ?thesis using assms(1) ax_ord_2 ax_ord_3 by blast
  qed
qed

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* mi19087_Andrijana_Bosiljcic_DOKAZ *)
theorem t2_8:
  assumes "bet a c b" and "bet a d b" and "c \<noteq> d"
  shows "(bet4 a d c b) \<or> (bet4 a c d b)"
  proof-
  have *: "(bet a d c) \<or> \<not>(bet a d c)" by simp 
  then show ?thesis 
  proof
    assume "bet a d c"
    then have "(bet4 a d c b)" using assms(1) t2_6 by blast
    then show ?thesis by auto
  next
    assume "\<not>(bet a d c)"
    then have "colinear a d c"
      by (smt (verit, ccfv_SIG) Geometry.colinear_def GeometryOrder.ax_ord_1 GeometryOrder_axioms assms(1) assms(2) ax_inc_3)
    then have "a \<noteq> d \<and> a \<noteq> c \<and> d \<noteq> c"
      by (metis GeometryOrder.ax_ord_1 GeometryOrder_axioms assms(1) assms(2) assms(3))
    then have "(bet d c a) \<or> (bet c a d)"
      using \<open>\<not> bet a d c\<close> \<open>colinear a d c\<close> ax_ord_5 by blast
    then show ?thesis 
    proof
      assume "bet d c a"
      from this and \<open>bet a d b\<close> show ?thesis using ax_ord_2 t2_6 by blast
    next
      assume "bet c a d"
      have *: "bet b c a" by (simp add: assms(1) ax_ord_2)
      then have "bet b a d"
        by (smt (verit, best) GeometryOrder.t2_6 GeometryOrder_axioms \<open>bet c a d\<close> assms(2) ax_ord_1 ax_ord_2 ax_ord_3 ax_ord_4 bet4_def t2_7)
      from this and \<open>bet a d b\<close> show ?thesis using ax_ord_2 ax_ord_3 by blast
    qed
  qed
qed

(* mi6407_Nevena_Radulovic_DOKAZ *)
lemma bet4_divide:
  assumes "bet4 a d c b"
  shows "bet a d b" "bet a c b"
proof-
  show "bet a d b"
    using assms
    unfolding bet4_def
    by (smt (verit, best) GeometryOrder.ax_ord_1 GeometryOrder.ax_ord_2 GeometryOrder.bet'_def GeometryOrder.t2_2 GeometryOrder.t2_6 GeometryOrder.t2_8 GeometryOrder_axioms assms ax_inc_3 bet4_def one_of_three_def)
next
  show "bet a c b"
    using assms
    unfolding bet4_def
    by (smt (verit, best) Geometry.colinear_def GeometryOrder.ax_ord_1 GeometryOrder.t2_6 GeometryOrder.t2_8 GeometryOrder_axioms ax_ord_2 ax_ord_5 bet4_def t1_11)
qed


chapter\<open>Segment and polygon\<close>

section \<open>Segment\<close>

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>segment_oo a b\<close> is set of all points between a and b. *)
definition segment_oo :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segment_oo a b = {c. bet a c b}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>segment_oc a b\<close> is set of all points between a and b, including b. *)
definition segment_oc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segment_oc a b = {c. bet a c b} \<union> {b}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>segment_co a b\<close> is set of all points between a and b, including a. *)
definition segment_co :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segment_co a b = {c. bet a c b} \<union> {a}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>segment_cc a b\<close> is set of all points between a and b, including a and b. *)
definition segment_cc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segment_cc a b = {c. bet a c b} \<union> {a} \<union> {b}"

(* mi6407_Nevena_Radulovic_DOKAZ *)
lemma segment_oo_reorder:
  shows "segment_oo a b = segment_oo b a"
  using segment_oo_def ax_ord_2 by fastforce

lemma segment_oo_endpoints:
  shows "a \<notin> segment_oo a b" "b \<notin> segment_oo a b"
  unfolding segment_oo_def
  using ax_ord_1 
  by auto

lemma segment_oc_endpoints:
  assumes "a \<noteq> b"
  shows "a \<notin> segment_oc a b" "b \<in> segment_oc a b"
  unfolding segment_oc_def
  using assms ax_ord_1
  by auto

lemma segment_co_endpoints:
  assumes "a \<noteq> b"
  shows "a \<in> segment_co a b" "b \<notin> segment_co a b"
  unfolding segment_co_def
  using assms ax_ord_1
  by auto

lemma segment_cc_endpoints:
  shows "a \<in> segment_cc a b" "b \<in> segment_cc a b"
  unfolding segment_cc_def
  by auto

(* mi19009_Mina Cerovic FORMULACIJA *)
(* mi6407_Nevena_Radulovic_DOKAZ *)
theorem t3_1:
  assumes "c \<in> segment_oo a b" and "c \<noteq> d"
  shows "d \<in> segment_oo a b \<longleftrightarrow> one_of_two (d \<in> segment_oo a c) (d \<in> segment_oo c b)" 
proof 
  assume "d \<in> segment_oo a b"
  then have "bet a d b" 
    by (auto simp add: segment_oo_def)
  with assms have "bet a c b" and "bet a d b"
    by (auto simp add: segment_oo_def)
  with assms have "(bet4 a d c b) \<or> (bet4 a c d b)"
    by (auto simp add:t2_8)
  then show "one_of_two (d \<in> segment_oo a c) (d \<in> segment_oo c b)"
  proof
    assume "bet4 a d c b"
    then have "bet a d c \<and> bet d c b"
      by (simp add:bet4_def)
    then have "bet a d c" and "bet d c b" and "bet b c d" 
      by (auto simp add:ax_ord_2)
    then have "bet a d c" and  "\<not> bet b d c"
      by (auto simp add:ax_ord_3) 
    then have "(d \<in> segment_oo a c)" and "(d \<notin> segment_oo b c)"
      by (auto simp add:segment_oo_def)
    then have "(d \<in> segment_oo a c)" and "(d \<notin> segment_oo c b)"
      by (auto simp add: segment_oo_reorder)
    then show "one_of_two (d \<in> segment_oo a c) (d \<in> segment_oo c b)" 
      by (auto simp add: one_of_two_def)
  next
    assume "bet4 a c d b"
    then have "bet a c d \<and> bet c d b" 
      by (simp add:bet4_def)
    then have "bet a c d" and "bet c d b" 
      by auto
    then have "bet c d b" and "\<not> bet a d c"
      by (auto simp add:ax_ord_3) 
    then have "(d \<in> segment_oo c b)" and "(d \<notin> segment_oo a c)"
      by (auto simp add:segment_oo_def)
    then show "one_of_two (d \<in> segment_oo a c) (d \<in> segment_oo c b)"
      by (simp add: one_of_two_def)
  qed   
next
  assume "one_of_two (d \<in> segment_oo a c) (d \<in> segment_oo c b)"
  from this show "d \<in> segment_oo a b"
    unfolding one_of_two_def
  proof
    assume "d \<in> segment_oo a c \<and> d \<notin> segment_oo c b"
    with assms have "d \<in> segment_oo a c" and "c\<in> segment_oo a b"
      by auto
    then have  "bet a d c" and "bet a c b" 
      by (auto simp add: segment_oo_def)
    then have "bet4 a d c b"
      by (auto simp add:t2_6)
    then have "bet a d b"
      by (simp add:bet4_divide)
    then show "d \<in> segment_oo a b"
      by (simp add: segment_oo_def)      
  next
    assume "d \<notin> segment_oo a c \<and> d \<in> segment_oo c b"
    with assms have "bet c d b" and "bet a c b"
      by (auto simp add: segment_oo_def)
    then have "bet b d c" and "bet b c a"
      by (auto simp add:ax_ord_2)
    then have "bet4 b d c a"
      by (auto simp add:t2_6)
    then have "bet b d a"
      by (simp add:bet4_divide)
    then have "bet a d b" 
      by (simp add:ax_ord_2)
    then show "d \<in> segment_oo a b"
      by (auto simp add: segment_oo_def)    
  qed 
qed

(* mi6407_Nevena_Radulovic_DOKAZ*)
lemma segment_oo_subset:
  assumes "bet a b c"
  shows "segment_oo a b \<subset> segment_oo a c"
proof safe
  fix x
  assume "x \<in> segment_oo a b"
  then show "x \<in> segment_oo a c"
    using assms
    unfolding segment_oo_def
    by (metis t2_6 bet4_divide(1) mem_Collect_eq)
next
  assume "segment_oo a b = segment_oo a c"
  then show False
    using assms
    unfolding segment_oo_def
    using ax_ord_1 by blast
qed

lemma segment_oo_empty:
  shows "segment_oo a a = {}"
  unfolding segment_oo_def
  using ax_ord_1 by blast

(* mi6407_Nevena_Radulovic_DOKAZ *)
lemma segment_oo_nonempty:
  assumes "a \<noteq> b"
  shows "segment_oo a b \<noteq> {}"
  using segment_oo_def
  by (simp add: assms t2_4)


(* mi19009_Mina Cerovic FORMULACIJA *)
(* mi6407_Nevena_Radulovic_DOKAZ *)
theorem t3_2:
  assumes "colinear a b c" "a\<noteq>b" "b\<noteq>c" "c\<noteq>a" 
  shows "segment_oo a b \<inter> segment_oo b c = {} \<longleftrightarrow> bet a b c"
proof 
  assume "segment_oo a b \<inter> segment_oo b c = {}"
  with assms have "bet a b c \<or> bet b c a \<or> bet c a b"
    by (auto simp add: ax_ord_5)
  show "bet a b c"
  proof (rule ccontr)
    assume "\<not> bet a b c"
    from assms have "bet a b c \<or> bet b c a \<or> bet c a b" 
      by (auto simp add: ax_ord_5)
    with \<open>\<not> bet a b c\<close> have "bet b c a \<or> bet c a b"
      by auto
    then
    show False
    proof
      assume "bet b c a"
      then have "bet a c b"
        by (simp add: ax_ord_2)
      then have "segment_oo a c \<subset> segment_oo a b"
        by (simp add: segment_oo_subset)
      then have "segment_oo a b \<inter> segment_oo b c = segment_oo b c"  
        using \<open>bet a c b\<close> ax_ord_2 segment_oo_reorder segment_oo_subset by blast
      from assms have "segment_oo b c \<noteq> {}"
        by (auto simp add: segment_oo_nonempty)
      with \<open>segment_oo a b \<inter> segment_oo b c = {}\<close> and \<open>segment_oo a b \<inter> segment_oo b c = segment_oo b c\<close>
      show False
        by auto
    next
      assume "bet c a b"
      then have "bet b a c"
        by (simp add: ax_ord_2)
      then have "segment_oo b a \<subset> segment_oo b c"
        by (simp add: segment_oo_subset)
      then have "segment_oo a b \<subset> segment_oo b c"
        by (simp add: segment_oo_reorder)
      then have  "segment_oo a b \<inter> segment_oo b c = segment_oo a b"  
        using \<open>bet b a c\<close> ax_ord_2 segment_oo_reorder segment_oo_subset by blast
      from assms have "segment_oo a b \<noteq> {}"
        by (auto simp add: segment_oo_nonempty)
      from this and \<open>segment_oo a b \<inter> segment_oo b c = {}\<close> and
                    \<open>segment_oo a b \<inter> segment_oo b c = segment_oo a b\<close>
      show False by auto
    qed
  qed
next
  assume "bet a b c"
  show "segment_oo a b \<inter> segment_oo b c = {}"
  proof(auto)
    fix x
    assume "x \<in> segment_oo a b" "x \<in> segment_oo b c"
    then show  False
      by (metis \<open>bet a b c\<close> ax_ord_2 ax_ord_3 bet4_def mem_Collect_eq segment_oo_def t2_6)   
  qed
qed


(* mi19009_Mina Cerovic FORMULACIJA *)
(*
 Given points (A1, A2,..., An), if Ai between Ai-1 and Ai+1 for all i\<in>[2, n-1], then \<open>bet_n [A1,...,An]\<close>
 The list is one linear arrangement of points
*)
fun bet_n :: "'a list \<Rightarrow> bool" where
  "bet_n [] = True" |
  "bet_n [a] = True" |
  "bet_n [a, b] = True" |
  "bet_n (a # b # c # as) \<longleftrightarrow> (bet a b c) \<and> bet_n (b # c # as)"

lemma bet_n_triv [simp]:
  assumes "length as < 3"
  shows "bet_n as"
proof-
  obtain x y where "as = [] \<or> as = [x] \<or> as = [x, y]"
    using assms
    by (metis (no_types, lifting) One_nat_def length_0_conv length_Suc_conv less_Suc_eq less_one numeral_3_eq_3)
  then show ?thesis
    by auto
qed

lemma bet_n_step:
  assumes "length as \<ge> 3" 
  shows "bet_n as \<longleftrightarrow> bet (as ! 0) (as ! 1) (as ! 2) \<and> bet_n (tl as)"
proof-
  from assms obtain x y z as' where "as = (x # y # z # as')"
    by (metis length_Cons less_Suc_eq linorder_not_less list.exhaust list.size(3) numeral_3_eq_3)
  then show ?thesis
    by auto
qed

lemma bet_n_lemma:
  assumes "3 \<le> n" "n = length as"
  shows "bet_n as \<longleftrightarrow> (\<forall> i \<in> {1..<n-1}. bet (as ! (i-1)) (as ! i) (as ! (i + 1)))"
  using assms
proof (induction arbitrary: as rule: dec_induct)
  case base
  then obtain x y z where "as = [x, y, z]"
    by (smt (verit, ccfv_threshold) length_0_conv length_Suc_conv numeral_3_eq_3)
  then show ?case
    by auto
next
  case (step m)
  have *:"(\<forall>i\<in>{1..<m - 1}. bet (tl as ! (i - 1)) (tl as ! i) (tl as ! (i + 1))) \<longleftrightarrow> 
          (\<forall>i\<in>{2..<m}. bet (as ! (i-1)) (as ! i) (as ! (i + 1)))"
  proof safe
    fix i
    assume "i \<in> {1..<m-1}" 
    then have "i + 1 \<in> {2..<m}"
      using `3 \<le> m`
      by auto
    assume "\<forall>i\<in>{2..<m}. bet (as ! (i - 1)) (as ! i) (as ! (i + 1))"
    then have "bet (as ! i) (as ! (i + 1)) (as ! (i + 2))"
      using \<open>i+1 \<in> {2..<m}\<close>
      by fastforce
    then show "bet (tl as ! (i - 1)) (tl as ! i) (tl as ! (i + 1))"
      using step.hyps step.prems \<open>i \<in> {1..<m-1}\<close>
      by (force simp add: nth_tl)
  next
    fix i
    assume "\<forall>i\<in>{1..<m - 1}. bet (tl as ! (i - 1)) (tl as ! i) (tl as ! (i + 1))" "i \<in> {2..<m}"
    then have *: "\<forall> i \<in> {1..<m - 1}. bet (as ! i) (as ! (i + 1)) (as ! (i + 2))"
      using step.hyps step.prems 
      by (force simp add: nth_tl)
    show "bet (as ! (i - 1)) (as ! i) (as ! (i + 1))"
      using *[rule_format, of "i-1"]
      using `i \<in> {2..<m}` step.hyps
      by fastforce
  qed

  have **: "\<And> P. P 0 \<and> (\<forall>i\<in>{2..<m}. P (i - 1)) \<longleftrightarrow> (\<forall>i\<in>{1..<Suc m - 1}. P (i - 1))"
    using \<open>3 \<le> m\<close>
    by (smt (verit, best) One_nat_def Suc_1 Suc_le_eq Suc_le_mono atLeastLessThan_iff diff_Suc_1 le_Suc_eq numeral_3_eq_3)

  have "bet_n as \<longleftrightarrow> bet (as ! 0) (as ! 1) (as ! 2) \<and> bet_n (tl as)"
    using step
    by (metis Suc_le_mono add_leD2 bet_n_step plus_1_eq_Suc)
  also have "\<dots> \<longleftrightarrow> bet (as ! 0) (as ! 1) (as ! 2) \<and> (\<forall>i\<in>{1..<m - 1}. bet (tl as ! (i - 1)) (tl as ! i) (tl as ! (i + 1)))"
    using step.IH[of "tl as"] step(1) step(2) step(4)
    by auto
  also have "\<dots> \<longleftrightarrow> bet (as ! 0) (as ! 1) (as ! 2) \<and> (\<forall>i\<in>{2..<m}. bet (as ! (i - 1)) (as ! i) (as ! (i + 1)))"
    using *
    by simp
  finally show ?case
    using **[of "\<lambda> i. bet (as ! i) (as ! (i + 1)) (as ! (i + 2))"]
    by (auto  simp add: numeral_2_eq_2)
qed    

(* a declarative definition for bet_n *)
lemma bet_n:
  shows "bet_n as \<longleftrightarrow> (\<forall> i \<in> {1..<length as-1}. bet (as ! (i-1)) (as ! i) (as ! (i + 1)))"
  using bet_n_lemma
  by (cases "length as < 3") auto

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*mi19096_Vladimir_Jovanovic_DOKAZ *)
theorem bet_n_ijk:
  shows "bet_n as \<longleftrightarrow> (\<forall> i j k. i < j \<and> j < k \<and> k < length as \<longrightarrow> bet (as ! i) (as ! j) (as ! k))"
proof
  assume "bet_n as"
  then show "\<forall>i j k. i < j \<and> j < k \<and> k < length as \<longrightarrow> bet (as ! i) (as ! j) (as ! k)"
  proof (induction as)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    then show ?case
    proof (cases "length xs < 3")
      case True
      then show ?thesis
        by (smt (verit, del_insts) Cons.prems One_nat_def Suc_less_eq add.right_neutral add_Suc_right bet_n_step length_Cons less_one less_trans_Suc linorder_not_le nat_neq_iff numeral_3_eq_3 one_add_one)
    next
      case False
      have h: "bet_n xs"
        using Cons.prems bet_n.elims(3) by fastforce
      from Cons(1)[OF h] have IH: "\<forall>i j k. i < j \<and> j < k \<and> k < length xs \<longrightarrow> bet (xs ! i) (xs ! j) (xs ! k)"
        by simp
      with Cons show ?thesis
        sorry
    qed
  qed
next
  assume "\<forall>i j k. i < j \<and> j < k \<and> k < length as \<longrightarrow> bet (as ! i) (as ! j) (as ! k)"
  then show "bet_n as"
  proof (induction as)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    then show ?case
    proof (cases "length as < 3")
      case True
      then show ?thesis
        by (metis Cons.prems One_nat_def add.right_neutral add_Suc_right bet_n_step bet_n_triv lessI linorder_not_le list.sel(3) not_less_eq numeral_3_eq_3 one_add_one)
    next
      case False
      then show ?thesis
        by (smt (verit) Cons.IH Cons.prems bet_n.elims(1) dual_order.strict_trans length_Cons less_Suc_eq list.sel(3) not_less_eq nth_Cons_0 nth_tl numeral_3_eq_3)
    qed
  qed
qed


(* mi16407_Nevena_Radulovic FORMULACIJA *)
(* mi19096_Vladimir_Jovanovic_DOKAZ *)
theorem bet_n_distinct:
  assumes "bet_n as" "length as \<ge> 3"
  shows "distinct as"
proof (cases "length as < 3")
  case True
  then show ?thesis
    by (simp add: assms(2) leD)
next
  case False
  then show ?thesis
    by (smt (verit, ccfv_SIG) One_nat_def assms(1) assms(2) ax_ord_1 bet_n_ijk bet_n_step distinct_conv_nth less_Suc_eq_0_disj not_less_iff_gr_or_eq)
qed

(* TODO: Move to List.thy *)
(* consecutive pairs of elements e.g. for consecutive_pairs [1, 2, 3, 4] = [(1, 2), (2, 3), (3, 4)] *) 
definition consecutive_pairs where
  "consecutive_pairs xs = zip (butlast xs) (tl xs)"

fun uncurry where 
  "uncurry f (x, y) = f x y"

lemma map_consecutive_pairs [simp]:
  "map (uncurry f) (consecutive_pairs xs) = map2 f (butlast xs) (tl xs)"
  by (metis cond_case_prod_eta consecutive_pairs_def uncurry.simps)

lemma length_consecutive_pairs [simp]:
  shows "length (consecutive_pairs xs) = length xs - 1"
  unfolding consecutive_pairs_def
  by auto

lemma tl_consecutive_pairs [simp]:
  shows "consecutive_pairs (tl xs) = tl (consecutive_pairs xs)"
  unfolding consecutive_pairs_def
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    by (smt (verit, ccfv_threshold) Nil_tl butlast_tl list.collapse list.inject zip_Cons_Cons zip_eq_Nil_iff)
qed

lemma nth_consecutive_pairs [simp]:
  assumes "i < length xs - 1"
  shows "consecutive_pairs xs ! i = (xs ! i, xs ! (i+1))"
  using assms
  unfolding consecutive_pairs_def
  by (auto simp add: nth_butlast nth_tl)

lemma consecutive_pairs_append [simp]:
  assumes "xs \<noteq> []" "ys \<noteq> []"
  shows "consecutive_pairs (xs @ ys) = consecutive_pairs xs @ [(last xs, hd ys)] @ consecutive_pairs ys"
  unfolding consecutive_pairs_def
  by (metis append_Cons append_Nil append_assoc append_butlast_last_id assms(1) assms(2) butlast_snoc length_butlast length_tl list.exhaust_sel tl_append2 zip_Cons_Cons zip_append)

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>segments_oo\<close> is a list of open segments created from consecutive points in the given list*)
fun segments_oo :: "'a list \<Rightarrow> 'a set list" where
  "segments_oo [] = []"
| "segments_oo [x] = []"
| "segments_oo (x#y#xs) = (segment_oo x y) # (segments_oo (y # xs))"

(* A more declarative definition of segments_oo *)
lemma segments_oo:
  shows "segments_oo as = map (uncurry segment_oo) (consecutive_pairs as)"
  by (induction as rule: segments_oo.induct) auto

(*\<open>segments_cc\<close> is a list of closed segments created from consecutive points in the given list*)
definition segments_cc :: "'a list \<Rightarrow> 'a set list" where
  "segments_cc as = map (uncurry segment_cc) (consecutive_pairs as)"

lemma segments_cc_oo:
  assumes "length as \<ge> 2"
  shows "(\<Union> (set (segments_cc as))) = (\<Union> (set (segments_oo as))) \<union> set as"
proof safe
  fix x X
  assume "X \<in> set (segments_cc as)" "x \<notin> set as" "x \<in> X"
  then obtain a b where "(a, b) \<in> set (zip (butlast as) (tl as))" "X = segment_cc a b"
    unfolding segments_cc_def
    by auto
  then have "a \<in> set as \<and> b \<in> set as"
    by (metis empty_iff empty_set in_set_butlastD list.set_sel(2) set_zip_leftD set_zip_rightD)
  then have "x \<in> segment_oo a b"
    using `x \<notin> set as` `x \<in> X` `X = segment_cc a b`
    unfolding segment_oo_def segment_cc_def
    by auto
  then show "x \<in> \<Union> (set (segments_oo as))"
    using `(a, b) \<in> set (zip (butlast as) (tl as))`
    unfolding segments_oo
    by auto
next
  fix x X
  assume "x \<in> X" "X \<in> set (segments_oo as)"
  then obtain a b where "(a, b) \<in> set (zip (butlast as) (tl as))" "X = segment_oo a b"
    unfolding segments_oo
    by auto
  then have "x \<in> segment_cc a b"
    using \<open>x \<in> X\<close>
    by (metis segment_cc_def segment_oo_def Un_iff)
  then show "x \<in> \<Union> (set (segments_cc as))"
    using `(a, b) \<in> set (zip (butlast as) (tl as))`
    unfolding segments_cc_def
    by auto
next
  fix x
  assume "x \<in> set as"
  then have "x \<in> set (butlast as) \<or> x \<in> set (tl as)"
    using assms
    by (metis One_nat_def Suc_1 add.commute butlast.simps(2) diff_Suc_1 diff_is_0_eq' list.sel(3) list.set_cases list.set_intros(1) list.size(3) list.size(4) nat.simps(3) plus_1_eq_Suc)
  then obtain y where "(x, y) \<in> set (zip (butlast as) (tl as)) \<or> 
                       (y, x) \<in> set (zip (butlast as) (tl as))"
    by (metis in_set_impl_in_set_zip1 in_set_impl_in_set_zip2 length_butlast length_tl)
  moreover
  have "x \<in> segment_cc x y \<and> x \<in> segment_cc y x"
    by (simp add: segment_cc_endpoints)
  ultimately show "x \<in> \<Union> (set (segments_cc as))"
    unfolding segments_cc_def
    by auto
qed

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem t3_3:
  assumes "bet_n as" "a \<notin> set as"
  shows "a \<in> segment_oo (hd as) (last as) \<longleftrightarrow> (\<exists>! s \<in> set (segments_oo as). a \<in> s)"
  sorry




(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>disjoint\<close> Given set of sets of points returns true if elements are disjoint*)
definition disjoint :: "'a set set \<Rightarrow> bool" where
  "disjoint S \<equiv> \<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> s1 \<inter> s2 = {}"

lemma disjoint_empty:
  shows "disjoint {}"
  unfolding disjoint_def
  by auto

lemma disjoint_insert:
  shows "disjoint (As \<union> {A}) \<longleftrightarrow> disjoint As \<and> (\<forall> A' \<in> As. A' = A \<or> A' \<inter> A = {})"
  unfolding disjoint_def
  by blast

(*mi16407_Nevena_Radulovic FORMULACIJA*)
(*mi19087_Andrijana_Bosiljcic_DOKAZ*)
theorem t3_4_a:
  assumes "disjoint (set (segments_oo as))" "colinear_n as"
  shows "bet_n as"
  using assms
  sorry
  
(*mi16407_Nevena_Radulovic FORMULACIJA*)
(*mi19087_Andrijana_Bosiljcic_DOKAZ*)

theorem t3_4_b:
  assumes "bet_n as"
  shows "disjoint (set (segments_oo as))" "colinear_n as"
  sorry



(* there exist exactly two objects that satisfy the predicate P *)
definition Ex2 where 
  "Ex2 P \<equiv> (\<exists> x y. x \<noteq> y \<and> P x \<and> P y \<and> (\<forall> z. P z \<longrightarrow> z = x \<or> z = y))"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(* there exist exactly two linear arrangements *)

theorem t3_5:
  assumes "colinear_set A" "card A > 3"
  shows "Ex2 (\<lambda> x. set x = A \<and> bet_n x)"
  sorry


section \<open>Convexity\<close>

(*mi18107 Lidija Djalovic FORMULACIJA  *)    
(*<convex> : the set F is convex iff for every two points A B from the set the points along the segment AB belong to F *)
definition convex :: "'a set => bool" where
  "convex F \<equiv> (\<forall> a \<in> F. \<forall> b \<in> F. \<forall> c \<in> segment_oo a b. c \<in> F)"

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*mi19096_Vladimir_Jovanovic_DOKAZ *)
theorem t3_6_aux:
  assumes "convex A" "convex B"
  shows "convex (A \<inter> B)"
  using assms
  by (smt (verit, best) Int_iff convex_def)

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*mi19218 Luka Bura DOKAZ *)
theorem t3_6:
  assumes "\<forall> F \<in> G. convex F"
  shows "convex (\<Inter> G)"
proof (unfold convex_def, intro ballI)
  fix a b c
  assume a_in: "a \<in> (\<Inter> G)"
     and b_in: "b \<in> (\<Inter> G)"
     and c_in: "c \<in> segment_oo a b"
  have "\<forall> F \<in> G. c \<in> F"
  proof
    fix F
    assume "F \<in> G"
    hence "convex F" using assms by simp
    from `F \<in> G` and a_in have "a \<in> F" by blast
    from `F \<in> G` and b_in have "b \<in> F" by blast
    with `convex F` and c_in show "c \<in> F" 
      unfolding convex_def
      using \<open>a \<in> F\<close> by blast
  qed
  thus "c \<in> (\<Inter> G)" by blast
qed


section \<open>Polygon\<close>

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(* <polygon_line> : function creates a set from a list of points that forms a polygon line  *)
fun polygon_line :: "'a list \<Rightarrow> 'a set" where
  "polygon_line [] = {}"
| "polygon_line [a] = {a}"
| "polygon_line (a # b # p) = {a} \<union> (segment_oo a b) \<union> polygon_line (b # p)"

(* A more declarative definition of polygon line *)
lemma polygon_line:
  shows "polygon_line p = set p \<union> \<Union> (set (segments_oo p))"
  by (induction p rule: polygon_line.induct) auto  

lemma polygon_line_cc:
  assumes "length p \<ge> 2"
  shows "polygon_line p = \<Union> (set (segments_cc p))"
  by (simp add: assms inf_sup_aci(5) polygon_line segments_cc_oo)

lemma segment_cc_oo:
  "segment_cc a b = segment_oo a b \<union> {a, b}"
  by (auto simp add: segment_cc_def segment_oo_def)

lemma segments_oo_append [simp]:
  assumes "p1 \<noteq> []" "p2 \<noteq> []"
  shows "segments_oo (p1 @ p2) = segments_oo p1 @ [segment_oo (last p1) (hd p2)] @ segments_oo p2"
  using assms
  unfolding segments_oo
  by simp

lemma polygon_line_append [simp]:
  assumes "p1 \<noteq> []" "p2 \<noteq> []"
  shows "polygon_line (p1 @ p2) = polygon_line p1 \<union> segment_cc (last p1) (hd p2) \<union> polygon_line p2"
  using assms
  by (auto simp add: polygon_line segment_cc_oo)  

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(* <polygon> :polygon represents the union of the polygon line of list as and open along the first and last points of the polygon line
  - we assume that no three points are collinear  *)
definition polygon :: "'a list \<Rightarrow> 'a set" where
  "polygon p \<equiv> (segment_oo (hd p) (last p)) \<union> polygon_line p"

lemma polygon_polygon_line:
  assumes "p \<noteq> []"
  shows "polygon p = polygon_line (p @ [hd p])"
  using assms
  unfolding polygon_def
  by (auto simp add: segment_cc_oo polygon_line segment_oo_reorder)

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*<triangle>: polygon formed by three points*)
definition triangle :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "triangle a b c \<equiv> polygon [a, b, c]"

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*<quadrilateral>: polygon formed by four points*)
definition quadrilateral :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "quadrilateral a b c d \<equiv> polygon [a, b, c, d]"

(* Definicija nije dobra jer ne iskjucuje slucaj da tacka p0 pripada nekoj kasnijoj duzi *)
(*mi18107 Lidija Djalovic FORMULACIJA  *)
(* <simple_polygon_line> : for a given list of points, we check whether it forms a simple polygonal line *)
fun is_simple_polygon_line :: "'a list \<Rightarrow> bool" where 
  "is_simple_polygon_line [] = True"
| "is_simple_polygon_line [a] = True" 
| "is_simple_polygon_line (a # b # A) \<longleftrightarrow> 
   segment_oo a b \<inter> polygon_line (b # A) = {} \<and> is_simple_polygon_line (b # A)"

(* Verovatno i ovo sadrzi gresku slicnu prethodnoj definiciji *)            
(*mi18107 Lidija Djalovic FORMULACIJA  *)
(* <simple_polygon> : for a given list of points, we define a simple polygon using the simple_polygon_line function*)
definition is_simple_polygon :: "'a list \<Rightarrow> bool" where
  "is_simple_polygon as \<equiv> segment_oo (hd as) (last as) \<inter> polygon_line as = {} \<and> is_simple_polygon_line as"

definition connected_in_figure :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "connected_in_figure a b F \<equiv> \<exists> p. a = hd p \<and> b = last p \<and> (\<forall> x \<in> polygon_line p. x \<in> F)"

definition connected_figure :: "'a set \<Rightarrow> bool" where
  "connected_figure F \<equiv> \<forall> a \<in> F. \<forall> b \<in> F. connected_in_figure a b F"

lemma convex_connected:
  assumes "convex F"
  shows "connected_figure F"
  unfolding connected_figure_def
proof safe
  fix a b
  assume "a \<in> F" "b \<in> F"
  define p where "p = [a, b]"
  have "a = hd p \<and> b = last p \<and> (\<forall> x \<in> polygon_line p. x \<in> F)"
    using assms \<open>a \<in> F\<close> \<open>b \<in> F\<close>
    unfolding polygon_line p_def convex_def
    by (metis Sup_insert Un_insert_left Union_empty empty_set insert_iff last_ConsL last_ConsR list.sel(1) list.simps(15) not_Cons_self2 segments_oo.simps(2) segments_oo.simps(3) sup_bot_left sup_bot_right)
  then show "connected_in_figure a b F"
    unfolding connected_in_figure_def
    by blast
qed
  
lemma t3_7:
  assumes "c \<in> segment_oo a b"
  shows "segment_oo a b - {c} = segment_oo a c \<union> segment_oo c b"
proof-
  {
    fix x
    assume "x \<noteq> c" "bet a x b" 
    then have "bet a x c \<or> bet c x b"
      by (metis CollectD assms bet4_def segment_oo_def t2_8)
  }
  moreover
  {
    fix x
    assume "bet a x c" 
    then have "bet a x b"
      using assms
      by (metis bet4_divide(1) mem_Collect_eq segment_oo_def t2_6)
  }
  moreover
  {
    fix x
    assume "bet c x b"
    then have "bet a x b"
      using assms
      by (metis CollectD segment_oo_def t2_6 ax_ord_2 bet4_divide(1))
  }
  ultimately
  show ?thesis
    using ax_ord_1
    unfolding segment_oo_def
    by blast
qed

lemma t3_8:
  assumes "bet_n A"
  shows "segment_oo (hd A) (last A) - set A = (\<Union> (set (segments_oo A)))"
  using assms
  sorry



section \<open>Half-line\<close>

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
definition same_side :: "'a  \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "same_side t a b \<equiv> colinear t a b \<and> a \<noteq> t \<and> b \<noteq> t \<and> \<not>bet a t b"

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
definition opposite_side :: "'a  \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "opposite_side t a b \<equiv> colinear t a b \<and> a \<noteq> t \<and> b \<noteq> t \<and> bet a t b"

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
(*mi20357_Jelena_Mitrovic_DOKAZ  *)
theorem same_side_refl:
  assumes "a \<noteq> t"
  shows "same_side t a a"
  unfolding same_side_def
  by (metis assms ax_ord_1 distinct_length_2_or_more t1_1)

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
(*mi20357_Jelena_Mitrovic_DOKAZ  *)
theorem same_side_sym:
  assumes "same_side t a b "
  shows "same_side t b a"
  using assms
  unfolding same_side_def
  by (metis ax_ord_2 colinear_def)

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
(*mi20357_Jelena_Mitrovic_DOKAZ  *)
theorem same_side_trans:
  assumes "colinear_set {a, b, c, t}"
  assumes "same_side t a b" and "same_side t b c" 
  shows "same_side t a c"
proof (cases "a = b \<or> a = c \<or> b = c")
  case True
  then show ?thesis
    using assms same_side_refl
    by (auto simp add: same_side_def)
next
  case False

  obtain l where l: "inc_p_l t l" "inc_p_l a l" "inc_p_l b l" "inc_p_l c l"
    using assms(1)
    unfolding colinear_set_def
    by auto

  have "\<not>bet a t b" "\<not>bet b t c" "a \<noteq> t" "b \<noteq> t" "c \<noteq> t"
    using assms(2-3)
    unfolding same_side_def
    by auto

  have "\<not> bet a t c"
  proof
    assume "bet a t c"
    have "bet a b t \<or> bet b a t"
      using t2_1[of a t b] \<open>\<not> bet a t b\<close> False \<open>a \<noteq> t\<close> \<open>b \<noteq> t\<close> l ax_ord_2
      unfolding bet'_def one_of_three_def colinear_def
      by auto
    then have "bet b t c"
      using t2_5 t2_6 \<open>bet a t c\<close>
      by (metis bet4_def bet4_divide(2))
    then show False
      using \<open>\<not> bet b t c\<close>
      by simp
  qed
  then show ?thesis
    unfolding same_side_def colinear_def
    using \<open>inc_p_l a l\<close> \<open>inc_p_l c l\<close> \<open>inc_p_l t l\<close> \<open>a \<noteq> t\<close> \<open>c \<noteq> t\<close>
    by blast
qed

(* Number of equivalence classes is two *)
lemma
  assumes "t \<in> line_points l"
  shows "\<exists> x \<in> line_points l. \<exists> y \<in> line_points l. opposite_side t x y \<and> 
                (\<forall> z \<in> line_points l. same_side t x z \<or> same_side t y z)"
  sorry

(* assumes that t \<noteq> x *)
definition half_line_o where
  "half_line_o t x = {a. same_side t x a}"

definition half_line_c where
  "half_line_c t x = {t} \<union> {a. same_side t x a}"

lemma half_line_c_o:
  shows "half_line_c t x = {t} \<union> half_line_o t x"
  by (simp add: half_line_c_def half_line_o_def)
                  
(*mi19218 Luka Bura-FORMULACIJA*)
(*mi18059 Luka_Radenkovic_DOKAZ*)

lemma same_side_segment:
  assumes "same_side t x a" "same_side t x b" "c \<in> segment_oo a b"
  shows "same_side t x c"
proof -
  have "colinear t a b" using assms(1) unfolding same_side_def 
  by (smt (verit) assms(2) ax_inc_3 colinear_def same_side_def)
  have "a \<noteq> t" using assms(1) unfolding same_side_def by blast
  have "b \<noteq> t" using assms(2) unfolding same_side_def by blast
  have "\<not>bet a t b" using assms(1) unfolding same_side_def 
  by (smt (verit) GeometryOrder.ax_ord_5 GeometryOrder.t2_5 GeometryOrder.t2_6 GeometryOrder_axioms \<open>a \<noteq> t\<close> assms(2) ax_ord_2 bet4_def bet4_divide(2) same_side_def)

  have "c \<in> {c. bet a c b}" using assms(3) unfolding segment_oo_def by simp
  hence "bet a c b" by simp

  have "colinear a c b" using \<open>bet a c b\<close>
  by (simp add: ax_ord_1)
  
  have "c \<noteq> a" using \<open>bet a c b\<close>
  using ax_ord_1 by auto

  have "c \<noteq> b" using \<open>bet a c b\<close> 
  by (simp add: ax_ord_1)

  have "\<not>bet a t b" using assms(1) unfolding same_side_def
  using \<open>\<not> bet a t b\<close> by auto
  
  have "\<not>bet a t c" using \<open>bet a c b\<close> \<open>\<not>bet a t b\<close> 
  by (metis GeometryOrder.bet4_divide(1) GeometryOrder.t2_6 GeometryOrder_axioms)

  have "colinear t c x"
  by (smt (verit, ccfv_SIG) GeometryOrder.ax_ord_1 GeometryOrder_axioms \<open>bet a c b\<close> \<open>colinear t a b\<close> assms(2) ax_inc_3 colinear_def same_side_def)

  have "t \<noteq> a" using assms(1) unfolding same_side_def by blast
  have "t \<noteq> b" using assms(1) unfolding same_side_def
  using \<open>b \<noteq> t\<close> by auto
 
  show ?thesis unfolding same_side_def
    using \<open>colinear a c b\<close> \<open>c \<noteq> a\<close> \<open>c \<noteq> b\<close> \<open>\<not>bet a t c\<close> \<open>t \<noteq> a\<close> \<open>t \<noteq> b\<close>
  by (smt (verit, ccfv_SIG) GeometryOrder.ax_ord_2 GeometryOrder.ax_ord_5 GeometryOrder.bet4_def GeometryOrder.bet4_divide(2) GeometryOrder.same_side_def GeometryOrder.same_side_sym GeometryOrder.t2_6 GeometryOrder_axioms \<open>\<not> bet a t b\<close> \<open>bet a c b\<close> \<open>colinear t c x\<close> assms(1))
qed



(*mi19218 Luka Bura-DOKAZ*)
lemma convex_half_line_o:
  assumes "t \<noteq> x"  
  shows "convex (half_line_o t x)"
proof (unfold convex_def, intro ballI)
  fix a b c
  assume a_in: "a \<in> half_line_o t x" 
      and b_in: "b \<in> half_line_o t x" 
      and c_in: "c \<in> segment_oo a b"
  
  have a_cond: "same_side t x a" using a_in half_line_o_def by simp
  have b_cond: "same_side t x b" using b_in half_line_o_def by simp

  from c_in a_cond b_cond have "same_side t x c" 
    using same_side_segment by blast

  then show "c \<in> half_line_o t x"
    using half_line_o_def by simp
qed

lemma convex_half_line_c:
  assumes "t \<noteq> x"  
  shows "convex (half_line_c t x)"
 

definition half_line_o_compl_c where
  "half_line_o_compl_c t x = line_points (line t x) - half_line_o t x"

definition half_line_o_compl_o where
  "half_line_o_compl_o t x = line_points (line t x) - half_line_o t x - {t}"

definition half_line_c_compl_o where
  "half_line_c_compl_o t x = line_points (line t x) - half_line_c t x"

definition half_line_c_compl_c where
  "half_line_c_compl_c t x = line_points (line t x) - half_line_o t x \<union> {t}"

lemma half_line_o_compl_c:                    
  assumes "t \<noteq> x"
  shows "\<exists> y \<in> line_points (line t y). half_line_o_compl_c t x = half_line_c t y"
  sorry

lemma half_line_o_compl_o:
  assumes "t \<noteq> x"
  shows "\<exists> y \<in> line_points (line t y). half_line_o_compl_o t x = half_line_o t y"
  sorry

lemma half_line_c_compl_o:
  assumes "t \<noteq> x"
  shows "\<exists> y \<in> line_points (line t y). half_line_c_compl_o t x = half_line_o t y"
  sorry

lemma half_line_c_compl_c:
  assumes "t \<noteq> x"
  shows "\<exists> y \<in> line_points (line t y). half_line_c_compl_c t x = half_line_c t y"
  sorry

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
(*mi19218 Luka_Bura_DOKAZ*)
theorem t4_2:
assumes "set as \<subseteq> line_points l"
shows "\<exists> x1 x2. line_points l = set as \<union> 
                     (\<Union> (set (segments_oo as))) \<union>
                     half_line_o (hd as) x1 \<union>
                     half_line_o (last as) x2"
proof -
  have "\<forall> x \<in> set as. x \<in> line_points l" using assms by blast
  then obtain x1 x2 where x1_def: "x1 \<in> line_points l - set as" 
                        and x2_def: "x2 \<in> line_points l - set as" 
                        and not_in_as: "x1 \<noteq> x2 \<and> x1 \<notin> set as \<and> x2 \<notin> set as"
    sorry
  then have "line_points l \<subseteq> set as \<union>
                     (\<Union> (set (segments_oo as))) \<union>
                     half_line_o (hd as) x1 \<union>
                     half_line_o (last as) x2"
    using half_line_o_def sorry
  moreover have "set as \<union> 
                     (\<Union> (set (segments_oo as))) \<union>
                     half_line_o (hd as) x1 \<union>
                     half_line_o (last as) x2 \<subseteq> line_points l" using assms
    sorry
  ultimately show ?thesis by auto
qed

section \<open>Half-plane\<close>

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
definition same_side_l :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "same_side_l l a b \<longleftrightarrow> a \<notin> line_points l \<and> b \<notin> line_points l \<and> 
                         coplanar_set ({a, b} \<union> line_points l) \<and> 
                         segment_oo a b \<inter> line_points l = {}"

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
definition opposite_side_l :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "opposite_side_l l a b \<longleftrightarrow> a \<notin> line_points l \<and> b \<notin> line_points l \<and>
   coplanar_set ({a, b} \<union> line_points l) \<and>
   segment_oo a b \<inter> line_points l \<noteq> {}"

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
(*mi18107_Lidija_Djalovic_DOKAZ  *)
theorem same_side_l_refl:
  assumes "a \<notin> line_points l"
  shows "same_side_l l a a"
proof -
  have "a \<notin> line_points l" by (fact assms)
  moreover have "a \<notin> line_points l" by (fact assms)
  moreover have "coplanar_set ({a} \<union> line_points l)" 
  by (smt (verit, ccfv_threshold) Geometry.inc_l_pl_def Geometry.line_points_def Un_insert_left assms coplanar_set_def insert_iff mem_Collect_eq sup_bot_left t1_8)
  moreover have "segment_oo a a \<inter> line_points l = {}" 
  by (simp add: segment_oo_empty)
  ultimately show ?thesis by (auto simp add: same_side_l_def)
qed

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
(*mi18107_Lidija_Djalovic_DOKAZ  *)
theorem same_side_l_sym:
  assumes "same_side_l l a b"
  shows "same_side_l l b a"
proof -
  from assms obtain pl where
    "inc_p_pl a pl"
    "a \<notin> line_points l"
    "b \<notin> line_points l"
    "coplanar_set ({a, b} \<union> line_points l)"
    "segment_oo a b \<inter> line_points l = {}"
  by (meson ax_inc_5 same_side_l_def)
  moreover have "b \<notin> line_points l" using assms by (auto simp add: same_side_l_def)
  moreover have "a \<notin> line_points l" using assms by (auto simp add: same_side_l_def)
  moreover have "coplanar_set ({b, a} \<union> line_points l)"
  by (metis calculation(4) insert_commute)
  moreover have "segment_oo b a \<inter> line_points l = {}"
  by (simp add: calculation(5) segment_oo_reorder)  
  ultimately show ?thesis by (auto simp add: same_side_l_def)
qed
  
(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
(*mi18107_Lidija_Djalovic_DOKAZ  *)
theorem same_side_l_trans:
  assumes "coplanar_set ({a, b, c} \<union> line_points l)"
    "same_side_l l a b"
    "same_side_l l b c"
  shows "same_side_l l a c"
proof -
  from assms obtain pl where
    "inc_p_pl a pl"
    "a \<notin> line_points l"
    "b \<notin> line_points l"
    "coplanar_set ({a, b} \<union> line_points l)"
    "segment_oo a b \<inter> line_points l = {}"
  by (meson ax_inc_5 same_side_l_def)

  from assms obtain ql where
    "inc_p_pl b ql"
    "b \<notin> line_points l"
    "c \<notin> line_points l"
    "coplanar_set ({b, c} \<union> line_points l)"
    "segment_oo b c \<inter> line_points l = {}"
  by (meson ax_inc_5 same_side_l_def)

  have "a \<notin> line_points l" using assms by (auto simp add: same_side_l_def)
  have "c \<notin> line_points l" using assms by (auto simp add: same_side_l_def)

  have "coplanar_set ({a, c} \<union> line_points l)"
    using assms(1)
  using coplanar_set_def by auto

  have "segment_oo a c \<inter> line_points l = {}"
    sorry
  show ?thesis
    using `inc_p_pl a pl` `a \<notin> line_points l` `c \<notin> line_points l` `coplanar_set ({a, c} \<union> line_points l)` `segment_oo a c \<inter> line_points l = {}`
    by (auto simp add: same_side_l_def)
qed

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
theorem t4_4: 
  assumes "opposite_side_l l a b" "set p \<subseteq> plane_points (plane_p_l a l)" "hd p = a" "last p = b"
  shows "line_points l \<inter> polygon_line p \<noteq> {}"
  sorry

(* Number of equivalence classes is two *)
lemma
  assumes "inc_l_p l P"
  shows "\<exists> x \<in> plane_points P. \<exists> y \<in> plane_points P. opposite_side_l l x y \<and> 
                (\<forall> z \<in> plane_points P. same_side_l l x z \<or> same_side_l l y z)"
  sorry

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
(* assumes that \<not> inc_p_l x l *)
definition half_plane_o :: "'b \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "half_plane_o l x = {a. same_side_l l x a}"

definition half_plane_c where
  "half_plane_c l x = line_points l \<union> {a. same_side_l l x a}"

lemma half_plane_c_o:
  shows "half_plane_c l x = line_points l \<union> half_plane_o l x"
  by (simp add: half_plane_c_def half_plane_o_def)

definition half_plane_o_compl_c where
  "half_plane_o_compl_c l x = plane_points (plane_p_l x l) - half_plane_o l x"

(* TODO: other complements *)

lemma half_plane_o_complement:
  assumes "\<not> inc_p_l x l"
  shows "\<exists> y \<in> plane_points (plane_p_l x l). half_plane_o_compl_c l x = half_plane_c l y"
  sorry

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
definition same_side_pl :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "same_side_pl \<pi> a b \<longleftrightarrow> \<not> inc_p_pl a \<pi> \<and> \<not> inc_p_pl b \<pi> \<and> 
                          plane_points \<pi> \<inter> segment_oo a b = {}"

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
definition opposite_sides_pl :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "opposite_sides_pl \<pi> a b \<longleftrightarrow> \<not>inc_p_pl a \<pi> \<and> \<not>inc_p_pl b \<pi> \<and>
                               plane_points \<pi> \<inter> segment_oo a b \<noteq> {}"

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
(*mi17060_Aleksandar_Milosevic_DOKAZ*)
theorem same_side_pl_refl:
  assumes "\<not> inc_p_pl a \<pi>"
  shows "same_side_pl \<pi> a a"
  using assms coplanar_def segment_oo_empty
  unfolding same_side_pl_def
  by auto

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
(*mi17060_Aleksandar_Milosevic_DOKAZ*)
theorem same_side_pl_sym:
  assumes "same_side_pl \<pi> a b"
  shows "same_side_pl \<pi> b a"
  using assms segment_oo_reorder
  unfolding same_side_pl_def
  by auto

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
(*mi17060_Aleksandar_Milosevic_DOKAZ*)
theorem same_side_pl_trans:
  assumes "same_side_pl \<pi> a b" "same_side_pl \<pi> b c"
  shows "same_side_pl \<pi> a c"
proof (cases "a = b \<or> a = c \<or> b = c")
  case True
  then show ?thesis 
    using assms same_side_pl_refl
    by (auto simp add: same_side_pl_def)
next
  case False
  then show?thesis
    sorry
qed
  

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
(* assumes \<not> inc_p_pl a \<pi> *)
definition half_space_o :: "'c \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "half_space_o \<pi> a = {b. same_side_pl \<pi> a b}"

definition half_space_c :: "'c \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "half_space_c \<pi> a = plane_points \<pi> \<union> {b. same_side_pl \<pi> a b}"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
definition half_space_o_compl_c :: "'c \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "half_space_o_compl_c \<pi> a = - (half_space_o \<pi> a)"

(*mi19436_Ana_Bolovic_DOKAZ *)

lemma half_space_o_compl:
  shows "\<exists> b. half_space_o_compl_c \<pi> a = half_space_c \<pi> b"
    shows "\<exists> b. half_space_o_compl_c \<pi> a = half_space_c \<pi> b"
proof -
  let ?complement = "half_space_o \<pi> a"
  let ?half_space = "plane_points \<pi> \<union> {b. same_side_pl \<pi> a b}"

  have "\<forall>x. x\<in> ?complement \<longrightarrow> x \<notin> ?half_space"
    by (auto simp add: half_space_o_compl_c_def)
  
  have "\<forall>x. x \<in> ?half_space \<longrightarrow> x \<notin> ?complement"
    by (auto simp add: same_side_pl_def)

  have "\<forall>x. x \<in> ?complement \<longleftrightarrow> x \<notin> ?half_space"
    using \<open>\<forall>x. x \<in> ?complement \<longrightarrow> x \<notin> ?half_space\<close> \<open>\<forall>x. x \<in> ?half_space \<longrightarrow> x \<notin> ?complement\<close>
    by auto

  have "\<exists>b. \<forall>x. x \<in> ?complement \<longleftrightarrow> x \<notin> ?half_space"
    using exI by auto
then obtain b where "\<forall>x. x \<in> ?complement \<longleftrightarrow> x \<notin> ?half_space" by auto

  then have "half_space_o_compl_c \<pi> a = ?complement"
    unfolding half_space_o_compl_c_def by simp

  ultimately show ?thesis by s
qed
qed

section \<open>Angle\<close>

definition is_angle where 
 "is_angle a c b \<longleftrightarrow> a \<noteq> c \<and> b \<noteq> c \<and> half_line_c c a \<noteq> half_line_c c b"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
(* assume is_angle a c b *)
definition angle_line :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "angle_line a c b = half_line_c c a \<union> half_line_c c b"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
definition same_side_ang :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "same_side_ang \<pi> a c b x y \<equiv> 
   {a, b, c} \<subseteq> plane_points \<pi> \<and>
   {x, y} \<subseteq> plane_points \<pi> - angle_line a c b \<and>
   (\<exists>p. x = hd p \<and> y = last p \<and>
        polygon_line p \<subseteq> plane_points \<pi> \<and> 
        (polygon_line p \<inter> angle_line a c b) = {})"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
definition opposite_side_ang :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "opposite_side_ang \<pi> a c b x y \<equiv> 
   {a, b, c} \<subseteq> plane_points \<pi> \<and>
   {x, y} \<subseteq> plane_points \<pi> - angle_line a c b \<and>
   (\<forall> p. x = hd p \<and> y = last p \<and>
        polygon_line p \<subseteq> plane_points \<pi> \<and> 
        (polygon_line p \<inter> angle_line a b c) \<noteq> {})"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
lemma same_side_ang_refl:
  assumes "is_angle a c b"
  assumes "{a, b, c, x} \<subseteq> plane_points \<pi>"
  assumes "x \<notin> angle_line a c b"
  shows "same_side_ang \<pi> a c b x x"
  sorry

(*mi19432_Marko_Bekonja_FORMULACIJA *)
lemma same_side_ang_sym:
  assumes "is_angle a c b"
  assumes "same_side_ang \<pi> a c b x y" 
  shows "same_side_ang \<pi> a c b y x"
  sorry
 
(*mi19432_Marko_Bekonja_FORMULACIJA *)
lemma on_the_same_side_of_the_angle_line_transitivity:
  assumes "is_angle a c b"
  assumes "same_side_ang \<pi> a c b x y"
      and "same_side_ang \<pi> a c b y z"
    shows "same_side_ang \<pi> a c b x z"
  sorry

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
definition angle_o :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "angle_o \<pi> a c b x \<equiv> {y. same_side_ang \<pi> a c b x y}"

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
definition angle_c :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "angle_c \<pi> a c b x \<equiv> angle_o \<pi> a c b x \<union> angle_line a c b"

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
definition angle_o_compl_o :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "angle_o_compl_o \<pi> a c b x \<equiv> plane_points \<pi> - angle_c \<pi> a c b x"
  
(*mi19208_Palve_Ciric_FORMULACIJA*)
(* Alternative definition of the definition above *)
lemma angle_o_compl_o:
  "angle_o_compl_o \<pi> a c b x \<equiv> {y. opposite_side_ang \<pi> a c b x y}"
  sorry

lemma angle_compl_not_empty:
  "angle_o_compl_o \<pi> a c b x \<noteq> {}"
  sorry

lemma
  assumes "is_angle a c b" "\<not> colinear a c b"
  shows "one_of_two (convex (angle_o \<pi> a c b x)) (convex (angle_o_compl_o \<pi> a c b x))"
  sorry

definition convex_angle_o :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "convex_angle_o \<pi> a c b = (THE \<alpha>. \<exists> x \<in> plane_points \<pi>. \<alpha> = angle_o \<pi> a c b x \<and> convex \<alpha>)"

(*mi19208_Pavle_Ciric_FORMULAICIJA*)
(*mi19208_Pavle_Ciric_DOKAZ*)
theorem t5_1:
  assumes "{P, X, Q} \<subseteq> plane_points \<pi>" and "is_angle P X Q"
  shows "(\<forall>x \<in> plane_points \<pi> - angle_line P X Q. x \<in> angle_o \<pi> P X Q x) \<and>
         (\<forall>x \<in> plane_points \<pi> - angle_line P X Q.
          \<forall>y \<in> plane_points \<pi> - angle_line P X Q.
          same_side_ang \<pi> P X Q x y \<longleftrightarrow> angle_o \<pi> P X Q x = angle_o \<pi> P X Q y) \<and>
         (\<forall>x \<in> plane_points \<pi> - angle_line P X Q.
          \<forall>y \<in> plane_points \<pi> - angle_line P X Q.
               angle_o \<pi> P X Q x = angle_o \<pi> P X Q y \<longleftrightarrow> 
               angle_o \<pi> P X Q x \<inter> angle_o \<pi> P X Q y \<noteq> {})"
         (is "?th1 \<and> ?th2 \<and> ?th3")
proof-
  have "?th1"
  proof
    fix x
    assume "x \<in> plane_points \<pi> - angle_line P X Q"
    then have "same_side_ang \<pi> P X Q x x"
      using assms same_side_ang_refl by auto
    then show "x \<in> angle_o \<pi> P X Q x" 
      using angle_o_def by auto
  qed
  moreover have "?th2"
  proof
    fix x
    assume "x \<in> plane_points \<pi> - angle_line P X Q" (is "x \<in> ?x_dom")
    show "\<forall>y\<in>plane_points \<pi> - angle_line P X Q.
              same_side_ang \<pi> P X Q x y = 
              (angle_o \<pi> P X Q x = angle_o \<pi> P X Q y)"
    proof
      fix y
      assume "y \<in> plane_points \<pi> - angle_line P X Q" (is "y \<in> ?y_dom")
      show "same_side_ang \<pi> P X Q x y = (angle_o \<pi> P X Q x = angle_o \<pi> P X Q y)"
      proof
        show "same_side_ang \<pi> P X Q x y \<Longrightarrow> angle_o \<pi> P X Q x = angle_o \<pi> P X Q y"
        proof
          assume asm:"same_side_ang \<pi> P X Q x y"
          show "angle_o \<pi> P X Q x \<subseteq> angle_o \<pi> P X Q y"
          proof
            fix z
            assume "z \<in> angle_o \<pi> P X Q x"
            then have "same_side_ang \<pi> P X Q x z" 
              using angle_o_def by auto
            then have "same_side_ang \<pi> P X Q y z"
              using assms asm same_side_ang_refl same_side_ang_sym
              using on_the_same_side_of_the_angle_line_transitivity
              by meson
            then show "z \<in> angle_o \<pi> P X Q y" 
              using angle_o_def by auto
          qed
        next
          assume "same_side_ang \<pi> P X Q x y"
          show "angle_o \<pi> P X Q y \<subseteq> angle_o \<pi> P X Q x" sorry
        qed
      next
        show "angle_o \<pi> P X Q x = angle_o \<pi> P X Q y \<Longrightarrow> same_side_ang \<pi> P X Q x y"
          using angle_o_def
          using \<open>y \<in> ?y_dom\<close> calculation 
          by blast
      qed
    qed
  qed
  moreover have "?th3"
  proof
    fix x
    assume x_def:"x \<in> plane_points \<pi> - angle_line P X Q" (is "x \<in> ?x_dom")
    show "\<forall>y\<in>plane_points \<pi> - angle_line P X Q.
             angle_o \<pi> P X Q x = angle_o \<pi> P X Q y \<longleftrightarrow> 
             angle_o \<pi> P X Q x \<inter> angle_o \<pi> P X Q y \<noteq> {}"
    proof
      fix y
      assume y_def:"y \<in> plane_points \<pi> - angle_line P X Q" (is "y \<in> ?y_dom")
      show "angle_o \<pi> P X Q x = angle_o \<pi> P X Q y \<longleftrightarrow> 
           angle_o \<pi> P X Q x \<inter> angle_o \<pi> P X Q y \<noteq> {}"
        unfolding one_of_two_def
      proof
        assume asm:"angle_o \<pi> P X Q x = angle_o \<pi> P X Q y"
        obtain x0 where 1:"x0 \<in> angle_o \<pi> P X Q x"
          using \<open>x \<in> ?x_dom\<close> calculation(1) by blast
        then have 2:"x0 \<in> angle_o \<pi> P X Q y"
          using asm by auto

        from 1 2 show "angle_o \<pi> P X Q x \<inter> angle_o \<pi> P X Q y \<noteq> {}" by auto
      next 
        assume "angle_o \<pi> P X Q x \<inter> angle_o \<pi> P X Q y \<noteq> {}"
        then obtain z where "z \<in> plane_points \<pi> - angle_line P X Q \<and>
                            z \<in> angle_o \<pi> P X Q x \<and> z \<in> angle_o \<pi> P X Q y"
          using angle_compl_not_empty angle_o_compl_o opposite_side_ang_def
          by fastforce
        then have "same_side_ang \<pi> P X Q x z \<and>
                   same_side_ang \<pi> P X Q y z \<and>
                   z \<in> plane_points \<pi> - angle_line P X Q"
          using angle_o_def by auto
        then have "angle_o \<pi> P X Q x = angle_o \<pi> P X Q z \<and>
                   angle_o \<pi> P X Q y = angle_o \<pi> P X Q z \<and>
                  z \<in> plane_points \<pi> - angle_line P X Q"
          using \<open>?th2\<close> x_def y_def
          by auto
          
        then show "angle_o \<pi> P X Q x = angle_o \<pi> P X Q y" by auto
      qed
    qed
  qed
  ultimately show ?thesis by auto         
qed
         

lemma t5_2_lemma1:
  assumes "{P, X, Q, A,T} \<subseteq> plane_points \<pi>"
      and "is_angle P X Q"
    shows "T \<in> angle_c \<pi> P X Q A \<longleftrightarrow> T \<notin> angle_o_compl_o \<pi> P X Q A"
  unfolding angle_o_compl_o_def
  using assms
  by auto

lemma t5_2_lemma2:
  assumes "{P, X, Q, A, B} \<subseteq> plane_points \<pi>"
      and "is_angle P X Q"
      and "same_side_ang \<pi> P X Q A B"
    shows "\<exists>p. A = hd p \<and> B = last p \<and>
                   (polygon_line p) \<subseteq> plane_points \<pi> \<and>
                   (\<forall>x \<in> (polygon_line p). x \<in> angle_o \<pi> P X Q A)"
  sorry
    
lemma t5_2_lemma3:
  assumes "{P, X, Q, A, T} \<subseteq> plane_points \<pi>"
      and "is_angle P X Q"
      and "T \<in> angle_line P X Q"
    shows "\<forall>x \<in> angle_o \<pi> P X Q A. same_side_l (line X T) A x"
  sorry

lemma t5_3_lemma4:
  assumes "{P, X, Q, A, B} \<subseteq> plane_points \<pi>"
      and "is_angle P X Q"
      and "B \<in> angle_o_compl_o \<pi> P X Q A"
    shows "\<forall>x \<in> angle_o_compl_o \<pi> P X Q A. x \<in> angle_o \<pi> P X Q B"
  sorry

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
(*mi19208_Pavle_Ciric_DOKAZ*)
theorem t5_2:
  assumes "{P, X, Q, A, B} \<subseteq> plane_points \<pi>" "is_angle P X Q"
      and "A \<in> angle_line P X Q"
      and "B \<notin> angle_line P X Q"
    shows "\<exists>p. A = hd p \<and> B = last p \<and> 
           polygon_line p \<subseteq> plane_points \<pi> \<and>
           (\<forall>x \<in> (polygon_line p - {A}). x \<in> angle_o \<pi> P X Q B)"

proof (cases "segment_oo A B \<inter> angle_o_compl_o \<pi> P X Q B = {}")
  case True
  define p_line where "p_line = [A,B]"
  then show ?thesis
  proof (rule_tac x=p_line in exI)
    have "A = hd p_line" 
      using p_line_def
      by auto
    moreover 
    have "B = last p_line" 
      using p_line_def
      by auto
    moreover 
    have p_line_subset_of_plane:"polygon_line p_line \<subseteq> plane_points \<pi>" 
      sorry
    moreover 
    have "(\<forall> x. x \<in> polygon_line p_line - {A} \<longrightarrow> x \<in> angle_o \<pi> P X Q B)"
    proof
      fix x
      show "x \<in> polygon_line p_line - {A} \<longrightarrow> x \<in> angle_o \<pi> P X Q B"
      proof
        assume x_def:"x \<in> polygon_line p_line - {A}"
        then have 1:"x = B \<or> x \<in> segment_oo A B"
          unfolding p_line_def
          by auto
        have 2:"x = B \<longrightarrow> x \<in> angle_o \<pi> P X Q B"
          unfolding angle_o_def
          using same_side_ang_refl assms
          by auto
        have 3:"x \<in> segment_oo A B \<longrightarrow> x \<in> angle_o \<pi> P X Q B"
          sorry
        from 1 2 3 show "x \<in> angle_o \<pi> P X Q B"
          unfolding angle_o_def
          by auto
      qed
    qed
    ultimately show "A = hd p_line \<and>
                     B = last p_line \<and>
                     polygon_line p_line \<subseteq> plane_points \<pi> \<and>
                     (\<forall>x \<in> polygon_line p_line - {A}. x \<in> angle_o \<pi> P X Q B)" by auto
  qed
next
  case False
  then have "\<exists>x. x \<in> (segment_oo A B \<inter> angle_o_compl_o \<pi> P X Q B)" by auto
  then obtain x where x_def:"x \<in> (segment_oo A B \<inter> angle_o_compl_o \<pi> P X Q B)" by auto
  then have x_in_B_comp:"x \<in> angle_o_compl_o \<pi> P X Q B"
    using x_def
    by auto
  then have x_in_angle:"x \<in> angle_o \<pi> P X Q x"
    unfolding angle_o_compl_o_def angle_o_def angle_c_def
    using assms same_side_ang_refl
    by auto

  define hp1 where "hp1 = half_plane_o (line X A) x"

  have compl_all_in_hp1:"\<forall>x \<in> angle_o_compl_o \<pi> P X Q B. x \<in> hp1"
    unfolding hp1_def half_plane_o_def angle_o_def 
    using assms t5_2_lemma3 x_in_angle x_in_B_comp t5_3_lemma4 angle_o_compl_o_def
    by auto

  have "\<not> inc_p_l x (line X A)" sorry

  then have "\<exists> y \<in> plane_points (plane_p_l x (line X A)). 
       half_plane_o_compl_c (line X A) x = half_plane_c (line X A) y"
    using half_plane_o_complement
    by auto

  then obtain T where T_def:"T \<in> plane_points (plane_p_l x (line X A)) \<and>
                      half_plane_o_compl_c (line X A) x = half_plane_c (line X A) T"
    by auto

  then have T_in_plane:"T \<in> plane_points \<pi>" sorry
  then have T_not_in_angle_line:"T \<notin> angle_line P X Q" sorry

  define hp2 where "hp2 = half_plane_c (line X A) T"

  have T_in_hp2:"T \<in> hp2"
    unfolding hp2_def half_plane_c_def
    using same_side_l_refl
    by auto

  have hp1_inter_hp2:"hp1 \<inter> hp2 = {}"
    unfolding hp1_def hp2_def
    using T_def half_plane_o_compl_c_def 
    by auto

  from compl_all_in_hp1 hp1_inter_hp2
  have 1:"\<forall>x \<in> angle_o_compl_o \<pi> P X Q B. (x \<notin> hp2)"
    by auto

  then have "T \<notin> angle_o_compl_o \<pi> P X Q B"
    using T_in_hp2
    by auto

  then have T_in_c_angle:"T \<in> angle_c \<pi> P X Q B"
    using assms t5_2_lemma1 T_in_plane
    by auto

  then have "T \<in> angle_o \<pi> P X Q B"
    unfolding angle_c_def
    using T_not_in_angle_line
    by auto

  then have T_same_side_B:"same_side_ang \<pi> P X Q B T"
    unfolding angle_o_def
    by auto

  have "\<exists>p . B = hd p \<and> T = last p \<and>
                     (polygon_line p) \<subseteq> plane_points \<pi> \<and>
                     (\<forall>x \<in> (polygon_line p). x \<in> angle_o \<pi> P X Q B)"
    using assms(1) assms(2) T_same_side_B  T_in_plane t5_2_lemma2
    by auto

  then obtain p1 where p1_def:"B = hd p1 \<and> T = last p1 \<and>
                              (polygon_line p1) \<subseteq> plane_points \<pi> \<and>
                              (\<forall>x \<in> (polygon_line p1). x \<in> angle_o \<pi> P X Q B)"
    by auto

  define p_line where "p_line = A # p1"

  then show ?thesis sorry
qed

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
(*mi19208_Pavle_Ciric_DOKAZ*)
theorem t5_3:                    
  assumes "is_angle A T B" "{T, A, B, C} \<subseteq> plane_points \<pi>"
  shows "\<exists> X1 X2. angle_o \<pi> A T C X1 \<inter> angle_o \<pi> B T C X2 = {} \<and>
                  (\<forall>x \<in> plane_points \<pi> - angle_line A T B.
                   x \<notin> angle_o \<pi> A T C X1 \<and> x \<notin> angle_o \<pi> B T C X2 \<longrightarrow>
                   x \<in> angle_o_compl_o \<pi> A T B C)"
  using assms
proof-

  define \<beta> where "\<beta> = angle_o_compl_o \<pi> A T C B"
  then obtain b where b_def:"b \<in> \<beta>" 
    using angle_compl_not_empty by fastforce
  then have b_in_plane:"b \<in> plane_points \<pi>" 
    unfolding angle_o_compl_o_def \<beta>_def by auto
  have \<beta>_def_2:"\<beta> = angle_o \<pi> A T C b" sorry

  define \<alpha> where "\<alpha> = angle_o_compl_o \<pi> B T C A"
  then obtain a where "a \<in> \<alpha>" 
    using angle_compl_not_empty by fastforce
  then have a_in_plane:"a \<in> plane_points \<pi>"
    unfolding \<alpha>_def angle_o_compl_o_def by auto
  have \<alpha>_def_2:"\<alpha> = angle_o \<pi> B T C a" sorry

  have 1:"\<alpha> \<inter> \<beta> = {}"
  proof (rule ccontr)
    assume "\<alpha> \<inter> \<beta> \<noteq> {}"
    then have "\<exists> X. X \<in> \<alpha> \<and> X \<in> \<beta>" 
      by auto
    then obtain X where X_def:"X \<in> \<alpha> \<and> X \<in> \<beta>" 
      by auto
    then have "\<forall>Y \<in> \<beta>. same_side_ang \<pi> A T C X Y" sorry
    then obtain Y where Y_def:"Y \<in> \<beta> \<and> same_side_ang \<pi> A T C X Y"
      using X_def by auto
    
    have "same_side_ang \<pi> A T C B Y"
    proof-
      from Y_def obtain l where l_def:"X = hd l \<and> Y = last l \<and>
                                      polygon_line l \<subseteq> plane_points \<pi> \<and> 
                                      (polygon_line l \<inter> angle_line A T C) = {}"
        unfolding same_side_ang_def
        by auto

      from X_def obtain l' where l'_def:"B = hd l' \<and> X = last l' \<and> 
                                        polygon_line l' \<subseteq> plane_points \<pi> \<and>
                                        ((polygon_line l' - {B}) \<inter> angle_line B T C = {})"
        using t5_2
        sorry
      then have "polygon_line l' \<inter> angle_line A T C = {}" sorry

      define L where "L = l' @ l"
      have "B = hd L \<and> Y = last L \<and> 
            polygon_line L \<subseteq> plane_points \<pi> \<and>
            polygon_line L \<inter> angle_line A C T = {}"
        unfolding L_def
        using l_def l'_def
        sorry
      then show "same_side_ang \<pi> A T C B Y"
        using Y_def \<beta>_def angle_o_compl_o opposite_side_ang_def 
        by auto
    qed
    then show False
      using Y_def \<beta>_def angle_o_compl_o angle_compl_not_empty opposite_side_ang_def 
      by fastforce
  qed
  have 2:"\<forall>x \<in> plane_points \<pi> - angle_line A T B. 
          x \<notin> \<alpha> \<and> x \<notin> \<beta> \<longrightarrow> x \<in> angle_o_compl_o \<pi> A T B C"
  proof
    fix z
    assume z_in_plane:"z \<in> plane_points \<pi> - angle_line A T B"
    show "z \<notin> \<alpha> \<and> z \<notin> \<beta> \<longrightarrow> z \<in> angle_o_compl_o \<pi> A T B C"
    proof
      assume "z \<notin> \<alpha> \<and> z \<notin> \<beta>"

      define \<gamma> where "\<gamma> = angle_o_compl_o \<pi> A T B C"
      then obtain w where w_def:"w \<in> \<gamma>"
        using angle_compl_not_empty
        by fastforce
      then have w_in_plane:"w \<in> plane_points \<pi>" sorry
      have \<gamma>_def_2:"\<gamma> = angle_o \<pi> A T B w" sorry

      have "same_side_ang \<pi> A T B w z"
      proof (cases "segment_oo w z \<inter> angle_line A T B = {}")
        case True
        define p where "p = [w, z]"
        then have "w = hd p \<and> z = hd p" sorry
        moreover have "polygon_line p \<subseteq> plane_points \<pi>" sorry
        moreover have "polygon_line p \<inter> angle_line A T B = {}"
          using \<gamma>_def \<gamma>_def_2 w_def angle_o_def angle_compl_not_empty angle_o_compl_o opposite_side_ang_def 
          by fastforce
        ultimately show ?thesis
          using assms same_side_ang_def w_in_plane w_def \<gamma>_def angle_o_compl_o_def angle_c_def
          using z_in_plane \<gamma>_def_2 angle_o_def
          by auto
      next
        show ?thesis sorry
      qed
      then have "z \<in> \<gamma>"
        using \<gamma>_def_2 angle_o_def
        by auto
      then show "z \<in> angle_o_compl_o \<pi> A T B C"
        using \<gamma>_def_2 \<gamma>_def
        by auto
      qed
  qed
  from 1 2
  show ?thesis
    using \<alpha>_def_2 \<beta>_def_2
    by auto
qed


(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
(* \<open>intersects_l_soo\<close> \<rightarrow> do line and open_segment have intersection. *)
definition intersects_l_soo :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "intersects_l_soo l a b \<equiv> \<exists> x . inc_p_l x l \<and> x \<in> segment_oo a b"

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
(* \<open>intersection_l_soo\<close> is a point where line and open_segment intersect *)
definition intersection_l_soo :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "intersection_l_soo l a b \<equiv> THE x. inc_p_l x l \<and> x \<in> segment_oo a b"

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
theorem t5_6:
  assumes "is_angle P T Q" "M \<in> half_line_o T X" "{P, T, Q, X} \<subseteq> plane_points \<pi>"
  shows "M \<in> convex_angle_o \<pi> P T Q \<longleftrightarrow> half_line_o T X \<inter> segment_oo P Q = {}"
  sorry

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
definition line_span :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "line_span t a b = \<Union> ((\<lambda> x. line_points (line t x)) ` segment_cc a b)"

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
theorem t5_8:
  assumes "\<not> colinear A B C" 
  shows "inc_p_pl D (plane A B C) \<longleftrightarrow> D \<in> line_span A B C \<or> 
                                      D \<in> line_span B C A \<or> 
                                      D \<in> line_span C A B"
  sorry
auto


chapter \<open>Orientation\<close>

(*mi17307_Dimitrije_Stankov_FORMULACIJA*)
fun connected_s_s :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "connected_s_s (a, b) (c, d) \<longleftrightarrow> b = c \<and> colinear a b d"

lemma connected_s_s: 
  shows "connected_s_s (a, b) (c, d) \<longleftrightarrow> b = c \<and> colinear a c d"
  by auto

(*mi17307_Dimitrije_Stankov_FORMULACIJA*)
(* Use under assumption: length ss > 1 *)
fun chain_s_o :: "('a \<times> 'a) list \<Rightarrow> bool" where
  "chain_s_o (s\<^sub>1 # s\<^sub>2 # ss) \<longleftrightarrow> connected_s_s s\<^sub>1 s\<^sub>2 \<and> chain_s_o (s\<^sub>2 # ss)"
| "chain_s_o _ \<longleftrightarrow> True"

(*mi18131_Jelena_Bondzic_FORMULACIJA*)
definition chain_s_fst :: "('a \<times> 'a) list \<Rightarrow> 'a \<times> 'a" where
  "chain_s_fst ss \<equiv> hd ss" 

(*mi18131_Jelena_Bondzic_FORMULACIJA*)
definition chain_s_lst :: "('a \<times> 'a) list \<Rightarrow> 'a \<times> 'a" where
  "chain_s_lst ss \<equiv> last ss" 

(*mi18131_Jelena_Bondzic_FORMULACIJA*)
(* Use under assumption: length ss > 1 *)
definition chain_s_c :: "('a \<times> 'a) list \<Rightarrow> bool" where
  "chain_s_c ss \<longleftrightarrow> hd ss = last ss \<and> chain_s_o ss"

(*mi18131_Jelena_Bondzic_FORMULACIJA*)
(* Use under assumption: lenght ss > 1 *)
definition connects_chain_s_s :: "('a \<times> 'a) list \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "connects_chain_s_s ss s\<^sub>1 s\<^sub>2 \<longleftrightarrow> chain_s_fst ss = s\<^sub>1 \<and> chain_s_lst ss = s\<^sub>2 \<and> chain_s_o ss"

(*mi18131_Jelena_Bondzic_FORMULACIJA*)
theorem t9_1:
  assumes "inc_p_l a l" "inc_p_l b l" "inc_p_l c l" "inc_p_l d l"
  shows "\<exists> ss. length ss > 1 \<and> connects_chain_s_s ss (a, b) (c, d)"
  sorry

(*mi18131_Jelena_Bondzic_FORMULACIJA*)
fun preoritation_s_s :: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool" where
  "preoritation_s_s (a, b) (c, d) \<longleftrightarrow> connected_s_s (a, b) (c, d) \<and> \<not> bet a b d"

lemma preoritation_s_s:
  shows "preoritation_s_s (a, b) (c, d) \<longleftrightarrow> connected_s_s (a, b) (c, d) \<and> \<not> bet a c d"
  by auto

(*mi19150_Aleksandra_Labovic_FORMULACIJA*)
(* Use under assumption: length ss > 1 *)
fun chain_s_parity :: "('a \<times> 'a) list \<Rightarrow> bool" where
  "chain_s_parity (s\<^sub>1 # s\<^sub>2 # ss) = 
      (if preoritation_s_s s\<^sub>1 s\<^sub>2 then \<not> chain_s_parity (s\<^sub>2 # ss) else chain_s_parity (s\<^sub>2 # ss))"
| "chain_s_parity _ = True"

(*mi19150_Aleksandra_Labovic_FORMULACIJA*)
theorem t9_2:
  assumes "length ss > 1" "chain_s_c ss"
  shows "chain_s_parity ss"
  sorry

(*mi19150_Aleksandra_Labovic_FORMULACIJA*)
theorem t9_3:
  assumes "length ss > 1" "length ss' > 1" 
      and "chain_s_fst ss = chain_s_fst ss'" "chain_s_lst ss = chain_s_lst ss'"
    shows "chain_s_parity ss = chain_s_parity ss'"
  sorry

(*mi19150_Aleksandra_Labovic_FORMULACIJA*)
definition same_direction :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "same_direction s\<^sub>1 s\<^sub>2 = (\<forall> ss. length ss > 1 \<and> connects_chain_s_s ss s\<^sub>1 s\<^sub>2 \<and> chain_s_parity ss)"

(*mi19150_Aleksandra_Labovic_FORMULACIJA*)
definition opposite_direction :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "opposite_direction s\<^sub>1 s\<^sub>2 = (\<not> same_direction s\<^sub>1 s\<^sub>2)"

(*mi18197_Nikola_Milosevic_FORMULACIJA*)
theorem same_direction_reflexivity:
  shows "same_direction s s"
  sorry

(*mi18197_Nikola_Milosevic_FORMULACIJA*)
theorem same_direction_symmetry:
  assumes "same_direction s\<^sub>1 s\<^sub>2"
    shows "same_direction s\<^sub>2 s\<^sub>1"
  sorry

theorem same_direction_transitivity:
  assumes "same_direction s\<^sub>1 s\<^sub>2"
      and "same_direction s\<^sub>2 s\<^sub>3"
    shows "same_direction s\<^sub>1 s\<^sub>3"
  sorry

(*mi18197_Nikola_Milosevic_FORMULACIJA*)
fun connected_t_t :: "('a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "connected_t_t (a\<^sub>0, a\<^sub>1, a\<^sub>2) (b\<^sub>0, b\<^sub>1, b\<^sub>2) \<longleftrightarrow> a\<^sub>1 = b\<^sub>0 \<and> a\<^sub>2 = b\<^sub>1 \<and> coplanar_set {a\<^sub>0, a\<^sub>1, a\<^sub>2, b\<^sub>2}"

(*mi18197_Nikola_Milosevic_FORMULACIJA*)
(* Use under assumption: length ts > 1 *)
fun chain_t_o ::   "('a \<times> 'a \<times> 'a) list \<Rightarrow> bool" where
  "chain_t_o (t\<^sub>1 # t\<^sub>2 # ts) \<longleftrightarrow> connected_t_t t\<^sub>1 t\<^sub>2 \<and> chain_t_o (t\<^sub>2 # ts)"
| "chain_t_o _ \<longleftrightarrow> True"

(*mi18197_Nikola_Milosevic_FORMULACIJA*)
definition chain_t_fst :: "('a \<times> 'a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<times> 'a )" where
  "chain_t_fst ts = hd ts"

(*mi18197_Nikola_Milosevic_FORMULACIJA*)
definition chain_t_lst :: "('a \<times> 'a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<times> 'a )" where
  "chain_t_lst ts = last ts"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* Use under assumption: length ts > 1 *)
definition chain_t_c :: "('a \<times> 'a \<times> 'a) list \<Rightarrow> bool" where
  "chain_t_c ts \<equiv> chain_t_fst ts = chain_t_lst ts \<and> chain_t_o ts"

(* mi19143_Iva_Citlucanin_FORMULACIJA*)
definition connects_chain_t_t :: "('a \<times> 'a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "connects_chain_t_t ts t\<^sub>1 t\<^sub>2 \<equiv> chain_t_fst ts = t\<^sub>1 \<and> chain_t_lst ts = t\<^sub>2 \<and> chain_t_o ts"

(* mi19143_Iva_Citlucanin_FORMULACIJA*)
theorem t9_5:
  assumes "inc_p_pi a\<^sub>0 \<pi>" "inc_p_pi a\<^sub>1 \<pi>" "inc_p_pi a\<^sub>2 \<pi>" 
      and "inc_p_pi b\<^sub>0 \<pi>" "inc_p_pi b\<^sub>1 \<pi>" "inc_p_pi b\<^sub>2 \<pi>"
    shows " \<exists> ts. length ts > 1 \<and> connects_chain_t_t ts t\<^sub>1 t\<^sub>2"
  sorry

(* mi19143_Iva_Citlucanin_FORMULACIJA*)
fun preorientation_t_t :: "('a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "preorientation_t_t (a\<^sub>0, a\<^sub>1, a\<^sub>2) (b\<^sub>0, b\<^sub>1, b\<^sub>2) \<longleftrightarrow> connected_t_t (a\<^sub>0, a\<^sub>1, a\<^sub>2) (b\<^sub>0, b\<^sub>1, b\<^sub>2) \<and> opposite_side_l (line a\<^sub>1 a\<^sub>2) a\<^sub>0 b\<^sub>2"

(* mi19143_Iva_Citlucanin_FORMULACIJA*)
(* Use under assumption: length ts > 1 *)
fun chain_t_parity :: "('a \<times> 'a \<times> 'a) list \<Rightarrow> bool" where
  "chain_t_parity (t\<^sub>1 # t\<^sub>2 # ts) = (if preorientation_t_t t\<^sub>1 t\<^sub>2 then \<not> chain_t_parity (t\<^sub>2 # ts) else chain_t_parity (t\<^sub>2 # ts))"
| "chain_t_parity _ = True"

(* mi19143_Iva_Citlucanin_FORMULACIJA*)
(* Function should never return 0 *)
definition fun_a :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> int" where
  "fun_a a b l = (if same_side_l l a b then 1 else if opposite_side_l l a b then -1 else 0)"

(*mi19180_Pavle_Parandilovic_FORMULACIJA*)
theorem fun_a_first_property:
  assumes "\<not> inc_p_l A p"
  assumes "\<not> inc_p_l B p"
  assumes "\<not> inc_p_l C p"
  assumes "segment_oo A B \<inter> line_points p = {}"
  assumes "segment_oo B C \<inter> line_points p = {}" 
  assumes "segment_oo  A C \<inter> line_points p = {}"
  assumes "coplanar_set({A, B, C} \<union> line_points p) "  
  shows "fun_a A B p = 1" "fun_a B C p = 1" "fun_a A C p = 1"
  sorry


(*mi19180_Pavle_Parandilovic_FORMULACIJA*)
theorem fun_a_second_property:
  assumes "coplanar_set({A, B, C, D} \<union> line_points p)"
  assumes "\<not>colinear A B D"
  assumes "\<not>colinear A C D"
  assumes "\<not>colinear B C D"
  assumes "\<not>colinear A B C"
  assumes "segment_oo A B \<inter> line_points p = {}"
  assumes "segment_oo B C \<inter> line_points p = {}" 
  assumes "segment_oo  A C \<inter> line_points p = {}"
  assumes "segment_oo A D \<inter> line_points p = {}"
  assumes "segment_oo  B D \<inter> line_points p = {}"
  assumes "segment_oo  C D \<inter> line_points p = {}"
  shows "fun_a A B (line C D) = -1" "fun_a B C (line A D) = -1" "fun_a C A (line B D) = -1"
  sorry

(*mi19180_Pavle_Parandilovic_FORMULACIJA*)
theorem fun_a_third_property:
  assumes "A = {a. list plane_points}"
  assumes "card A = m"
  assumes "finite A"
  shows "\<exists> A'. card A' = m \<and> finite A' \<and> (\<forall> Ai' Aj' Ak' Al'. Ai' \<in> A' \<and> Aj' \<in> A' \<and> Ak' \<in> A' \<and> 
        Al' \<in> A' \<and> Ai' \<noteq> Aj' \<and> Aj' \<noteq> Ak' \<and> Ak' \<noteq> Al' \<and> Ai' \<noteq> Ak' \<and> Ai' \<noteq> Al' \<and> Aj' \<noteq> Al'
        \<longrightarrow> fun_a Ai' Aj' (line Ak' Al') = fun_a Ai Aj (line Ak Al))"
  sorry

(*mi19180_Pavle_Paranidilovic_FORMULACIJA*)
theorem t9_6:
  assumes "chain_t_c ts \<and> m = length ts"
  shows "\<Prod>i=0..<m. fun_a((ts ! i) (ts ! (i+3)) (line (ts ! (i+1)) (ts ! (i+2)))) = 1"
  sorry

(*mi19180_Pavle_Parandilovic_FORMULACIJA*)
theorem t9_7:
  assumes "chain_t_fst l1 = chain_t_fst l2"
  assumes "chain_t_lst l1 = chain_t_lst l2"
  assumes "chain_t_parity l1 = True"
  assumes "chain_t_parity l2 = True"
  shows " even (length l1) = even (length l2)"
  sorry

(* mi19436_Ana_Bolovic_FORMULACIJA *)
definition oriented_angle :: "('a set \<times> 'a set) \<Rightarrow> bool" where
"oriented_angle pq \<longleftrightarrow> (\<exists>p' q'. pq = (p', q') \<or> pq = (q', p'))"

(* mi19436_Ana_Bolovic_FORMULACIJA *)
definition convex_angle :: "('a set \<times> 'a set) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"convex_angle pq C P Q \<longleftrightarrow>
  (C \<noteq> P) \<and> (C \<noteq> Q) \<and> (P \<noteq> Q) \<and>
  (C \<in> fst pq) \<and>
  (C \<in> snd pq) \<and>
  (\<forall> R. R \<in> fst pq \<longrightarrow> ((bet C R P) \<or> (bet C P R))) \<and>
  (\<forall> S. S \<in> snd pq \<longrightarrow> ((bet C S Q) \<or> (bet C Q S)))"

(* mi19436_Ana_Bolovic_FORMULACIJA *)
definition parallel_angle :: "('a set \<times> 'a set) \<Rightarrow> ('a set \<times> 'a set) \<Rightarrow> bool" where
"parallel_angle pq p'q' \<longleftrightarrow>
  (oriented_angle pq) \<and>
  (oriented_angle p'q') \<and>
  (\<forall>C C' P Q P' Q'. P \<in> fst pq \<and>
                    Q \<in> snd pq \<and>
                    convex_angle pq C P Q \<and> 
                    convex_angle pq C' P' Q')" (* \<and> 
                    same_direction_triangle[(C,P,Q), (C', P', Q')])" *)

(* mi19436_Ana_Bolovic_FORMULACIJA *)
definition opposite_angle :: "('a set \<times> 'a set) \<Rightarrow> ('a set \<times> 'a set) \<Rightarrow> bool" where
"opposite_angle pq p'q' \<longleftrightarrow>  \<not> parallel_angle pq p'q'"

(* mi19209_Pavle_Ciric_FORMULACIJA *)
(* Nadovezani tetraedri *)
fun attached_tthd :: "('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "attached_tthd (A\<^sub>0, A\<^sub>1, A\<^sub>2, A\<^sub>3) (B\<^sub>0, B\<^sub>1, B\<^sub>2, B\<^sub>3) \<longleftrightarrow> A\<^sub>1 = B\<^sub>0 \<and> A\<^sub>2 = B\<^sub>1 \<and> A\<^sub>3 = B\<^sub>2"

(* mi19209_Pavle_Ciric_FORMULACIJA *)
(* Lanac orijentisanih tetraedara *)
fun tthd_oriented_chain :: "('a \<times> 'a \<times> 'a \<times> 'a) list \<Rightarrow> bool" where
  "tthd_oriented_chain [] = True"
| "tthd_oriented_chain [A] = True"
| "tthd_oriented_chain (A # B # lst) \<longleftrightarrow> 
    (attached_tthd A B) \<and> (tthd_oriented_chain (B # lst))"

(* mi19209_Pavle_Ciric_FORMULACIJA *)
(* Pocetak lanca *)
definition first_tthd_in_chain :: "('a \<times> 'a \<times> 'a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a)" where
  "first_tthd_in_chain chain = hd chain"

(* mi19209_Pavle_Ciric_FORMULACIJA *)
(* Kraj lanca *)
definition last_tthd_in_chain :: "('a \<times> 'a \<times> 'a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a)" where
  "last_tthd_in_chain chain = last chain"

(* mi19209_Pavle_Ciric_FORMULACIJA *)
(* Zatvoreni lanac orijentisanih tetraedara *)
definition closed_tthd_chain :: "('a \<times> 'a \<times> 'a \<times> 'a) list \<Rightarrow> bool" where
  "closed_tthd_chain chain \<equiv> (tthd_oriented_chain) chain \<and> 
                              (last_tthd_in_chain chain = first_tthd_in_chain chain)"

(* mi19209_Pavle_Ciric_FORMULACIJA *)
(* Lanac povezuje tetraedre *)
definition tthds_connected :: "('a \<times> 'a \<times> 'a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "tthds_connected chain t\<^sub>1 t\<^sub>2 \<equiv> (tthd_oriented_chain chain) \<and> 
                                 (first_tthd_in_chain chain = t\<^sub>1) \<and>
                                 (last_tthd_in_chain chain = t\<^sub>2)"

(* mi19240_Mina_Zivic_FORMULACIJA *)
definition connect1 :: "('a \<times> 'a \<times> 'a \<times> 'a) list \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "connect1 ts t\<^sub>1 t\<^sub>2 \<equiv> (first_tthd_in_chain ts = t\<^sub>1) \<and> 
  (last_tthd_in_chain  ts = t\<^sub>2) \<and> (tthd_oriented_chain ts)"



(* mi19240_Mina_Zivic_FORMULACIJA *)
(* preorijentacija tetraedra *)
fun connect__1 :: "('a × 'a × 'a × 'a) ⇒('a × 'a × 'a × 'a) ⇒ bool" where
  "connect__1 (A⇩0, A⇩1, A⇩2, A⇩3) (B⇩0, B⇩1, B⇩2, B⇩3)
 ⟷ A⇩1 = B⇩0 ∧ A⇩2 = B⇩1 ∧ A⇩3 = B⇩2"

fun preorientation_1 :: "('a × 'a × 'a × 'a) ⇒('a × 'a × 'a × 'a) ⇒ bool" where
"preorientation_1  (A⇩0, A⇩1, A⇩2, A⇩3) (B⇩0, B⇩1, B⇩2, B⇩3) ⟷ connect__1 (A⇩0, A⇩1, A⇩2, A⇩3) (B⇩0, B⇩1, B⇩2, B⇩3) ∧
 same_side_pl (plane A⇩1 A⇩2 A⇩3) A⇩0 B⇩3"

(* mi19240_Mina_Zivic_FORMULACIJA *)
(* parnost lanca tetraedra *)
fun parity_1 :: "('a \<times> 'a \<times> 'a \<times> 'a) list \<Rightarrow> bool" where
  "parity_1 (a\<^sub>1 # a\<^sub>2 # as) = (if preorientation a\<^sub>1 a\<^sub>2
 then \<noteq> parity_1 ( a\<^sub>2 # as)
 else parity_1 ( a\<^sub>2 # as))" |
"parity_1 _ = True"


(* mi19240_Mina_Zivic_FORMULACIJA *)
(* funkcija b *)
definition fun_b :: "'a ⇒ 'c ⇒ 'a ⇒ int" where
  "fun_b a α b = (if same_side_pl α a b then 1 else 
if opposite_sides_pl α a b then -1 else 0)"

(* mi19240_Mina_Zivic_FORMULACIJA *)
(* prva osobina funkcije b *)
theorem fun_b_first_property:
  assumes "\<not> inc_p_pl A \<alpha>"
  assumes "\<not> inc_p_pl B \<alpha>"
  assumes "\<not> inc_p_pl C \<alpha>" 
  shows "fun_b A \<alpha> B = -1" "fun_b B \<alpha> C = -1" "fun_b C \<alpha> A = -1"
  sorry

(*mi19079_Jelena_Zaric_FORMULACIJA*)
(*Zatvoreni lanci su parni*)
theorem t9_11:
  assumes "length chain > 1" "closed_tthd_chain chain"
  shows "parity_1 chain"

(*mi19079_Jelena_Zaric_FORMULACIJA*)
(*Lanci koji imaju zajednicki i pocetak i kraj, iste su parnosti*)
theorem t9_12:
  assumes "length chain > 1" "length chain' > 1" 
  assumes "first_tthd_in_chain chain = first_tthd_in_chain chain'" "last_tthd_in_chain chain = last_tthd_in_chain chain'"
    shows "parity_1 chain = parity_1 chain'"
  
(*mi19079_Jelena_Zaric_FORMULACIJA*)
(*Definija istosmernih tetraedara*)
definition same_direction_tetrahedron :: "('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "same_direction_tetrahedron t\<^sub>1 t\<^sub>2 = (\<forall> chain. length chain > 1 \<and> tthds_connected chain t\<^sub>1 t\<^sub>2 \<and> parity_1 chain)"




end
end
