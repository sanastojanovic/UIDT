theory drugi_seminarski
  imports Complex_Main

begin

section "Glavna definicija"

type_synonym 'a word = "'a list"
type_synonym 'a lang = "'a word set"

text "Eksplicitno navođenje skupa terminala i skupa neterminala nije potrebno,
jer tipovi 'n i 't 'određuju' ta dva skupa."

record ('n, 't) cfg =
  init :: "'n"
  prod :: "'n \<Rightarrow> ('t + 'n) lang"

inductive derives where
derives_self:  "derives G \<alpha> \<alpha>" |
derives_step: "derives G s1 (s2 @ (Inr left # s3)) 
             \<and> right \<in> (prod G left) \<Longrightarrow> derives G s1 (s2 @ right @ s3)"

text "Iz induktivne definicije `derives` ne može da se izvede kod, 
ali se za konkretne vrednosti može dokazati da izvode jedna drugu."

code_pred derives . (* Ovde ne izlazi greška, ali derives.equation ostaje prazno *)

thm derives.equation

definition list_inl :: "'a list \<Rightarrow> ('a + 'b) list" where
  "list_inl xs = map (\<lambda> x. Inl x) xs"

definition list_deinl :: "('a + 'b) list \<Rightarrow> 'a list" where
  "list_deinl xs = map (\<lambda> x . projl x) xs"

lemma list_inl_inverse:
  "x = list_deinl (list_inl x)"
  unfolding list_deinl_def list_inl_def
  by (simp add: nth_equalityI)

text "Prethodne dve definicije olakšavaju rad sa Sum tipovima."

definition generates :: "('n, 't) cfg \<Rightarrow> ('t + 'n) word \<Rightarrow> bool" where
  "generates G s = derives G [Inr (init G)] s"

definition produces :: "('n, 't) cfg \<Rightarrow> 't word \<Rightarrow> bool" where
  "produces G w = derives G [Inr (init G)] (list_inl w)"

inductive derive_list where
  dl_empty: "derive_list G []"
| dl_start: "derive_list G [s]"
| dl_step:  "derive_list G l \<and> l \<noteq> [] \<and>
             (last l) = (s2 @ (Inr left # s3)) \<and> 
             right \<in> (prod G left) \<Longrightarrow> derive_list G (l @ [s2 @ right @ s3])"

text "Nekada je prikladnije da se koristi `derive_list` umesto `derives`.
One su ekvivalentne, pa je to moguće."

lemma derives_list:
  fixes G :: "('n, 't) cfg"
  fixes s1 s2 :: "('t + 'n) word"
  shows "derives G s1 s2 \<longleftrightarrow> 
        (\<exists>l. derive_list G l \<and> 
             l \<noteq> [] \<and> 
             (hd l) = s1 \<and> 
             (last l) = s2)" (is "?l \<longleftrightarrow> ?d")
proof
  show "?l \<Longrightarrow> ?d"
  proof (induction rule: derives.induct)
    case (derives_self G \<alpha>)
    then show ?case
      by (meson dl_start last_ConsL list.discI list.sel(1))
  next
    case (derives_step G s1 s2 left s3 right)
    have "derives G s1 (s2 @ right @ s3)"
      by (meson derives.derives_step derives_step.IH)
    then obtain l1 :: "('t + 'n) word list" where
        "l1 \<noteq> []"
        "derive_list G l1" 
        "hd l1 = s1"
        "last l1 = (s2 @ Inr left # s3)"
      using derives_step.IH by blast
    then have "derive_list G (l1 @ [s2 @ right @ s3])"
      using derives_step.IH
      by (meson dl_step)
    then show ?case
      using \<open>hd l1 = s1\<close> \<open>l1 \<noteq> []\<close> by auto
  qed
next
  show "?d \<Longrightarrow> ?l"
  proof-
    assume "?d"
    from this obtain l :: "('t + 'n) word list" where
        "derive_list G l" 
        "l \<noteq> []"
        "hd l = s1"
        "last l = s2"
      by blast
    then show ?thesis
    proof (induction arbitrary: "s1" "s2"  rule: derive_list.induct)
      case (dl_empty G)
      then show ?case
        by blast
    next
      case (dl_start G s)
      then show ?case
        by (simp add: derives_self)
    next
      case (dl_step G l1 s3 left s4 right)
      then show ?case
        using derives_step by fastforce
    qed
  qed
qed

section "Primer"

subsection "Primer gramatike"

datatype t = a | b
datatype nt = S

fun prod_palindrome :: "nt \<Rightarrow> (t + nt) lang" where
  "prod_palindrome S = {[Inl a, Inr S, Inl a],
                        [Inl b, Inr S, Inl b],
                        [Inl a],
                        [Inl b],
                        []}"

definition palindrome_cfg :: "(nt, t) cfg" where
  "palindrome_cfg = make S prod_palindrome"

value "print_record palindrome_cfg"

lemma prod_palindrome[simp]:
  "prod palindrome_cfg \<equiv> prod_palindrome"
  using palindrome_cfg_def make_def by (smt select_convs(2))

lemma init_palindrome[simp]:
  "init palindrome_cfg \<equiv> S"
  by (smt nt.exhaust)

lemma produces_aa:
  "produces palindrome_cfg [a, a]"
  unfolding produces_def
proof-
  have "list_inl [a, a] = [Inl a, Inl a]"
    by (simp add: list_inl_def)
  have "derive_list palindrome_cfg [[Inr S]]"
    by (simp add: dl_start)
  then have "derive_list palindrome_cfg [[Inr S], [Inl a, Inr S, Inl a]]"
    using dl_step[of palindrome_cfg "[[Inr S]]" "[]" "S" "[]" "[Inl a, Inr S, Inl a]"]
    by simp
  then have "derive_list palindrome_cfg [[Inr S], [Inl a, Inr S, Inl a], [Inl a, Inl a]]"
    using dl_step[of palindrome_cfg "[[Inr S], [Inl a, Inr S, Inl a]]" "[Inl a]" "S" "[Inl a]" "[]"]
    by simp
  then have "derives palindrome_cfg [Inr S] [Inl a, Inl a]"
    using derives_list
    by fastforce
  then show "derives palindrome_cfg [Inr (init palindrome_cfg)] (list_inl [a, a])"
    by (simp add: \<open>list_inl [a, a] = [Inl a, Inl a]\<close>)
qed

subsection "Palindrom - induktivno"

text "Palindrom se može definisati sa `x = rev x`, ali je sa induktivnom definicijom
lakše raditi."

inductive pally where
  pally_empty: "pally []"
| pally_start: "pally [s]"
| pally_step: "pally l \<Longrightarrow> pally (x # l @ [x])"

lemma pally_split:
  "pally l \<Longrightarrow> \<exists>l1 l2 l3. l = l1 @ l2 @ l3 \<and> l1 = rev l3 \<and> length l2 \<le> 1"
proof (induction rule: pally.induct)
case pally_empty
  then show ?case by auto
next
  case (pally_start s)
  then show ?case
    by (metis One_nat_def append_Cons append_Nil 
        length_Cons list.size(3) order_refl rev.simps(1))
next
  case (pally_step l x)
  from this obtain l1 l2 l3 where "l = l1 @ l2 @ l3" "l1 = rev l3" "length l2 \<le> 1"
    by auto
  then have "x # l @ [x] = (x # l1) @ l2 @ (l3 @ [x])"
    by auto
  moreover have "x # l1 = rev (l3 @ [x])"
    by (simp add: \<open>l1 = rev l3\<close>)
  then show ?case
    using \<open>length l2 \<le> 1\<close> calculation by blast
qed

lemma pally_rev:
  "pally l \<longleftrightarrow> (l = rev l)" (is "?l \<longleftrightarrow> ?d")
proof
  show "?l \<Longrightarrow> ?d"
  proof (induction rule: pally.induct)
    case pally_empty
    then show ?case by auto
  next
    case (pally_start s)
    then show ?case by auto
  next
    case (pally_step l)
    then show ?case by auto
  qed
next
  show "?d \<Longrightarrow> ?l"
  proof (induction "length l" arbitrary: l rule: nat_less_induct)
    case 1
    assume "l = rev l"
    then show ?case
    proof (cases "l = []")
      case True
      then show ?thesis using pally_empty by auto
    next
      case False
      have "hd l = last l"
        using hd_rev \<open>l = rev l\<close> False by fastforce
      then have "tl (butlast l) = rev (tl (butlast l))"
        by (metis "1.prems" butlast_rev butlast_tl rev_swap)
      moreover have "length (tl (butlast l)) < length l"
        using False by auto
      ultimately have "pally (tl (butlast l))"
        using 1 by blast
      then have "pally ((hd l) # (tl (butlast l)) @ [hd l])"
        by (simp add: pally_step)
      have "l = hd l # (tl l)"
        by (simp add: False)
      moreover have "l = (butlast l) @ [last l]"
        by (simp add: False)
      ultimately have "l = hd l # (tl ((butlast l) @ [hd l]))"
        using \<open>hd l = last l\<close> by auto
      then show ?thesis
        by (metis \<open>l = butlast l @ [last l]\<close> 
            \<open>pally (hd l # tl (butlast l) @ [hd l])\<close> 
            append_Nil pally_start tl_append2)
    qed
  qed
qed

lemma rev_half_palindrome:
  "l1 = rev l3 \<Longrightarrow> 
  generates palindrome_cfg (list_inl l1 @ Inr S # list_inl l3)"
  unfolding generates_def init_palindrome
proof (induct "length l1" arbitrary: "l1" "l3")
  case 0
  then show ?case
    by (metis \<open>l1 = rev l3\<close> append_Nil derives_self length_0_conv list.simps(8) list_inl_def rev.simps(1) rev_rev_ident)
next
  case (Suc xa)
  then have "length (list_inl (butlast l1)) = xa"
    using list_inl_def length_Suc_conv by fastforce
  moreover have "butlast l1 = rev (tl l3)"
    using butlast_rev \<open>l1 = rev l3\<close> by auto
  ultimately have "derives palindrome_cfg [Inr S] 
    (list_inl (butlast l1) @ Inr S # list_inl (tl l3))"
    by (smt Suc.hyps(1) length_map list_inl_def)
  then have "derives palindrome_cfg [Inr S]
            (list_inl (butlast l1) @ 
            [Inl (last l1), Inr S, Inl (hd l3)] @ 
            list_inl (tl l3))"
    using derives_step[of 
        palindrome_cfg 
        "[Inr S]" 
        "list_inl (butlast l1)" 
        "S" 
        "list_inl (tl l3)" 
        "[Inl (last l1), Inr S, Inl (hd l3)]"]
    by (smt Suc.hyps(2) Suc.prems insert_iff last_rev 
        length_greater_0_conv prod_palindrome 
        prod_palindrome.simps rev.simps(1) t.exhaust zero_less_Suc)
  moreover have "list_inl l1 = (list_inl (butlast l1)) @ [Inl (last l1)]"
    by (metis Suc.hyps(2) append_butlast_last_id length_greater_0_conv 
        list.simps(8) list.simps(9) list_inl_def map_append zero_less_Suc)
  moreover have "list_inl l3 = Inl (hd l3) # (list_inl (tl l3))"
    by (metis Suc.hyps(2) Suc.prems hd_Cons_tl length_greater_0_conv 
        list.simps(9) list_inl_def rev.simps(1) zero_less_Suc)
  ultimately show ?case
    by (simp add: \<open>list_inl l1 = list_inl (butlast l1) @ [Inl (last l1)]\<close> 
                  \<open>list_inl l3 = Inl (hd l3) # list_inl (tl l3)\<close>)
qed

subsection "Leme o count_list"

lemma count_in:
  "x \<in> set l \<Longrightarrow> count_list l x > 0"
proof (induction "length l" arbitrary: l)
case 0
  then show ?case
    by auto
next
  case (Suc xa)
  then show ?case
    by (smt add.left_neutral add_diff_cancel_right' 
        count_list.simps(2) gr0I insert_iff length_Suc_conv 
        length_tl list.sel(2) list.set(2) list.size(3) zero_less_one)
qed

lemma count_sum:
  "count_list l1 x + count_list l2 x = count_list (l1 @ l2) x"
  by (induction l1) auto

lemma count_one_split:
  "count_list l x = 1 \<and> l = l1 @ x # l2 \<and> l = l3 @ x # l4 \<Longrightarrow> l1 = l3 \<and> l2 = l4"
  apply (erule conjE)
proof (induction l arbitrary: l1 l2 l3 l4)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
  proof (cases "a = x")
    case True
    then show ?thesis
      by (metis Cons.prems(1) Cons.prems(2) add_diff_cancel_right' 
          append_eq_append_conv2 append_self_conv 
          cancel_comm_monoid_add_class.diff_cancel count_in 
          count_list.simps(2) in_set_conv_decomp 
          less_numeral_extra(3) list.sel(3) tl_append2)
  next
    case False
    then show ?thesis
      by (metis Cons.IH Cons.prems(1) Cons.prems(2) append_same_eq 
          count_list.simps(2) list.inject list.sel(3) 
          self_append_conv2 tl_append2)
  qed
qed

subsection "Pomoćne leme"

lemma palindrome_S_unique:
  "derives G s1 l \<and> G = palindrome_cfg \<and> s1 = [Inr S] \<Longrightarrow> 
    count_list l (Inr S) \<le> 1"
  apply (erule conjE)
proof (induction rule: derives.induct)
  case (derives_self G \<alpha>)
  then show ?case
    by simp
next
  case (derives_step G s1 s2 left s3 right)
  then have "left = S"
    using nt.exhaust by blast
  then have "Inr S \<in> set (s2 @ Inr left # s3)"
    by simp
  then have "count_list (s2 @ Inr left # s3) (Inr S) = 1"
    by (metis One_nat_def antisym count_in derives_step.IH derives_step.prems le_zero_eq length_greater_0_conv list.size(3) not_less_eq_eq)
  have "right \<in> {[Inl a, Inr S, Inl a],
                 [Inl b, Inr S, Inl b],
                 [Inl a], [Inl b], []}"
    using derives_step prod_palindrome \<open>left = S\<close> prod_palindrome.simps
    by simp
  then have "count_list right (Inr S) \<le> 1"
    by force
  have "count_list s2 (Inr S) + count_list (Inr left # s3) (Inr S) = 1"
    by (metis \<open>count_list (s2 @ Inr left # s3) (Inr S) = 1\<close> count_sum)
  then have "count_list s2 (Inr S) = 0"
    by (simp add: \<open>left = S\<close>)
  moreover have "count_list s3 (Inr S) = 0"
    using \<open>count_list s2 (Inr S) + count_list (Inr left # s3) (Inr S) = 1\<close> \<open>left = S\<close> by auto
  then show ?case
    by (metis \<open>count_list right (Inr S) \<le> 1\<close> append_Nil2 calculation count_sum plus_nat.add_0)
qed

lemma palindrome_rev_half:
  "derives G s1 l \<and> G = palindrome_cfg \<and> s1 = [Inr S] \<and> l = (l1 @ Inr S # l3) \<Longrightarrow> l1 = rev l3"
  apply (erule conjE)
proof (induction arbitrary: l1 l3 rule: derives.induct)
  case (derives_self G \<alpha>)
  then show ?case
    by (metis Nil_is_append_conv Nil_is_rev_conv butlast.simps(2) butlast_append list.distinct(1))
next
  case (derives_step G s1 s2 left s3 right)
  then have "s2 = rev s3"
    using nt.exhaust by blast
  have "left = S"
    using nt.exhaust by blast
  then have "count_list (s2 @ Inr left # s3) (Inr S) \<le> 1"
    using derives_step.IH derives_step.prems palindrome_S_unique by blast
  moreover have "count_list (s2 @ Inr left # s3) (Inr S) > 0"
    by (simp add: \<open>left = S\<close> count_in)
  ultimately have "count_list (s2 @ Inr left # s3) (Inr S) = 1"
    by linarith
  then have "count_list s2 (Inr S) = 0"
    by (metis \<open>left = S\<close> add_le_same_cancel1 count_in count_sum less_one list.set_intros(1) not_le)
  then have "count_list s3 (Inr S) = 0"
    by (metis \<open>count_list (s2 @ Inr left # s3) (Inr S) = 1\<close> \<open>left = S\<close> add_cancel_right_left count_list.simps(2) count_sum)
  have "derives G s1 (s2 @ right @ s3)"
    by (meson derives.derives_step derives_step.IH)
  then have "count_list (s2 @ right @ s3) (Inr S) \<le> 1"
    using derives_step.prems palindrome_S_unique by blast
  moreover have "count_list (s2 @ right @ s3) (Inr S) > 0"
    by (simp add: count_in derives_step.prems)
  ultimately have "count_list (s2 @ right @ s3) (Inr S) = 1"
    by linarith
  then have "count_list right (Inr S) = 1"
    by (metis \<open>count_list s2 (Inr S) = 0\<close> \<open>count_list s3 (Inr S) = 0\<close> add.commute add.right_neutral count_sum)
  moreover have "right \<in> {[Inl a, Inr S, Inl a],
                 [Inl b, Inr S, Inl b],
                 [Inl a], [Inl b], []}"
    using derives_step prod_palindrome \<open>left = S\<close> prod_palindrome.simps
    by simp
  then have "right = [Inl a, Inr S, Inl a] \<or> right = [Inl b, Inr S, Inl b]"
    apply (normalization)
    using calculation by force
  from this obtain x where "right = [Inl x, Inr S, Inl x]"
    by auto
  then have "l1 @ Inr S # l3 = s2 @ [Inl x] @ Inr S # Inl x # s3"
    using derives_step.prems by auto
  moreover have "count_list (l1 @ Inr S # l3) (Inr S) = 1"
    using \<open>count_list (s2 @ right @ s3) (Inr S) = 1\<close> derives_step.prems by auto
  ultimately have "l1 = s2 @ [Inl x] \<and> l3 = Inl x # s3"
    by (metis append.assoc count_one_split)
  then show ?case
    by (simp add: \<open>s2 = rev s3\<close>)
qed

subsection "Dokaz glavne teoreme"

text "Pokušavamo da dokažemo `produces palindrome_cfg w = pally w`"

lemma palindrome_cfl_left:
  fixes w :: "t word"
  shows "pally w \<Longrightarrow> produces palindrome_cfg w"
proof-
  assume "pally w"
  then obtain l1 l2 l3 where "w = l1 @ l2 @ l3" "l1 = rev l3" "length l2 \<le> 1"
    using \<open>pally w\<close> pally_split by blast
  then have "l2 = [] \<or> l2 = [a] \<or> l2 = [b]"
    by (metis (full_types) One_nat_def antisym le_zero_eq length_0_conv length_Suc_conv not_less_eq_eq t.exhaust)
  then have "(list_inl l2) \<in> (prod palindrome_cfg S)"
    unfolding prod_palindrome
    by (metis (no_types, lifting) insert_iff list.simps(8) list.simps(9) list_inl_def prod_palindrome.simps)
  moreover have "derives palindrome_cfg [Inr S] ((list_inl l1) @ Inr S # (list_inl l3))"
    using \<open>l1 = rev l3\<close> rev_half_palindrome
    by (simp add: generates_def)
  ultimately have "derives palindrome_cfg [Inr S] ((list_inl l1) @ (list_inl l2) @ (list_inl l3))"
    using derives_step by fastforce
  moreover have "(list_inl l1) @ (list_inl l2) @ (list_inl l3) = (list_inl w)"
    by (simp add: \<open>w = l1 @ l2 @ l3\<close> list_inl_def)
  ultimately show ?thesis
    by (simp add: \<open>list_inl l1 @ list_inl l2 @ list_inl l3 = list_inl w\<close> produces_def)
qed

lemma derives_pally_induction:
  fixes w :: "(t + nt) word"
  shows "derives G s1 w \<and> G = palindrome_cfg \<and> s1 = [Inr S] \<Longrightarrow> pally w"
  apply (erule conjE)
proof (induction rule: derives.induct)
  case (derives_self G \<alpha>)
  then show ?case
    by (simp add: pally_start)
next
  case (derives_step G s1 s2 left s3 right)
  then have "left = S"
    using nt.exhaust by blast
  then have "s2 = rev s3"
    using derives_step.IH derives_step.prems palindrome_rev_half by blast
  have "right \<in> {[Inl a, Inr S, Inl a],
                 [Inl b, Inr S, Inl b],
                 [Inl a], [Inl b], []}"
    using derives_step prod_palindrome \<open>left = S\<close> prod_palindrome.simps
    by simp
  then have "pally right"
    apply (normalization)
    using pally_empty pally_start pally_step by fastforce
  then show ?case
    by (simp add: \<open>s2 = rev s3\<close> pally_rev)
qed

lemma derives_pally:
  "derives palindrome_cfg [Inr S] w \<Longrightarrow> pally w"
  using derives_pally_induction by blast

lemma pally_map:
  "pally x \<Longrightarrow> pally (map f x)"
  by (simp add: pally_rev rev_map)

lemma palindrome_cfl_right:
  shows "produces palindrome_cfg w  \<Longrightarrow> pally w"
proof-
  assume "produces palindrome_cfg w"
  then have "derives palindrome_cfg [Inr S] (list_inl w)"
    by (simp add: produces_def)
  moreover obtain s :: "(t + nt) word" where "s = (list_inl w)"
    by simp
  ultimately have "pally s"
    by (simp add: derives_pally)
  then have "w = list_deinl s"
    by (simp add: \<open>s = list_inl w\<close> list_inl_inverse)
  then show ?thesis
    by (simp add: \<open>pally (s::(t + nt) list)\<close> list_deinl_def pally_map)
qed

theorem palindrome_cfl:
  "produces palindrome_cfg w = pally w"
  using palindrome_cfl_left palindrome_cfl_right by blast
